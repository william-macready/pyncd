#!/usr/bin/env bash
# Test mutation-manifest.sh's validation scope and run path without Lean.
# Usage: bash leanncd/scripts/mutation-manifest-selftest.sh

set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)

exec python3 - "$script_dir" <<'PY'
import json, os, pathlib, shutil, subprocess, sys, tempfile

script = pathlib.Path(sys.argv[1]) / "mutation-manifest.sh"
checks = 0

def require(condition, message):
    if not condition:
        sys.exit(f"FAIL: {message}")

with tempfile.TemporaryDirectory(prefix="mutation-manifest-selftest-") as tmp:
    root = pathlib.Path(tmp)
    (root / "real.lean").write_text("first needle\nsecond needle\nrepeated needle\nrepeated needle\n")
    manifest = root / "manifest.json"
    first = dict(label="task1-first", task="1", file="real.lean", old="first needle",
                 new="changed needle", targets=["Stub.Target"], expect=["intended failure"])
    second = dict(label="task2-missing", task="2", file="missing.lean", old="future needle",
                  new="changed needle", targets=["Stub.Future"])
    filtered = ("manifest OK: 2 entries, 1 selected; 1 outside the selection not validated; "
                "every selected old-string unique\n")
    unfiltered = "manifest OK: 2 entries, 2 selected, every old-string unique\n"

    def check(name, entries, status, text, *filters):
        global checks
        manifest.write_text(json.dumps(entries))
        options = filters[:2] if filters[:1] == ("--task",) else ()
        result = subprocess.run(["bash", str(script), "--check", *options, str(root), str(manifest),
                                 *filters[len(options):]],
                                capture_output=True, text=True)
        require(result.returncode == status,
                f"{name}: expected exit {status}, got {result.returncode}\n"
                f"stdout: {result.stdout}stderr: {result.stderr}")
        if status == 0:
            require(result.stdout == text and not result.stderr,
                    f"{name}: unexpected output\nstdout: {result.stdout}stderr: {result.stderr}")
        else:
            require(text in result.stderr and not result.stdout,
                    f"{name}: missing diagnostic {text!r}\n"
                    f"stdout: {result.stdout}stderr: {result.stderr}")
        checks += 1
        print(f"PASS: {name}", flush=True)

    for name, future, problem in [
        ("missing file", second, "no such file missing.lean"),
        ("non-unique old-string", {**second, "label": "task2-repeated", "file": "real.lean",
                                  "old": "repeated needle"}, "old-string occurs 2 times"),
        ("absent old-string", {**second, "label": "task2-absent", "file": "real.lean"},
         "old-string occurs 0 times"),
    ]:
        entries = [first, future]
        check(f"{name}: unfiltered rejects task 2", entries, 125, problem)
        check(f"{name}: task 1 ignores future text", entries, 0, filtered, "--task", "1")
        check(f"{name}: task 2 rejects future text", entries, 125, problem, "--task", "2")
        check(f"{name}: task-1 prefix ignores future text", entries, 0, filtered, "task1-")
        check(f"{name}: task-2 prefix rejects future text", entries, 125, problem, "task2-")
        check(f"{name}: unknown task selects nothing", entries, 125,
              "no manifest entries selected", "--task", "unknown")

    schema_errors = [
        ("label", 42, "'label' must be a string"),
        ("label", [], "'label' must be a string"),
        ("file", None, "'file' must be a string"),
        ("old", 42, "'old' must be a string"),
        ("new", False, "'new' must be a string"),
        ("targets", [], "'targets' must be a non-empty list of strings"),
        ("targets", "Stub.Future", "'targets' must be a non-empty list of strings"),
        ("targets", [42], "'targets' must be a non-empty list of strings"),
        ("expect", "failure", "'expect' must be a list of strings"),
        ("expect", [42], "'expect' must be a list of strings"),
    ]
    for key, value, problem in schema_errors:
        entries = [first, {**second, key: value}]
        for filters in [("--task", "1"), ("task1-",)]:
            check(f"global schema: {key}={value!r}, {filters}", entries, 125, problem, *filters)
    check("global schema: non-object entry", [first, None], 125, "entry 1: not an object",
          "--task", "1")
    check("global schema precedes empty selection", [first, {**second, "targets": []}], 125,
          "'targets' must be a non-empty list of strings", "--task", "unknown")
    check("global duplicate labels across task boundary", [first, {**second, "label": first["label"]}],
          125, "duplicate label", "--task", "1")
    check("global duplicate labels with prefix filter", [first, {**second, "label": first["label"]}],
          125, "duplicate label", "task1-")

    healthy = {**second, "file": "real.lean", "old": "second needle"}
    check("unfiltered healthy output unchanged", [first, healthy], 0, unfiltered)
    check("prefix selecting all keeps output unchanged", [first, healthy], 0, unfiltered, "task")
    check("task selecting all keeps output unchanged", [first, {**healthy, "task": "1"}],
          0, unfiltered, "--task", "1")
    check("multiple prefixes form a union", [first, healthy], 0, unfiltered, "task1-", "task2-")
    check("task and prefix filters intersect", [first, healthy], 125, "no manifest entries selected",
          "--task", "1", "task2-")
    check("unknown prefix selects nothing before filesystem checks", [first, second], 125,
          "no manifest entries selected", "unknown-")
    check("empty manifest selects nothing", [], 125, "no manifest entries selected")

    stub_dir = root / "scripts"
    stub_dir.mkdir()
    shutil.copyfile(script, stub_dir / script.name)
    (stub_dir / "mutation-cycle.sh").write_text(
        '#!/usr/bin/env bash\nset -euo pipefail\n'
        'printf "%s\\n" "$@" >> "$MUTATION_CALLS"\n'
        'printf "%s\\n" "intended failure" > "$MUTATION_LOG"\n'
        'echo "stub cycle: $1"\nexit 0\n')
    other_first = {**first, "label": "task1-second", "old": "second needle"}
    del other_first["expect"]
    manifest.write_text(json.dumps([first, other_first, second]))
    calls = root / "calls"
    table_path = root / "table.md"
    result = subprocess.run(
        ["bash", str(stub_dir / script.name), "--task", "1", "--out", str(table_path),
         str(root), str(manifest)],
        env={**os.environ, "MUTATION_CALLS": str(calls)}, capture_output=True, text=True)
    require(result.returncode == 0 and not result.stderr,
            f"stub run: expected exit 0, got {result.returncode}\n"
            f"stdout: {result.stdout}stderr: {result.stderr}")
    expected_args = []
    for e in [first, other_first]:
        expected_args += [e["label"], str(root), e["file"], e["old"], e["new"], *e["targets"]]
    require(calls.read_text().splitlines() == expected_args,
            "stub run: selected entries or mutation-cycle arguments changed")
    table = (
        "| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |\n"
        "|---|---|---|---|---|\n"
        "| task1-first | yes | yes | yes | PASS |\n"
        "| task1-second | yes | yes | n/a | PASS |\n"
        "\n2/2 cycles passed.\n")
    banners = "".join(f"stub cycle: {e['label']}\n=== {e['label']} MANIFEST VERDICT: PASS ===\n"
                      for e in [first, other_first])
    require(result.stdout == banners + "\n" + table, f"stub run: unexpected table\n{result.stdout}")
    require(table_path.read_text() == table, "stub run: --out table differs from stdout")
    checks += 1
    print("PASS: stub run selects only task 1, preserves arguments, restore/expect checks, and table")

print(f"mutation-manifest selftest: {checks} checks passed")
PY
