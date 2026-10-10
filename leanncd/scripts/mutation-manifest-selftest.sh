#!/usr/bin/env bash
# Test mutation-manifest.sh's validation scope, task diagnostics, and run path without Lean.
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

    def check(name, entries, status, text, *filters, exact_error=False):
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
            require((result.stderr == text if exact_error else text in result.stderr) and not result.stdout,
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

    for value in [1, 1.0, True, False, None, [], {}]:
        for filters in [(), ("--task", "1"), ("task1-",)]:
            check(f"global task schema: {value!r}, {filters}", [first, {**second, "task": value}],
                  125, "'task' must be a string", *filters)
    check("global task schema precedes unknown task hint", [first, {**second, "task": None}],
          125, "'task' must be a string", "--task", "unknown")

    no_task = {k: v for k, v in first.items() if k != "task"}
    single = "manifest OK: 1 entries, 1 selected, every old-string unique\n"
    check("task field is optional without filters", [no_task], 0, single)
    check("task field is optional with prefix selection", [no_task], 0, single, "task1-")
    check("missing task is not the string None", [no_task], 125,
          "error: no manifest entries selected: unknown task 'None'; available tasks: (none)\n",
          "--task", "None", exact_error=True)
    check("explicit string None remains selectable", [{**first, "task": "None"}],
          0, single, "--task", "None")
    check("task strings are exact, not parsed as numbers", [{**first, "task": "01"}, second],
          0, filtered, "--task", "01")
    check("unknown numeric-looking task lists exact strings", [{**first, "task": "01"}, second],
          125, "error: no manifest entries selected: unknown task '1'; available tasks: '01', '2'\n",
          "--task", "1", exact_error=True)

    task_ids = [{**second, "task": "T2"}, {**first, "task": "T1"},
                {**first, "label": "another-T2", "task": "T2"}, {**no_task, "label": "taskless"}]
    hint = "error: no manifest entries selected: unknown task 'unknown'; available tasks: 'T1', 'T2'\n"
    check("unknown task hint is sorted, unique, and omits taskless entries", task_ids,
          125, hint, "--task", "unknown", exact_error=True)
    check("unknown task hint ignores prefix and future filesystem state", task_ids,
          125, hint, "--task", "unknown", "task1-", exact_error=True)
    check("empty manifest has no available tasks", [], 125,
          "error: no manifest entries selected: unknown task 'unknown'; available tasks: (none)\n",
          "--task", "unknown", exact_error=True)
    check("known task excluded by prefix is not called unknown", [first, second], 125,
          "error: no manifest entries selected\n", "--task", "1", "task2-", exact_error=True)
    check("prefix-only empty selection keeps its diagnostic", [first, second], 125,
          "error: no manifest entries selected\n", "unknown-", exact_error=True)

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
