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

    # Schema and filesystem problems arrive in ONE pass, in entry order (an author fixing a
    # manifest should not need one round trip per class of problem).
    bad_targets = {**first, "targets": []}
    schema_0 = "entry 0 (task1-first): 'targets' must be a non-empty list of strings\n"
    fs_1 = "entry 1 (task2-missing): no such file missing.lean\n"
    check("single pass: unfiltered reports schema and filesystem problems together",
          [bad_targets, second], 125, schema_0 + fs_1, exact_error=True)
    check("single pass: filtered check still reports global schema plus selected filesystem",
          [bad_targets, second], 125, schema_0 + fs_1, "--task", "2", exact_error=True)
    check("single pass: filesystem problems of unselected entries stay unreported",
          [bad_targets, second], 125, schema_0, "--task", "1", exact_error=True)
    check("single pass: duplicate label precedes the same entry's filesystem problem",
          [first, {**second, "label": first["label"]}], 125,
          "entry 1 (task1-first): duplicate label\nentry 1 (task1-first): no such file missing.lean\n",
          exact_error=True)
    check("single pass: entry order wins over discovery order (disk problem before schema problem)",
          [second, bad_targets], 125,
          fs_1.replace("entry 1", "entry 0") + schema_0.replace("entry 0", "entry 1"),
          exact_error=True)
    check("single pass: problems within one entry keep discovery order, not alphabetical order",
          [{**first, "targets": [], "expect": "failure"}], 125,
          "entry 0 (task1-first): 'targets' must be a non-empty list of strings\n"
          "entry 0 (task1-first): 'expect' must be a list of strings\n", exact_error=True)
    check("single pass: non-string label is still located by index and checked on disk",
          [{**second, "label": 42}], 125,
          "entry 0 (42): 'label' must be a string\nentry 0 (42): no such file missing.lean\n",
          exact_error=True)
    check("single pass: non-object entry does not hide a later filesystem problem",
          [None, second], 125, "entry 0: not an object\n" + fs_1, exact_error=True)
    check("single pass: unselectable label under a prefix filter cannot crash selection",
          [{**second, "label": 42}, first], 125, "entry 0 (42): 'label' must be a string\n",
          "task1-", exact_error=True)
    check("task schema error names the offending value and how to fix it",
          [first, {**second, "task": 2}], 125,
          "entry 1 (task2-missing): 'task' must be a string (got 2); "
          "quote task ids, e.g. \"task\": \"2\"\n" + fs_1, exact_error=True)

    # Unreadable inputs and flags without values are diagnosed, never a Python traceback.
    (root / "bad.bin").write_bytes(b"ok \xff\xfe bad bytes")
    binary = dict(label="binary", task="3", file="bad.bin", old="ok", new="y", targets=["Stub.Binary"])
    not_utf8 = "entry {i} (binary): cannot read bad.bin: not valid UTF-8\n"
    check("non-UTF-8 file is a clean diagnostic", [binary], 125, not_utf8.format(i=0),
          exact_error=True)
    check("non-UTF-8 file is reported in entry order with other problems",
          [bad_targets, binary], 125, schema_0 + not_utf8.format(i=1), exact_error=True)
    check("non-UTF-8 file of an unselected entry is never read", [first, binary], 0, filtered,
          "--task", "1")
    locked = root / "locked.lean"
    locked.write_text("needle")
    locked.chmod(0)
    if os.access(locked, os.R_OK):  # root can read anything: skip rather than flake
        print("SKIP: unreadable file is a clean diagnostic (this user can read a mode-0 file)",
              flush=True)
    else:
        check("unreadable file is a clean diagnostic",
              [dict(binary, label="locked", file="locked.lean")], 125,
              "entry 0 (locked): cannot read locked.lean: Permission denied\n", exact_error=True)
    locked.chmod(0o644)

    def run_raw(*args):
        return subprocess.run(["bash", str(script), *args], capture_output=True, text=True)
    for flag in ("--task", "--out"):
        for lead in ((), ("--check",)):
            result = run_raw(*lead, flag)
            require(result.returncode == 1 and not result.stdout
                    and result.stderr == f"error: {flag} requires a value\n",
                    f"{flag} without a value after {lead}: got exit {result.returncode}\n"
                    f"stdout: {result.stdout}stderr: {result.stderr}")
            checks += 1
            print(f"PASS: {flag} without a value is a clean error ({' '.join(lead) or 'alone'})",
                  flush=True)

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

    for filters in [(), ("--task", "1")]:
        check(f"task ids starting with -- are refused (--task could not select them), {filters}",
              [first, {**second, "task": "--x"}], 125, "'task' must not start with '--'", *filters)

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
        'printf "\\377 stray non-UTF-8 byte in a build log\\n" >> "$MUTATION_LOG"\n'
        'echo "stub cycle: $1"\n'
        'printf "error: bad \\377 byte\\n"\n'
        'printf "warn \\377\\n" >&2\n'
        'exit 0\n')
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
    # The cycle's stdout and stderr carry a stray non-UTF-8 byte: shown as U+FFFD, never a traceback.
    banners = "".join(f"stub cycle: {e['label']}\nerror: bad \ufffd byte\nwarn \ufffd\n"
                      f"=== {e['label']} MANIFEST VERDICT: PASS ===\n" for e in [first, other_first])
    require(result.stdout == banners + "\n" + table, f"stub run: unexpected table\n{result.stdout}")
    require(table_path.read_text() == table, "stub run: --out table differs from stdout")
    checks += 1
    print("PASS: stub run selects only task 1, preserves arguments, restore/expect checks, and table")

    # Flags taking a value refuse a following flag; --out is validated before any cycle runs;
    # --cd without a value is a clean usage error.
    manifest.write_text(json.dumps([first]))
    stub_script = stub_dir / script.name
    calls2 = root / "calls2"

    def run_stub(*args, cwd=root):
        calls2.unlink(missing_ok=True)
        return subprocess.run(["bash", str(stub_script), *args], cwd=cwd,
                              env={**os.environ, "MUTATION_CALLS": str(calls2)},
                              capture_output=True, text=True)

    def refuses(name, result, status, stderr):
        global checks
        require(result.returncode == status and not result.stdout and result.stderr == stderr
                and not calls2.exists(),
                f"{name}: expected exit {status} with {stderr!r} and no cycle run, got "
                f"exit {result.returncode}\nstdout: {result.stdout}stderr: {result.stderr}"
                f"\ncycles ran: {calls2.exists()}")
        checks += 1
        print(f"PASS: {name}", flush=True)

    for flag in ("--out", "--task"):
        refuses(f"{flag} refuses a following flag as its value",
                run_stub(flag, "--check", str(root), str(manifest)), 1,
                f"error: {flag} requires a value, not the flag --check\n")
    require(not (root / "--check").exists(), "--out swallowed --check and wrote a file named --check")

    missing = root / "missing-dir" / "t.md"
    refuses("--out in a missing directory fails before any cycle runs",
            run_stub("--out", str(missing), str(root), str(manifest)), 125,
            f"error: cannot write --out {missing}: directory {missing.parent} does not exist\n")
    refuses("--out naming a directory fails before any cycle runs",
            run_stub("--out", str(root), str(root), str(manifest)), 125,
            f"error: cannot write --out {root}: it is a directory\n")
    readonly_dir = root / "ro"
    readonly_dir.mkdir()
    readonly_dir.chmod(0o555)
    if os.access(readonly_dir, os.W_OK):  # root can write anywhere: skip rather than flake
        print("SKIP: --out in a read-only directory (this user can write to a mode-555 directory)",
              flush=True)
    else:
        target = readonly_dir / "t.md"
        refuses("--out in a read-only directory fails before any cycle runs",
                run_stub("--out", str(target), str(root), str(manifest)), 125,
                f"error: cannot write --out {target}: directory {readonly_dir} is not writable\n")
    readonly_dir.chmod(0o755)
    readonly_file = root / "ro.md"
    readonly_file.write_text("")
    readonly_file.chmod(0o444)
    if os.access(readonly_file, os.W_OK):
        print("SKIP: --out onto a read-only file (this user can write to a mode-444 file)", flush=True)
    else:
        refuses("--out onto a read-only file fails before any cycle runs",
                run_stub("--out", str(readonly_file), str(root), str(manifest)), 125,
                f"error: cannot write --out {readonly_file}: file is not writable\n")
    readonly_file.chmod(0o644)

    result = run_stub("--check", "--out", str(missing), str(root), str(manifest))
    require(result.returncode == 0 and not result.stderr and not missing.parent.exists()
            and result.stdout == "manifest OK: 1 entries, 1 selected, every old-string unique\n",
            f"--check must ignore --out entirely\nstdout: {result.stdout}stderr: {result.stderr}")
    checks += 1
    print("PASS: --check ignores --out and neither validates nor creates it", flush=True)

    refuses("--cd without a value is a clean usage error", run_stub("--cd"), 1,
            "error: --cd requires a value\n")
    result = run_stub("--cd", str(root), "--check", ".", str(manifest), cwd=root.parent)
    require(result.returncode == 0 and not result.stderr
            and result.stdout == "manifest OK: 1 entries, 1 selected, every old-string unique\n",
            f"--cd <dir> must resolve the leanncd dir relative to <dir>\n"
            f"stdout: {result.stdout}stderr: {result.stderr}")
    checks += 1
    print("PASS: --cd <dir> resolves a relative leanncd dir inside <dir>", flush=True)

    # Errors that were already reported before this change keep priority over an unwritable --out,
    # and --out is judged only when cycles are really about to run.
    refuses("a manifest problem is reported before an unwritable --out",
            run_stub("--out", str(missing), str(root), str(root / "bad.json")), 125,
            f"error: cannot read manifest {root / 'bad.json'}: "
            f"[Errno 2] No such file or directory: '{root / 'bad.json'}'\n")
    manifest.write_text(json.dumps([bad_targets]))
    refuses("a schema problem is reported before an unwritable --out",
            run_stub("--out", str(missing), str(root), str(manifest)), 125, schema_0)
    manifest.write_text(json.dumps([first]))
    refuses("an unknown task is reported before an unwritable --out",
            run_stub("--task", "9", "--out", str(missing), str(root), str(manifest)), 125,
            "error: no manifest entries selected: unknown task '9'; available tasks: '1'\n")
    refuses("--out under a path component that is a file says so",
            run_stub("--out", str(root / "real.lean" / "t.md"), str(root), str(manifest)), 125,
            f"error: cannot write --out {root / 'real.lean' / 't.md'}: "
            f"{root / 'real.lean'} is not a directory\n")
    refuses("--out with an empty path is a usage error",
            run_stub("--out", "", str(root), str(manifest)), 1,
            "error: --out requires a non-empty path\n")

    # A write that fails only at the end (dangling symlink) is a clean 125; the table is already shown.
    dangling = root / "dangling.md"
    dangling.symlink_to(root / "no-such-dir" / "x.md")
    result = run_stub("--out", str(dangling), str(root), str(manifest))
    require(result.returncode == 125 and calls2.exists() and "| Mutation |" in result.stdout
            and result.stderr == f"error: cannot write --out {dangling}: No such file or directory\n",
            f"final --out write failure: got exit {result.returncode}\n"
            f"stdout: {result.stdout}stderr: {result.stderr}")
    checks += 1
    print("PASS: a write that fails after the run is a clean 125 with the table already printed",
          flush=True)

    # A single dash is not a flag, and an existing writable file is simply overwritten.
    result = run_stub("--out", "-x", str(root), str(manifest))
    require(result.returncode == 0 and (root / "-x").read_text().startswith("| Mutation |"),
            f"--out -x must be accepted as a path\nstdout: {result.stdout}stderr: {result.stderr}")
    existing = root / "existing.md"
    existing.write_text("old contents")
    result = run_stub("--out", str(existing), str(root), str(manifest))
    require(result.returncode == 0 and existing.read_text().startswith("| Mutation |"),
            f"an existing writable --out file must be overwritten\n"
            f"stdout: {result.stdout}stderr: {result.stderr}")
    checks += 1
    print("PASS: --out -x is a path, and an existing writable --out file is overwritten", flush=True)

print(f"mutation-manifest selftest: {checks} checks passed")
PY
