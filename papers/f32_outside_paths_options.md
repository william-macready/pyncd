# F32 default flip: what to do about the paths outside the checked backend

Written for: the repo owner, to decide the last open bullet of `papers/f32_evalplan.md` section 1.4
item 5 ("a decision for the paths outside the checked backend"). Evidence below comes from reading
the code on `main` at `2e850b14` (2026-10-07); no runner or build was executed for this note.

## Status

- **Decision 1: option A chosen (2026-10-07).** The legacy evaluator stays the binary64 reference
  oracle; recorded in `leanncd/LeanNCD/Eval/AGENTS.md` (Contracts) and `papers/f32_evalplan.md` section 1.4.
- Decision 2 (compile-only check for the JAX drivers): not yet approved. Decision 3: no action.

## Short answer

The master plan lists three paths that "assume f64 today". Reading them, only one is a real
decision.

| Path | Verdict |
|---|---|
| pyncd Python, JSON, CSV, tsncd | **No decision needed.** None of it carries an element type, and no path sends tensor declarations from Python to Lean. The flip cannot affect it. |
| Lean-to-Python JAX bridge | **Already handled; one cheap hardening choice.** The drivers spell `f64`, and an f32 affine route exists. They sit outside every build target, so the flip broke four of them silently until Task 6b. |
| Legacy / reference evaluator (`TLProgram.eval`, `evalScheduled`) | **The real decision.** It stays binary64-only and refuses every unannotated program (`unsupportedDtype`). The question is its intended role. |

## Facts the options rest on

- **Python side has no dtype.** `TensorDeclaration` has `kind`, `shape`, `bias` and nothing else.
  `data_transfer/json.py` and tsncd's `json.ts` carry no precision. The ACSet `DataTag` is
  `reals | natural | bool`, with no f32/f64. There is no Lean executable, CLI or server, and no Python
  code writes Lean source. Source enters Lean only through `tl!` in `.lean` files.
- **`torch_compile` already behaves like the new default.** It never sets a dtype, so it follows the
  inputs, and tests use float32 tensors (torch's default).
- **JAX bridge.** Lean drivers run under `lake env lean --run` and write a `.py` module of
  `Float.toBits` / `Float32.toBits` integer lists. Python never sees the evidence label (derived in
  Lean by `orderedReferenceFor`). `einsumOnly` admits binary64 only (`einsumStorageAdmitted`); the
  f32 route is `affineReference` with `EvalPlanAffineSmoke32` (3,849 fixtures bit-identical at
  stride 1; assign-only, context-free, real sum-product only). An unannotated program reaching a
  driver fails in Lean before any Python is written, and Python would also reject mismatched dtypes.
- **Legacy evaluator.** `evalScheduled` refuses the first f32 name before size inference. In
  `LeanNCD/` it has no non-comment callers outside `Eval/`; its callers are tests (through the
  `explicitF64` lever) and the three tracked `spikes/` files. In practice it is the binary64 reference
  oracle for the differential tests (3832 and 17 cases).

## Decision 1: the legacy evaluator's role (needs a choice)

| Option | What it means | Cost | Risk |
|---|---|---|---|
| **A. Keep as the binary64 reference oracle (recommended)** | Status quo. Users and tests spell `f64` to use it. f32 is verified by the checked f32 backend, the independent f32 oracles (`Scatter32OracleTest`, `ScanDense32Test`) and the JAX route. Add one sentence to `Eval/AGENTS.md` and the README saying so. | ~0 (docs) | An unannotated program cannot be run through the reference path. That is a usability cost, not a correctness one. |
| B. Add an f32 reference evaluator | A `Float32` twin of `Eval/` so unannotated programs have an independent reference. | Large: a second evaluator, about a full slice or more. The master plan scheduled none. | Two evaluators can drift; the checked backend is already the f32 executor. |
| C. Make the legacy entry treat unannotated names as f64 | A shim only in `TLProgram.eval`. | Small | **Not recommended.** The same source would mean binary64 in one entry and binary32 in the others, which silently breaks the differential comparison and contradicts the "no second default" decision. |
| D. Retire it as a user-facing entry | Keep it test-only and document that. | Small | Mostly A with a stronger label; do it only if nobody uses it interactively. |

Recommendation: A. It is already the behaviour and was chosen explicitly in slice 2. B is only worth
it if you want f32 results checked against something other than the checked backend and JAX.

## Decision 2: guard the JAX drivers against the next flip (cheap)

The drivers are not in any Lake target (`JaxExperiment` globs only `EvalPlanCodegen`), so nothing
caught the flip. Task 6b found it by hand, including one driver (`EvalPlanAffineSmoke32`) that the
plan had not listed.

| Option | Cost | Note |
|---|---|---|
| A. Leave as is | 0 | Next precision change breaks them silently again. |
| **B. Add a compile-only check (recommended)** | Small, about one Direct-path dispatch: a script or target that runs `lean` on the four drivers (as the runners do, without Python) and is part of the pre-merge checklist. | Catches typing and rejection regressions; does not run JAX. |
| C. Extend f32 JAX evidence to scans, Booleans and so on | A future JAX slice | Separate scope. `einsumOnly` binary32 is a NO-GO per the F32-JAX spike (up to 122 ULP versus XLA). |

## Decision 3: Python, JSON, tsncd (no action now)

Nothing to change. If a Python-to-Lean path is built later, decide then: add an `element_type` to
`TensorDeclaration` and the serialization, with the same default as Lean (binary32). `torch_compile`
already agrees. Adding the field now would be speculative (no consumer exists).

## Minor

The three tracked files under `leanncd/spikes/` that call the evaluator are in no build glob. Leave or
delete; neither affects the migration.

## What I did not check

I did not run any `run-*.sh`, any Python verifier, or the drivers after the merge; the post-flip
status of the drivers rests on the Task 6b compiles (exit 0, Lean side only). I did not grep the whole
repo for other callers of the legacy evaluator beyond `LeanNCD/` and the tracked tests/spikes.
