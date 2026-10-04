# Slice-2 plan audit (f32 default flip): Opus adversarial audit

Branch `f32-flip-slice2-proto` (prototype flip applied). Every claim is marked VERIFIED (a build or
compiled probe ran) or READ (by reading the source only).

## Q1: the new default is never tested AS a default

**Verdict: needs a plan change (one new task, small). The prototype fixture is written and green.**

Fixture: `leanncd/test/Eval/Plan/DefaultF32Test.lean`, registered in `leanncd/lakefile.toml`'s
`Tests` globs after `Eval.Plan.ScanDense32Test`. It imports only `LeanNCD.Eval.Entry` and
`LeanNCD.Eval.Plan.Adapter32` (no test module, so it does not depend on the modules Tasks 2-6 migrate).

Design: each corpus program is written with EXPLICIT `tensor f32` declarations (written by hand, so
no helper has to guess ranks). Two variants are derived from it mechanically: `plain` (`tensor f32`
re-spelled `tensor`) and `undeclared` (`tensor f32` declarations dropped). For each variant it compares
the WHOLE outcome against the explicit one: compile/signature/prepare rejection text, or on acceptance
the `Repr` of `PreparedPlan.plan` (raw plan: slot signature table, steps, algebras; per-step checked
evidence; `storageKind`), `Repr` of the bindings, the warning count, and the exact `Float32.toBits`
of every published name from `runPreparedDense32`. Every explicit program must also be accepted as
`.float32`, and `corpus.length == 10 && accepted == 10` is pinned, so the comparison can never pass
vacuously.

Corpus (10 programs, 20 variant comparisons, 10 acceptance pins): `contract` (tlprog contraction),
`rounding-chain` (binary32 rounding of an intermediate that is read later), `relu` (pointwise
nonlinearity), `softmax` (axiswise), `normalize-where` (`where` mask), `scatter` (`Out[2*i] := X[i]`),
`pred-mixed` (predicate times undeclared real), `lin-scan` (scan with undeclared initial value,
input and state), `scatter-scan` (scatter base inside a scan), `pred-scan` (predicate-only scan block
plus an undeclared real assign outside it).

Evidence:
- VERIFIED: `lake-build.sh <wt>/leanncd Eval.Plan.DefaultF32Test` green (8520 jobs). Before pinning,
  the module logged per program: all 10 accepted as `StorageKind.float32` and all variants agreed.
  **No program where unannotated differs from explicit f32 (no class (iii) finding).**
- VERIFIED mutation: `dtypeOfDecl`'s `none` arm set to `.f64` (Signature.lean). Result: build FAILS
  with `unannotated ≠ explicit f32 on 10 variant(s)`, all 10 `undeclared` variants (the `plain`
  variants still agree, as they should: they go through the `.tensor` arm). Observed shape:
  `explicit = (some float32) { raw := { tensorSigs := #[{ shape := #[2], dtype := f32 } …`,
  `variant = (some float64) { raw := { tensorSigs := #[{ shape := #[2], dtype := f64 } …`.
  So under the mutation the undeclared program is silently ACCEPTED as a binary64 plan from binary32
  buffers; only an end-to-end comparison sees that. Production was restored afterwards and
  `git status` showed only the two test-side files changed.
- Cost: it took 4 build cycles here (one `Repr (List EvalWarning)` compile fix). For an implementer:
  about 10-15 turns, one targeted build plus one mutation cycle.
- Not duplicated: no file in `test/Eval/Plan` compares variants of one program; the `*32Test`
  suites run only explicit-f32 programs.

### Recommended plan changes (paste)

> **Task 1d (new, after 1c): `Eval.Plan.DefaultF32Test`, the acceptance fixture for the default.**
> Cherry-pick the prototype commit (`wip(f32-flip-slice2): opus audit Q1`): add
> `leanncd/test/Eval/Plan/DefaultF32Test.lean` and its glob entry `"Eval.Plan.DefaultF32Test"`
> after `"Eval.Plan.ScanDense32Test"` in `leanncd/lakefile.toml`. Verify:
> `lake-build.sh <wt>/leanncd Eval.Plan.DefaultF32Test` is green. Mutation (record the message): set
> `dtypeOfDecl`'s `none` arm to `.f64`, rebuild; the build MUST fail with
> `unannotated ≠ explicit f32 on 10 variant(s)`; restore and rebuild green. Commit
> `test(leanncd): unannotated programs equal explicit f32 end to end`.
>
> **Task 8 step 3 (change):** add `Eval.Plan.DefaultF32Test` to the flip-reversal targets; it must
> fail (all `undeclared` variants; with flip #1 also reverted, all `plain` variants too).
>
> **Section 4 fixture count:** T1 gains 1 fixture module (10 programs, 20 comparisons).

## Q2: do the storage-kind derivations agree on shapes that become common after the flip?

**Verdict: OK on every shape probed (no class (iii) finding). One shape not constructed (see Unverified).**

Probe: `check-snippet.sh` on a scratch snippet that imports `Eval.Plan.DefaultF32Test` (for
`outcome`/`env32`) and prints, per program, `scheduleStorageKind` (Step 0b) over `buildDeclEnv decls`,
`prepareEvalPlan`'s `plan.storageKind` (from `checkPlan`), and `deriveStorageKind` over the outer
`plan.raw.tensorSigs`. Signatures from `InputSignature.ofDenseInputs32ForDecls`.

| Shape | Result | Step 0b | checkPlan | derive(outer) | Agree | How |
|---|---|---|---|---|---|---|
| (a) predicate-only outer input `M`, undeclared real scan state `S` built from `M` | accepted | float32 | float32 | float32 (outer `#[bool, f32]`) | yes | VERIFIED |
| (a-f32) same with `S` declared `tensor f32` | accepted | float32 | float32 | float32 | yes | VERIFIED |
| (b) predicate times undeclared reals in one assign (`pred-mixed`) | accepted float32, equal to explicit f32 | - | float32 | - | yes | VERIFIED (Q1 fixture) |
| (c) undeclared `S0`/`S`, recurrence `S[l+1] := S[l] · P[l]` with external predicate `P` | accepted | float32 | float32 | float32 (outer `#[f32, bool, f32]`) | yes; full outcome and bits equal to the explicit-f32 twin (`S = [2, 2, 0]`) | VERIFIED |
| (d) scatter into an undeclared destination (`scatter`, `scatter-scan`) | accepted float32, equal to explicit | - | float32 | - | yes | VERIFIED (Q1 fixture) |
| predicate-only scan block, undeclared real outer assign (`pred-scan`): the reverse of the historical bug | accepted float32, equal to explicit | - | float32 | - | yes | VERIFIED (Q1 fixture) |
| (e) unannotated `Y[i] := W[i, j] · x[j] + b[i]` (EvalPlanSmoke's `affineProg`) with `InputSignature.ofDenseInputs` (binary64 sigs) | REJECTED `inputSignature (dtypeMismatch "W" f32 f64)` (expected first, supplied second) | - | - | - | n/a | VERIFIED |
| (e2) same with `ofDenseInputsForDecls` | REJECTED at signature build: `InputSignatureBuildError.storageKindMismatch "W" float64 float32` | - | - | - | n/a | VERIFIED |

So a wrong-dtype signature on undeclared names is caught as a typed error before admission; skipping the
binary64 admission gate does not let a binary64 buffer through.

**Unverified.** (1) The exact historical shape, a bool-only OUTER table plus real scan-LOCAL scratch
that never reaches the outer table: (a) did not build it, because the scan state is published, so the
outer table already holds an `f32` slot. Building it needs a scan with an internal intermediate (not
attempted, budget). (2) (g), a hand-built `RawEvalPlan` with a bool-only outer table and mixed blocks:
not built. By reading, `checkPlanBlockCore` rejects a block whose derived kind differs from the kind
it is checked under (`storageKindNotAdmitted`, Block.lean:220), so a mixed block fails in either
derivation. That is reading, not a proof.

### Recommended plan changes (paste)

> **Task 1d addendum:** add probe (c) (`S[l+1] := S[l] · P[l]`, undeclared `S0`/`S`, external
> predicate `P(l)`, inputs `S0 = 2`, `P = [1, 0, 1]`) and probe (a) (predicate-only external `M`,
> undeclared state `S`) to `DefaultF32Test`'s corpus. Update the pin to `corpus.length == 12 && accepted == 12`.
>
> **Task 7 (change):** the `Compile.lean` Step B comment ("every real external of an f32 schedule is
> `tensor f32`-declared") is false after the flip, because undeclared externals are now binary32 too.
> It is a comment-only edit at a site Task 7 must list. Re-word it to "declared `tensor f32`/plain
> `tensor`, or undeclared".
>
> **Section 4 open unknowns (add):** "bool-only outer table + undeclared real scan-local scratch":
> unprobed. Owner: T1d, if a scan with an internal intermediate can be written cheaply; otherwise parked.

## Q3: capability regressions for UNANNOTATED programs after the flip

**Verdict: needs plan changes (documented regressions plus one unscoped breakage). No BLOCKING
program class was found: every construct probed runs natively in binary32.**

| # | Construct | f64 | f32 | Verification | Consequence for an unannotated program | Class |
|---|---|---|---|---|---|---|
| 1 | `dtypeAdmitted` / `dtypeAdmittedF32` (Check.lean:168/179) | f64, bool | f32, bool | READ | symmetric, nothing lost | ACCEPTABLE |
| 2 | `admittedAlgebrasFor` / `admittedAlgebrasForF32` (Check.lean:90/130); `admittedAlgebra{,Max,Min}` vs `admittedAlgebraF32{,Max,Min}` | sum/max/min + bool | sum/max/min (f32 identities, -inf/+inf seeds) + bool | READ (the list bodies at Check.lean:75/121 were not read line by line) | same algebra menu | ACCEPTABLE |
| 3 | `unaryNotAdmittedForStorage` | - | - | VERIFIED by rg: the constructor (Error.lean:207) has NO producer anywhere in `LeanNCD/` or `test/`; its doc says F32-B made binary32 unary real | no unary op is refused per kind | ACCEPTABLE |
| 4 | assign, pointwise `relu`, axiswise `softmax`, `normalize(where …)`, scatter, scan (plain, scatter base, predicate-masked, predicate-only block) | accepted | accepted, bit-equal to explicit f32 | VERIFIED (Q1 fixture, Q2 probe c) | runs natively in f32 | ACCEPTABLE |
| 4b | other nonlinearities (`sigmoid`, `tanh`, `gelu`, `exp`, `log`, …) | accepted | not probed here | UNVERIFIED (F32-B record claims coverage) | expected the same | — |
| 5 | `einsumStorageAdmitted` (Executable.lean:440) | true | false (spike: up to 122 ULP vs XLA) | READ | an unannotated program loses `einsumOnly` JAX evidence; JAX gets `affineReference`/`orderedReference32` only | REGRESSION-TO-DOCUMENT |
| 6 | Float doors: `runPreparedDense` / `runDensePlan` on a `.float32` plan | runs | `storageKindMismatch .float64 .float32` (pinned in `EvalPlan32Test` 2.3) | READ + pinned test | Float-buffer callers must switch to the `…32` adapter | REGRESSION-TO-DOCUMENT |
| 7 | Float signatures on unannotated programs: `prepareEvalPlan s (InputSignature.ofDenseInputs env)` | accepted | REJECTED `dtypeMismatch "W" f32 f64`; `ofDenseInputsForDecls` → `storageKindMismatch "W" float64 float32` | VERIFIED (Q2 e/e2) | every Float-buffer caller of an unannotated program fails at prepare (typed, loud) | REGRESSION-TO-DOCUMENT |
| 8 | Reference evaluator (`TLProgram.eval`, `evalScheduled`) | runs | refuses (`unsupportedDtype`) | READ (ExplicitF64.lean doc; plan non-goal) | an unannotated program has NO reference-evaluator path; it must spell `f64` | REGRESSION-TO-DOCUMENT (already a non-goal; make it user-facing) |

**Default-dependent callers outside the plan's task list (VERIFIED by rg plus reading one program):**
`leanncd/experiments/jax_bridge/EvalPlanSmoke.lean` (`affineProg`, `shiftedProg`: unannotated,
`ofDenseInputs` + `runPreparedDense`), `EvalPlanAffineSmoke.lean` (10 `tlprog!` programs, same
entries), `EvalPlanAffineCorpus.lean` (same entries), and `experiments/jax_bridge/README.md`
(lines 10, 76-77 describe that path). After the flip, probe (e) shows `affineProg` is rejected at
prepare. These drivers are compiled ad hoc (lakefile.toml comment, line 86), not by the default
targets, so **the Task 8 gate cannot see the breakage.** The plan's "not done" table names only
`leanncd/spikes/`. Other hits (`test/Eval/Plan/{EvalPlanTest,GraphDenseTest,NonlinDenseTest,BlockTest,
ScanTest,ExecutableTest}`) build hand-made `RawEvalPlan`s with explicit `.f64` signatures, so they do
not depend on the default (READ, by the rg context); `ComplexElementTypeTest` is Task 1's.
`LeanNCD/Bridge`, `LeanNCD/Acset`: no dtype/default hits (VERIFIED, empty rg).
`data_transfer`/`websocket_transfer` `*.py`: no `float64|f64|dtype` hits (VERIFIED, empty rg).

### Recommended plan changes (paste)

> **Task 6b (new, small, 10-15 turns): jax_bridge drivers under the flip.** For each of
> `leanncd/experiments/jax_bridge/{EvalPlanSmoke,EvalPlanAffineSmoke,EvalPlanAffineCorpus}.lean`,
> re-spell every name in each `tlprog!` program `tensor f64 …` (or wrap with `TLProgram.explicitF64`;
> the drivers are binary64 smoke tests, and `einsumOnly` evidence exists only in binary64). Compile
> each the way the lakefile comment (line 86) says; pass = each driver's own success line. Update
> `experiments/jax_bridge/README.md` lines 10/76-77 to say the fixtures are spelled `f64`. If not
> done in this slice, add a row to the section-1 "Deliberately NOT done" table instead:
> "`experiments/jax_bridge` binary64 drivers: unannotated programs now rejected at prepare
> (`dtypeMismatch`); not in default targets".
>
> **Task 7 (add to the node edits):** `Eval/Plan/AGENTS.md` and `DSL/AGENTS.md` state the
> user-visible regressions: (5) an unannotated program gets no `einsumOnly` JAX evidence (spell `f64`
> for it); (6, 7) Float buffers plus `ofDenseInputs`/`ofDenseInputsForDecls` on an unannotated program
> fail at prepare with `dtypeMismatch` / `storageKindMismatch` (use `ofDenseInputs32ForDecls` +
> `runPreparedDense32`, or spell `f64`); (8) the reference evaluator needs `f64`.
>
> **Section 1 non-goals (add):** "binary32 `einsumOnly` JAX evidence (F32-JAX spike: 122 ULP);
> unannotated programs lose it by design."
