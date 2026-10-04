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
