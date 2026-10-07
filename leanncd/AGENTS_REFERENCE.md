# leanncd guidance reference

Detailed patterns moved from the root guidance to keep automatic context
small. Read the relevant rules before editing their covered surfaces.

### Patterns

- **When the same logic is genuinely duplicated across two or more call sites, unify it into one
  general routine — don't leave parallel near-copies to drift.** The trigger is an actual second
  occurrence, not an anticipated one: this does not license speculative generalization (building a
  general routine for a hypothetical future second caller is exactly what the root `CLAUDE.md`'s
  "no abstractions for single-use code" rule forbids). Duplicated logic across real call sites is
  also where correctness bugs hide, precisely because nothing forces the copies to stay in sync —
  treat "these two blocks look alike" as a prompt to check whether they've already diverged, not
  just an opportunity to tidy up.
  Concrete precedent: `docs/superpowers/plans/2026-07-31-wave-b-eval-unification.md` (Eval
  contraction/nonlinearity unification) is built entirely around this — `evalAssignWith`/
  `evalAssignSeeded` unify into one `evalAssignSeeded` (`evalAssignWith` becomes its empty-seed
  wrapper); `evalPlain`'s and `Scan.evalStmtSliceSeeded`'s duplicated norm-axis-lookup blocks
  unify into one `resolveNonlin`; their duplicated dtype dispatch unifies into one
  `evalAssignDtypedSeeded`. In each case the two copies had already silently diverged (a real
  defect, not a style nit) — the strongest evidence a unification is overdue, not premature.

- **Value-parity test claims must be source-generated (`tlprog!{…}`); hand-built plan values may
  assert only REJECTION or component-isolation contracts, and each hand-built fixture should state
  its reachability.** The checked backend (`Eval/Plan/`) accepts hand-built `ScheduledProgram`/
  `AssignPlan`/`ScatterPlan` values directly — the §12.2 programmatic escape hatch — so a test can
  hand it a state the source compiler provably never emits. A hand-built plan asserting a *correct
  value* is unsound in both directions: it can bless a value for an unreachable state (false
  confidence), or flag a divergence from the reference for a state that can't occur (false alarm —
  you chase a non-bug). So route every parity/agreement assertion ("does the backend compute the
  right number / match `evalScheduled`") through the full `compileToScheduled` path only; reserve
  hand-built inputs for (a) isolating one checker/worker (`ScatterCheckTest`/`ScatterDenseTest`) and
  (b) pinning that a malformed or out-of-fragment plan is *rejected* (`CompileTest`'s capability
  fixtures). Label each hand-built fixture with its reachability ("source-unreachable; pins the
  boundary" vs "source-reachable via X") so the two purposes never blur.
  Concrete precedent: the S-A scatter slice. Task 6's differential corpus (`scatterPrograms`,
  `DifferentialTest.lean`) is source-generated for exactly this reason — its brief forbade porting
  the hand-built `test/Eval/ScatterTest.lean`, which "must exercise the real source-to-checked-plan
  path." The whole-branch review's one Critical (a `predicate` scatter destination silently
  diverging, `predicateScatterDest`) was **source-reachable** and slipped through only because the
  corpus lacked that dtype×shape combination — a *coverage* gap in the source-generated tests, not a
  hand-built-plan problem; the strongest robustness win there is making the generated parity corpus
  cover the whole accept surface (dtype × placement shape), not policing hand-built tests. By
  contrast the follow-up `unloweredScatterAssign` guard covers a shape reachable ONLY by a hand-built
  plan (`lowerArith` always lowers a source scatter-shaped `.assign` to `Stmt.scatter`), so it is
  pinned by a rejection fixture, never a value-parity entry. Two bugs, opposite lessons: broaden
  source-generated coverage; keep hand-built tests to rejection/isolation.

- **Most eval-based tests declare `f64` explicitly (`test/Eval/ExplicitF64.lean`).**
  `explicitF64Decls`/`TLProgram.explicitF64` and the `…F64` wrappers declare only UNDECLARED names
  `f64`; plain `tensor`/`linear` are re-spelled `f64` at the source. Covered: Harness/Portfolio,
  EvalExamplesTest, EntryTest, AffineShapeSolverTest, ScanTest, ContractTest, WaveBRegressionTest,
  Plan/ContractTest, PropertyOracle/*, ScanDense32Test. NOT covered (slice-2 of the f32 default
  flip): Plan CompileTest, ScanCompileTest, ScatterCompileTest, NonlinCompileTest, AdapterTest,
  Adapter32Test, DifferentialTest still call the evaluator unwrapped.
