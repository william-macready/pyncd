import LeanNCD.Eval.Slots
import LeanNCD.Eval.SizeSolve
import LeanNCD.Eval.SizeInfer

/-!
# `Eval/Shape.lean` — compatibility umbrella (Wave E, 4e)

This file used to hold the whole axis-shape subsystem (475 lines: LHS-slot shape helpers, the
pure affine constraint solver, and the concrete shape-driven inference fixpoint, in one file).
It has been split along its real dependency boundaries into three modules, each independently
buildable and independently importable:

  `Slots.lean`      `normAxisUidOf`, `outputShape` — the shared LHS-slot shape vocabulary.
                    Depends only on `DSL.Ast`; no notion of axis-size *inference* at all.
  `SizeSolve.lean`  `SizeConstraint`, `SizeSolve.solveSizeConstraints`, and the
                    RREF/diagnostic-rendering machinery behind them — a pure solver over
                    already-built constraints, with no notion of a `Stmt`, tensor environment, or
                    read position. Cross-module helpers live under the `SizeSolve` namespace rather
                    than leaking former private names into `LeanNCD.Eval`.
  `SizeInfer.lean`  `AffinePosition`, `scatterOutputShapes`, `inferAxisSizes` — walks statements
                    and known shapes to build constraints, drives `SizeSolve` to a fixpoint, and
                    reports the two "which axis" failure modes (bare-axis conflict, Issue D's
                    purely-negatively-constrained axis) that aren't about constraint arithmetic.

`Contract.lean`, `Nonlin.lean`, and `Scan.lean` now import the narrow module each one actually
needs (`Slots` and/or `SizeInfer`) instead of this umbrella, so a change to, say, the RREF pivoting
in `SizeSolve.lean` cannot even in principle force `Nonlin.lean` (which only calls
`normAxisUidOf`) to recompile.

This file remains as a compatibility import for anything (tests, docs, external callers) that
still names `LeanNCD.Eval.Shape` — every symbol it used to export is re-exported here unchanged.
Nothing in this file's *behavior* changed: no error message, warning string, or inferred value
differs from before the split (Wave E, 4e is organizational only; see `AGENTS.md`).

`LHSSlot.outExtent` (the scatter-slot extent formula) is deliberately NOT among the moved/re-
exported symbols — it already lives in `DSL/Ast.lean` and was never part of this file.

Addendum (Wave E, 4h): `SolveFailureKind`/`SolveDiagnostic` and their renderer/remediation helpers
have since moved out of `SizeSolve.lean` into `Error.lean` (the module that owns rendering every
Eval diagnostic), and every `String` error this subsystem used to throw is now a structured
`EvalError`/`ShapeError` constructor — see `Error.lean`. This is still behavior-preserving in the
sense that matters to this umbrella: every `ToString`-rendered message is byte-identical to before,
so nothing that named `LeanNCD.Eval.Shape` for its re-exported symbols needs to change.
-/
