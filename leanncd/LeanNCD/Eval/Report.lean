import LeanNCD.Eval.Tensor
import LeanNCD.Eval.Error

namespace LeanNCD.Eval

/-- The complete result of evaluating an already-scheduled program, over one scalar carrier `α`.
    `env` deliberately preserves the evaluator's established full-environment behavior (inputs plus
    every computed tensor); `warnings` makes non-fatal sizing diagnostics persistent data instead of
    trace output. Moved here verbatim from `Eval.lean` (C4) — a neutral leaf shared by the legacy
    scheduled evaluator and the new `Plan/Adapter.lean`, so the latter does not need to import the
    whole `Eval.lean` dependency chain just to name this type.

    Only the carrier SHELL is generic (f32 slice, Task 4), the same parameterization
    `DenseTensorOf` already carries and for the same reason: the named result of a run is
    shape/warning bookkeeping with nothing carrier-specific in it, so parameterizing it is what lets
    the binary32 named adapter (`Plan/Adapter32.lean`) publish native `Float32` results under source
    names without a second, drift-prone copy of this shell. `EvalWarning` is deliberately NOT
    parameterized: a padded-access or sizing diagnostic is a statement about shapes, identical in
    both precisions. -/
structure EvalReportOf (α : Type) where
  env : Std.HashMap String (DenseTensorOf α)
  warnings : List EvalWarning

/-- The binary64 report: the original `EvalReport`, unchanged in meaning and in field names. -/
abbrev EvalReport := EvalReportOf Float

/-- The binary32 report, published by `Plan/Adapter32.lean`'s `runPreparedDense32`. Its `env` holds
    native `Array Float32` buffers — NOT `Array Float` relabelled — so a caller reading a result out
    of it reads the bits the binary32 worker actually produced. -/
abbrev EvalReport32 := EvalReportOf Float32

/-! ### `EvalReport`'s old generated names

Changing a structure into an alias does NOT synthesize the alias's old `mk`/field projections, and
a bare `abbrev` of a generic projection is not usable through legacy field notation (verified the
hard way by the f32 slice's Task 3 — see `Eval/Tensor.lean`'s `DenseTensor.mk`/`.shape`/`.data`,
whose exact shape this mirrors). So all three are preserved explicitly: `mk` as an abbreviation, and
the two projections as definitions whose `self` parameter is typed with the legacy alias. Every
pre-existing user — `Eval/Eval.lean`'s `evalScheduled`, `Eval/Entry.lean`,
`Plan/Adapter.lean`'s `runPreparedDense`, and the `EntryTest`/`AdapterTest`/`PropertyOracle.Compare`
test sites — therefore compiles unmigrated, which is what `AdapterTest`'s fixture 11 pins. -/

/-- Compatibility: the binary64 report's old generated constructor. -/
abbrev EvalReport.mk (env : Std.HashMap String DenseTensor) (warnings : List EvalWarning) :
    EvalReport :=
  EvalReportOf.mk env warnings

/-- Compatibility: the binary64 report's old generated `env` projection. -/
def EvalReport.env (self : EvalReport) : Std.HashMap String DenseTensor := EvalReportOf.env self

/-- Compatibility: the binary64 report's old generated `warnings` projection. -/
def EvalReport.warnings (self : EvalReport) : List EvalWarning := EvalReportOf.warnings self

end LeanNCD.Eval
