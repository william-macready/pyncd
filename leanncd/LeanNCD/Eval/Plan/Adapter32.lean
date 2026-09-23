import LeanNCD.Eval.Plan.Adapter
import LeanNCD.Eval.Plan.Dense32

/-!
# The named binary32 boundary (f32 slice, Task 4)

`pack32`/`unpack32`/`runPreparedDense32` — the public named-input/named-output adapter for a
`.float32` prepared plan, the exact parallel of `Adapter.lean`'s `pack`/`unpack`/`runPreparedDense`.
Task 3 gave an f32 program a native worker (`runDensePlan32`, `Dense32.lean`); this file is what lets
a caller hand it `Float32` buffers BY NAME and read `Float32` results back by name, which is the last
boundary an f32 program had no public door through.

**This file adds no traversal of its own.** Shape/storage validation, slot→name resolution, result
arity, and publication order all come from `Adapter.lean`'s carrier-polymorphic cores
(`packBodyOf`/`unpackBodyOf`/`runPreparedDenseOf`) at `α := Float32`, and so do the `.float32`
storage-kind guards: each core's first statement compares the plan's storage kind against
`StorageCarrier Float32`'s `.float32`, the same line that guards the Float side at `.float64`
(final-review fix wave; before it, this file carried its own private guard helpers in front of
guardless cores).

**Native buffers all the way through.** `NamedDenseEnv32` is `HashMap String DenseTensor32`, the
positional store is `Array DenseTensor32`, and the worker is `runDensePlan32`. There is no widen-to-
binary64-and-narrow-back leg anywhere on this path: such a shortcut would answer a binary32 question
with binary64 rounding and then hide the difference behind a final narrowing, which is precisely the
substitution the whole slice exists to prevent (`Adapter32Test`'s reduction fixture discriminates it
directly).
-/

namespace LeanNCD.Eval.Plan
open LeanNCD.Eval Std

/-- Source-facing NATIVE binary32 tensor environment, keyed by name — the binary32 sibling of
    `NamedDenseEnv`. `Array Float32` buffers, not `Array Float` relabelled. -/
abbrev NamedDenseEnv32 := NamedDenseEnvOf Float32

/-- Resolve every input slot `runDensePlan32` needs, by NAME, from a native binary32 environment.
    The binary32 sibling of `pack`: `checkPreparedBindings`, then `packBodyOf` at `α := Float32`,
    whose first statement is the `.float32` storage-kind guard. See `packBodyOf` (`Adapter.lean`)
    for what the resolution and the shape/storage checks actually do and why they are reproduced at
    this boundary rather than deferred to the positional worker. -/
def pack32 (plan : PreparedPlan) (env : NamedDenseEnv32) :
    Except InputBindingError (Array DenseTensor32) := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidPreparedBindings e)
  packBodyOf plan checked env

/-- Reconstruct the named binary32 environment from a positional binary32 result. The binary32
    sibling of `unpack`, sharing its publication order, its repeated-name last-write-wins semantics,
    and its "the store's arity is the plan's, not the caller's" rule verbatim through
    `unpackBodyOf` — including that body's `.float32` storage-kind guard, which runs after
    `checkPreparedBindings` and before the arity check. -/
def unpack32 (plan : PreparedPlan) (env : NamedDenseEnv32) (result : Array DenseTensor32) :
    Except PlanRunCause NamedDenseEnv32 := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidBindings e)
  unpackBodyOf plan checked env result

/-- The BINARY32 named runner: `pack32 → runDensePlan32 → unpack32`, with the runner's `.float32`
    guard first — before `checkPreparedBindings`, before `packBodyOf`, and before the worker — so a
    caller who hands the binary32 runner a binary64 plan sees the adapter-tier
    `PlanRunCause.storageKindMismatch` rather than a nested pack or worker diagnostic naming a
    boundary further in. Preparation warnings are preserved through every outcome, success and
    failure alike, exactly as `runPreparedDense` preserves them. -/
def runPreparedDense32 (plan : PreparedPlan) (env : NamedDenseEnv32) :
    Except PlanRunFailure EvalReport32 :=
  runPreparedDenseOf runDensePlan32 plan env

end LeanNCD.Eval.Plan
