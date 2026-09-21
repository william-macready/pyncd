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
(`packBodyOf`/`unpackBodyOf`/`runPreparedDenseOf`) at `α := Float32`. What is genuinely new here is
three `.float32` storage-kind guards — one per public entry, each placed BEFORE that entry's own
pre-existing work, mirroring Task 2's `.float64` guards on the Float side.

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

/-- `packBodyOf` behind the BINARY32 storage-kind door.

    STORAGE KIND FIRST, before any name is resolved and before any shape or storage is validated —
    the mirror of `packChecked`'s own guard, and for the mirrored reason: `NamedDenseEnv32` holds
    binary32 buffers, so packing them into a `.float64` plan's positional store would relabel
    `Array Float32` data as that plan's own binary64 inputs without any numeric worker running.
    Placed on this private helper, not on `pack32` below, so `runPreparedDense32`'s own call site
    inherits it too.

    Before the STORAGE check specifically, not merely present: `packBodyOf`'s storage-size check
    (`t.data.size` against the signature's element product) would otherwise report a size complaint
    about a buffer this adapter must never have been handed at all. -/
private def packChecked32 (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnv32) : Except InputBindingError (Array DenseTensor32) := do
  unless plan.plan.storageKind == .float32 do
    throw (.storageKindMismatch .float32 plan.plan.storageKind)
  packBodyOf plan checked env

/-- Resolve every input slot `runDensePlan32` needs, by NAME, from a native binary32 environment.
    The binary32 sibling of `pack`; see `packBodyOf` (`Adapter.lean`) for what the resolution and
    the shape/storage checks actually do and why they are reproduced at this boundary rather than
    deferred to the positional worker. -/
def pack32 (plan : PreparedPlan) (env : NamedDenseEnv32) :
    Except InputBindingError (Array DenseTensor32) := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidPreparedBindings e)
  packChecked32 plan checked env

/-- `unpackBodyOf` behind the BINARY32 storage-kind door.

    STORAGE KIND FIRST, before the result store's ARITY is examined and before any name is
    published. The environment this builds is a `NamedDenseEnv32`, so publishing a `.float64` plan's
    outputs through it would hand a caller `Array Float32` buffers under that plan's own output
    names. Before the arity check specifically, not merely present: a `storeArityMismatch` would
    otherwise be reported for a store this adapter must never have been offered. -/
private def unpackChecked32 (plan : PreparedPlan) (checked : CheckedPreparedBindings)
    (env : NamedDenseEnv32) (result : Array DenseTensor32) :
    Except PlanRunCause NamedDenseEnv32 := do
  unless plan.plan.storageKind == .float32 do
    throw (.storageKindMismatch .float32 plan.plan.storageKind)
  unpackBodyOf plan checked env result

/-- Reconstruct the named binary32 environment from a positional binary32 result. The binary32
    sibling of `unpack`, sharing its publication order, its repeated-name last-write-wins semantics,
    and its "the store's arity is the plan's, not the caller's" rule verbatim through
    `unpackBodyOf`. -/
def unpack32 (plan : PreparedPlan) (env : NamedDenseEnv32) (result : Array DenseTensor32) :
    Except PlanRunCause NamedDenseEnv32 := do
  let checked ← match checkPreparedBindings plan with
    | .ok checked => pure checked
    | .error e => throw (.invalidBindings e)
  unpackChecked32 plan checked env result

/-- The BINARY32 named runner: `pack32 → runDensePlan32 → unpack32`, with its OWN `.float32` guard
    first — before `checkPreparedBindings`, before `packChecked32`, and before the worker — so a
    caller who hands the binary32 runner a binary64 plan sees the adapter-tier
    `PlanRunCause.storageKindMismatch` rather than a nested pack or worker diagnostic naming a
    boundary further in. Preparation warnings are preserved through every outcome, success and
    failure alike, exactly as `runPreparedDense` preserves them. -/
def runPreparedDense32 (plan : PreparedPlan) (env : NamedDenseEnv32) :
    Except PlanRunFailure EvalReport32 :=
  runPreparedDenseOf .float32 packChecked32 unpackChecked32 runDensePlan32 plan env

end LeanNCD.Eval.Plan
