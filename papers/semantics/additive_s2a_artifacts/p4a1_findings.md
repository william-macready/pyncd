# S2a P4 A1 findings: origin-bound confirmation of the scatter conditions (review F1, F11)

Branch `proto-s2a-p4` (base df84fce8). Everything below is read off `observe` / `tag` output
(`#eval`s appended temporarily to `SourceDifferentialScatterTest.lean`, then replaced by guards),
not predicted. `Z` is declaration 6 over `a` (declared extent 4); fixtures use order `[5, 6]`.

NOTE: `papers/semantics/additive_s2a_review_plan.md` and `additive_s2a_plan.md` are NOT present in
this worktree (nor anywhere under the repo); the task text of the dispatch was used as the spec.

## 1. Which native errors carry an identity

| leg / cause | constructor | identity carried | A1 treatment |
|---|---|---|---|
| legacy evaluation collision | `EvalError.scatterCollision (nm) outCoord first second` | destination TENSOR name (`evalScatter Z: collision ...`) | ORIGIN-BOUND: `nm` must be the source name of the condition's declaration |
| checked runtime collision | `PositionalInputError.scatterCollision destCoord first second` (under `PlanRunCause.execution`) | coordinates only; `PlanRunFailure` has no locator (positional by design, Error.lean:169-171) | CAUSE-ONLY (docstring on `checkedCollision`) |
| checked preparation refusal | `PlanCompileCause.capability (multiAxisScatterLhs ctx / scatterOrAffineLhs ctx)` | context string `"{tensor}: affine LHS slot"` / `"{tensor}: constant affine LHS slot"` | ORIGIN-BOUND: the prefix before `": "` must be the condition's tensor |
| legacy compile multi-writer | `CompileError.scanAxisNotIter (String)` | the AXIS name (`"a"`), no tensor/statement | CAUSE-ONLY (docstring on `legacyCompile`) |
| checked sourceCompilation multi-writer | same `CompileError.scanAxisNotIter` | axis only | CAUSE-ONLY |
| extent override (both legs) | `BindingIssue.shape/length (metadata : TensorOrigin) ..` | declaration | already origin-bound (`shapeOnly` checks `m.declaration`) — unchanged |

Consequence: `scatterCollisionRejected` is bound on legacy always, on checked when the checked leg
fails at preparation; when the checked leg fails at runtime it stays cause-only on that leg.
`multiWriterScatter` is cause-only on BOTH legs (no leg can be bound).

Cause tightening that binding needed: to read the context string structurally the checked
preparation arm now matches only the two affine-slot capability constructors
(`multiAxisScatterLhs`, `scatterOrAffineLhs`) instead of ANY `.capability _`. Another capability
refusal no longer confirms a collision condition (no existing fixture relied on it).

## 2. F11 probe (bare-slot `rejectCollisions` scatter, contracted axis)

`Z[a] := X[a]*W[b]` as `.scatter "Z" [.free a] readXW {reduce := .rejectCollisions}`, plus a parity
write `Y[2a] := X[a]`:

| leg | observed |
|---|---|
| admission / oracle | admitted (plain assign), oracle sums over `b` (order `[5]` gives `omittedTarget 6`, hence `[5, 6]`) |
| `detectConditions` | no condition (bare slot, `nonBareWrite` false) |
| legacy | failure scheduledEvaluation `evalScatter Z: collision writing output coord [0] — source coords [0, 0] and [0, 1] both write here` |
| checked | runtime `execution (scatterCollision [0] [0, 0] [0, 1])` |
| classification | `nativeFailure` |

So production DOES reject it as a collision; the oracle sums; the differential reports a native
failure (fail-loud, but unexplained: it is the same contract difference as `scatterCollisionRejected`
on a bare slot). Pinned as `fF11`. Side issue (not done): extend `detectConditions` to bare-slot
`.scatter` with `rejectCollisions` and a contracted axis — ~1 dispatch.

## 3. Negative fixtures, before/after

| fixture | legacy (observed) | checked (observed) | before A1 (cause-only) | after A1 |
|---|---|---|---|---|
| `fOriginL` = `[zBare, Y[a+b] := X[a]*W[b]]`, `|k|=6` | `evalScatter Z: collision` (Z fails first) | preparation `multiAxisScatterLhs "Y: affine LHS slot"` | `known:collision` (WRONG) | `nativeFailure` |
| accept-neighbour (Z := X[a] bare parity write, same Y) | not recorded per leg | not recorded per leg | `known:collision` | `known:collision` |
| `fOriginC` = `[Z[3] += X[a] (sum), Y[2a] := X[a]*W[b]]`, `|k|=8` | `evalScatter Y: collision ... [0] [0,0] [0,1]` | preparation `scatterOrAffineLhs "Z: constant affine LHS slot"` | `known:collision` (WRONG) | `nativeFailure` |
| accept-neighbour (Z := X[a], same Y) | not recorded per leg | not recorded per leg (fE alone: runtime collision) | `known:collision` | `known:collision` |

The reverse statement order `[yConv, zBare]` and `[yE, zConst]` also classified `known:collision`
before A1 (observed; their per-leg causes were not recorded and they are not pinned).

Choice of the correct classification: `nativeFailure`. With the condition not confirmed,
`classification` (unchanged) falls through to the native outcome match, and both pairs have at least
one failed native leg. A failure raised by a different tensor is an unexplained native failure; it is
not a value mismatch (no leg produced values), so `nativeDiscrepancy` would be wrong.
Each negative fixture differs from its accept-neighbour in ONE statement (the Z write), and each
pins the per-leg error text it relies on (`mentions` guards), so a fixture drift is caught.

Existing guards: all unchanged and green; no existing fixture relied on cause-only confirmation.

## 4. Production change (Differential.lean only)

* `ownedBy native declaration name`: `name` is the source name of the tensor declared at the
  condition origin's `declaration` (table lookup in the admitted source).
* `legacyCollision owner`: `.scatterCollision nm ..` confirms only if `owner nm`.
* `checkedCollision owner`: the preparation arm matches `multiAxisScatterLhs ctx` /
  `scatterOrAffineLhs ctx` and requires `owner` of the prefix of `ctx` before `": "`; the runtime
  arm is unchanged (cause-only).
* `confirms (.scatterCollisionRejected origin)` passes `ownedBy native origin.declaration` to both.
  `multiWriterScatter`, `scatterExtentOverridesDeclared` and `classification` are untouched
  (head-only confirmation kept).
* Granularity: the binding is to the destination TENSOR (declaration), not the statement: no native
  error carries a statement index. Two collisions on one tensor from different statements cannot be
  told apart (a second writer of the same tensor is `multiWriterScatter`, which is detected first).

## 5. Mutation controls (`mutation-cycle.sh`, target `Semantics.SourceDifferentialScatterTest`)

| label | mutation | failing positions (observed) | restored build |
|---|---|---|---|
| A1-M1 | legacy `.scatterCollision nm .. => owner nm` to `.scatterCollision .. => true` | `SourceDifferentialScatterTest.lean:288:0` (`tag fOriginL`) only | green |
| A1-M2 | checked `let named (context : String) := owner (...)` to `let named (_ : String) := true` | `SourceDifferentialScatterTest.lean:298:0` (`tag fOriginC`) only | green |

No survivors. Manifest `p4a1_mutations_draft.json` (`mutation-manifest.sh --check` OK). Not
mutated: the cause tightening (any capability to the two constructors); no fixture distinguishes
it (side issue, ~0.5 dispatch: a fixture whose checked leg fails with another capability naming Y).

## 6. Builds

`LeanNCD.Semantics.Source.Differential`, `Semantics.SourceDifferentialScatterTest`,
`Semantics.SourceDifferentialPolicyTest`, `Semantics.SourceDifferentialGeometryTest`,
`Semantics.SourceDifferentialIdentityTest`, `Semantics.SourceDifferentialTest`: all green after the
change (single targets). The full `Tests` target was NOT run (the controller does).

## 7. Side issues (parked)

* F11 detection gap (section 2): ~1 dispatch.
* `multiWriterScatter` cannot be origin-bound on either leg (axis-only error). Binding to "the
  axis is one of the writers' form axes" is possible but weak: ~0.5 dispatch, value doubtful.
* The checked runtime collision is positional: binding it needs a tensor/statement locator in
  `PlanRunFailure` (a production change outside Differential.lean): out of scope.

Harness tool calls this dispatch: ~42 (within the ~50 budget).
