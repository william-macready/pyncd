# F3-b stage 1 record: a scan statement may carry a surface constant slot

Process: Direct path (slice-plan section 0): a localized change that removes a guard; the differential oracles
and the three-leg fixtures already see the surface. One implementer, one cost probe before it, one review lens.
Base `edaf7781` (F3-a). Not pushed.

## What landed

- `84cbf47c` (code and fixtures). In `lowerArith` (`DSL/Pipeline/Structural.lean`) the `.assign`-arm guard that
  raised `overlappingScatter` for a scan slot beside a raw constant is deleted; `lowerConstSlots` no longer returns
  early for a scan statement; the orphaned `LHSSlot.isRawConst` is removed. A scan constant `G[=n, ..]` now takes
  the same path as a top-level one: `.affine (.const n)` becomes `.affine (.affine n [(1, ax)])` over a fresh
  synthetic size-1 axis `#const<uid>` declared `.axis ax (some 1)`. The checked scan path then sees a single-axis
  strided row `.strided p 1 n`, the reference already placed it (F3-a).
- `13a481cd` (docs sweep): `Eval`, `DSL`, `Semantics`, `Eval/Plan` AGENTS nodes, the `Uid.lean` comment, the
  geometry design note, `backend_missing_functionality`, `max_min_aggregation`, semantics path part 5.
- Review follow-up (this commit): two pins (R1, R3), docs wording (R4), this record.

Behaviour (all OBSERVED bit-equal across the reference, the checked f64 plan and the checked f32 plan):
the state's extent in a constant's dimension is `n + 1`; base and step constants must agree or evaluation and
plan preparation fail with `inconsistentStateExtent` (not at compile); rows never written stay at the sort's
`0_K` (0 real, -inf max-plus); across-step collisions stay impossible by construction.

`CompileError.overlappingScatter` is now producer-less and is KEPT on purpose (Eval/Plan AGENTS pitfall "Don't
delete producer-less constructors"; Rule 11). A raw `.affine (.const _)` survives only in a hand-built
`ScheduledProgram` that skips `lowerArith`; a hand-built `TLProgram` constant is lowered.

## Fixtures (`test/Eval/Plan/ScatterSurfaceTest.lean`, `test/DSL/Pipeline/StructuralTest.lean`)

`scanConstStep` (constant in the step only), `scanConstBase` (typed `inconsistentStateExtent`), `scanConstBoth`,
`scanConstTrop` (-inf in unreached rows), `scanConstFirst` (scan axis first), `scanConstFar` (`=5`, shape [6,3]),
`scanTwoConst`, `scanCoupled` (second state reads the first), plus three `StructuralTest` pins flipped from refusal
to acceptance. Mutants run by hand: m1 restore the `.assign` guard, m2 restore the `lowerConstSlots` early return,
m3 bias `n + 1` to `n`; each killed the fixtures that depend on it and every new fixture is killed by at least one.
The `G` assertion of `scanCoupled` cannot fail under this feature (an unmutated free state).
Test-first was not red for the implementer (the worktree oleans held the probe-edited state), compensated by m1/m2.
The mutation manifest was not extended (Direct path).

## Review adjudication (lens: wrongly accepted programs and siblings; `additive_f3b1_review.md`)

| Finding | Verdict | Action |
|---|---|---|
| R1 P2: a pinned declaration of the scan state's axis is overridden by a constant slot's extent (`axis j = 3`, `G[=1, ..]` publishes [2,3]; `=5` publishes [6,3]); the top-level twin is boxed or refused (`writerExtentExceedsBox`) | Real. NOT a regression of an accepted program (the constant was refused before), and the same gap already exists for a strided scan slot `G[2*j, ..]`, so it is a scan-wide limit that stage 1 extends to constants. Fixing it is a new scan-wide check, not part of stage 1 | PARKED (Rule 14). Pinned by `scanConstPinned` with a KNOWN LIMIT comment; documented in `Eval/AGENTS.md`. Cost: about 1 Direct dispatch (preflight/reference check that a scan state's derived dimension equals a pinned declared extent, typed refusal; touches strided slots too, so decide that with the user) |
| R2 P3: two base statements with different constants cannot coexist (`inconsistentStateExtent`; scale-1 rows never separate by residue) | Correct and typed; two identical constants give `baseWritesOverlap` as the free-slot control does | No action; limit of the `n + 1` extent model |
| R3 P3: predicate scan state with a constant: reference runs, both plans refuse (`predicateScatterDest`) | Pre-existing capability tier, now reachable with a constant | Fixed: `scanConstPred` pins `compErr` (preflight), `refErr == none`, both plan errors |
| R4 P3: docs say a "hand-built raw" constant is refused; only a hand-built `ScheduledProgram` carries one | Real wording | Fixed in `Eval`, `Semantics`, `Eval/Plan` AGENTS (the `Compile.lean` doc was already right) |

Lens questions answered clean: two base statements on one cell (R2), synthetic axis name never read (`rg "#const"`
finds only the construction), a constant in the advancing dimension (`missingBaseCase` or `noAdvancingAxis`, typed
on every leg), negative hand-built constant (typed errors, no panic), nonlinear body with a constant
(`unsupportedNonlinScatter`, refused before `lowerArith`; `where` is unreachable).

Not examined by the review (state as open, Rule 12): `ScanOracle`, `ScanGen` and the `DifferentialTest` generators
with a constant scan slot; display and serialization of the synthetic axis inside a scan; a scan whose only LHS
slots are constants with no sizing input (`unsizedAxis`).

## Parked

- R1 above (scan state extent vs pinned declaration; strided slots included).
- F3-b stage 2 (multi-axis scan rows): needs a new `WriteRowKind`, position lists, multi-coefficient row extents and a
  `commitWrite` fold with per-state combine and copy-on-untouched; about 8 mutants; full path. Do it only when a real
  program needs it.
- Top-level `evalScatter` signed-zero parity with the checked top-level plan (unprobed, cheap).
- D5 boolean-state scan fixture; a dedicated rank-mismatch error constructor (the rank case reuses
  `scatterWriteOutOfRange` text); a reference guard for a state that omits a scan axis; a hand-built const -1 gives
  different constructors in the reference (`scatterWriteOutOfRange`) and the plan (`scanWriteRowNotAdmitted`), both
  loud and not surface-spellable.
- Slice A's mutation manifest and patches still mention the deleted `isRawConst` (historical; nothing runs them).

## Measurements (Rule 6, harness counts)

- Cost probe (read-only): 55 turns against a 45 budget (breach).
- Implementer: 84 turns by the harness against 60 allowed (self-reported about 52; breach, caused by waiting on builds).
- Review lens: 47 tool calls against 45 (slight breach); about 140k tokens.
- Controller builds: full `LeanNCD Tests JaxExperiment` green at 8844 jobs on `84cbf47c` and `13a481cd`, and
  again at 8844 jobs on the branch tip after the review follow-ups (R3 and R1 pins, R4 wording).
