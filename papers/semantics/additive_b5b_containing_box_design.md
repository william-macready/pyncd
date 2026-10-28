# B5b: declared containing box for multi-writer scatter

**Status: approved by the owner 2026-10-28 (all three recommendations: M1, leave the single-writer
asymmetry, accept the M4 slack); implementation plan `additive_b5b_plan.md`.** Read against local `main` `342106e4`. It narrows the one option the B5 design
([additive_b5_design.md](additive_b5_design.md) section 1) deferred: *"declared shape is an
arbitrary containing box"*. Approval authorized writing one implementation plan.

## 1. The problem

B5 requires every writer's realized extent to **equal** the collector basis. The commonest
multi-writer shape, concatenation into a larger declared tensor, is therefore refused:

```
axis i = 2; axis k = 4; tensor A(i), B(i), S(k)
S[i]     := A[i]
S[i + 2] := B[i]          -- intended: S = [A0, A1, B0, B1]
```

Today collection accepts this and the shape obligation refuses it with
`writerExtentMismatch "S" 1 0 4 2` (writer 1, dimension 0: expected 4, actual 2). Measured on
main with the second writer spelled `S[1*i + 2]`; the `S[i + 2]` spelling compiles
but was not run through evaluation. In the B5 corpus the same strictness shows up as 81 of 99 shape5-only rows
SHAPED-refused (`additive_b5_record.md`); that corpus is generated, so it shows the rule bites,
not how often real programs hit it. Which of those rows would be accepted is not known until
the predictor is restated (section 6); do not read 81 as an expected acceptance count.

## 2. What is already true (probes on main, 2026-10-28)

The earlier B5 note expected this option to need changes to "raw plan extent validation and
inference". Probing says the plan side is not involved.

| Probe (declared box `S(k)`, `k = 4`) | Reference f64 / checked f64 / checked f32 |
| --- | --- |
| Assign-produced scratch of extent 2, read by a collector `S[k] := S1[k]` | accepted, **bit-identical** `[5, 7, 0, 0]` on all three legs; no error, no warning |
| Scatter-produced scratch of extent 2 (`S1[2*j]`, `j = 1`), read bare by `S[k] := S1[k]` | refused on every leg: `sizeConflict` uid k, `4 vs 2` |
| Same scatter scratch, read non-bare (`S[k] := S1[k + w]`, `w = 1`, so a padded read) | accepted, bit-identical `[5, 0, 0, 0]` on all three legs |

Consequences:

1. **Assign writers smaller than the box already collect correctly**, because a bare
   out-of-range read pads with the group's `0_K` (S3b) and assign outputs are not shape sources.
   Only B5's own equality obligation (`checkCollectorShapes`) blocks them.
2. **Scatter writers smaller than the box are blocked by a second, independent mechanism**:
   `inferAxisSizesCore` turns every scatter output into a read-position source
   (`scatterOutputShapes`, B3), and a bare single-axis read of a known size that differs from the
   scratch extent is a hard `sizeConflict`
   ([SizeInfer.lean](../../leanncd/LeanNCD/Eval/SizeInfer.lean)). The padded-read probe shows the
   plan, kernels and reference already execute a short scatter scratch correctly once that check
   does not fire.
3. So the change is **an obligation relaxation plus one inference exemption**. No `ScatterPlan`,
   `checkScatterCore`, dense kernel, algebra table, JAX or bridge change.

## 3. Options

| Option | Rule | Verdict |
| --- | --- | --- |
| **M1 (recommended): fit against an explicitly pinned declared box** | Box `D` exists only when the destination has a tensor declaration whose every axis is pinned by `axis … = n` (present in `explicitSizes`). Each writer, per dimension, needs realized extent `<= D`. Collector pads. Scatter scratches of a boxed group are exempt from the B3 bare-read conflict. | Smallest change; deterministic; keeps today's behavior everywhere else |
| M1' : box = any declaration | Same, but axes whose size is inferred also count | Rejected: the box size could be learned from one scratch and conflict with another in fixpoint order, so acceptance would depend on inference order. Also breaks `inferredBasis` (F30), where the scratch read is what sizes the basis |
| M2: allocate scatter scratches at `D` | Override `ScatterPlan.destShape` / `scatterOutShape` to the box | Rejected: reopens the B6 range-audit surface (`checkScatterCore`, extent clauses) to avoid a filter M1 does in inference |
| M3: union box for undeclared destinations | Box = max extent over writers | Rejected again, as in B5: acceptance and shape would depend on the writer set, and there is no declared authority |
| M4: judge fit by actual write image, not derived extent | Accept `S[2*i+2]` (`i = 2`, writes 2 and 4) into `S(5)` although its derived extent is 6 | Deferred: needs the scratch sliced to the box, i.e. M2 machinery. M1 is conservative by exactly the stride-aligned slack |

## 4. Proposed rule (M1)

For a bounded B5 group (unchanged eligibility: top-level plain assign/scatter writers, real or
tropical, bounded geometry):

1. **Box.** If `writerGroupBasis` selects a *declared* basis (distinct declared axes) and every
   basis axis UID is in `explicitSizes`, `D` is those pinned extents and the group is **boxed**.
   Otherwise the group is **exact**: B5's equality rule, byte-for-byte unchanged (declaration
   with inferred sizes, undeclared first-bare-assign basis).
2. **Fit.** In a boxed group, writer `k`, dimension `d`: realized extent `<= D[d]`. Realized
   extent is today's: assign = slot sizes, scatter = `LHSSlot.outExtent`. Ranks are still equal.
   Equal-rank, `<=`-per-dimension; no truncation, broadcast, or coordinate shift.
3. **Collector.** Unchanged. It reads each `T#k` over the declared basis axes; short scratches
   pad with the agreed sort's `0_K`, holes included. The published `T` has shape `D`.
4. **Inference exemption.** Scatter scratches `T#k` of a boxed group contribute no
   scatter-output read positions to `inferAxisSizesCore`. They need none: every basis axis is
   already pinned, so those positions could only ever raise the conflict. Mechanically an extra
   name set (computed from the obligations) passed to `inferAxisSizesCore`, which
   `evalScheduled` and `prepareEvalPlan` both call. Exact groups keep the current behavior.
5. **Diagnostic.** In boxed groups the failure is "exceeds", not "differs". Keep the constructor
   if the payload still reads honestly, else rename (`writerExtentExceedsBox`); the builder
   decides, but the render text must not say "expected extent" for a `<=` rule. A fit failure
   must still precede any B6 error for the same group.

Unchanged by M1: B6 (a write outside the scratch's own derived extent still errors), votes and
casts, route (`routeUnsupportedMultiWriter`), JAX, undeclared and exact groups, scan
conflicts, all-bare UID agreement, single-writer programs.

## 5. Conflicts and risks to settle before a plan

- **Declaration authority differs by writer count (Rule 7).** A *single* scatter into a
  declared tensor already lets the derived extent win over the declaration
  (`scatterExtentOverridesDeclared`; `S[2*i]` into `S(8)` yields shape 4). In a boxed
  multi-writer group the declaration wins (`T` has shape `D`). Adding a second writer would
  change a tensor's shape. Recommendation: leave the single-writer rule alone and document the
  asymmetry; reconciling it is a separate, owner-sized decision that also touches
  `Differential.lean`. Not part of B5b.
- **"Pinned" is a source-visible, order-free test.** Because it depends only on declarations, an
  accepted program stays accepted under writer reordering. The cost is that a user who leaves
  the box size to inference gets the old exact rule and a mismatch message; the diagnostic for
  an exact group whose writers would fit a pinned box should say so only if cheap (builder's
  call, not a requirement).
- **Tropical padding.** The probes were real-sum. The tropical pad identity (`-inf` / `+inf`)
  for a short scratch read by a max/min collector must be pinned on all three native legs, not
  assumed from S3b's single-read pad rule.
- **Conservative slack (M4).** `S[2*i+2]` style strided offsets can be refused although every
  write fits. Document it; do not widen here.

## 6. Oracle and test impact (to be recounted, not trusted from this note)

[OracleSortRules](../../leanncd/test/Semantics/OracleSortRules.lean) states strict equality in
`predictedExtent` / the shape-stage predictor (~lines 263-331), and its observation maps
`sizeConflict` onto a predicted `writerExtentMismatch`. M1 changes both: the predictor must
restate box membership (pinned declared basis, `<=` per dimension) independently of production,
and the `sizeConflict`-allowed-for-mismatch coupling must be re-examined, since a scatter
scratch fit under a box no longer conflicts. C1 SHAPED counts (the 81/99 split) and the
`strictCoverage`/vacuity guards need recomputation after the predictor change.

Existing pins that the rule flips, to be inspected one by one in the plan:
`B5NativeTest.bareMismatch` (pinned `k = 4`, bare writer over `j = 3`: becomes an accepted
box with a hole), `declaredMismatch` (pinned `k = 5`, scatter extent 4: expected to become accepted, once the exemption
removes its `sizeConflict`),
`B5BoundaryTest.lateMismatch` (writer 3, dimension 1: 2 `<=` 3, accepted), and the F07-F09
families that pin `writerExtentMismatch`. Each needs a nearest *refused* neighbor (a writer
that exceeds the box) and an inferred-size exact twin proving the old rule survives.

## 7. Verification bar and estimate

Process: **Full** (new accepted programs, changed shape authority, predictor restated) but
materially smaller than B5: no new carriers, kernels or backends. Rough shape, to be measured
by the plan: 10-14 fixture families, 8-12 mutation rows. Rules to pin and their distinguishing
mutants:

| Rule | Fixture / mutation |
| --- | --- |
| Concat accepted | `S[i]` + `S[i+2]` into pinned `S(4)` on three native legs and four oracle legs; mutate `<=` to `==` |
| Fit, not exceed | Writer one past the box refused with the new diagnostic, nearest accepted neighbor; mutate `<=` to `<`, or drop the check for scatter writers |
| Exact survives | Declared-but-inferred-size and undeclared groups keep B5's equality (old `bareMismatch`-shaped twins with inferred sizes); mutate "pinned" test to "declared" |
| Inference exemption scoped | Short scatter scratch accepted only in boxed groups; exact group still `sizeConflict`; mutate exemption to apply to all groups |
| Tropical holes | Short scratch under max and min, native f32 bits; mutate pad identity |
| Order independence | Reverse writer order; boxed acceptance unchanged |
| B6 untouched | Negative / zero-coefficient writer inside a box still `scatterWriteOutOfRange` or fit failure, by priority |
| Single-writer untouched | `scatterExtentOverridesDeclared` pins unchanged |

Token estimate, explicitly a guess: **25-45M** total (plan and prototype 5-8M; implementation
and fixtures 12-25M; mutation, review, close-out 8-12M), well under the ~175M execution
ceiling and the ~95M of the oracle-sorts effort. The assumption that breaks it: if the
tropical-pad or inference-exemption probes in the plan's T0 gate fail, M1 degrades toward M2
and the estimate must be redone. Plan T0 should re-run the three probes of section 2 and add
the tropical one before any production edit.

## 8. Owner decisions requested

1. **M1 over M1' / M2 / M3** (pinned declared box only; inferred and undeclared stay exact)?
2. **Leave the single-writer declaration asymmetry** (section 5) alone for now?
3. **Accept the M4 slack** (extent-based fit, strided offsets may be refused though they fit)?

Not requested: route/bridge or JAX (unchanged refusals), predicate or multi-axis scatter, scan
collection (F3).

Probe sources: scratch Lean files, not committed (`Probe.lean`, `Probe2.lean`, in the session
scratchpad); they import `Eval.Plan.B5NativeTest` and use its `ref64`/`run64`/`run32`
helpers. Re-create them in the plan's T0 gate rather than depending on them.
