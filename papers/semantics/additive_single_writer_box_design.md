# B5c: a pinned declaration decides the shape for every writer count

**Status: approved by the owner 2026-10-29: the rule (option A, all writers), D1-D3 as recommended,
the go decision (D4) and the D5 refinement. Implementation plan `additive_b5c_plan.md` (D3's identity
criterion is subsumed by D5, plus a rank-0 exclusion, see the plan section 2). Not yet executed.** Read against local
`main` `b45deb9b`. It removes the asymmetry B5b left between a single writer and a boxed group
([additive_b5b_containing_box_design.md](additive_b5b_containing_box_design.md) section 5).

## 1. The asymmetry, measured

Probes on `b45deb9b`; reference, checked f64 and checked f32 agree in every row.

| Program (`axis i = 2`, `A = [-5, -2]`) | Published `S` shape |
| --- | --- |
| one scatter `S[2*i] := A[i]`, `S` declared with `k = 4` pinned | `[4]` (derived) |
| same, `k = 8` pinned (declared larger) | `[4]` |
| same, `k = 3` pinned (declared smaller, yet the writes at 0 and 2 fit it) | `[4]`, no error |
| same, `k` unpinned | `[4]` |
| one bare assign `S[i] := A[i]`, `S` declared with `k = 4` pinned | `[2]` (the declaration is ignored) |
| two writers `S[2*i]`, `S[2*i + 1]`, `k = 8` pinned (B5b box) | `[8]` (declared) |
| a reader `R[k] := S[k]` over pinned `k = 8` after a single writer | refused, `sizeConflict 8 vs 4` |

So a single writer silently publishes its derived shape and ignores a pinned declaration, in either
direction and for bare assigns as well as scatters, while a second writer makes the declaration win.
The independent oracle already uses the declared shape: the single-writer
`scatterExtentOverridesDeclared` condition (`Semantics/Source/NumericalProfile.lean`,
`Differential.lean`) is exactly this difference, recorded as a known divergence.

## 2. The rule (approved)

A destination is **boxed** when it has a tensor declaration whose every axis is pinned by
`axis … = n` or `iter … = n` (B5b's test, unchanged). For a boxed destination, whatever the number
of top-level plain writers:

1. the published tensor has exactly the declared extents;
2. each writer's realized extent (assign: slot sizes; scatter: `LHSSlot.outExtent`) must fit,
   per dimension `<=` the box, else `writerExtentExceedsBox T writer dimension box actual`
   (the same diagnostic as B5b; a declared extent smaller than the derived one is refused even when
   the actual writes happen to fit, the M4 slack, deliberately);
3. cells no writer reaches hold the sort's `0_K`.

Every other destination (undeclared, declared with an inferred axis) keeps the derived shape, as
today. **Refinement found by the spike (D5):** a declared axis that the writer itself uses as a
*source* axis does not count as a claim about the extent. The idiom `tensor Out(i)` with
`Out[2*i] := X[i]` declares `Out` over the source axis `i` (pinned to the size of `X`); the output is
legitimately twice as wide, and the declaration names the axis, not the output extent. A destination
is therefore boxed for a given writer only if no declared axis occurs in that writer's slot
expressions. Taken literally, the rule below refuses that idiom (section 5).

D1 (predicate destinations excluded) and D2 (geometry a single writer has today keeps the
derived-shape rule) are taken as the owner's recommendations.

## 3. Why a mechanism is needed, and the one proposed

Single-writer programs are "byte-identical through every later phase" today (`desugarMultiWriters`
is the identity unless a name has two writers). Padding the published tensor to the box needs
either a collector or a destination-shape override in the scatter plan.

| Mechanism | Verdict |
| --- | --- |
| **MC (proposed): treat a boxed single writer as a one-writer group** | Reuses the B5b collector, fit check, `boxedScratchNames` / `sizingView` and diagnostics. No change to `ScatterPlan`, `checkScatterCore` or the dense kernels, so the B6 range audit is untouched. |
| MD: override the scatter destination shape to the box | Rejected: reopens `scatterDestExtentMismatch` and the range clauses B6 audited, and does nothing for bare assigns. |
| ME: pad in a post-execution step | Rejected: a second implementation of padding in both backends. |

**Identity writers.** Routing every pinned-declared tensor through a scratch and a collector would
change the plan of nearly every program. So a single writer stays untouched when its extents equal
the box by construction: a plain assign whose slots are all bare free slots with UIDs equal,
position by position, to the declared axes (same axis, same pinned size). Every other single writer
into a boxed destination (any scatter; an assign over different axes) becomes a one-writer group.

## 4. What changes and what does not

- `desugarMultiWriters` (`Collect.lean`): `writerGroups` also yields a single plain writer of a
  boxed destination unless it is an identity writer. `needsB5` / `checkWriterGroup` / the shape
  obligations and `boxed` flag extend to it. Geometry a single writer has today but a group may not
  is decision D2.
- **`route`**: the B5 refusal stays at two or more writers. A single boxed writer keeps routing as
  today (route carries no extents), so route and the native backends publish different shapes for
  these programs; document it rather than refuse a program route accepts now.
- **Oracle**: `scatterExtentOverridesDeclared` is retired for boxed destinations (it becomes
  value parity); `predictShaped` / `pinnedBox` extend to one-writer groups. The unpinned/undeclared
  single-writer case keeps the condition.
- **Unchanged**: B6, scan-local writers (top-level plain statements only), votes and casts,
  JAX, unpinned destinations, all multi-writer behaviour.

## 5. Blast radius (measured by a throwaway spike, 2026-10-29)

Spike branch `worktree-b5c-spike` (kept, not for merge): a `boxedSingleGroups` function feeds
single non-identity writers of boxed destinations into the existing group machinery from
`collectDefinitions` only, so `route` and the `Bridge/Agreement` proof are untouched. `LeanNCD`
compiles. Full `Tests JaxExperiment` builds, counting failing modules:

| Rule | Failing modules | What fails |
| --- | --- | --- |
| A as first written (a pinned declaration is a box for every writer) | **8**: `CompileTest` (6 guards), `SourceDifferentialScatterTest` (3), `DefaultF32Test`, `Scatter32OracleTest`, `BoolCastTest`, `GenerativeTest` (DF4 sinusoidal embedding), `DualityTest`, `PropertyOracle/ScanUnroll` | The idiom above: `Out[2*i]` into `Out(i)`, refused with `writerExtentExceedsBox` (extent 4 against 2). In most of these the declaration is not in the source: the f64 test harness (`explicitF64Decls`, `test/Eval/ExplicitF64.lean`) synthesizes `tensor f64 name(axes)` for every undeclared tensor from its first use site, which for `te[2*i]` (DF4) is the slot axis `i`. A hand-written `tensor f64 Out(i)` behaves the same. |
| A with D5 (declared axes the writer uses as source axes are not a claim) | **2**: `SourceDifferentialScatterTest` (3 guards), `DefaultF32Test` (1 variant) | The three oracle known-difference pins (`fH9` is `known:extent` today, `fR`'s legacy and checked failure texts) move as expected, since `scatterExtentOverridesDeclared` is the divergence this removes. `DefaultF32Test` compares a program with undeclared tensors against the same program declared `f32`; a boxed declaration now changes the plan (an extra scratch and collector), so that variant needs its declaration migrated. |

Neither row counts modules that depend on a failing module and were skipped by the build (not
checked whether the two failing modules in the second row have dependents). The residual asymmetry under D5 is only the idiom: a
single writer whose declaration names its own source axis keeps the derived shape, and a multi-writer
group of that shape was already refused (B5 equality, B5b fit), so nothing regresses there.

## 6. Cost and process

Process **Full**: changed shapes for accepted programs, a restated predictor, a retired differential
condition. Estimate, a guess: 30-50M tokens, similar to B5b plus the blast-radius migration. The
B5b patch-driven plan format fits unchanged.

## 7. Decisions requested

- **D1: predicate-declared destinations.** B5 refuses predicate scatter groups (bool collision rule).
  Either exclude predicate destinations from this rule (they keep the derived-shape rule, a
  documented residual asymmetry), or extend the collector to bool first. Recommended: exclude.
- **D2: geometry a single writer has today but a group may not.** A single multi-axis, constant-slot
  or predicate scatter into a boxed destination is accepted today (derived shape). Under MC it would
  join the group path, which refuses those geometries. Recommended: keep them on the derived-shape
  rule when boxed (excluded from this rule, documented), so no accepted program becomes refused for
  geometry; revisit with the scatter-geometry slice.
- **D3: the identity-writer criterion** (UID equality with the declared axes, all bare free slots).
  Recommended: accept.
- **D4: go/no-go.** Measured above: with D5, two modules and four guards move, all expected.
  Recommended: go.
- **D5: the refinement.** A declared axis used as a source axis of the writer is not an extent
  claim (the upsample idiom keeps today's derived shape). Recommended: accept; the alternative is to
  refuse the idiom, which the spike shows breaks eight modules including real portfolio programs.

Not in scope: the geometry extensions behind D1/D2, route or JAX shapes, fit by actual write image
(M4), inferred-size boxes, F3.
