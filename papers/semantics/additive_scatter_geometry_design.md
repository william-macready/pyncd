# Scatter geometry: multi-axis (`S[a+b]`) and constant-slot (`S[3]`) writes

## Execution status

| Slice | Implemented scope | Evidence |
| --- | --- | --- |
| A | Exact-reach multi-axis extents, constant lowering, top-level checked admission | [Slice A record](additive_scatter_geometry_a_record.md) |
| B | Multi-axis and lowered-constant groups and boxed single writers; surface `S[a + b]` and `S[=3]`; name marker deleted | [Slice B execution record](additive_scatter_geometry_b_record.md) |

The original admission table and probe descriptions below describe the pre-slice baseline, not
the current boundary. A lone numeral still denotes a scan base case. D5 still excludes a single
writer whenever any declared axis occurs among its source axes, including identity positions.
Scan-local multi-axis/constant slots, predicate groups and routed/JAX scatter remain outside scope.

**Decisions D1-D6 approved by the owner on 2026-10-30, all as recommended (section 7); not an
implementation plan.** Approval authorizes the P0 probe and then the plan for slice A only; slice B's
plan is written after A lands. Read against local `main` `87cfb2fb` on 2026-10-30. No
production change, prototype, or Lean run accompanies this note; every current-behaviour claim is read
from the linked source or from the S2a observation table
([p3_observed.md](additive_s2a_artifacts/p3_observed.md)) and is marked **(probe)** where P0 (section 6)
must confirm it before the plan ships. This is the "scatter-geometry slice" that
[B5 §1](additive_b5_design.md) and B5c D2
([single-writer box note §7](additive_single_writer_box_design.md)) deferred.

## 1. What is refused today, and where

| Layer | `S[a+b]` (multi-axis) | `S[3]` (constant coordinate) |
| --- | --- | --- |
| Surface syntax (`elabTLLHSSlot`, `DSL/Elab.lean`) | not parseable (slots are `x`, `x .`, `n`, `x +1`, `n*x`, `x+n`, `n*x+m`) | `S[3]` parses, but as `.iterAt` (a **scan base case**), not a coordinate |
| `lowerArith` (`DSL/Pipeline/Structural.lean`) | no guard | `.assign` arm: `overlappingScatter` (a conservative guard older than S3a); hand-built `.scatter` arm: no guard |
| Legacy evaluator | accepts, ⊕-sums collisions, derived extent `c0 + Σ c·n` | accepts via hand-built `.scatter`, extent `n+1` |
| Reference `evalScatter` | defined: source-driven, ⊕-fold, B6 range error | defined, same |
| Checked plan preflight (`checkScatterAffineExpr`, `Eval/Plan/Compile.lean`) | `multiAxisScatterLhs` | `scatterOrAffineLhs` |
| B5/B5b/B5c collector (`LHSSlot.boundedScatter`, `Collect.lean`) | group refused (`multiWriterScatter`); boxed single writer keeps the derived shape (B5c D2) | same |
| Scan-local scatter | checked refuses; reference overwrites instead of summing (F3) | same |
| Oracle / differential | admits both; fixtures (d), (d'), (f') end as `nativeFailure` with no condition | same |

So the gap is not semantics, and it is not (probably) the kernel. The reference already defines both
forms, and `ScatterPlan` already stores one coefficient row plus one bias per destination dimension
(`outCoeffs`, `outBias`, `Eval/Plan/Kernel.lean`); `scatterImageBounds` computes corner extremes over any
number of axes, so B6 range checking is already multi-axis-correct **(probe)**. What blocks admission
is one extent rule that disagrees with itself, a surface that cannot say these forms, and gates that
were written when the checked path could not run them.

## 2. Semantics (nothing new is decided here)

The reference is the specification. Each source coordinate (LHS axes plus every contracted RHS axis)
writes its value to the slot images; collisions ⊕-fold in the destination sort; an unwritten cell is
`0_K`; a write outside the extents is an error (S3a, B6).

* `S[3] := W[j]` is the **total reduction of `W` placed at coordinate 3**.
* `S[a+b] := A[a]*B[b]` is the **anti-diagonal sum, i.e. polynomial multiplication**; under `agg max`
  it is (max,+) convolution. S2a's fixture (d), `A=[1,2,3,4]`, `B=[1,10,100]`: `[1,12,123,234,340,400]`.

Both are well-defined because collisions sum. The `overlappingScatter` message ("a constant coordinate
collapses a dimension") describes the pre-S3a world where a collision was an error.

## 3. The three real problems

**P-extent (multi-axis).** `LHSSlot.outExtent` (`DSL/Ast.lean`, the single home) uses the stride-aligned
rule for one positive axis and a legacy `c0 + Σ c·n` for everything else. For `a+b` with `|a|=4, |b|=3`
that is 7, but the reachable coordinates are `0…5` (extent 6). Three derivations (reference, legacy,
checked `scatterDestExtent`) all call `outExtent`, so they agree with each other; they agree on an
over-approximation. S2a recorded this as `known:extent` against an oracle that uses the declared 6.

**P-const (constant slot).** `outExtent`'s `.const n` arm answers `n+1` (correct: coordinate `n` needs
extent `n+1`). The checked plan cannot tell it apart: `scatterDestExtent` rebuilds an `.affine` slot from
the placement row, and a constant is the row `[0…0]` with bias `n`, which is exactly `Out[0*i+n]`, whose
documented extent is `n` and whose every write is out of range (B6). `checkScatterAffineExpr` exists to
stop that silent disagreement; the refusal is a symptom of the plan IR having no way to say "constant".

**P-surface.** A user cannot write either form today (table row 1), so lifting the checked refusal alone
helps hand-built programs and the differential only.

## 4. Options

### P-const: how the plan says "constant"

| Option | Mechanism | Tradeoff |
| --- | --- | --- |
| **C1 (recommended): unit axis** | Compile `n` as the placement `n + 1·u` over a synthetic size-1 source axis `u` appended to the scatter's source domain. The existing `.affine` arm then gives `1·1 + (n/1)·1 = n+1` and the image is `n`. | Zero change to `ScatterPlan`, `checkScatterCore`, the range check, the kernels, or the extent function: the compile emits a legal plan the existing clauses already accept. Costs one extra extent-1 output dimension in the compute half (**probe**: that the compute half tolerates an output axis no factor reads). |
| C2: masked assign | Rewrite `S[3] := rhs` as `S[k] := [k = 3] * rhs` over a fresh axis `k` pinned to the declared extent. | No plan change either, but it needs a pinned declaration (no inference), silently drops out-of-range constants unless a separate static check is added, and replaces a scatter by an O(extent) masked assign. |
| C3: plan marker | Add `isConst` per placement row; the extent clause reads it. | Changes `ScatterPlan` (`DecidableEq`/`BEq`), the checker, both dtype workers and anything that pattern-matches the structure. The most invasive; rejected like MD in the B5c note. |

### P-extent: the multi-axis rule

| Option | Rule for a row naming 2+ axes | Tradeoff |
| --- | --- | --- |
| **M1 (recommended): exact reach** | `max image + 1` (clamped at 0; 0 if a source extent is 0), computed from the same corner formula as `scatterImageBounds`. `a+b` over (4,3) → 6; `a+4b` → 12. | Changes the published shape of the (hand-built only) multi-axis programs legacy accepts today. P0 counts which test modules move. A true single-home change: reference, legacy, checked, collector and scan all inherit it. |
| M2: keep `Σ c·n` | Extent 7 for `a+b`; the trailing cell holds `0_K`. | No existing shape moves, but new programs publish an extra unreachable cell, the S2a `known:extent` divergence against the declared-shape oracle stays for these forms, and the over-approximation is permanent. |

The single-axis stride-aligned rule (`2*i`, n=4 → 8) is **unchanged** under either option: it is a
deliberate whole-strides convention, and changing it would move the shape of every accepted upsample.

### P-surface: how a user writes them

* Multi-axis: add a slot form `x + y` / `n*x + m*y` (a sum of two or more axis terms, optional numeral
  bias), elaborated to `.affine bias [(c, axis)…]`. The existing single-axis patterns keep elaborating to
  their current constructors (`.shift`, `.scale`, `.affine`), because `Out[0*i]` versus `.const` is pinned
  by `CompileTest` and `ScatterCompileTest` S9 and must not move. Coefficients stay non-negative
  numerals as today (a negative reach is a B6 error anyway).
* Constant: **do not** reinterpret a lone numeral. `S[3]` is already the scan base case, and a mistyped
  scan (a base case with the step statement forgotten) would silently become a constant write, which
  Rule 12 forbids. Use an explicit marker (placeholder `S[=3]`; the builder picks a token that cannot
  collide with `n`, `x .`, `x +1`).

## 5. Recommended design

Two slices, engine first (the B5 → B5b → B5c ordering that worked):

**Slice A, engine and oracle (programmatic forms).**
1. `outExtent`: multi-axis reach (M1). Constant arm unchanged.
2. Compile the constant slot as a unit-axis placement (C1), as a `lowerArith` rewrite (P0 item 2);
   delete the `.multiAxis` throw at **top level** in `checkScatterLHSSlot`. *Refined at plan time,
   2026-10-30:* the top-level `.constant` throw **stays**, narrowed to its true remaining meaning: a
   hand-built schedule that bypasses `lowerArith` and hands the preflight a raw constant slot is refused
   with `scatterOrAffineLhs` (without it, P0 item 1 shows that program failing later with a confusing
   `scatterImageOutOfRange`). Every program through `compileToScheduled` has its constants rewritten
   first, so none reaches that arm. `checkScanScatterLHSSlot` keeps both refusals (scan-local placement
   is non-injective for multi-axis and overwrites in the reference, F3), so `scatterAffineClass` stays.
3. Drop the `.assign`-arm `overlappingScatter` guard for constant slots (stale since S3a; the
   `.scatter` arm has had none since then). *Refined at plan time (owner, 2026-10-30):* the guard stays,
   narrowed, for a constant slot inside a scan statement (one carrying `iterAt`/`iterNext`), because
   deleting it outright made such a program compile and then overwrite in the reference and legacy
   evaluators (F3) while the checked preflight refuses it: a fail-loud regression. So
   `overlappingScatter` keeps one producer (scan-local `.assign`), it does **not** become producerless.
4. Oracle/differential: retire the capability-gap `nativeFailure` for (d), (d'), (f'); they become parity
   fixtures. Add: tropical convolution **on the four-leg sorted differential** (owner, 2026-10-30:
   `Source.SortedDifferential.compareSortedSource`, brief
   [additive_scatter_geometry_tropical_fixture_brief.md](additive_scatter_geometry_tropical_fixture_brief.md)),
   f32, mixed-sign and negative rows (B6 error, both backends). Parked, not in slice A: mutation-checking
   the new-module pins independently of the older B5 pins (they share an import chain, about 0.3
   dispatch).
   *Refined at plan time:* the constant-writer-under-a-boxed-declaration fixture (fit failure reports
   `writerExtentExceedsBox`) is **slice B**, because boxed single writers of these geometries stay on the
   derived-shape rule until `boundedScatter` stops gating (B5c D2). Slice A pins that residual instead.
5. Update the live nodes in the same plan (`Eval/Plan/AGENTS.md`, `Semantics/AGENTS.md` lines about
   `scatterOrAffineLhs`/`multiAxisScatterLhs`, `Error.lean` doc comments), not as a later audit.

**Slice B, groups and surface.**
1. `LHSSlot.boundedScatter` stops gating top-level groups: multi-axis and constant writers join B5
   groups, and a boxed single writer of these forms joins the one-writer group. This **closes B5c D2**.
   `checkCollectorShapes` already calls `outExtent` per slot, so it needs no new arithmetic.
2. Surface syntax for both forms (section 4).
3. Scan-local stays refused; documented, not worked around.

**Invariants the slices must keep** (each becomes a test that fails when violated):
* every program accepted today publishes the same shape and values, **except** hand-built multi-axis
  scatters (M1 shrinks their extent); the exception list is measured in P0, not assumed;
* single-axis extents (stride-aligned rule) do not move;
* reference, legacy, checked f64 and checked f32 agree on value and shape for every new fixture;
* a constant or multi-axis write outside its extents is an error in both backends, never a silent skip.

## 6. Probe P0 (Direct path, before any plan; throwaway)

Cheap facts the design leans on and this note has not measured:
1. Remove the two `checkScatterAffineExpr` throws in a scratch worktree: does the checked backend then
   match the oracle on (d) `A=[1,2,3,4], B=[1,10,100]` (declared 6 and 7) and on a mixed-sign row? (Tests
   that the kernel and range check really are multi-axis-ready.)
2. C1 feasibility: where `compileScatter` builds the source domain, can an extent-1 axis no factor reads
   be appended, and does `checkScatterCore` accept `n + 1·u` as extent `n+1`?
3. What `route`, the bridge agreement proof and the experimental JAX codegen do with one multi-axis or
   constant scatter today (the stance below is "unchanged"; confirm they do not newly break).
4. M1 blast radius: run the full `Tests` build with the extent change and list failing modules and
   guards, as the B5c spike did.

### P0 results (run 2026-10-30, throwaway worktree on `6c4a737e`, since removed)

Probe source: [P0ScatterGeometryProbe.lean.txt](additive_scatter_geometry_artifacts/P0ScatterGeometryProbe.lean.txt)
(each case prints reference, checked, and `route` outcomes). Inputs `X=[1,2,3,4]`, `W=[1,10,100]`. The
edits (the `checkScatterAffineExpr` throws, an M1 arm in `LHSSlot.outExtent`) were never committed.

1. **Lifting the refusal: confirmed for multi-axis, confirmed as predicted for constants.** With the
   throws removed and no M1: `Y[a+b]` and `Y[a+4b]` give checked = reference in value and shape
   (`[7]`, `[16]`). So the kernel, the placement rows and the range check are multi-axis-ready. A
   constant slot fails in `prepareEvalPlan` with `scatterImageOutOfRange "Y" 0 3 3 3` (image 3..3 in
   extent 3) while the reference publishes `[4]`: exactly P-const. Mixed-sign `a-b` is an error in both
   backends (reference `coord [-1]`, checked `scatterImageOutOfRange`).
2. **C1 holds at source level, which suggests it is a `lowerArith` rewrite, not a plan change.**
   `tlprog!{ axis u : ℕ = 1  Y[u+3] := X[a] }` (an extent-1 axis read by no tensor) gives `[4]`,
   `[0,0,0,10]` in both backends, with `route` OK. The compute half accepts an unread output axis, and
   the existing `.affine` arm derives `n+1`. Not tested: the rewrite itself (a fresh UID plus a size-1
   pin from inside `FreshM`), and its interplay with groups and boxed declarations. P0 does not
   exercise those, so the plan must.
3. **`route` and JAX.** `route` returned OK for every case, including the four the checked backend
   refuses today (it carries no extents), so the "unchanged" stance in D1 holds. The JAX codegen
   refuses every `.scatter` step categorically (`unsupportedStep`, `EvalPlanCodegen.lean`), by
   reading only: geometry cannot change that. The bridge agreement proof was not examined; `Bridge/`
   mentions scatter only in the `AcsetCodec` tag table, and `route` is untouched by slice A.
4. **M1 blast radius, two full builds (`LeanNCD Tests JaxExperiment`).** Not checked: whether Lake
   skipped dependents of a failing module.

   | Build | Failing modules | Guards |
   | --- | --- | --- |
   | M1 only (refusals kept) | 2 | `ScatterCheckTest` 162, 220, 238; `SourceDifferentialScatterTest` 250, 252, 265, 266 |
   | M1 plus top-level lift | 3 | the 7 above, plus `CompileTest` 99, 120 (refusal pins) and 336 (a still-refused donor that must be re-donored), `SourceDifferentialScatterTest` 131, 137, 138, 295, 296, 304 (nativeFailure tags and refusal-text pins) |

   Every failing guard pins the legacy extent convention or a refusal slice A deliberately removes;
   no other `Tests` module and nothing in `JaxExperiment` moved. Reference shapes under M1: `a+b` →
   `[6]` (the oracle's declared shape), `a+4b` → `[12]`.

**Wrinkle P0 found in M1.** For rows with a negative coefficient the legacy `c0 + Σ c·n` is not an
over-approximation; it can be *smaller* than the reach. `ScatterCheckTest` 220 and 238 build their B6
boundary cases from that (`2a - b + 1` over `[3,2]`: legacy extent 5, image `[0,5]`, so a write at 5 is out
of range). Under M1 the extent is 6 and the same row is in range. M1 therefore also *widens* acceptance
for mixed-sign rows whose minimum is already non-negative (hand-built only; refused by the checked
backend until slice A). D3 stands, since reach is the right extent, but the slice-A plan must re-pin
those guards with an explicit `destShape` rather than a derived extent, and must say so in the record.

## 7. Decisions (all approved as recommended, 2026-10-30)

* **D1 scope.** Checked f64/f32, legacy and oracle in slice A; `route`, JAX and scan-local unchanged.
  Recommended: accept (the same cut B5 and B5b made).
* **D2 constant representation.** C1 unit axis (recommended), C2 masked assign, or C3 plan marker.
  If P0 item 2 fails, fall back to C2 (declaration required, so a constant slot into an unpinned
  destination is refused with a locator), not to C3.
* **D3 multi-axis extent.** M1 exact reach (recommended) or M2 keep `Σ c·n`. M1 is the only option that
  removes the `known:extent` divergence for these forms.
* **D4 surface.** Add multi-axis `x + y…` and an explicit constant marker in slice B, with the
  lone-numeral meaning unchanged (recommended); or leave both programmatic-only.
* **D5 guard.** Delete the `.assign`-arm constant-slot `overlappingScatter` guard (recommended); it
  contradicts S3a and is reachable only through the new constant syntax or hand-built programs.
* **D6 slicing.** A then B (recommended), or one slice. Rough cost, a guess calibrated on B5b/B5c
  (30-50M each): A about 35M, B about 35M. One slice would exceed the Rule 6 authoring target.

## 8. Non-goals and anti-goals

* Not in scope: scan-local multi-axis/constant (needs F3, overwrite versus ⊕), predicate/bool
  destinations (B5 D1), negative coefficients or biases in surface syntax, a new `route` or JAX scatter
  capability, M4 actual-image box fit.
* **Anti-goals (a failure even if tests pass):** changing the stride-aligned single-axis extent;
  reinterpreting a lone numeral slot; a constant or multi-axis write that is silently skipped or
  clamped; a second extent formula (the extent stays computed in one place).
