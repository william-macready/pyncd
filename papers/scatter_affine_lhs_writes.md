# Scatter and affine LHS writes — slice decomposition and verified design inputs

**Status:** planning artifact, authored 2026-09-09 against `main` = `79fa71f`, tree clean, default
`lake build` green at **8660 jobs** and `lake build JaxExperiment` green at **8513 jobs**.

**This is NOT yet an implementation plan.** It is the measured decomposition of what
`papers/post_audit_roadmap.md` Section B calls "Slice 2", plus the design work already verified for
one half of it. Section B assumed a single slice; measurement says two, nearly disjoint. §1 is the
evidence, §2 the decision, §3 the parked design, §4 what remains to author.

---

## 0. The three corrections to this document's own inputs

Each would have changed what got built.

> **Correction 1 — strided rows are admitted at STEP as well as base; the compile-error list says
> the opposite and is wrong.**
>
> `docs/superpowers/plans/2026-09-09-slice2-compile-error-list.md` site S2 concludes *"the audit's
> answer is already fixed: `| some (.strided ..) => false`, i.e. strided is a base-phase-only
> kind."* It reaches that by reading the audit's R15/R16 × column-5 cells, marked **`b`**, as a
> prescription. They are a **description of current behaviour** — finding B2-F2 is explicit that it
> is a census (*"Every site either forbids a strided row (6 `b` cells, all at step) or ignores
> it"*), taken before any decision was made.
>
> Roadmap §0 is the binding authority and post-dates the audit. The question it settled: *"may a
> strided write row appear in the base block, or only in the step block?"* — **Decision A: both.**
> Decision B, rejected, was step-only; audit §B2.1 spells it out as *"the same branch additionally
> gated `&& contextWidth > 0`, i.e. step writes only."* **Step is admitted under either decision.**
> "Base-phase-only" is a third option no input endorses.

> **Correction 2 — the classifier branch the audit adopted has a live soundness hole.**
>
> Audit §B2.1's adopted branch carries no guard on the sign of `scale`/`offset`. Measured: within
> `scale ∈ 1..5`, `offset ∈ -6..-1`, `outDim ∈ 1..8` there are **200** combinations where the extent
> check *passes* and a written coordinate is still negative, which `commitWrite`'s `Int.toNat`
> collapses onto index 0. Concretely `scale = 2, offset = -1, outDim = 3` demands `stateDim = 5`,
> writes `[-1, 1, 3]`, stores to `[0, 1, 3]`: the write meant for cell −1 silently overwrites cell 0
> and cell 4 is never written [snippet, `negative.lean`]. Independently confirmed by the
> write-pipeline recon, which measured the stronger form — a negative index **clobbers a legitimate
> write** (`Out[i-1]` with 10,20,30,40 into a 4-cell state → `#[20,30,40,0]`), no panic, no
> diagnostic.
>
> §3.1's branch therefore adds `c > 0 && bias ≥ 0`. It closes all 200 and costs nothing a surface
> program can express (the elaborator builds coefficients through `Int.ofNat`, audit B1-F9). It is
> also how audit §B2.6 Tier-1 item 10 gets satisfied at the classifier rather than downstream.

> **Correction 3 — the canonical interleave is recoverable, not a documented limitation.**
>
> The compile-error list's S6 records that `writesCollide` can never separate two strided rows, so
> `dp[0, 2*j] := A[j]` alongside `dp[0, 2*j+1] := B[j]` is inexpressible. A sound rule exists: two
> strided rows at one dimension are disjoint when their scales are equal and their offsets differ
> modulo that scale. Verified exhaustively over `scaleA, scaleB ∈ 1..5`, `offsetA, offsetB ∈ 0..7`,
> `extentA, extentB ∈ 0..7` (~102,000 combinations) that the rule **never** claims disjoint when the
> images intersect [snippet, `collide.lean`]. Of 300 different-scale pairs sampled only 24 (8%) are
> genuinely disjoint, so restricting to equal scales gives up very little.

---

## 1. The scoping finding — this is two slices, not one

### 1.1 A strided write into scan state is unreachable from surface syntax, in BOTH phases

Measured [ran `lake env lean spikes/L3Probe.lean`, probe since removed, tree clean]:

```
STEP strided  -> LeanNCD.CompileError.scatterInScan "S"
BASE strided  -> LeanNCD.CompileError.scatterInScan "S"
top-level     -> COMPILED
plain scan    -> COMPILED
```

with programs `iter l = 3 / S[2*j, 0] := X[j] / S[2*j, l +1] := S[2*j, l]` (step), the same with a
plain step (base), `Out[2*i] := X[i]` (top level), and `S[j,0] / S[j,l+1]` (control).

`checkScatterNoScan` (DSL phase 7) rejects a scatter-shaped LHS combined with any iteration slot,
identically in base and step. **So Decision A vs B was a choice between two options that are both
currently unreachable**, and making either reachable means lifting a deliberate DSL guard whose own
docstring gives its reason. Neither the audit nor the roadmap mentions this — an omission in both,
not a wrong assertion, which is why no review round caught it.

### 1.2 The two slices

| | **S-A · top-level scatter** (`Out[2*i] := X[i]`) | **S-B · strided scan-state writes** (`dp[l+1, 2*j]`) |
|---|---|---|
| Blocked by | one barrier (`checkStmt`'s `.scatter` arm), over a **missing IR node** | DSL guard L3, then the nine `WriteRowKind` sites |
| Touches `WriteRowKind`? | **no** — `writeRowKinds` has three call sites, all scan machinery | yes — all of Slice 1's tripwire |
| Reference semantics | **exists, tested, measured working** | **none** — `evalStmtSliceSeeded` rejects non-`.assign` in a scan slice |
| Differential leg 2 | available | unavailable |
| Closes `backend_missing_functionality.md`'s Hard row | yes | no |

**Consequence worth stating plainly: Slice 1's tripwire and the entire nine-site compile-error list
serve S-B, not S-A.** Section B pointed the planning at the smaller and less valuable half.

### 1.3 Decision: S-A first

Chosen by the user, 2026-09-09. Reasons: it matches an already-implemented, already-tested reference
semantics so the differential harness can prove it; it closes the Hard row; and it delivers the
capability the whole enquiry started from. S-B is deferred with its design already verified (§3).

---

## 2. What S-A requires (outline — the detailed task breakdown is still to author)

### 2.1 The reference semantics it must reproduce, not invent

`Eval/Eval.lean` executes affine LHS writes end to end from surface syntax today. Measured:

| Program | Result |
|---|---|
| `Out[2*i] := X[i]`, `X=[1,2,3]` | `shape=[6] data=#[1,0,2,0,3,0]` |
| `Out[2*i+1] := X[i]`, `X=[1,2,3]` | `shape=[7] data=#[0,1,0,2,0,3,0]` |
| `Out[i+2] := X[i]`, `X=[1,2,3]` | `shape=[5] data=#[0,0,1,2,3]` |
| `Y[i,i] := V[i]`, `V=[7,8,9]` (diagonal trigger, no `.affine` slot) | `shape=[3,3] data=#[7,0,0, 0,8,0, 0,0,9]` |
| `Up[2*i] := X[i]` then `Z[k] := Up[k]` | `Z: shape=[6] data=#[1,0,2,0,3,0]` |

The last is load-bearing: sizing already flows *out of* a scatter into a downstream consumer, with
`test/Eval/Portfolio/GnnScatterTest.lean` SC1–SC8 as the permanent regression suite.

Collision semantics is fully defined on the reference path: `CollisionReduce` is
`rejectCollisions | overwrite | sum | max | min`, `ScatterOpts := { fill := 0, reduce := .rejectCollisions }`,
out is initialised to `fill`, a `writtenBy` map detects collisions, and **out-of-range output
coordinates are skipped silently**. The checked layer's obligation is to *reproduce* this, including
the silent skip and the two `.toNat` degeneracies (negative extent → 0 → empty tensor; zero
coefficient → empty tensor), because differential parity against leg 2 is the gate.

Only `fill = 0` + `rejectCollisions` are surface-reachable — `lowerArith` hard-codes them and there
is no `fill`/`reduce` syntax. The other four policies are implemented and tested but unreachable.

### 2.2 The representation decision — the sharpest hazard

Two options, and they differ in whether the compiler helps:

- **New `PlanStep.scatter` + a `ScatterPlan` kernel type.** Every exhaustive match becomes a compile
  error, including the JAX leg's `lowerCheckPlanToCandidate`. **Recommended** — it is the discipline
  Slice 1 exists to install.
- **Widen `AssignPlan`** with a write map / fill / reduce. **No compile error anywhere on the JAX
  side**; `jaxAssignSupported` passes the new fields silently and `loweringToAffineTableCandidate`
  renders a *dense* assignment for a plan that means a scatter — a silently wrong result stamped
  with `ExecutionEvidence`.

### 2.3 The build gate is two targets, not one

`leanncd/lakefile.toml` sets `defaultTargets = ["LeanNCD", "Tests"]`; `JaxExperiment` carries the
comment *"Deliberately absent from `defaultTargets`: it only builds when explicitly requested."*
So **`lake build` can be green while the JAX leg no longer compiles.** Both gates are required:
default **8660 jobs**, `JaxExperiment` **8513 jobs**. The ad-hoc driver
`experiments/jax_bridge/EvalPlanAffineCorpus.lean` is in no library and needs building by hand.

JAX need not move in lockstep: `checkJaxAssignSupport` is an independent subset filter that already
rejects four things the checked backend executes (Boolean destination, Boolean source, tropical
max/min, contextful assignment). "Checked-plan admits, JAX declines" is the documented normal state
— but it must be made explicit with a `JaxSupportError`/`unsupportedStep` arm; nothing prompts it.

### 2.4 Corpus and test surface

- **Do not add a scatter program to `enumPrograms`.** It breaks three gates at once: the
  `#guard total == 3832 && accepted == 3832 && rejCounts.isEmpty` in `DifferentialTest.lean`, the
  `expectedCount := 3832` in `EvalPlanAffineCorpus.lean`, and the corpus driver's own fatal-on-
  rejection throw. The repo's own solved pattern is a **separate curated corpus** mirroring
  `predicatePrograms` (10 entries, kept out of `enumPrograms` with the rationale written twice).
- **6 category-(a) pinning fixtures** must change: 2 in `CompileTest.lean`, 4 in
  `ScanCompileTest.lean`. **6 further sites are frozen historical classifiers**
  (`ContractTest.lean`, `ScanContractTest.lean`) and updating them would be the defect.
- Live corpus values for the value-grep sweep: scan-free **3832/3832**, curated scan corpus
  **17 / 17 / 0 / 0**. The "13/0/4" triple in older prose is **stale** Thread-4-era text.
- The constructor-enumeration count is **6 prose sites + 1 AGENTS.md node**, not the "four
  docstrings and one node" Section B claims.

### 2.5 Still to measure before the task breakdown is written

The compile-error set produced by adding the scatter IR node — the analogue of the nine-site list
that sized S-B. A measurement agent for this was dispatched and stopped when the session ran low; it
had not mutated anything. **This is the first thing to do on resuming.**

---

## 3. S-B's design, verified and parked

Not to be built yet. Every claim below was compiled and evaluated against the real `leanncd`
environment via `bash .claude/skills/slice-plan/check-snippet.sh`, not reasoned about.

### 3.1 The classifier branch

```lean
| [(c, p)] =>
    if c == 1 && p < contextWidth && bias == 1 then some (.advancing p)
    else if c == 1 && p ≥ contextWidth && bias == 0 then some (.free (p - contextWidth))
    else if c > 0 && bias ≥ 0 && p ≥ contextWidth then some (.strided (p - contextWidth) c bias)
    else none
```

Audit §B2.1's adopted form plus Correction 2's sign guard. Measured: ordering is load-bearing
(`classifyM 2 #[1,0,0] 1 == some (.advancing 0)` vs `classifyM 2 #[0,0,1] 1 == some (.strided 0 1 1)`
— a strided branch placed *before* the advancing branch swallows every advancing row); `scale = 0`
is not a singleton nonzero and classifies as `.pinned bias`; negative scale, negative bias and
multi-nonzero rows all give `none`.

### 3.2 The extent rule — one call, and it subsumes `.free`

```lean
/-- Synthetic single-axis spec standing in for "the block output axis at `outputPos`".
    The checked plan is positional and UID-free, so the UID is arbitrary and never escapes. -/
private def synthAxis : AxisSpec := { name := "·", uid := 0, kind := .nat }

/-- Output extent of a strided write row, obtained by CALLING the shared scatter-extent
    formula rather than restating it. -/
def stridedExtent (scale offset : Int) (outDim : Nat) : Option Nat :=
  LHSSlot.outExtent (.affine (.affine offset [(scale, synthAxis)])) (fun _ => some outDim)
```

**This CALLS `LHSSlot.outExtent`; it does not restate it.** Recording that explicitly because a
reviewer misread the signature alone as a second extent formula — the `scatterOutDim` duplication
this repo already paid for once. The docstring must keep saying so.

Measured: agrees with the `.shift` arm over `s, c ∈ 0..7`, the `.scale` arm over the same, and the
`.affine` arm over `s, c, c₀ ∈ 0..5` — so **one call covers all three families** the payload
selects, and a three-way dispatch is unnecessary. `stridedExtent 1 0 s == some s` for `s ∈ 0..11`,
so it **subsumes** `freeExtentsAgree`'s `.free` equality (roadmap E5 / audit B2-F4) rather than
sitting beside it. Reproduces audit §B2.4's S21 numbers: `(some 6, some 6, some 9)`. Compiles inside
`namespace LeanNCD.Eval.Plan` with **no `open` and no new import**.

**Do not write the tighter bound** `scale·(outDim − 1) + offset < stateDim`: measured to disagree
with `outExtent` by exactly `scale − 1` over `scale ∈ 1..8`, `offset ∈ 0..8`, `outDim ∈ 1..11`. That
is the `scatterOutDim` drift in miniature (fix `fc10d70`, duplicate deleted `6a26825`).

**Why `pinnedLiteralsInRange => true` is then defensible for strided.** With the classifier's
`c > 0 && bias ≥ 0` gate and equality `stateDim == stridedExtent scale offset outDim`, every written
coordinate provably lands in `[0, stateDim)` — brute-forced over `scale ∈ 1..8`, `offset ∈ 0..8`,
`outDim ∈ 1..11`. The compile-error list flags that site as a trap where the right answer and the
lazy answer are the same text; this is what separates them, and the dependency must be recorded in
the arm's own comment.

⚠️ **Do not uniformize the pinned arm to equality.** `freeExtentsAgree` is the `.axis` arm and
`advancingSizeMismatch` the `.shift` arm, but `pinnedLiteralsInRange` is deliberately an
**inequality**; making it an equality would break every pinned base write.

### 3.3 The cover rule — uniform across both phases

**Wherever a clause counts `.free p` into the positional cover, it counts `.strided p _ _` too**, in
both phases. Measured: B2-F1's sixth-instance cell closes (the audit's bug case
`#[pinned 0, strided 0 2 0, free 0]` goes `true` → `false`); well-formed strided writes are admitted
at base and step; clause 2 is untouched so a strided row at an *advancing* dimension stays forbidden;
and out-of-order or duplicated cover positions still fail.

**Consequence for audit §B2.6's Tier-1 list: item 2 stands, items 1 and 3 invert.**

### 3.4 Also required for S-B, beyond the nine sites

- Lift DSL guard L3 (`checkScatterNoScan`), with pins in `StructuralTest.lean` and
  `RouteFragmentDiagnosticTest.lean` case 11.
- Decide what a pinned literal LHS coordinate means: a bare numeral elaborates to `LHSSlot.iterAt`
  ("scan base case on an anonymous axis"), never `.affine (.const n)`, so `dp[0, 2*j]` does not mean
  what it looks like. There is **no surface spelling of `.affine (.const _)` at all**, which makes
  `lowerArith`'s `overlappingScatter` guard dead from the surface.
- Extend `allRowKinds` in the same commit as the frozen oracle's arms, and update the
  7 kinds → 49 rows → 588 cases arithmetic to 9 → 81 → **972**.
- Extract `baseWriteRowsOk`'s clause 3 into a named predicate both it and `compileScan` call
  (inherited from Slice 1 Task 3).

---

## 4. Reconnaissance reports backing this document

All gitignored under `docs/superpowers/plans/`, all measured at `79fa71f`:

| File | Contents |
|---|---|
| `2026-09-09-slice2-compile-error-list.md` | the nine-site list for S-B (its S2 conclusion is corrected by §0) |
| `2026-09-09-slice2-barrier-inventory.md` | 18 rejection sites (5 live-source, 10 live-direct, 3 shadowed); the reference-evaluator finding |
| `2026-09-09-slice2-write-pipeline.md` | emission/checking/evaluation trace; five confirmed verdicts including that the evaluator is already generic over the coefficient |
| `2026-09-09-slice2-test-doc-surface.md` | pinning fixtures, corpus counts, JAX gate structure, doc surface |

**The evaluator needs no work for either slice.** `applyAffine`/`commitWrite`/`runDenseScan` never
mention `WriteRowKind` and are fully generic over the coefficient, so both slices are "widen the
checks", not "widen the checks and the evaluator".

Two latent defects found in passing, neither in scope: coefficient-row **width** is unchecked on both
the write side (`checkWrites` guards row count only; `applyAffine` `zip`s and truncates) and the read
side (`Check.lean` checks `coeffs.size == sourceShape.size`, never per-row width). And
`CompileTest.lean`'s `predicateSourceSched` docstring claims an affine LHS slot the code does not
have.
