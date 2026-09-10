# Scatter and affine LHS writes — slice decomposition and verified design inputs

**Status:** planning artifact, authored 2026-09-09 against `main` = `79fa71f`, tree clean, default
`lake build` green at **8660 jobs** and `lake build JaxExperiment` green at **8513 jobs**.

**This is the implementation plan for S-A (top-level scatter).** It is also the measured
decomposition of what `papers/post_audit_roadmap.md` Section B calls "Slice 2": Section B assumed a
single slice, and measurement says two, nearly disjoint. **§1** is the evidence for the split;
**§2** is S-A — the decided representation, the measured 18-site inventory, and the seven-task
breakdown in **§2.7**; **§3** is S-B's already-verified design, parked; **§4** lists the
reconnaissance reports behind all of it.

Everything asserted here was measured against the tree, not reasoned about. Where a claim of this
document's own earlier drafts was later falsified, the correction is kept inline and marked rather
than quietly edited away — §0 and the ⚠️ blocks in §2.2, §2.5 and §2.6.

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

## 2. S-A: what it requires, and the task breakdown (§2.7)

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

### 2.2 The representation decision — DECIDED 2026-09-10

**Decision: a new `PlanStep.scatter` case carrying `ScatterPlan`, which CONTAINS an `AssignPlan`
("A-nested"), with exactly ONE `ContractionAlgebra` — the nested one.**

Six fields, and all six are needed:

```lean
-- `CollisionReduce` has DecidableEq but not BEq; mirror Kernel.lean's existing `BEq UnaryOp`.
instance : BEq LeanNCD.CollisionReduce := ⟨fun a b => decide (a = b)⟩

structure ScatterPlan where
  compute   : AssignPlan          -- the compute half; its outputShape is the SOURCE iteration domain
  destShape : Array Nat           -- the computed destination extent
  outCoeffs : Array (Array Int)   -- the placement map
  outBias   : Array Int
  fill      : ScalarConst         -- coherent with compute.algebra.reduceId (§2.5)
  reduce    : LeanNCD.CollisionReduce
  deriving DecidableEq, BEq, Repr, Inhabited
```

[snippet, `scatterplan.lean` — compiles, with `#guard sampleScatter.fill == sampleScatter.compute.algebra.reduceId`
passing. Note `admittedAlgebra` lives in `Check.lean`, not `Kernel.lean`, so a fixture constructing
one imports `LeanNCD.Eval.Plan.Check`.]

**`destShape` is provably not derivable from the placement map**, which is why it must be stored:
`Out[2*i]` over `i:3` has extent **6** while max-coordinate + 1 is **5**; and `.const n` has
coordinate `n` but extent `n+1`. Derive it by calling `LHSSlot.outExtent` (§2.1) and store the
result. The three `Array` fields cost nothing in diagnostics (see below).

**Why A-nested over A-flat — the sole objection turned out to be an artifact.** A-nested carrying
one algebra produces `lake build JaxExperiment` output **byte-for-byte the same size as A-flat**:
15,384 total lines, per-site payloads `[5120, 5120, 5120]`, same timeout site. The 1,310,720
blow-up that had condemned it was `256² × 20` — purely a redundant *second* `ContractionAlgebra` in
the measured variant. A nested `AssignPlan` already owns one; a second was never needed. The square
law was confirmed independently with a 2×2 control (two copies → 16 = 4²).

**What A-nested buys, now unopposed:** it reuses `checkAssign`'s validation instead of duplicating
it. The extraction is **3 lines in 1 file (+18/−5)**, all **100** real `checkAssign` invocations
compile untouched (3 in `LeanNCD/`, 78 in `test/`, 17 in `experiments/`, 2 in `spikes/`), and both
targets stay green at **8660 / 8513**.

**Clause-by-clause tally over `checkAssign` — the artifact that settles viability:** **16 clauses,
0 wrong, 13 correct-and-live, 3 correct-but-vacuous** for a scatter's compute half. Exactly one
clause clashed (`destinationShapeMismatch`), and no second clash was found.

> **⚠️ Correction to an earlier draft of this section, which said "28 validation clauses."** That
> number was wrong — it came from counting `grep -c "unless\|throw"`, which double-counts each
> `unless`/`throw` pair. `checkAssign` has **16** clauses, and they are **nested** (6 top-level, 3
> per-term, 7 per-factor), not the linear block that draft described. The conclusion is unchanged
> and slightly strengthened: 16 clauses reused rather than duplicated, with none of them wrong for
> a scatter.

**The payload mechanism, for whoever hits it:** Lean eta-expands every single-constructor type
unconditionally, then enumerates every constructor of every non-recursive multi-constructor field;
recursive types (`Nat`, `List`) stop at `_`. Hence `ContractionAlgebra` = 4 (`ScalarBinOp`) × 4
(`ScalarConst`, since `Bool` splits and `UInt64` does not) × 4 × 4 = **256**, then × 4 `fill` × 5
`CollisionReduce` = **5,120**. **Sibling arm depth has zero effect** — tested both ways, so there is
no site-to-site difference to exploit.

**Mitigations exist. Revised advice: apply one TEMPORARILY while implementing, then remove it.**
An earlier draft of this section said "apply none", on the view that the bloat was mere transient
noise. §2.2.2 shows it is worse than noise: a 5,120-line payload **blew the 200,000-heartbeat budget
inside a `do`-arm**, so one site reported a *timeout* instead of `Missing cases`, and a second site
behind it **was reported by nothing at all** — found only by deleting the arm and typechecking the
file directly. A diagnostic that silently hides a site is not an ergonomic problem. Use a mitigation
as scaffolding during the work and drop it before the slice lands, so the shipped types stay honest.
The options: `@[irreducible] def AlgOpaque : Type := Algebra` → 20 patterns,
and an algebra held as a `Nat` index into a table → 20, both confirmed working and both shrinking
A-flat equally. Each costs real ergonomics to shrink a *transient* error message. Holding `fill` as
a raw `UInt64` also works (→ 1,280) but is **rejected**: it destroys the dtype tag
`constMatchesDtype` depends on, and §2.5's coherence rule needs it. Failed approaches, so nobody
retries them: shallow siblings, deep siblings, a single-constructor `inductive` wrapper (eta-expanded
exactly like a structure), a reducible alias, `private mk ::`, and dropping `deriving`.

> **Also corrected:** an earlier draft said the JAX leg gave "3 clean errors under A-flat and 40
> under A-nested". **A-flat already produces a heartbeat timeout too** (`EvalPlan.lean`), so that
> gap was narrower than reported even before the redundant algebra was removed — and with one
> algebra it is nil.

**Option B (widening `AssignPlan` with a sum-typed `target` field) remains rejected**; that
measurement was direct and is unaffected. Details in §2.2.1.

**The site inventory is now measured against this decided design — see §2.2.2.** In short: **18
compile-error sites across 9 site-bearing files** (11 touched), arriving in **two structurally
distinct phases**. The old "18 across 10 files" figure was measured against a rejected variant; the
count coincides, the file count does not, and the *composition* is the usable result.

### 2.2.1 Option B, and the earlier A-flat comparison (superseded by §2.2)



**Decision: a new `PlanStep.scatter` case carrying a flat `ScatterPlan` structure ("A-flat").**
Three candidates were built to a green build and compared; reports in
`docs/superpowers/plans/2026-09-{09,10}-option{A,B}-error-set.md`.

**Rejected — widening `AssignPlan` with a sum-typed `target` field ("Option B").** It fails on all
three counts it was proposed to win:

1. **No value of `outputShape` can describe a scatter.** `checkAssign` pins it simultaneously to the
   destination signature (`destSig.shape == a.outputShape`) *and* to every term's iteration-basis
   projection (`t.outputProjection == a.outputShape`), and a scatter separates those two. Measured
   for `Out[2*i] := X[i]`, `i:4`: `#[8]` gives `outputProjectionMismatch 0 #[4] #[8]`; `#[4]` against
   a truthful destination gives `destinationShapeMismatch #[4] #[8]`; the only passing configuration
   declares the destination at the wrong size.
2. **A mandatory sum-typed field does not force construction sites.** 83 literal sites errored — but
   only **1** in production — while **59 record-update sites compiled unchanged, 3 of them in
   production `Compile.lean`**. Silent sites outnumber forcing ones 3:1 in the real compiler.
3. **The JAX leg produced zero errors** and silently accepted a `.scattered` plan:
   `runDenseAssign` returned `shape [4] data #[1,2,3,4]` where the correct answer is `[8]`,
   `#[1,0,2,0,3,0,4,0]`.

> **The principle that explains all three, worth carrying:** an exhaustiveness tripwire comes from
> adding a **constructor to a type that is already matched**, never from adding a **field**, however
> sum-typed. Nothing matches a field nobody looks at — zero exhaustiveness errors were produced
> anywhere by Option B, because no existing `match` scrutinises the new field. This is exactly the
> property Slice 1 spent a slice installing, and it is why the plan-step option wins.

**Rejected — `ScatterPlan` *containing* an `AssignPlan` ("A-nested").** Semantically viable, and the
reuse is real at the worker layer: `runDenseAssignAt` never mentions `destinationSlot` (grep: no
match) and returns the correct source-domain value tensor with a wide destination in the store. But
it is blocked at the checker layer by exactly one line — `checkAssign`'s `destinationShapeMismatch`
— which cannot be routed around from outside `Check.lean` because `CheckedAssignPlan.mk` is
`private`. That makes it *"edit `checkAssign`"*, not *"reuse it"*, against **105 call sites** and a
`runDenseScan` doc comment that explicitly relies on the invariant. It also **degrades diagnostics
badly**: the `Missing cases` payloads are already 5,120 lines each (256 `ContractionAlgebra` × 4
`fill` × 5 `CollisionReduce`), and A-nested's two nested algebras push three sites past that into
opaque heartbeat timeouts — `lake build JaxExperiment` reported **3** errors under A-flat and **40**
under A-nested.

**Size did not decide it.** A-flat `10 files changed, 53 insertions(+), 11 deletions(-)`; A-nested
`54 insertions(+)`, same ten files. A wash.

**What A-flat costs, stated honestly:** it restates `AssignPlan`'s five fields and will eventually
re-derive `checkAssign`'s validation. That duplication is accepted deliberately, in exchange for a
checker that owns its own invariant — which is precisely what lets its `outputShape` legitimately
hold the *source* iteration domain rather than the destination shape.

**The measured error set:** **18 sites** — production `LeanNCD` **7**, `Tests` **6**,
`JaxExperiment` **3**, ad-hoc `lake env lean` drivers **2**. Rounds: 5 error rounds + green on the
default target, 1 + green on `JaxExperiment`, 1 + green on the ad-hoc drivers. Job counts at green
are **8660** and **8513**, unchanged from baseline — the option adds no module.

**The JAX leg DOES error under A**, at `lowerPlan`, `renderAffineNodesArray` and
`lowerCheckPlanToCandidate` — a hard `error: build failed`. This is the confirmed advantage over
Option B, and the reason `lake build JaxExperiment` must be in the gate (§2.3).

**Two findings that change the task list:**

- **`ScatterPlan` is one field short.** Neither variant can name both the source iteration domain
  and the destination extent. `outputShape` holds the source domain, `destinationSlot` says where to
  write — but the *computed* destination extent (6, for `Out[2*i]` over `i:3`) has no home. Add an
  explicit field for it, derived by calling `LHSSlot.outExtent` (§2.1, §3.2).
- **⚠️ The new `PlanStep` case is UNREACHABLE from source, and nothing errors to tell you.**
  `Compile.lean` still rejects every `Stmt.scatter` at six places. The IR node is necessary but not
  sufficient; lifting those six is a separate deliverable with **no tripwire of its own**. Among the
  six no-compile-error sites, also note `rawPublicationSlots`' inner lookahead
  (`| _ => acc.push a.destinationSlot`), which silently publishes an internal scratch slot for an
  `.assign → .scatter` chain.

**Found in passing, pre-existing, not caused by this work:** `BridgeSmoke.lean` fails with
`unknown module prefix 'Jax'` at baseline. It is in no library and no target, so nothing catches it.

### 2.2.2 The measured site inventory

Measured against the §2.2 design (one algebra, six fields), iterating to green on every target.

**18 compile-error sites, 9 site-bearing files, in two phases:**

| Phase | Perturbation | Sites |
|---|---|---|
| 1 | `ScatterPlan` + `PlanStep.scatter` | **11** |
| 2 | `CheckedPlanStepEvidence.scatter` — **forced, not optional** | **7** |

Phase 2 is mandatory, not a design choice: `checkPlan`'s `localCheck` arm must return a
`CheckedPlanStepEvidence`, and there is no honest value for a scatter step. The only way to avoid
it is for `checkPlan` to reject every scatter — i.e. not to ship the feature.

| Target | Ph1 | Ph2 | Total | Rounds |
|---|---|---|---|---|
| `lake build` | 10 | 3 | **13** | 3 / 2 |
| `lake build JaxExperiment` | 0 | 3 | **3** | 0 / 1 |
| ad-hoc drivers (`experiments/jax_bridge/`) | 0 | 1 | **1** | 0 / 1 |
| ad-hoc spikes (`spikes/`) | 1 | 0 | **1** | 1 / 0 |

`JaxExperiment` has **zero unique Phase-1 sites** — its Phase-1 exposure is entirely library sites
the default target already forces. Its own three arrive with Phase 2.

Both targets end green at **8660** and **8513**, unchanged from baseline.
`git diff --stat`: 11 files, 39 insertions, 12 deletions.

**⚠️ Round 1 surfaces only 4 of the default target's 13.** A build halts at the first failing
module, so the site list cannot be read off one build — this is why the earlier figure was
untrustworthy. Worse, one of those 4 was a **heartbeat timeout**, not a `Missing cases`, and a
fifth site behind it (`checkPlan`/`localCheck`) was **reported by nothing at all**; it was found
only by deleting that arm and typechecking the file. A strictly mechanical iterator needs **4**
rounds there, not 3. See §2.2's revised mitigation advice.

**Three findings that shape the task list:**

- **`Compile.lean` is SEVEN rejections, not six, and of two kinds** — 3 reject `Stmt.scatter` by
  constructor, 4 reject the `.affine` LHS slot form. `Compile.lean` built **clean in every round**,
  confirming that `PlanStep.scatter` is reachable from nothing and **no compile error says so**.
  The seven rejections and Step D's emitter must be **one task**; split them and the slice can go
  green with a feature that no source program can reach.
- **`spikes/` is a fourth ad-hoc target nobody was tracking.** Six files carry
  `Run with: lake env lean spikes/…` headers, are in no lake target, and one
  (`AxisABoundaryProbe.stepKind`) is a genuine site. `lake build` will never surface it, and the
  audit's twelve tracked spikes are supposed to be reproducible evidence.
- **`rawPublicationSlots`' inner lookahead is confirmed** as a silent catch-all (the outer match
  errored, the inner did not). Whether it is reachable under this design is **UNCERTAIN** and turns
  on the Step D lowering shape — flagged, not asserted.

**One finding for the deferred slice (S-B):** `BlockStep` has no `.scatter` case and produces no
error, so scatter-inside-a-scan is **structurally impossible in the plan IR** — and nothing in the
tree records that as a decision. Lifting DSL guard L3 (§3.4) is therefore necessary but nowhere
near sufficient.

### 2.3 The build gate is FOUR targets, not one

`leanncd/lakefile.toml` sets `defaultTargets = ["LeanNCD", "Tests"]`; `JaxExperiment` carries the
comment *"Deliberately absent from `defaultTargets`: it only builds when explicitly requested."*
So **`lake build` can be green while the JAX leg no longer compiles.** Both gates are required:
default **8660 jobs**, `JaxExperiment` **8513 jobs**. The ad-hoc driver
`experiments/jax_bridge/EvalPlanAffineCorpus.lean` is in no library and needs building by hand.

**⚠️ ADD-ON, measured 2026-09-10:** two further sources are in **no** lake target and are reached
only by `lake env lean` — `experiments/jax_bridge/` (the corpus/smoke drivers) and **`spikes/`**,
six files carrying `Run with: lake env lean spikes/…` headers. Each contributes a real site
(§2.2.2). Neither `lake build` nor `lake build JaxExperiment` will ever surface them, so the gate is
**four** things to compile, not two. The audit's tracked spikes are supposed to be reproducible
evidence, which makes a silently-rotting spike a real loss.

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

### 2.5 Fill and collision policy — carry the field, defer the behaviour

Collision-`sum` is wanted eventually but deferred. It is deferrable **without rework** under three
rules, and one of them is load-bearing.

**Fill is a `ScalarConst` defaulted from the destination algebra's `reduceId` — not an `Int`, and
not a hard-coded `0`.** `ScatterOpts.fill` is `Int` [read, `DSL/Ast.lean`], which cannot express a
tropical identity, so the plan node must **not** copy that field's type. The identities already
exist in `Eval/Plan/Check.lean` [read]:

| Algebra | `reduceId` |
|---|---|
| real sum-product (`admittedAlgebra`) | `0.0` |
| tropical max-product (`admittedAlgebraMax`) | `Float.toBits (-1.0 / 0.0)` — **−∞** |
| tropical min-product (`admittedAlgebraMin`) | `Float.toBits (1.0 / 0.0)` — **+∞** |
| Boolean (`admittedAlgebraBool`) | `false` |

`admittedAlgebraMax`'s own docstring gives the reason this matters: *"Identity `−∞` so an
all-negative reduction still returns its greatest element (a `0` identity would spuriously win)."*
`AssignPlan` already carries `algebra`, so the identity is in hand and fill becomes an optional
override rather than a required datum. Today's behaviour falls out as a special case: real
sum-product's `reduceId` **is** `0.0`, which is exactly what `lowerArith` hard-codes.

**Fill and collision-reduce are the identity and the operation of one monoid.** `ScatterOpts` treats
them as independent fields, which is how an incoherent pair arises — `reduce := .max` with
`fill := 0` silently yields `0` for every all-negative output cell instead of its true maximum. Not
live today (the surface hard-codes reject-with-`0`; only a hand-built `Stmt.scatter` could produce
it), but the checked layer should make it unrepresentable rather than inherit it. If an explicit
fill is ever supplied, validate it against the algebra's identity and reject a mismatch with a
located error — **never silently normalise**, which is this codebase's recurring defect shape.
`ScalarConst.f32` is documented inert in a checked plan, so the fill's dtype must track the
destination's; reuse the existing destination-specific algebra-admission check rather than writing
a second one.

**Match `CollisionReduce` exhaustively and `throw` on the unimplemented arms** — explicit arms,
never a catch-all:

```
| .rejectCollisions => …implement…
| .overwrite | .sum | .max | .min => throw …
```

Fail-loud today, a compile error if a sixth policy is added, and landing `sum` later is replacing
one `throw` with a fold — no IR change, no signature change. Note `rejectCollisions` is the
**harder** policy: it needs the per-cell first-writer map to report which two sources collided,
whereas `sum` only folds. The deferred arm is strictly less work, not more.

**Do not defer `fill` itself.** The output array must be initialised to something, so reading the
field is free; hard-coding `0` would be more work to undo later.

### 2.6 Sequencing, and how much S-A and S-B actually share

**Order: S-A first, then S-B.** The reasons are the oracle and the IR node, *not* a large shared
substrate:

- S-A has a **reference implementation to differential-test against** (`evalScatter` already does
  fill and collision). S-B has none — `evalStmtSliceSeeded` rejects non-`.assign` in a scan slice.
  Building the most delicate new code with no oracle is the worse order.
- The missing IR node is an S-A problem only. S-B already has a write-map representation
  (`StateWriteMap`, coefficient rows, `WriteRowKind`).
- S-B additionally needs semantics decided and DSL guard L3 lifted.

> ⚠️ **Correction to an earlier draft of this section, which overstated the sharing.** It claimed
> a shared "fill + collision commit" that both sides need. **Both halves are wrong**, and the
> conclusion drawn from them — that collision-`sum` would later be *"one change serving both
> clients"* — is wrong with them. Measured:
>
> - `commitWrite` [read, `Eval/Plan/Scan.lean`] does **no fill** and **no collision detection**. It
>   iterates the block output's own coordinates, maps each through `applyAffine`, and does a
>   straight `set!` — last write wins.
> - Scan-state initialisation is owned by a different mechanism entirely,
>   `boundaryPolicy := .zeroThenBaseOverlay` [read, `Compile.lean`, `Scan.lean`].
> - **Scan writes cannot collide.** The iteration is exactly over the output slice, one value per
>   output coordinate, and a strided map with `scale ≥ 1` is injective. Assign-side collisions come
>   from a source axis absent from the output (`Out[i] := X[i]·Y[j]`, with `j` summed away); the
>   scan cover rule forbids that shape by construction.
>
> So collision-`sum` serves **one** client, and fill is S-A-only.

**What is genuinely shared is real but modest:** the extent formula (both sides must *call*
`LHSSlot.outExtent`, never restate it — see §3.2 for why) and the in-bounds argument (equality
against `outExtent` ⇒ every written coordinate in range, the same lemma on both sides). One function
and one lemma. Centralise both — that is the `scatterOutDim` drift this repo already shipped a
soundness bug over — but do not plan S-A as "the shared substrate."

The two writers have genuinely different jobs: one fills-and-reduces into a fresh tensor, the other
overlays into persistent state something else already initialised. Unifying them means making scan
writes *be* scatter writes through one mechanism — a refactor of working, load-bearing code adjacent
to the hub decomposition roadmap §F defers repeatedly. That is a slice of its own, not something to
fold into S-A.

### 2.7 Task breakdown

Seven tasks. Sized by fixtures and mutation cycles, not diff size, per
`.claude/skills/slice-plan/SKILL.md`. Split only where a reviewer could reject one task while
approving its neighbour.

#### Global constraints

- **FOUR build gates, not one.** `lake build` (**8660** at baseline), `lake build JaxExperiment`
  (**8513**), the ad-hoc drivers under `experiments/jax_bridge/` via `lake env lean`, and the six
  `spikes/` files carrying `Run with: lake env lean spikes/...` headers. The first two job counts
  hold only while no module is added; a task that adds test modules **must explain the new number,
  not assert it**.
- **The missing-cases mitigation is scaffolding.** Apply `@[irreducible] def AlgOpaque : Type := Algebra`
  (or the table-index form) while working — §2.2 — and **remove it before the slice lands**, with a
  final build proving the shipped types are unwrapped. Leaving it in silently changes the design.
- **Discharging an arm by mirroring its neighbour is the failure mode**, not the fix. Each arm cites
  the reference semantics (§2.1) or an audit cell, never the arm beside it.
- **Do not add anything to `enumPrograms`** (§2.4), and **do not touch the six frozen classifier
  sites** in `test/Eval/Plan/ContractTest.lean` and `ScanContractTest.lean` — updating those is the
  defect, not the fix.
- No line numbers in shipped text; identifiers only. Every Lean snippet compiled via
  `bash .claude/skills/slice-plan/check-snippet.sh` before it enters a commit.
- Worktree setup via `.claude/skills/new-slice/prepare-worktree.sh`.
- **⚠️ A killed agent poisons `.lake/build`, and neither `git status` nor a source grep can see
  it.** Found the hard way while authoring this plan: a stopped agent had built a nine-field
  `ScatterPlan` into `Kernel.olean`; reverting the source left the stale declaration resident, so a
  later snippet failed with *"`ScatterPlan` has already been declared"* against a tree that greps
  clean. After stopping any agent that touched Lean sources, `touch` the modules it edited and
  rebuild before trusting a measurement. This also means a `.lake` copied from a poisoned checkout
  carries the poison.
- **Every task that adds a checker clause owes a case audit, not just fixtures.** This repo's
  recurring defect is a predicate that says which cases MUST hold without saying which MAY NOT.
  Tasks 3 and 4 each deliver an explicit table over the new surface — every case × class cell
  marked (a) required, (b) forbidden, or (c) silently ignored — because **every (c) cell is the
  next instance**. `slice-plan` requires this of any task touching the family; producing it inside
  the task costs ~20k tokens, and finding the same gap at the final review has cost ~560k.

#### The tasks

**Task 1 — Phase 1: the IR node (11 sites).**
`ScatterPlan` in `Eval/Plan/Kernel.lean` with the six fields of §2.2 and **exactly one**
`ContractionAlgebra` (the nested `compute`'s). `PlanStep.scatter` in `Eval/Plan/RawStep.lean`.
Discharge all 11 Phase-1 sites. Needs a hand-written `instance : BEq LeanNCD.CollisionReduce`
(mirror the existing `BEq UnaryOp` in `Kernel.lean`). **Iterate to green — round 1 shows only 4 of
13, and one site hid behind a heartbeat timeout.**
*Files:* `Kernel.lean`, `RawStep.lean`, `EvalPlan.lean`, `Prepared.lean`,
`spikes/AxisABoundaryProbe.lean`.

**Task 2 — Phase 2: checked evidence and the JAX boundary (7 sites, 3 of them JAX).**
`CheckedPlanStepEvidence.scatter` in `Eval/Plan/EvalPlan.lean` — **forced**, since `checkPlan`'s
`localCheck` must return one. The three `JaxExperiment` sites arrive here, not in Task 1, so the JAX
rejection policy belongs in this task: an explicit `unsupportedStep`-style arm plus fixtures in
`test/Eval/Plan/ExecutableTest.lean`, a default target that already exercises
`checkJaxAssignSupport` directly.
*Reviewer question:* does the checked/JAX boundary say the right thing about scatter?
*Fixtures:* 2 JAX-rejection assertions. *Donor:* the existing `checkJaxAssignSupport` call sites in
`ExecutableTest.lean`.

**Task 3 — the `checkAssign` extraction and the scatter checker.**
Parameterise `checkAssign`'s destination-shape clause (3 lines, +18/-5, all 100 invocations
untouched — §2.2), then write `checkScatter` on it. It must validate: the compute half via the
shared core; `destShape` against `LHSSlot.outExtent` **by calling it**, never restating it (§3.2's
drift warning applies verbatim on this side); `fill` coherent with `compute.algebra.reduceId`
(§2.5), rejecting a mismatch with a located error rather than silently normalising; and
placement-map row widths, which are unchecked on the existing write path.
*Fixtures:* 4 acceptance + 4 rejection. *Mutation cycles:* 4, one per new clause.
**Name the fixture for the locator requirement:** "rejecting a mismatch with a located error rather
than silently normalising" is a claim about a diagnostic payload, and no value-comparing test can
see it. The distinguishing fixture is a `ScatterPlan` whose `fill` disagrees with
`compute.algebra.reduceId`, asserting the specific error **constructor** — under silent
normalisation it would instead return `.ok`, so the two readings are separable.

**Task 4 — the dense worker.**
Reproduce `Eval/Scatter.lean` exactly: initialise to `fill`; enumerate **source** coordinates (this
is source-driven, unlike the output-driven assign worker); place through the map; **skip
out-of-range coordinates silently**; `rejectCollisions` via a first-writer map yielding the typed
collision error. The silent skip and the two `.toNat` degeneracies are reproduced deliberately,
because differential parity is the gate — record that as a comment, not a bug.
*Fixtures:* 5 data-comparing, values already measured (§2.1) — `[1,0,2,0,3,0]`, `[0,1,0,2,0,3,0]`,
`[0,0,1,2,3]`, the 3x3 diagonal, and the chained `Up`->`Z` case. Plus 1 collision fixture:
`Out[i] := X[i]*Y[j]`, `X=[1,2,3]`, `Y=[10,100]` -> collision at output coord `[0]` between source
coords `[0,0]` and `[0,1]`. *Donors:* `test/Eval/Portfolio/GnnScatterTest.lean` SC1-SC8 for the
reference values; `test/Eval/ScatterTest.lean`'s `.scatterCollision` fixture for the error shape.
*Mutation cycles:* 3 — drop the fill, drop the bounds skip, drop collision detection.

**Task 5 — source reachability. ONE task, do not split.**
Lift `Compile.lean`'s **seven** rejections (3 by `Stmt.scatter` constructor, 4 by `.affine` LHS slot
form) **and** write Step D's emitter building a `ScatterPlan` from a `Stmt.scatter`. Measured:
`Compile.lean` built clean in every round of Task 1's perturbation, so **the new plan step is
reachable from nothing and no compile error will tell you.** Split this and the slice can go green
around a feature no source program can reach. Keep a located `CapabilityError` for the multi-axis
case (§1.5) so `Out[i+j]` still fails with a source locator rather than degrading to
`writeGeometryNotAdmitted`. Flip the 6 category-(a) pinning fixtures here (2 in `CompileTest.lean`,
4 in `ScanCompileTest.lean`).
*Also confirm or refute:* `rawPublicationSlots`' inner lookahead, whose reachability under this
design is **UNCERTAIN** (§2.2.2).

> **Feasibility of the emitter: ANSWERED, 2026-09-10 — Step D already has what it needs.** This was
> the slice's one open feasibility question and it is closed, so Task 5 starts from a known-good
> footing rather than a probe.
>
> - **Step C binds `sizes` before Step D runs.** `prepareEvalPlan` calls
>   `inferAxisSizesFromSignature explicitSizes sig flatStmts` and binds `(sizes, warnings)`; Step D
>   is the next statement. `flatStmts` flattens `.plain s`, so a `Stmt.scatter` flows through
>   inference [read].
> - **The scatter output-shape derivation already exists and already runs on this path.**
>   `SizeInfer.scatterOutputShapes (sizes : HashMap UID Nat) (stmts : List Stmt)` is wired into the
>   sizing fixpoint (`let producedShapes := scatterOutputShapes sizes stmts`), and Step C's own
>   comment records that `inferAxisSizesCore` inspects LHS slots *only* for `.scatter`, via that
>   function [read].
> - **`LHSSlot.outExtent` is in scope in `Compile.lean` with no new import** — it imports
>   `LeanNCD.DSL.Ast` directly. Computing `destShape` is one call per slot.
>
> **⚠️ The trap this creates.** `Eval/Eval.lean`'s `scatterOutShape` is exactly the function Step D
> wants — but it belongs to the **reference** path, which the checked plan deliberately does not
> import (`Scan.lean`: *"Independent of `Eval.evalScan`/`evalScheduled` by construction — imports
> neither"*). **Copying its body into `Compile.lean` would be a THIRD copy of the extent
> convention**, which is precisely the `scatterOutDim` mistake. Call `LHSSlot.outExtent`, or reuse
> `SizeInfer.scatterOutputShapes`; do not restate the formula.
>
> Note also that the reference fails loud on an unsized scatter axis
> (`EvalError.shape (.unsizedScatterOutput sl)`) rather than defaulting the extent to 0. The checked
> path owes an equivalent rejection — **not** a `getD 0`, which would silently produce an
> empty output tensor (§2.1's second `.toNat` degeneracy, one layer up).
**Name the fixture for the locator requirement:** "`Out[i+j]` still fails with a source locator" is
again a diagnostic-payload claim. The distinguishing fixture compiles a two-axis affine LHS and
asserts the `CapabilityError` constructor; if the preflight arm were dropped, the same program
would still be *rejected* — by `writeGeometryNotAdmitted` — so a fixture asserting only "rejected"
cannot tell the two apart and would pass either way.

**Task 6 — curated corpus and differential.**
A separate corpus mirroring `predicatePrograms` in `test/Eval/Plan/DifferentialTest.lean` (10
entries, kept out of `enumPrograms` with its rationale stated twice — copy that pattern verbatim).
Parity between the checked plan and the reference evaluator over it. This is the proof the slice
works, and the reason S-A was sequenced first.
*Fixtures:* 6-8 corpus entries. *Donor:* `predicatePrograms`' structure; the GN/SC programs for
content.

**Task 7 — documentation and the value-grep sweep.**
`leanncd/LeanNCD/Eval/AGENTS.md`, the six prose sites enumerating the constructor surface, and
`papers/backend_missing_functionality.md`'s Hard row, which this slice closes. **Value-grep the
whole repo for the numbers that move** — `3832`, `8660`, `8513`, and the curated-corpus counts —
per §2.4. Low judgment; cheapest model; per-task review trimmable.

#### Risk and size

| Task | Fixtures | Mutation cycles | Risk |
|---|---|---|---|
| 1 IR node (11 sites) | 0 | 0 | **High** — 11 judgment calls, the mirror-the-neighbour trap, a site hidden behind a timeout |
| 2 Evidence + JAX (7 sites) | 2 | 0 | Moderate |
| 3 Extraction + checker | 8 | 4 | **High** — touches shared `checkAssign`; the extent rule is the drift surface |
| 4 Dense worker | 6 | 3 | **High** — largest test cycle; reproduces deliberate misbehaviour |
| 5 Source reachability | 6 flipped | 0 | **High** — no compile error guards it |
| 6 Corpus + differential | 6-8 | 0 | Moderate |
| 7 Docs + value-grep | 0 | 0 | Low |

Tasks 1, 3, 4 and 5 are each independently rejectable and each is a natural rollback unit. Per
`slice-plan`'s measured guidance, budget for **two independent final whole-branch reviewers with
different lenses** rather than one: this slice has a real soundness surface (write geometry, the
extent rule, collision handling), and the final tier is where such findings have always surfaced.

### 2.8 Measurement status

**Planning complete (2026-09-10).** The representation is decided (§2.2), the site inventory is
authoritative (§2.2.2), the task breakdown is written (§2.7), and the one open feasibility question
— whether Step D can build a `ScatterPlan` at all — is **closed affirmatively** (§2.7, Task 5).
S-A is ready to execute; nothing further needs measuring before Task 1.

**No de-risking spikes are recommended.** Three were considered and rejected on cost/benefit: a
dense-worker spike would *be* Task 4 rather than de-risk it (the reference implementation can simply
be read); a `rawPublicationSlots` reachability spike answers in-context for free during Task 5; and
the emitter-feasibility spike — the only one with real value — is closed above by a ten-minute read
instead. The genuinely mechanical external carve-out is roadmap D2, correctly queued behind Task 1,
and now measured at **six prose sites plus one node**, not the "four docstrings plus one" that
section still states.

⚠️ **Process note for whoever runs the next measurement.** The first attempt dispatched two mutating
agents into the **same working checkout** concurrently; they overwrote each other's edits in
`Kernel.lean` and `RawStep.lean`, and one agent's round-1 errors named the other's constructors. One
full agent-run was discarded. Measurement that mutates tracked files is implementation for this
purpose: **one at a time, or each in its own detached worktree** with `.lake` APFS-cloned
(`cp -c -R`) and the 8660/8513 baseline re-verified inside the worktree before the first edit. The
re-run did exactly that and its numbers are the ones in §2.2.

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

**The chokepoint guard must be a WITNESS FUNCTION, not a `#guard` set** (absorbed from roadmap
Section B, which is now a stub). `classifyWriteRow` is structurally untripwireable, so nothing will
remind you to guard it. A `#guard` set naming `pinned`/`free`/`advancing` never mentions `.strided`
and keeps passing unchanged. What works is a function matching exhaustively over `WriteRowKind` —
e.g. `classifyWitness : WriteRowKind → (Nat × Array Int × Int)` with one
`#guard classifyWriteRow (witness k) == some k` per constructor — so a new constructor breaks the
witness's own exhaustiveness, which is a compile error.

**Require a `contextWidth = 0` witness AND a `contextWidth > 0` witness per constructor.** The
compile error forces the author to *supply* a `contextWidth`; it does not force them to *exercise
the discrimination*. At `contextWidth = 0` the correct `outputPos = p - contextWidth` and a broken
`outputPos = p` coincide, so a lone base-phase witness passes under both readings and the
off-by-`contextWidth` bug ships green. Slice 1's three `classifyWriteRow` guards are the precedent:
one at `contextWidth = 0`, two at `contextWidth = 2`, one of those with the nonzero coefficient in
the output half.

**Two value checks in `classifyWriteRow` are genuinely unpinned** — measured in Slice 1's final fix
wave by weakening each in place and rebuilding the full default target:

| Weakening | Observed | Firing set |
|---|---|---|
| advancing branch, drop `bias == 1` | build FAILS | one assertion — the pre-existing `lookAheadStepWrite` fixture. Pinned incidentally, not deliberately |
| free branch, drop `bias == 0` | build PASSES, 8660 jobs | **empty — genuinely unpinned** |
| multi-nonzero arm, route length-≥2 rows through free-branch logic | build PASSES, 8660 jobs | **empty — genuinely unpinned** |

So the accurate scope is **two unpinned checks, not three**. Add a dedicated guard for the
advancing branch's `bias == 1` too if cheap — an incidental pin in an unrelated fixture is a poor
home for a load-bearing rule — but do not plan it as coverage of a live hole. Note §3.1's branch
adds `c > 0 && bias ≥ 0`, which is new surface needing its own guards.

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
