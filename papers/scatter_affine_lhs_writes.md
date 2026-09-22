# Scatter and affine LHS writes — slice decomposition and verified design inputs

**Status:** S-A and S-B implemented; authored 2026-09-09 against `main` = `79fa71f`, updated
2026-09-12 after S-A landed and S-B planning completed, and refreshed after S-B implementation.
The original baseline was default
`lake build` green at **8660 jobs** and `lake build JaxExperiment` green at **8513 jobs**; the
post-S-A baseline used for S-B planning is **8663 / 8514**.

**This is the implementation plan for S-A (top-level scatter).** It is also the measured
decomposition of what `papers/post_audit_roadmap.md` Section B calls "Slice 2": Section B assumed a
single slice, and measurement says two, nearly disjoint. **§1** is the evidence for the split;
**§2** is S-A — the decided representation, the measured 18-site inventory, and the seven-task
breakdown in **§2.7**; **§3** records S-B's finalized design and the later measurements that
supersede its parked sketch; **§4** lists the reconnaissance reports behind all of it. The
executable S-B task plan is
`leanncd/docs/superpowers/plans/2026-09-12-lhs-scatter-in-scans.md`.

Everything asserted here was measured against the tree, not reasoned about. **§0's four
corrections are load-bearing and must not be pruned**: each falsifies a claim in a document that
still exists and is still read (the compile-error list, the audit). Corrections that only narrated
this document's own drafting have been removed; the ⚠️ blocks that remain each prevent a specific
wrong turn.

---

## 0. Four corrections to this document's own inputs

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
> §3.2's branch therefore adds `c > 0 && bias ≥ 0`. It closes all 200 and costs nothing a surface
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

> **Correction 4 — canonical even/odd interleaving requires a stride-aligned global extent.**
>
> The parked rule `scale*n + offset` gives different inferred state extents for the two halves of
> the canonical example: `2*j` over `j : 3` gives 6, while `2*j+1` gives 7. The scan checker rejects
> those writes as inconsistent before collision logic or execution can observe that their
> coordinate images interleave.
>
> S-B therefore changes the shared `LHSSlot.outExtent` rule for exactly one normalized positive
> affine axis with nonnegative bias and nonzero source extent:
>
> ```
> alignedExtent(c, b, n) = c*n + floor(b/c)*c
>                        = c*n + b - (b mod c)
> ```
>
> Thus `2*j` and `2*j+1` both infer 6, while `2*j+3` infers 8 and `j+2` remains 5. This is a global
> semantic change, so S-A's shifted-stride fixtures are rebaselined in the same task. All fallback
> classes retain the old result: `.const`, zero source extent, zero/negative coefficient, negative
> bias, cancellation, missing sizes, and genuine multi-axis expressions. A broader normalized-gcd
> rule was rejected because it would change multi-axis semantics outside the admitted S-A/S-B
> placement language.

---

## 1. The scoping finding — this is two slices, not one

### 1.1 A strided write into scan state is unreachable from surface syntax, in BOTH phases

> **Historical measurement, superseded by S-B:** this subsection records the pre-S-B barrier that
> motivated the split. The current boundary is §3: `checkScatterNoScan` is gone and the bounded
> positive affine scan-state subset is admitted.

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
capability the whole enquiry started from. S-A and S-B have since landed; §3 records S-B's shipped
boundary and the task plan that implemented it.

---

## 2. S-A: what it requires, and the task breakdown (§2.7)

### 2.1 The reference semantics it must reproduce, not invent

`Eval/Eval.lean` executes affine LHS writes end to end from surface syntax today. Measured:

| Program | Result |
|---|---|
| `Out[2*i] := X[i]`, `X=[1,2,3]` | `shape=[6] data=#[1,0,2,0,3,0]` |
| `Out[2*i+1] := X[i]`, `X=[1,2,3]` | pre-S-B: `shape=[7] data=#[0,1,0,2,0,3,0]`; S-B rebaseline: `shape=[6] data=#[0,1,0,2,0,3]` |
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

**`destShape` is provably not derivable from the placement map**, which is why it must be stored
(and computed by *calling* `LHSSlot.outExtent` — see the ONE EXTENT CONVENTION constraint in §2.7):
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

**The payload mechanism, for whoever hits it:** Lean eta-expands every single-constructor type
unconditionally, then enumerates every constructor of every non-recursive multi-constructor field;
recursive types (`Nat`, `List`) stop at `_`. Hence `ContractionAlgebra` = 4 (`ScalarBinOp`) × 4
(`ScalarConst`, since `Bool` splits and `UInt64` does not) × 4 × 4 = **256**, then × 4 `fill` × 5
`CollisionReduce` = **5,120**. **Sibling arm depth has zero effect** — tested both ways, so there is
no site-to-site difference to exploit.

**Mitigations exist. Apply one TEMPORARILY while implementing, then remove it.** The bloat is not
merely noise: a 5,120-line payload **blew the 200,000-heartbeat budget
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

**Option B (widening `AssignPlan` with a sum-typed `target` field) remains rejected**; that
measurement was direct and is unaffected. Details in §2.2.1.

**The site inventory is now measured against this decided design — see §2.2.2.** In short: **18
compile-error sites across 9 site-bearing files** (11 touched), arriving in **two structurally
distinct phases**. The old "18 across 10 files" figure was measured against a rejected variant; the
count coincides, the file count does not, and the *composition* is the usable result.

### 2.2.1 Option B — rejected, retained so it is not re-proposed

Widening `AssignPlan` with a sum-typed `target` field. Measured directly; it fails on all three
counts it was proposed to win.

1. **No value of `outputShape` can describe a scatter.** `checkAssign` pins it simultaneously to the
   destination signature (`destSig.shape == a.outputShape`) *and* to every term's iteration-basis
   projection (`t.outputProjection == a.outputShape`), and a scatter separates those two. Measured
   for `Out[2*i] := X[i]`, `i:4`: `#[8]` gives `outputProjectionMismatch 0 #[4] #[8]`; `#[4]`
   against a truthful destination gives `destinationShapeMismatch #[4] #[8]`; the only passing
   configuration declares the destination at the wrong size.
2. **A mandatory sum-typed field does not force construction sites.** 83 literal sites errored — but
   only **1** in production — while **59 record-update sites compiled unchanged, 3 of them in
   production `Compile.lean`**. Silent sites outnumber forcing ones 3:1 in the real compiler.
3. **The JAX leg produced zero errors** and silently accepted a `.scattered` plan: `runDenseAssign`
   returned `shape [4] data #[1,2,3,4]` where the correct answer is `[8]`, `#[1,0,2,0,3,0,4,0]`.

> **The principle that explains all three, worth carrying beyond this slice:** an exhaustiveness
> tripwire comes from adding a **constructor to a type that is already matched**, never from adding
> a **field**, however sum-typed. Nothing matches a field nobody looks at — Option B produced zero
> exhaustiveness errors anywhere, because no existing `match` scrutinises the new field. This is
> exactly the property Slice 1 spent a slice installing.

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

**One finding later corrected for S-B:** `BlockStep` has no `.scatter` case and produces no
exhaustiveness error. That does not make scan scatter structurally impossible: the block computes
the dense logical slice as `.assign`, while `StateWriteMap` performs affine placement into state.
Lifting DSL guard L3 is still necessary but nowhere near sufficient; checked geometry, source
lowering, reference semantics, and the independent oracle all need explicit S-B work (§3).

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

> **⚠️ RE-VALIDATE THIS SECTION BEFORE ACTING ON IT — one premise has expired.** Unlike the rest of
> this document, §2.5 is **forward-looking guidance for work that has not happened** (collision-`sum`,
> explicit fills, and a binary32 scatter are all still deferred), so the "S-A and S-B implemented"
> status at the top does *not* make its present-tense claims historical. One is now false: the
> paragraph below says "`ScalarConst.f32` is documented inert in a checked plan". It is **not inert**
> — the f32 slice made it live, and `admittedAlgebraF32`/`Max`/`Min` are built from `ScalarConst.f32`
> payloads (see [`f32_evalplan.md`](f32_evalplan.md)). Two consequences for whoever implements this
> section: (a) "the fill's dtype must track the destination's" is still right but no longer trivially
> satisfied, because a destination can now legitimately be `f32`; (b) "reuse the existing
> destination-specific algebra-admission check" now names **two** tables, `admittedAlgebrasFor` and
> `admittedAlgebrasForF32`, selected by the graph's storage kind. Neither is reachable for a scatter
> today: a binary32 scatter is refused at source tier as `CapabilityError.unsupportedDtype`
> ("`{nm}: f32 scatter`") and is deferred to slice F32-D. The rest of the section — the fill/reduce
> monoid argument, the `ScalarConst`-not-`Int` rule, and the exhaustive-`CollisionReduce` rule — is
> unaffected and still stands.

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
  fill and collision). At sequencing time S-B had none — `evalStmtSliceSeeded` rejects
  non-`.assign` in a scan slice. Section 3.6 now specifies both the required reference semantics and
  an independent scan-free oracle; S-B subsequently implemented both.
- The missing IR node is an S-A problem only. S-B already has a write-map representation
  (`StateWriteMap`, coefficient rows, `WriteRowKind`).
- S-B additionally needs semantics decided and DSL guard L3 lifted.

> **⚠️ Do NOT build a shared fill/collision layer between S-A and S-B.** It looks like the obvious
> common ground and it is not there, measured:
>
> - `commitWrite` [read, `Eval/Plan/Scan.lean`] does **no fill** and **no collision detection** —
>   it iterates the block output's coordinates, maps each through `applyAffine`, and does a
>   straight `set!`, last write wins.
> - Scan-state initialisation is owned elsewhere entirely, by
>   `boundaryPolicy := .zeroThenBaseOverlay`.
> - **One admitted scan write cannot collide with itself.** The block contracts RHS-only axes into
>   a dense logical output first, then a positive strided map injectively places one value per dense
>   coordinate. Multiple base writes can still overlap each other, so `writesCollide` must prove
>   their regions disjoint; S-B adds only the equal-scale/different-residue proof.
>
> So configurable fill and collision reduction are **S-A-only**, and collision-`sum` when it lands
> serves one client, not two. S-B fixes the policy at zero-fill/reject-collisions and separately
> proves disjointness between multiple base-write regions before execution.

**What is genuinely shared is real but modest:** the extent formula (both sides must *call*
`LHSSlot.outExtent`, never restate it — see §3.1 for why) and the in-bounds argument (equality
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
- **⚠️ ONE EXTENT CONVENTION. This is the slice family's single most dangerous rule.** S-A landed
  with `scale·n + offset`; S-B deliberately replaces that global one-axis case with Correction 4's
  stride-aligned rule. The convention still lives in exactly one place: `LHSSlot.outExtent`
  (`DSL/Ast.lean`). A second copy — `scatterOutDim` — already drifted from it and **shipped a
  soundness bug**: a downstream reader sized to 3 while the evaluator materialised 4 (fix
  `fc10d70`, duplicate deleted `6a26825`).

  This slice creates **three fresh temptations to write a fourth copy**, and each looks locally
  reasonable:

  | Task | The temptation | Why it looks right |
  |---|---|---|
  | 3 | inline the extent check into `checkScatter` | it is two lines of arithmetic |
  | 4 | compute the output size when allocating the tensor | the worker needs a size anyway |
  | 5 | copy `Eval/Eval.lean`'s `scatterOutShape` into `Compile.lean` | it is *exactly* the function wanted — same signature, same job — but it sits on the **reference** path, which the checked plan deliberately does not import (`Scan.lean`: *"imports neither"*), so copying feels like the only option |

  **Every one of them CALLS the shared formula — `LHSSlot.outExtent`, in scope in both
  `Compile.lean` and `Scan.lean` with no new import, or `SizeInfer.scatterOutputShapes`. None
  restates it.** If a call is genuinely impossible somewhere, that is a finding to escalate, not a
  licence to copy.

  **Also forbidden: deriving a local memory-sufficient bound**
  `scale·(n−1) + offset + 1`. It can be memory-safe for one write yet assign different ambient
  extents to writes intended to share a state. Before S-B it disagreed with `outExtent` by exactly
  `scale − 1`; after S-B the precise difference depends on the offset residue. Either way, a second
  formula is the exact shape of the bug this repo already paid for.

  **"But doesn't the affine solver determine the extent?" No — it CONSUMES it.** Expect this
  question; it is the natural one, and getting it wrong is how the original bug shipped. The
  division of labour is deliberate and documented in three places (`outExtent`'s docstring,
  `Eval/Shape.lean`'s header, `Eval/Slots.lean`'s header):

  - the affine machinery (`idxAffineForm`, `Eval/Shape.lean`, `SizeSolve.lean`) solves **axis
    sizes** from **read** constraints — given `Y[i] := X[2*i]`, how large must `i` be;
  - `outExtent` answers a different question — given known axis sizes, how large must the
    **scatter output tensor** be. Its docstring calls this *"deliberately not derivable from
    `idxAffineForm`"*.

  **And yes — the solver really does compute maximal values per axis.** `SizeInfer` builds
  `maxCoeffs`/`maxIdx` for each affine read position and `SizeSolve.mkConstraint` turns it into
  `Σ coeffs·size(uid) ≤ rhs`, an *upper-envelope* inequality; `solveSizeConstraints` reduces the
  batch by RREF over `ℚ` (an exact linear-constraint system, not a simplex LP with an objective).
  So the machinery for "maximum index along each axis" already exists.

  **It still cannot determine a scatter output extent, and the reason is the direction of the
  constraint.** Each inequality bounds axis sizes *against a tensor whose dimension is already
  known* — `maxIdx ≤ pos.dim`, where `pos.dim` is the **source** tensor's dimension. A scatter
  output is being *produced*; there is no known dimension to constrain against. Causality runs
  reads → constraints → axis sizes → `outExtent` → output shape, and the solver sits strictly
  upstream of the last arrow.

  **This is exactly the reasoning that produced the original bug, which is why it deserves a
  named constraint rather than a footnote.** The deleted duplicate `scatterOutDim` was, in the
  audit's words, *"an upper-envelope `max index + 1`"* — i.e. the solver's own idiom applied to the
  output side. Reconstructed concretely: for `Out[2*i]` over `i:2` the coordinates are `{0,2}`,
  so upper-envelope max + 1 = **3**, while the convention gives `2·2` = **4**. That is precisely
  the shipped symptom the audit records — *"a downstream reader sized to 3 while the evaluator
  materialized 4"* (fix `fc10d70`, duplicate deleted `6a26825`).

  The aligned cell is a policy choice — upsample stride semantics, so writes in the same
  stride-`k` residue block infer one ambient extent and can tile it — and no affine algebra implies
  it. The bias is aligned down to its stride block rather than always extending the output by
  `offset`.

  **Why this is a trap rather than an error:** deriving the extent from the coordinate map is
  *correct for every case except the one this feature exists to add.* For a shift, `Out[i+2]` over
  `i:3` writes `{2,3,4}`, max + 1 = 5, and the convention also gives 5 — **they agree**. They
  diverge only on the strided cases this feature adds. Under the S-B rule some shifted residues,
  such as `2*i+1`, now coincide with max + 1; that does **not** make max + 1 the contract, because
  `2*i` and `2*i+3` still demonstrate the policy boundary.

  `SizeInfer.scatterOutputShapes` is the model caller: it is wired into the sizing fixpoint and
  obtains its extents by **calling** `outExtent`. Be like the solver — call it.

  **The tell that the rule has been broken:** `grep -rn "outExtent\|scatterOutputShapes" LeanNCD/`
  should show the new sites *calling* one of them. A new site that computes an extent without
  appearing in that grep is a fourth copy.
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
shared core; `destShape` against `LHSSlot.outExtent` **by calling it**, never restating it (the
ONE EXTENT CONVENTION constraint above — this is temptation 1 of 3); `fill` coherent with `compute.algebra.reduceId`
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
> **⚠️ The trap this creates is temptation 3 of 3** in the ONE EXTENT CONVENTION constraint above,
> and it is the most seductive of the three because `Eval/Eval.lean`'s `scatterOutShape` is exactly
> the function Step D wants and is unreachable by import. Call `LHSSlot.outExtent` (in scope here
> already) or reuse `SizeInfer.scatterOutputShapes`. Do not copy the body.
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

**Execution complete (S-A landed).** All seven tasks landed and were reviewed: the IR node,
outer-graph wiring, checker, dense worker, source reachability, the eight-entry curated
`scatterPrograms` parity corpus, and documentation/value-grep closure. Final S-A build-gate counts:
**`lake build` 8663**, **`lake build JaxExperiment` 8514** — up from the planning-time baseline of
8660/8513 by +3/+1, all from three new test modules and one new import, each explained in the
ledger. The 8660/8513 figures elsewhere in this document remain as planning-time snapshots, the
same way `pre_scatter_backend_audit.md` and `post_audit_roadmap.md` keep their own eras' counts.

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
purpose: **one at a time, in an isolated worktree**, prepared through
`.claude/skills/new-slice/prepare-worktree.sh`. That procedure uses `rsync` to warm-start Mathlib
and project oleans before re-verifying the baseline.

---

## 3. S-B's implemented design

Planning completed 2026-09-12 and the slice has since landed. The implementation record is
`leanncd/docs/superpowers/plans/2026-09-12-lhs-scatter-in-scans.md`. The design below incorporates
compiled probes, a complete routed source probe, and three independent Sol review passes. It
supersedes the earlier parked extent and evaluator assumptions in this document.

### 3.1 Global stride-aligned extent

`LHSSlot.outExtent` remains the single authority. It resolves every syntactically mentioned axis
size before normalization, normalizes coefficients by UID, and applies Correction 4's aligned rule
only when exactly one normalized nonzero coefficient remains, with positive coefficient,
nonnegative bias, and nonzero source extent.

Measured examples over `i : 3`:

| Slot | Extent |
|---|---:|
| `2*i` | 6 |
| `2*i+1` | 6 |
| `2*i+3` | 8 |
| `i+2` | 5 |
| duplicate terms `i+i+1` | 6 |
| cancelling terms `i-i+1` | 1 |
| `0*i` | 0 |
| `-2*i+1` | 0, legacy fallback |

Zero/cancelled raw terms still require their named sizes to resolve before normalization. `.const`,
zero source extent, negative forms, missing sizes, and multi-axis expressions retain the legacy
result. Checked scan geometry calls the shared `scatterDestExtent` adapter; it does not introduce a
`stridedExtent` formula beside `outExtent`.

### 3.2 Classifier and checked geometry

`WriteRowKind` gains `.strided outputPos scale offset`. Classification order is load-bearing:
`.advancing`, then `.free`, then `.strided`, then rejection. The strided arm requires one nonzero
coefficient in the output half, `scale > 0`, and `offset >= 0`. A zero coefficient remains
`.pinned`; negative scale, negative bias, a context-half coefficient, and multiple nonzero
coefficients are rejected.

Both base and recurrence phases admit strided rows, but only at **non-advancing state
dimensions**. Advancing dimensions retain their scan meaning:

| Dimension class | Base write | Recurrence write |
|---|---|---|
| advancing | `.pinned` boundary coordinates or dense `.free` boundary faces; never `.advancing` or `.strided` | exactly the matching `.advancing` row |
| non-advancing | `.pinned`, `.free`, or `.strided` | `.free` or `.strided` |

This distinction is not implied by the positional cover. A hand-built base row array
`[.pinned 0, .strided 0 2 0, .free 1]` with both first dimensions advancing satisfies
recognition, ordered cover, and boundary touch unless `baseWriteRowsOk` has an explicit
dimension-class clause. The checker must therefore forbid both synthetic `.advancing` base rows
and reachable `.strided` rows at base-phase advancing dimensions.

Wherever a positional cover counts `.free p`, it counts `.strided p _ _` identically. Extent
agreement treats `.free` as identity placement and `.strided` by calling `scatterDestExtent`.
Pinned range remains an inequality; strided range is discharged by positive classification plus
exact shared extent equality. Advancing sizes retain their history-extent check.

The complete case table is a required implementation artifact, not commentary: each
predicate-by-row-kind cell must be classified as required, forbidden, or deliberately ignored.
This is the fifth member of the recurring write-soundness defect family where a predicate states
which rows must be present but omits which rows may not be present.

### 3.3 Collision and placement

Two strided rows prove a dimension disjoint only when their positive scales are equal and their
offsets differ modulo that scale. Different scales, free-versus-strided, and all other new
pairings remain conservatively colliding. The rule was checked over all **102,400** tuples with
scales `1..5`, offsets `0..7`, and source extents `0..7`: whenever it claimed disjointness, the two
finite coordinate images had empty intersection.

The write worker remains generic. `applyAffine`, `commitWrite`, and `runDenseScan` already execute
arbitrary affine maps and need no `.strided` branch. The new work is admission, extent agreement,
and collision proof before those functions run.

### 3.4 Compute dense values, then place them

S-B does **not** add `BlockStep.scatter`. A scan scatter has two independent operations:

1. compute the statement's dense logical output slice with the existing `AssignPlan`, including
   RHS-only contraction axes; and
2. place that dense slice into persistent state through an affine `StateWriteMap`.

This keeps contraction in one block-operation representation and uses the state-write map for the
new capability. It also fixes the output-basis rule: exclude an axis only when its LHS role is
`.iterAt` or `.iterNext`, not merely because its UID belongs to scan context. A base boundary face
such as `.free c` is a real dense output dimension and must remain in the block output basis.

Multiple base contributions may overlay one state in source order when their checked regions are
disjoint. Exactly one recurrence write per state remains enforced.

### 3.5 Source reachability and typed failures

Remove `checkScatterNoScan` from both production compile chains and the test-local logical chain,
then delete the obsolete barrier. Keep `CompileError.scatterInScan` as a producerless compatibility
constructor rather than rewriting unrelated error APIs.

A complete base-plus-recurrence scan-scatter program already reaches `route` when only that barrier
is omitted, so routed/categorical production code needs no new scan-scatter representation.
Diagnostic case 11 in `RouteFragmentDiagnosticTest.lean` must move from `scatterInScan "Out"` to
the already-correct `missingBaseCase "Out"` at final fresh state 3; removing the barrier does not
make the malformed program valid.

Source lowering accepts exactly `fill == 0` with `.rejectCollisions`. Nonzero fill is rejected
because scan state initializes once with `zeroThenBaseOverlay`; applying fill per contribution
would overwrite unrelated state. Nonlinear placement, predicate destinations, and non-default
reductions remain rejected.

New source failures are typed and located:

- `scanWriteRowNotAdmitted`: scan, destination, phase, original statement index, dimension,
  coefficient row, and bias;
- `scatterScratchNotAdmitted`;
- `contextAxisAsAffineOutput`.

Existing `inconsistentStateExtent` owns disagreement between otherwise valid placements, and
`multiAxisScatterLhs` continues to own one affine slot naming multiple normalized UIDs. Capability
checks precede shape, scan-specialization, and checked-plan failures. Locator fixtures must include
a non-assignment statement between assignments so original and filtered statement indices differ.

### 3.6 Reference evaluator and independent oracle

The low-level checked worker needs no change, but both comparison legs do.

The legacy scan evaluator now computes the dense source slice with seeded assignment semantics, then
evaluates the original LHS expressions independently for placement. Calling top-level `evalScatter`
directly would be wrong when the RHS has a
contraction-only axis, because that path does not share the scan slice's seeded contraction
semantics. Base overlays preserve source order.

The independent scan-free oracle must not import checked geometry, compiler residualization, or
scan-worker placement helpers. For each affine scan statement it:

1. emits a dense temporary assignment that performs contraction;
2. emits a top-level scatter reading only that temporary;
3. gives each base contribution a private name;
4. independently enumerates destination coordinates and rejects overlaps;
5. merges disjoint zero-filled contributions into the canonical state leaf before recurrence;
6. resolves recurrence reads to that canonical merged leaf; and
7. validates leaf shapes with an oracle-local derivation of the aligned extent.

Synthetic non-advancing state-slice axes and explicit sizes are required for canonical merge
assignments. Pointwise sum is valid only because fill is fixed at zero and disjointness is proven
independently. A test-the-tester assertion must pin that scatter leaves and the canonical merge
cannot silently disappear.

### 3.7 Test and tripwire surface

The nine existing `WriteRowKind` exhaustiveness sites remain compile-time tripwires: six in
`Eval/Plan/Scan.lean`, one in `Eval/Plan/Compile.lean`, and two in the frozen test oracle in
`ScanTest.lean`. No wildcard is added. `allRowKinds` grows from 7 to 9 values, row pairs from 49 to
81, and the frozen agreement window from 588 to **972** cases.

The classifier needs width-zero and positive-width witnesses, including output-half witnesses that
distinguish `p` from `p - contextWidth`, plus direct negative-scale, negative-bias, and
multi-nonzero rejection guards. Every new checker clause gets an isolated mutation cycle,
including the base advancing-dimension `.strided` prohibition.

Corpus boundaries remain explicit:

- generated scan corpus: **17 / 17 accepted**;
- generated scan-free differential corpus: **3832 / 3832 accepted**;
- curated S-A scatter corpus: **8 → 9**, adding shifted stride under the aligned rule;
- new curated S-B three-way corpus: **7** cases.

---

## 4. Reconnaissance reports backing this document

All gitignored under `docs/superpowers/plans/`, all measured at `79fa71f`:

| File | Contents |
|---|---|
| `2026-09-09-slice2-compile-error-list.md` | the nine-site list for S-B (its S2 conclusion is corrected by §0) |
| `2026-09-09-slice2-barrier-inventory.md` | 18 rejection sites (5 live-source, 10 live-direct, 3 shadowed); the reference-evaluator finding |
| `2026-09-09-slice2-write-pipeline.md` | emission/checking/evaluation trace; five confirmed verdicts including that the evaluator is already generic over the coefficient |
| `2026-09-09-slice2-test-doc-surface.md` | pinning fixtures, corpus counts, JAX gate structure, doc surface |

**The checked scan worker needs no S-B changes.** `applyAffine`/`commitWrite`/`runDenseScan` never
mention `WriteRowKind` and are fully generic over the coefficient. The broader statement that “the
evaluator needs no work” was wrong: the legacy scan evaluator rejects non-assignment slice
statements and needs independent compute-then-place semantics, while the scan-free oracle needs a
dense-temporary/scatter/merge lowering (§3.6).

Two latent defects found in passing, neither in scope: coefficient-row **width** is unchecked on both
the write side (`checkWrites` guards row count only; `applyAffine` `zip`s and truncates) and the read
side (`Check.lean` checks `coeffs.size == sourceShape.size`, never per-row width). And
`CompileTest.lean`'s `predicateSourceSched` docstring claims an affine LHS slot the code does not
have.
