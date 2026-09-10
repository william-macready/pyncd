# Pre-Scatter backend audit — boundary invariants and write geometry

Findings-only audit of the checked `EvalPlan` backend (`leanncd/LeanNCD/Eval/Plan/`), conducted
**before** the Scatter + affine LHS writes feature is built. **No production code was changed by this
audit**, and nothing here is a fix — every entry is a finding, a refutation, or a decision recorded
for the Scatter slice to inherit.

## ⚠️ SUPERSEDING BANNER — 2026-09-09: Slice 1 (write-geometry hardening) has landed

**This audit is a snapshot of the tree at `2159d28`/`267976e`/`9680b92` and is deliberately NOT
rewritten.** Its findings, refutations and cell adjudications stand as taken, and the verbatim arm
quotes scattered through it (`| _ => true`, `| _, _ => false`, `| _ => pure ()`, …) are evidence of
the *pre-slice* tree — do not "correct" them; they are what the tripwire replaced. The current spec
is `post_audit_roadmap.md` Section A, whose Slice 1 completion record supersedes this document
wherever the two disagree.

**⚠️ ADDENDUM 2026-09-09 — three further places this audit misleads, found while planning the
Scatter slice. The current authority is `papers/scatter_affine_lhs_writes.md`.**

- **§B2.1's Decision A analysis concerns a path unreachable from surface syntax.** A scatter-shaped
  LHS combined with an iteration slot is rejected at DSL phase 7 by `checkScatterNoScan`, in the
  base block and the step block alike — measured by probe. So decisions A and B chose between two
  currently-unreachable options, and reaching either requires lifting a deliberate DSL guard this
  audit never mentions. The base-vs-step question is real but it is not the gate.
- **§B2.6's Tier-1 negative-coverage list: items 1 and 3 INVERT; item 2 stands.** Both assert
  rejection of a strided row at a *non-advancing* step dimension — which is exactly the step-phase
  strided write Decision A admits. They must become acceptances. Item 2 (strided at an *advancing*
  dimension) is correct under any decision: that dimension carries the recurrence.
- **§B2.1's adopted `classifyWriteRow` branch has a live soundness hole.** It carries no guard on
  the sign of `scale`/`offset`. Measured: within `scale ∈ 1..5`, `offset ∈ -6..-1`, `outDim ∈ 1..8`
  there are **200** combinations where the extent check passes and a written coordinate is still
  negative, which `commitWrite`'s `Int.toNat` collapses onto index 0 — clobbering a legitimate
  write, no panic, no diagnostic. Add `c > 0 && bias ≥ 0`; it costs nothing a surface program can
  express, since the elaborator builds coefficients through `Int.ofNat` (B1-F9).

**Five load-bearing places where this audit is now stale.** One of them contradicts a shipped
`AGENTS.md`, so read this list before quoting any of them as current:

1. **`B1-F6`** — *"Two hand-inlined duplicates confirmed"* and *"the two copies will not see it"*.
   **One of the two is gone.** Slice 1 routed the pinned-literal check through a real
   `pinnedLiteralsInRange` call (mutation-verified: deleting the predicate's pinned-row rule now
   breaks `ScanCompileTest`'s two `baseWritePinOutOfRange` guards, which the inlined copy survived
   unchanged), leaving only the LOCATOR at the call site. `leanncd/LeanNCD/Eval/AGENTS.md` accordingly
   says *"the one surviving duplicate"* — the `baseWriteNotAtBoundary` guard restating
   `baseWriteRowsOk`'s advancing-pin clause, whose extraction is owned by the Scatter slice. **Two
   shipped documents, opposite counts; `Eval/AGENTS.md` is the current one.** Separately, the
   duplicated *computation* B1-F6 records alongside — `writeRowKinds` run twice over the same writes
   in one pass — was hoisted to a single `baseWriteRows`.
2. **`B1-F10`**, and the same measurement where it is used as this slice's justification
   (*"Reconciling the two parts"*, item 2: *"zero base-phase geometry fixtures exist. There is
   currently no test that could fail"*). **All of it is now false — because Slice 1 landed.** Current
   figures: **14** `#guard`s exercise `baseWriteRowsOk`/`stepWriteRowsOk`, **9 of them negations**,
   plus **3** negative guards on the `classifyWriteRow` chokepoint (12 negative assertions where the
   audit correctly measured zero); and **6** plan-level `writeGeometryNotAdmitted` assertions, three
   `isBase = false` and three `isBase = true` (`true 0`, `true 0`, `true 1`), so the base-phase leg
   of that locator is pinned in both directions and is demonstrably load-bearing. B1-F10's *cell*
   accounting (which of the 16/22 `b` cells has a located test) has not been re-derived against the
   new fixtures and should be redone rather than trusted.
3. **§B2.7's barrier-1 analysis.** Both of its site-2 observations have moved. *"`Compile.lean`'s
   Phase 5 source-facing pass, which hard-codes the same `0` twice"* — now **once**, hoisted into the
   shared `baseWriteRows`. And the pinned-literal check's *"`| _ => pure ()` arm is
   constructor-blind"* — that arm now spells out `some (.free _) | some (.advancing _) | none`, so a
   fourth constructor is a **compile error** there, not a silent pass. The polarity argument itself
   (barrier 1 is no defence for a strided row, because `p ≥ contextWidth` holds for every `p` at
   `contextWidth = 0`) is untouched and still governs.
4. **"Reconciling the two parts", item 3** — *"Making each match exhaustive … is only useful at the
   moment the fourth constructor arrives, so do it then, **not before**."* **Deliberately reversed.**
   `post_audit_roadmap.md` Section A's "Why before Scatter, not with it" carries the argument: done
   first it is a behaviour-preserving refactor the existing suite proves, and it installs the
   tripwire so the constructor addition produces compile errors instead of silence; done
   simultaneously the compile errors appear inside a larger diff and cannot be separated from the
   new-kind work.
5. **Two counts in the doc-obligation findings.** `WriteRowKind`'s production **signature positions
   are 12, not 11** — Task 3 added `Compile.lean`'s `baseWriteRows` annotation to the eleven the
   call-site sweep enumerates. And **`B2-F3`'s "four docstrings and one `AGENTS.md` node" now
   undercounts**: Slice 1 added a second enumerating passage to that same `Eval/AGENTS.md` node (the
   write-geometry exhaustiveness Contracts row), extended `WriteRowKind`'s and
   `pinnedLiteralsInRange`'s docstrings with further enumerating prose, and added Part 9's prose plus
   `allRowKinds` in `ScanTest.lean`. Note the asymmetry Slice 1 introduced: the enumerations *in
   match arms* are now compiler-enforced, so they cannot go silently stale; only the **prose**
   enumerations carry B2-F3's risk, and there are more of them than five.

## Why this exists

The Boolean/predicate declared-outputs slice needed roughly **six whole-branch review rounds and
~20 fix commits** after its "done" commits. A post-mortem traced the cost not to Boolean semantics
but to shared infrastructure, and that slice's own consolidation task named the problem:

> public, hand-constructible values reach several consumers, and those consumers independently
> re-establish only the subset of invariants they happen to need

Scatter lands on the same surface, and additionally on the **write path** — home to a defect shape
this repo has now hit five times, each time found one review round at a time:

> a geometry predicate validates *which rows MUST be a given kind* without validating *which rows
> MAY NOT be*.

This audit characterises both surfaces in advance, so the sixth occurrence is designed against rather
than discovered.

## Provenance

Two axes were audited independently and are merged here as Part I and Part II. The parts declare
different "taken at" commits (`2159d28` and `267976e`) because they were written at different points
on the same branch. **This is immaterial to every source claim**: the audit's whole branch
(`2159d28..0cf7e88`, 11 commits) has an *empty* production diff —

```
git diff 2159d28 0cf7e88 -- leanncd/LeanNCD leanncd/lakefile.toml leanncd/test   # empty
```

— so the production tree the two parts describe is one and the same. Build green at **8660 jobs**
throughout. `WriteRowKind` still has exactly three constructors; no `strided` constructor exists in
any committed file.

## Evidence inventory

Every `[snippet, Sn]` citation resolves to one of six spike files, each committed with its verbatim
captured output, tracked in `leanncd/spikes/` via `leanncd/.gitignore` exceptions (alongside the
pre-existing `BrNF.lean`) and deliberately **off** the default build. Re-run any of them with
`lake env lean spikes/<file>.lean` from `leanncd/`. All six were verified to reproduce
byte-identically against their `.output.txt` at merge time.

| Spike | Probes | Part |
|---|---|---|
| `AxisABoundaryProbe.lean` | S1–S11 | I |
| `AxisBWriteGeometryProbe.lean` | S1–S13 | II |
| `AxisBBaseBoundaryProbe.lean` | S14–S16 | II |
| `AxisBStridedProbe.lean` | S17–S22 | II |
| `AxisBZeroExtentProbe.lean` | S23–S25 | II |
| `AxisBSurfaceZeroExtentProbe.lean` | S26 | II |

Note: Part II's own header sentence says "Two spike files" — accurate when written, before the
strided work appended three more. This table is the authoritative inventory; §B1.5 lists the same
six. Spike S-numbering restarts per part, so cite as *Part I S8* / *Part II S8*.

These spikes are not in any build target, so **nothing in CI compiles them.** They can rot silently;
treat a failure to reproduce as a signal that the code moved, and re-derive rather than assuming the
spike is wrong.

## Findings index

Severity/status is as each part states it. "Latent" means reachable at the predicate but blocked by
something upstream; "live" means reachable end-to-end today or on the stated decision.

### Part I — boundary / invariant re-establishment

| # | Finding | Status |
|---|---|---|
| BND-01 | a `requiredInputs` name↔slot pairing is never re-established; swapping it silently feeds the wrong tensor to the wrong slot | **live**, silently-wrong-answer |
| BND-02 | a `materializedNames` binding's NAME is never re-established, so an output can be published under an input's name | **live**, silently-wrong-answer |
| BND-03 | four doc comments make a stale producer-discipline claim; two misname the shared resolver | documentation defect |
| BND-04 | `PreparedPlan.warnings` is unvalidated — a real diagnostic can be dropped and a false one invented | **live** |
| BND-05 | the plan-level JAX executable path discards `checkJaxAssignSupport`'s located cause | **live**, diagnostic-quality |
| — | input dtype at the runtime input boundaries | **REFUTED** (§4.7) |

### Part II — write-geometry predicate surface

| # | Finding | Status |
|---|---|---|
| B1-F1 | the inherited "F4 seven-predicate table" does not exist; the closest precedent covers a different predicate family | stale-claim correction (§B1.1) |
| B1-F2 | `baseWriteRowsOk` admits an `.advancing` row at base | **latent** (10 cells), two barriers |
| B1-F3 | coeff-row width is unchecked but provably irrelevant | **REFUTED** |
| B1-F4 | a `free` row may sit at an advancing dimension in a base write | open (5 cells), memory-safe |
| B1-F5 | base writes need touch the lower boundary of only ONE advancing dimension | open, memory-safe |
| B1-F6 | `Compile.lean`'s second call site is a strict subset of `Scan.lean`'s rules | open |
| B1-F7 | `commitWrite`'s docstring is complete over constructors but step-scoped for `.advancing` | open |
| B1-F8 | `writesCollide` is length-blind in both directions | **REFUTED as harmful** |
| B1-F9 | `DSL/Ast.lean` slot functions — zero-extent scatter output | **answered in §B2.5**: not rejected; reachable via a **zero coefficient**, live from four words of surface syntax |
| B1-F10 | 10 of the 16 `b` cells have no located test | **live coverage gap** |
| B2-F1 | the write-geometry defect family recurs a **SIXTH** time, LIVE at base | **live** under decision A (16 cells) |
| B2-F2 | not one `a` cell among 56 | structural observation |
| B2-F3 | four docstrings and one AGENTS.md node enumerate the constructor set exhaustively | doc defect, breaks on a new kind |
| B2-F4 | `freeExtentsAgree`'s equality is the `scale = 1, offset = 0` special case | open |
| B2-F5 | the 6 new `b` cells are not locatable by any test that could exist today | coverage gap |
| B2-F6 | the minimal strided kind admits a strict subset of the affine LHS forms | scope note |

## The one decision this audit does not make

Part II §B2.1 adopts **decision A** — the strided branch carries `.free`'s existing
`p ≥ contextWidth` guard with **no phase gate** — and everything downstream follows from it. That
rests on one assumption which is *not* derivable from the code: **that affine LHS writes are wanted
in base blocks, not only step blocks.** That is a scope question about the Scatter feature.

Whoever sets Scatter's scope must answer it, and Part II is written to be usable either way: all 14
groups G17–G30 carry a decision-B reading.

**What flips.** Under decision A, `B2-F1` is live and unsafe at base. Under **decision B**
(phase-gate the strided branch), `classifyWriteRow` returns `none` for a strided-shaped row at base,
the site rejects, and **B2-F1 has zero open cells** — all 16 become latent behind barrier 1.

**A census caveat that the parts do not state.** Part II's headline census — 224 cells,
`24 a / 22 b / 122 c / 24 — / 32 ▷` — is **decision-A-only**. G19 is the one group whose decision-B
reading shifts a letter (4 cells `c` → `b`), so under decision B the table reads
`24 a / 26 b / 118 c`, and `B2-F5`'s "6 `b` cells not locatable" becomes 10 — of which the 4 new ones
*are* locatable today (Part II S18 already exhibits the shape), unlike the 6 step-phase ones. No
verdict changes either way.

## Reconciling the two parts: what to do first

Each part names something that must be settled "first". They are not competing, because **they are
different kinds of obligation on different surfaces**, and conflating them is how a fix wave goes
wrong:

- **Part I's BND-01/BND-02 are policy decisions to make, not defects to squash.** The checked plan
  proves *slot* identity and deliberately never proves *name* identity. That choice is documented in
  four places and **pinned by a live green `#guard`** asserting that a wholesale rename is accepted
  as valid. Part I §4.3 carries the retire list. A drive-by "fix" turns that guard red and
  contradicts an `AGENTS.md` contract line. What the audit establishes is that the choice has a
  reachable, silent, wrong-answer consequence through the public API — which is new information for
  the decision, not a mandate to reverse it.
- **Part II's B2-F1 is a defect to fix**, conditional on the scope decision above. Under decision A
  it is live memory-unsafety at base.

Recommended ordering — write-geometry track:

1. **Answer the scope question** (base vs. step-only affine LHS). Everything else in Part II
   branches on it; doing it later means redoing the analysis.
2. **Add the Tier 1 negative coverage Part II §B2.6 names, *before* editing `stepWriteRowsOk`'s
   clause 2.** This is the crux of `B1-F10`: all five existing `#guard`s on the geometry predicates
   are *acceptances*, none is negated, and all three plan-level `writeGeometryNotAdmitted` assertions
   are `false 0` — so **zero base-phase geometry fixtures exist**. There is currently no test that
   could fail. That, mechanically, is why this defect family recurs rather than being caught.
3. **Remove the catch-alls as the constructor is added.** `freeExtentsAgree` and
   `pinnedLiteralsInRange` end in `| _ => true`; `writesCollide` in `| _, _ => false`;
   `stepWriteRowsOk`'s coverage clause drops anything unrecognised via `filterMap`. A new row kind
   lands in those arms and is exempted from every value check **by default, silently**. Making each
   match exhaustive over the constructors converts that into a compile error at every site that must
   be updated — which is only *useful* at the moment the fourth constructor arrives, so do it then,
   not before.
4. **Honour the single shared extent formula.** Part II §B2.4 ties every strided cell to an
   `LHSSlot.outExtent` arm. A duplicate formula (`scatterOutDim`) previously drifted from it and
   shipped a soundness bug (fix `fc10d70`, duplicate deleted `6a26825`). Call it; do not copy it.

Binding/adapter track — **independent, neither blocks the other**:

5. **Decide the name-authentication policy** (BND-01/BND-02), as a decision with the retire list in
   hand. Then BND-04 and BND-05, which are narrower and unblocked.

## What this audit does NOT cover

- **Semantic-payload finding #6's four boundary decoders** (`realizeStMat`, `realizeBrBaseP`,
  `AcsetCodec`, `realizeSBr`) were deliberately out of scope: different subsystem, no Scatter
  overlap, and the `realize*` family is `noncomputable`, so the construction-attempt evidence bar
  used throughout this audit is not even available there. **This audit does not close
  `leanncd/AGENTS.md`'s UNAUDITED flag on finding #6.**
- Scatter collision **Gap 2** (a symbolic over-approximation of non-injective scatter maps; no
  concrete axis sizes exist at compile time).
- Decomposing `DSL/Pipeline/Structural.lean` or `Eval/Plan/Compile.lean` (the two size outliers, and
  structural hubs — their own slice).
- Whether a nonlinearity activates before or after collision reduction — a Scatter design question,
  deferred by policy long before this audit.

---

# Axis A — boundary / invariant re-establishment audit (findings only)

Base: `worktree-pre-scatter-audit` @ `2159d28`. Build green at **8660 jobs** before and after; no
production code was changed (`git diff 2159d28 HEAD -- leanncd/LeanNCD/` empty).

Construction evidence lives in `leanncd/spikes/AxisABoundaryProbe.lean` (tracked in git via a
`leanncd/.gitignore` exception, off the default build) with its verbatim run recorded in
`leanncd/spikes/AxisABoundaryProbe.output.txt`. Spike blocks are cited below as `S1`…`S11`. (`S11`'s
index contrast is not sound evidence for any claim in this fragment — see BND-05, §4.6 — and is not
cited below.)

## 1. Scope

### In scope

| Boundary family | Entry points examined |
|---|---|
| Named↔positional runtime seam | `packChecked`, `unpackChecked`, `pack`, `unpack`, `runPreparedDense` (`Adapter.lean`) |
| Positional runtime seam | `runDensePlan`'s input loop and store allocation (`EvalPlan.lean`) |
| Prepared-plan type set | `RequiredBindings`, `PlanBindings`, `PreparedPlan`, `CheckedPreparedBindings`, `checkBindings`, `checkPreparedBindings`, `materializedWith`, `materializedSignatures` (`Prepared.lean`) |
| JAX executable phase | `checkJaxAssignSupport`, `jaxAssignSupported`, `JaxExecutableCandidate`, `stepTiedToPreparedStep`, `preparedBindingsTied`, `JaxExecutableWellFormed`, `validateAndConstructExecutable` (`Executable.lean`) |
| Signature producers | `InputSignature.ofDenseInputs`, `InputSignature.ofDenseInputsForDecls`, `dtypeOfDecl` (`Signature.lean`) |
| Post-consolidation schedule authority | one bounded row only: does `prepareEvalPlan` or `evalScheduled` read a raw `sched` field after `validateScheduled`? |

### Out of scope — deliberately not audited

- **This audit does NOT close `leanncd/AGENTS.md`'s UNAUDITED flag on semantic-payload finding #6.**
  The four boundary decoders that finding names — `realizeStMat`, `realizeBrBaseP`, `AcsetCodec`,
  and `realizeSBr` — were not examined here at all, and nothing in this fragment may be read as
  evidence about them. They remain UNAUDITED.
- `experiments/jax_bridge/EvalPlanCodegen.lean` and the other `experiments/jax_bridge` modules.
  Only the LeanNCD-side gates they call are covered, via `Executable.lean`.
- `LeanNCD/Eval/Plan/Scan.lean`'s write-geometry predicates — Task B's territory.

## 2. Verified facts

| Claim | How it was verified |
|---|---|
| Baseline and post-audit builds are green at 8660 jobs | `[built]` `cd leanncd && lake build` → `Build completed successfully (8660 jobs).` |
| The repo has **12** `private mk ::` declaration sites, not 16 | `[read]` `grep -rn --include=*.lean -E "^\s*(structure .* where )?private mk ::" .` (excluding `.lake`) returns 12 declaration lines; the remaining `private mk ::` grep hits are prose inside doc comments. Ten are under `Eval/Plan` (`CheckedAssignPlan`, `CheckedPointwisePlan`, `CheckedAxiswisePlan`, `CheckedScanPlan`, `CheckedPlanBlock`, `CheckedEvalPlan`, `RequiredBindings`, `CheckedPreparedBindings`, `JaxKernel`, `JaxExecutable`); the other two are `CheckedScheduledProgram` and `RouteFragments.lean`'s. No other constructor-privatization idiom is used anywhere. |
| The hand-constructible checked-surface set audited as its own boundary family here is **three** types, and other public hand-constructible types were excluded with reason | `[read]` type census of `Eval/Plan` minus the ten `private mk ::` types. Public-constructor types whose fields include an already-validated payload, audited directly as their own boundary family: `PreparedPlan`, `PlanBindings`, `JaxExecutableCandidate`. **`JaxKernelCandidate`** — a public inductive over the public structures `OrderedAffineTableKernelCandidate` and `EinsumExperimentKernelCandidate` — is also hand-constructible, and its `tables`/`operands`/`outputAxes` fields are genuinely unconstrained; it is not omitted from the audit, only from this list of three, because it is covered as row E9 (`re-checked`, via `validateAffineTable`/`validateEinsum`), and both S8 and S11 hand-build it directly as scaffolding for their own constructions. **`SomeJaxKernel` and `SomeJaxExecutable` are also public-constructor wrappers over `private mk ::` payloads and are deliberately excluded**, not overlooked: each has a dependent second field (`kernel : JaxKernel evidence`, `executable : JaxExecutable evidence`) that forces the exposed index to be the one a validated payload was built with, so the wrapper admits no state its payload does not already permit. The brief named only `PreparedPlan` and `JaxExecutableCandidate`; `PlanBindings` is the one it omitted, and it is the type on which every finding below rests. |
| The unchecked-name axis is a **documented, test-pinned deliberate decision**, recorded in four places | `[read]` (a) `Prepared.lean`, `checkPreparedBindings`'s doc comment: "Names remain deliberately unauthenticated: positional raw IR can prove slots and required-name uniqueness, not origins."; (b) `LeanNCD/Eval/AGENTS.md`, the `Prepared.lean` row: "Raw plans prove slots but cannot authenticate names."; (c) `test/Eval/Plan/CompileTest.lean`, comment "Exact publication is structural slot identity, not name authentication … changing only names is valid", and a live `#guard` later in the same section asserting `checkPreparedBindings` returns `.ok` on a plan whose every `materializedNames` entry has been renamed to `"renamed"`; (d) `experiments/jax_bridge/README.md`: "Every named codegen entry first validates the prepared binding sidecar against the raw plan's exact publication slots; raw IR cannot authenticate the user-visible names themselves." |
| Every production `PreparedPlan` consumer in `LeanNCD/` routes through `checkPreparedBindings` | `[read]` the complete consumer list is `pack`, `unpack`, `runPreparedDense`, `packChecked`, `unpackChecked`, `materializedSignatures`, `preparedBindingsTied`, `stepTiedToPreparedStep`, and `checkPreparedBindings` itself; each either calls it or receives the `CheckedPreparedBindings` a caller obtained from it |
| No function anywhere takes `PlanBindings` as a parameter | `[read]` `grep -rn --include=*.lean "PlanBindings" LeanNCD/ experiments/` returns **16 hits**: one `structure` declaration, one `PreparedPlan.bindings` field, and fourteen mentions inside doc comments. None is a parameter binder — the type is reachable only through `PreparedPlan.bindings`, which is why its own invariants are checked, if at all, by `PreparedPlan`'s consumers rather than by anything it owns. |
| `packChecked`'s and `runDensePlan`'s `raw.tensorSigs.getD` defaults are unreachable | `[snippet]` S9 — `checkPlan { raw with inputSlots := #[99] }` → `PlanStepError.assign (PlanError.slotOutOfRange 99 3)`. The bound is `checkStepGraph`'s first loop (`unless s < n`), which runs before any `CheckedEvalPlan` exists |
| `runDensePlan`'s `Array.replicate` placeholder can never be read | `[snippet]` S9 — adding an unproduced `tensorSigs` slot gives `PlanError.missingProduction 3` from `checkStepGraph`'s final loop |
| `runDensePlan`'s `inputs[i]!`, `store.set! slot` are in range | `[snippet]` S7 — `runDensePlan plan #[]` is rejected (`arityMismatch`), and slot bounds come from the same `checkStepGraph` bound above |
| `runDensePlan` re-checks shape and storage exactly as `packChecked` does | `[snippet]` S7 — wrong shape and wrong storage are both rejected; `[read]` the two loops apply the same two `unless` comparisons against `sig.shape`, in two independent copies |
| `packChecked`'s `| none => .missingEnvBinding` arm is **dead code** | `[snippet]` S2 — a `PreparedPlan` pairing a validly-checked one-input `RequiredBindings` against a two-slot `raw.inputSlots` is rejected earlier by `checkPreparedBindings` with `PreparedBindingsError.requiredInputs (BindingsError.notAPermutation #[0, 1] #[0])`. `checkPreparedBindings` re-runs `checkBindings` against `raw.inputSlots`, ignoring `RequiredBindings`' own stored field |
| A name↔slot *pairing* swap in `requiredInputs` is accepted and silently changes the answer | `[snippet]` S1 — `checkBindings`, `checkPreparedBindings`, and `preparedBindingsTied` all accept it; `runPreparedDense` returns `.ok` with `W = #[110.0, 220.0]` where the correct value is `#[30.0, 300.0]` |
| **No test covers the `requiredInputs` pairing swap (BND-01's axis)** | `[read]` `AdapterTest.lean` Check 5 reverses the `requiredInputs` **array** while preserving each binding's own name↔slot pair, and asserts the *correct* result; that fixture is about array-position-vs-`.slot` resolution. Nothing in the suite perturbs the pairing itself. |
| **A test DOES cover the `materializedNames` rename (BND-02's axis) — and pins acceptance as intended** | `[read]` `test/Eval/Plan/CompileTest.lean`'s `#guard` on `checkPreparedBindings` applied to `materializedNames.map fun b => { b with name := "renamed" }` asserts `.ok`. BND-02 is therefore not an untested gap but a *deliberately pinned* one; any fix must retire that `#guard`. |
| Renaming a materialized binding to an input's name is accepted and clobbers that input | `[snippet]` S3 — `runPreparedDense` returns `.ok`, `env["A"]` becomes the computed output `#[30.0, 300.0]`, and `W` is absent from the result environment |
| **The input-dtype candidate is REFUTED** — checked and reference backends agree on non-binary data through a Boolean destination | `[snippet]` S4 — a `predicate P(i)` destination over `X = [0.5, 0.25]`, `Y = [0.75, 0.1]` gives `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]`, identical |
| An **input** slot's `bool` dtype tag changes no Dense behavior at all | `[snippet]` S5 — the same Float data through a `bool`-signature input slot and an `f64`-signature input slot both give `Q = #[0.25, 9.0]` |
| The declaration-blind signature producer is caught downstream, loudly | `[snippet]` S6 — `prepareEvalPlan sched (InputSignature.ofDenseInputs …)` on a program declaring a `predicate` input fails with `InputSignatureError.dtypeMismatch "Z" bool f64` at Step B |
| A validated JAX kernel cannot be re-used at a non-`.assign` step index | `[snippet]` S8 — `Y[i] := relu(X[i])` lowers to `#["assign", "pointwise"]`; a candidate whose step-0 einsum kernel is repeated at index 1 is rejected as `JaxExecutableValidationError.invalidCandidate` — with no step index and no underlying cause |
| `PreparedPlan.warnings` can be silently emptied AND silently fabricated | `[snippet]` S10 — a plan whose producer recorded one real `paddedAccess` warning runs `.ok` with `warnings reported = 0` after `warnings := []`; a plan whose producer recorded none runs `.ok` reporting a borrowed warning about a read that does not exist in it |
| The plan-level JAX executable path discards `checkJaxAssignSupport`'s located cause; the gate itself is correctly located at every real caller | `[snippet]` S8 — reusing a validated JAX kernel at a `.pointwise` step yields `JaxExecutableValidationError.invalidCandidate`, with no step index and no underlying cause; `[read]` `jaxSupportOk` hardcodes `checkJaxAssignSupport sigs 0` and returns only a `Bool`, and `validateAndConstructExecutable`'s well-formedness branch throws bare `.invalidCandidate`. `checkJaxAssignSupport` itself is a plain public `def`, correctly located, and is reached with a real outer step index by `EvalPlanCodegen.requireJaxSupport` at a plan-level call site (`renderAffineNode`); `validateAndConstructKernel`'s own hardcoded `0` is the documented standalone-entry convention, not a defect — `requireJaxSupport`'s doc states "0 at a standalone one", and `test/Eval/Plan/ExecutableTest.lean` pins exactly this: its `step1BoolAssign` fixture (commented as step 1 of the two-step `step1BoolRaw` plan) is validated in isolation via `affineOutcome`/`jaxOutcome`/`validateAndConstructKernel`, and the `#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))` asserting index `0` there is green. |
| Neither `prepareEvalPlan` nor `evalScheduled` reads a cached `sched` field after validation | `[read]` `prepareEvalPlan` binds `checked.declEnv`, `checked.explicitSizes`, `checked.extNames`; `evalScheduled` binds `checked.explicitSizes`. The only raw reads on either side are `sched.decls`/`sched.stmts`, which `ScheduledProgram`'s own contract makes authoritative (not cached products), and which are the exact values `validateScheduled` validated |
| `evalPlain sched.decls` and `checked.declEnv` provably cannot disagree | `[read]` `buildDeclEnv` rejects a second tensor-bearing declaration of a name (`CompileError.duplicateTensorDecl`), so `combineFor`'s first-match `decls.find?` and a `DeclEnv` lookup see the same declaration for every name that survives validation |

## 3. Boundary inventory

Columns: `Boundary` | `Consumed type` | `Constructor` | `Invariant` | `Producer establishes` | `Consumer re-checks` | `Verdict` | `Failure mode` | `Scatter` | `Severity`

**One departure from the closed Failure-mode vocabulary, stated up front.** Rows **A7** and **C6**
carry `n/a (no invariant)` rather than one of the five vocabulary values. Both concern the claim
"input tensor values are 0/1 when the slot's signature dtype is `bool`". Nothing establishes it and
nothing checks it, so the Verdict is honestly `assumed-unchecked` — but the system does not *hold*
that claim (`Check.lean`'s `admittedAlgebraBool` doc comment and `Eval/AGENTS.md` Contract (c) both
state the opposite explicitly), so there is no violation for a failure mode to describe. Assigning
one of the five values would either overstate harm (S4 proves both backends agree) or import a
different consumer's behavior. **Consequence for finding arithmetic: these two rows are
`assumed-unchecked` but are NOT findings, and §4's reconciliation table accounts for them
explicitly.**

### 3.1 `Adapter.packChecked` / `pack`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| A1 | `PreparedPlan` | public | every `raw.inputSlots` slot has a bound name | `prepareEvalPlan` (`inputSlotsAcc`/`requiredInputsAcc` built together) | `checkPreparedBindings` → `checkBindings` (`Perm` against `raw.inputSlots`) | `re-checked` | loud typed error | direct | — |
| A2 | `PreparedPlan` | public | `raw.tensorSigs.getD slot` is in range | `checkStepGraph`'s input bound | `checkPlan` (before `CheckedEvalPlan` exists) | `enforced-by-type` | loud typed error | direct | — |
| A3 | `NamedDenseEnv` | public | each bound name is present in `env` | — | `packChecked`'s `env[name]?` → `InputBindingError.missingEnvBinding` | `re-checked` | loud typed error | direct | — |
| A4 | `DenseTensor` | public | tensor shape = signature shape | — | `packChecked` `unless t.shape == tsig.shape.toList` | `re-checked` | loud typed error | direct | — |
| A5 | `DenseTensor` | public | `data.size = ∏ shape` | — | `packChecked` `unless t.data.size == …foldl (· * ·) 1` | `re-checked` | loud typed error | direct | — |
| **A6** | `PlanBindings` | public | each `requiredInputs` binding's NAME is the name the schedule gave THAT slot | producer discipline only (`prepareEvalPlan` pushes `{name := nm, slot}` in one step); documented as deliberate in `checkPreparedBindings`' doc comment and `Eval/AGENTS.md` | none — `checkBindings` checks the slot multiset and name uniqueness, never the pairing | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| A7 | `DenseTensor` | public | values are 0/1 when the slot's signature dtype is `bool` | nothing — and the system does not hold this claim (`admittedAlgebraBool` doc comment; `Eval/AGENTS.md` Contract (c) states values are deliberately unrestricted) | nothing | `assumed-unchecked` | *n/a (no invariant)* | adjacent | S4 |
| A8 | `PreparedPlan` | public | `requiredInputs.inputSlots` = the enclosing plan's `raw.inputSlots` | producer discipline (per four files' doc comments) | `checkPreparedBindings` — it ignores the stored field and re-runs `checkBindings` against `raw.inputSlots` | `re-checked` | loud typed error | direct | — |

### 3.2 `Adapter.unpackChecked` / `unpack` / `runPreparedDense`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| B1 | `Array DenseTensor` | public | store arity = `raw.tensorSigs.size` | `runDensePlan` returns exactly that | `unpackChecked`'s exact-equality guard → `PositionalInputError.storeArityMismatch` | `re-checked` | loud typed error | direct | — |
| B2 | `PlanBindings` | public | every `materializedNames` slot is in the table | `prepareEvalPlan` allocates each in `tensorSigs` | `rawMaterializedWith` → `PlanError.slotOutOfRange` (via `checkPreparedBindings` and again via `materializedWith`) | `re-checked` | loud typed error | direct | — |
| B3 | `PlanBindings` | public | the materialized slot SEQUENCE is the raw plan's publication sequence | `prepareEvalPlan`'s per-statement push order | `checkPreparedBindings` vs `rawPublicationSlots` → `PreparedBindingsError.publicationSlots` | `re-checked` | loud typed error | direct | — |
| **B4** | `PlanBindings` | public | each `materializedNames` binding's NAME is the name the schedule assigns that slot | producer discipline only; documented as deliberate, and a `CompileTest.lean` `#guard` pins acceptance of a wholesale rename | none — only the slot sequence is compared; names are unconstrained | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| B5 | `PreparedPlan` | public | metadata and execution resolve the same bindings | one shared `rawMaterializedWith` behind `CheckedPreparedBindings.materializedWith`, used by both `unpackChecked` and `materializedSignatures` | n/a — shared, not duplicated | `enforced-by-type` | loud typed error | direct | — |
| B6 | `PreparedPlan` | public | `pack` and `unpack` inside one run see the same checked view | `runPreparedDense` calls `checkPreparedBindings` once and threads the result | n/a | `enforced-by-type` | loud typed error | direct | — |

### 3.3 `EvalPlan.runDensePlan` positional input loop

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| C1 | `Array DenseTensor` | public | `inputs.size = raw.inputSlots.size` (guards `inputs[i]!`) | `packChecked` pushes exactly that many | `runDensePlan`'s `arityMismatch` guard | `re-checked` | loud typed error | direct | — |
| C2 | `CheckedEvalPlan` | `private mk ::` + `checkPlan` | `raw.tensorSigs.getD slot` and `store.set! slot` in range | `checkStepGraph`'s `unless s < n` | — (not re-derived; the type carries it) | `enforced-by-type` | loud typed error | direct | — |
| C3 | `CheckedEvalPlan` | `private mk ::` + `checkPlan` | every store slot is written before it is read, so the `Array.replicate` placeholder is never observed | `checkStepGraph`'s forward-read check + `missingProduction` | — | `enforced-by-type` | loud typed error | direct | — |
| C4 | `DenseTensor` | public | shape = signature shape | — | `runDensePlan`'s own `shapeMismatch` guard | `re-checked` | loud typed error | direct | — |
| C5 | `DenseTensor` | public | `data.size = ∏ shape` | — | `runDensePlan`'s own `storageMismatch` guard | `re-checked` | loud typed error | direct | — |
| C6 | `DenseTensor` | public | data respects the slot's `bool` dtype tag | nothing — and the system does not hold this claim (see A7) | nothing (S5: the tag is behaviorally inert here) | `assumed-unchecked` | *n/a (no invariant)* | adjacent | S4 |
| C7 | `CheckedEvalPlan` | `private mk ::` | the signature table executed under is the table checked against | `runDensePlan` reads `c.raw.tensorSigs`; there is no caller-supplied table to disagree with (unlike `runDenseScan`, which needs and has `signatureContextMismatch`) | n/a | `enforced-by-type` | loud typed error | direct | — |

### 3.4 `Prepared.lean` type set

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| D1 | `RequiredBindings` | `private mk ::` + `checkBindings` | binding slots are a `Perm` of its own `inputSlots`, names `Nodup` | `checkBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D2 | `CheckedPreparedBindings` | `private mk ::` + `checkPreparedBindings` | the whole sidecar has been validated against the plan's own raw slots | `checkPreparedBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D3 | `PreparedPlan` | public | every consumer sees a validated sidecar | — | every production consumer calls `checkPreparedBindings` (complete list in §2) | `re-checked` | loud typed error | direct | — |
| **D4** | `PlanBindings` | public | name↔slot pairings — BOTH axes: `requiredInputs` (see A6) and `materializedNames` (see B4) | producer discipline only, documented as deliberate | none | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| **D5** | `PreparedPlan` | public | `warnings` are the preparation's own | producer discipline only | none — a hand-built plan can carry any warning list, or drop them | `assumed-unchecked` | silent no-op | none | S4 |

### 3.5 `Executable.lean`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| E1 | `Array TensorSignature` | public | the caller-supplied table really describes the assignment | — | `checkJaxAssignSupport` re-runs `checkAssign` → `JaxSupportError.invalidSignatureContext` | `re-checked` | loud typed error | none | — |
| E2 | `CheckedAssignPlan` | `private mk ::` | the assignment is JAX-renderable (dest dtype, algebra, context, source dtype, unary) | `checkAssign` admits all of these | `jaxAssignSupported`, in the declared order | `re-checked` | loud typed error | none | — |
| E3 | `JaxExecutableCandidate` | public | step count = the prepared plan's raw step count | — | `JaxExecutableWellFormed`'s first conjunct | `re-checked` | loud typed error | adjacent | — |
| E4 | `JaxExecutableCandidate` | public | each kernel's stored table = the prepared plan's own | — | `stepTiedToPreparedStep`'s first conjunct | `re-checked` | loud typed error | adjacent | — |
| E5 | `JaxExecutableCandidate` | public | each kernel's assignment is THAT step's checked assignment (and a non-`.assign` step gets none) | — | `stepTiedToPreparedStep`'s `| _ => false` arm | `re-checked` | loud typed error | adjacent | — |
| E6 | `JaxExecutableCandidate` | public | declared evidence = the aggregation of its steps' | the `aggregated : evidence = …` proof field | `validateAndConstructExecutable`'s `decide`, and the fourth `JaxExecutableWellFormed` conjunct | `enforced-by-type` | loud typed error | none | — |
| E7 | `JaxExecutableCandidate` | public | the source's own bindings describe its own raw plan | — | `preparedBindingsTied` → the same `checkPreparedBindings` | `re-checked` | loud typed error | adjacent | — |
| **E8** | `JaxExecutableCandidate` | public | which NAME belongs to which slot in the source's `PlanBindings` | producer discipline only (documented as deliberately not re-derivable — `raw` carries no names; see `Executable.lean`'s `JaxExecutableWellFormed` note and `experiments/jax_bridge/README.md`) | none — `preparedBindingsTied` inherits `checkPreparedBindings`' blind spot (S1: it returns `true` on a name-swapped plan) | `assumed-unchecked` | silently-wrong-answer | adjacent | **S1** |
| E9 | `JaxKernelCandidate` | public | tables/operands are the ones the checked factor maps mean | — | `validateAffineTable`/`validateEinsum` recompute from the checked factors | `re-checked` | loud typed error | none | — |
| **E10** | `JaxExecutableCandidate` | public | the located rejection reason and step index survive to the caller | `checkJaxAssignSupport` takes and carries a real `nodeIndex` | none — `validateAndConstructKernel` hardcodes `nodeIndex 0`, `jaxSupportOk` discards the located cause entirely, and `validateAndConstructExecutable` collapses every per-step failure into bare `invalidCandidate` | `assumed-unchecked` | silent no-op | adjacent | S4 |

### 3.6 `Signature.lean`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| F1 | `InputSignature` | public | every signature dtype is admitted by the plan layer | `ofDenseInputs` (always `f64`), `ofDenseInputsForDecls` (`dtypeOfDecl`) | `prepareEvalPlan` Step B → `InputSignatureError.dtypeNotAdmitted` | `re-checked` | loud typed error | none | — |
| F2 | `InputSignature` | public | signature dtype = the declaration's dtype | `ofDenseInputsForDecls` via the shared `dtypeOfDecl`; `ofDenseInputs` does NOT | `prepareEvalPlan` Step B → `InputSignatureError.dtypeMismatch` (S6) | `re-checked` | loud typed error | none | — |
| F3 | `List Decl` | public | the declaration list is itself well-formed | — | `ofDenseInputsForDecls` re-runs the shared `buildDeclEnv` → `CompileError.duplicateTensorDecl`; `ofDenseInputs` consults no declaration and so has nothing to degrade | `re-checked` | loud typed error | none | — |
| F4 | `InputSignature` | public | signature shapes match the tensors later bound at run time | producer discipline when the caller uses either `ofDense*` constructor on the same map | `packChecked`/`runDensePlan` shape+storage guards | `re-checked` | loud typed error | direct | — |

### 3.7 Post-consolidation schedule authority (single bounded row)

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| G1 | `ScheduledProgram` | public | neither execution entry consults a cached `sched` field after validation | `validateScheduled` projects `declEnv`/`explicitSizes`/`extNames` onto `CheckedScheduledProgram` | both entries bind only those projections; the only raw reads are `sched.decls`/`sched.stmts`, which are authoritative rather than cached, and `Eval.lean`'s `evalPlain sched.decls` provably agrees with `checked.declEnv` because `buildDeclEnv` already rejected the one disagreement (`duplicateTensorDecl`) | `re-checked` | loud typed error | adjacent | — |

**The known instance named in the brief is confirmed present and benign.** `Eval/Eval.lean` does pass
`sched.decls` into `evalPlain`/`evalScan` rather than `checked.declEnv`, but `sched` there is
`checked.program` and `declEnv` is a total function of `decls` that `validateScheduled` already
computed; the historical disagreement (`combineFor`'s first-match scan vs the env's last-wins
lookup) is exactly what `duplicateTensorDecl` closes. This is a style/authority inconsistency, not a
defect: it costs nothing today and is worth one line of cleanup if `DeclEnv` ever gains a field
`decls` cannot re-derive.

## 4. Findings

### 4.1 Reconciliation with the brief's mechanical rule

The rule: a finding is a row where Verdict = `assumed-unchecked` AND Failure mode ≠
`loud typed error`. **Amendment:** the rule presupposes an invariant that is assumed-but-unchecked —
it has no subject to apply to on a row whose Invariant column records no invariant at all. Rows
carrying `n/a (no invariant)` (A7, C6; see §3's preamble) therefore fall outside the rule entirely,
regardless of whatever value happens to sit in their Failure-mode column — this is a clause on the
rule's own domain, not an extra verdict value or an ad hoc third exception. Applied to the remaining
rows:

| Rows with Verdict `assumed-unchecked` | Failure mode | Finding under the rule? | Number |
|---|---|---|---|
| A6 | silently-wrong-answer | yes | BND-01 |
| B4 | silently-wrong-answer | yes | BND-02 |
| D4 | silently-wrong-answer | yes | BND-01 **and** BND-02 (D4 is the `Prepared.lean` face of both name axes) |
| E8 | silently-wrong-answer | yes | BND-01 (its `Executable.lean` face) |
| D5 | silent no-op | yes | BND-04 |
| E10 | silent no-op | yes | BND-05 |
| A7 | *n/a (no invariant)* | **no** — outside the rule's domain (amendment above); also §3 preamble | — |
| C6 | *n/a (no invariant)* | **no** — outside the rule's domain (amendment above); also §3 preamble | — |

**8 `assumed-unchecked` rows; 6 of them are findings under the rule; those 6 map to 4 distinct
defects (BND-01, BND-02, BND-04, BND-05)**, because one defect spans several consumers of the same
type.

**BND-03 is deliberately outside the rule and is labelled so.** It sits on row **A8**, whose verdict
is `re-checked` / `loud typed error` — not a finding by the mechanical rule. It is recorded anyway,
under a BND number for continuity with the review thread, because it is a documentation defect that
actively misdirects an implementer at this exact seam. A controller counting `assumed-unchecked`
rows should expect **4** rule-derived findings and see BND-03 listed as a fifth, explicitly
out-of-rule entry.

### 4.2 BND-01 — a `requiredInputs` name↔slot pairing is never re-established, and swapping it silently feeds the wrong tensor to the wrong slot

- **Rows:** A6, D4, E8. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.packChecked`; propagates to `Executable.preparedBindingsTied`.
- **What is unchecked:** `checkBindings` establishes exactly two properties of a `RequiredBindings` —
  the binding slots are a `List.Perm` of `inputSlots`, and the binding names are `Nodup`. Swapping
  the *pairing* (`A→0, B→1` becomes `B→0, A→1`) preserves both. `checkPreparedBindings` adds only the
  tie to `raw.inputSlots`, which the swapped multiset also satisfies. Nothing anywhere compares a
  name against the slot the schedule actually allocated for it.
- **This is a documented deliberate decision, not an oversight.** `checkPreparedBindings`' own doc
  comment states it ("Names remain deliberately unauthenticated: positional raw IR can prove slots
  and required-name uniqueness, not origins"), `LeanNCD/Eval/AGENTS.md` carries it as a contract
  ("Raw plans prove slots but cannot authenticate names"), and `experiments/jax_bridge/README.md`
  repeats it. The row is nevertheless classified by observed behavior, per the brief's Rule-12
  instruction — "deliberate" is not one of the verdict values, and the consequence below is real
  regardless of intent.
- **Construction and observed output** (`S1`), on `W[i] := A[i] · B[j]` with `A = [10, 100]`,
  `B = [1, 2]`:

  ```
  S1 producer bindings   : #[{ name := "A", slot := 0 }, { name := "B", slot := 1 }]
  S1 raw.inputSlots      : #[0, 1]
  S1 checkBindings ACCEPTED the name swap
  S1 checkPreparedBindings on swapped plan: true
  S1 preparedBindingsTied on swapped plan: true
  S1 runPreparedDense .ok  W = shape=[2] data=#[110.000000, 220.000000]  (correct is shape=[2] data=#[30.000000, 300.000000])
  S1 baseline (unswapped)  W = shape=[2] data=#[30.000000, 300.000000]
  ```

  `runPreparedDense` returns `.ok`. No warning, no diagnostic. `110/220` is `B · ΣA`; the correct
  answer is `A · ΣB = 30/300`.
- **Reachability, not hypothetical:** `PlanBindings` and `PreparedPlan` both have public
  constructors, `checkBindings` is the public builder, and `AdapterTest.lean` already builds these
  values by struct update. The swap above uses only public API.
- **Test coverage:** none. `AdapterTest.lean` Check 5 reverses the `requiredInputs` *array* while
  preserving each binding's own name↔slot pair, and asserts the correct result; that fixture is
  specifically about array-position-vs-`.slot` resolution. The pairing itself is untested.
- **Why it matters before Scatter:** Scatter + affine LHS writes adds destination-side geometry that
  will need its own binding-sidecar entries. Any new sidecar field added beside `requiredInputs`
  inherits this same "checked-shape, unchecked-pairing" posture unless the pairing question is
  settled first.

### 4.3 BND-02 — a `materializedNames` binding's NAME is never re-established, so an output can be published under an input's name

- **Rows:** B4, D4. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.unpackChecked`; the same blind spot in `checkPreparedBindings`.
- **What is unchecked:** `checkPreparedBindings` compares `materializedNames.map (·.slot)` against
  `rawPublicationSlots raw` for exact equality — a genuinely strong slot-sequence check — and
  `rawMaterializedWith` bounds every slot. The `name` field is compared against nothing.
- **This axis is not merely undefended; acceptance is PINNED BY A LIVE TEST.**
  `test/Eval/Plan/CompileTest.lean` carries the comment "Exact publication is structural slot
  identity, not name authentication. … changing only names is valid", followed by a `#guard`
  asserting `checkPreparedBindings` returns `.ok` on a plan whose every `materializedNames` entry
  has been renamed to `"renamed"`. So unlike BND-01, this is not an untested gap — it is a tested,
  intended one, and any fix necessarily turns that green `#guard` red.
- **Construction and observed output** (`S3`), same fixture, renaming the single materialized
  binding from `W` to `A` (an input's name) while keeping its slot:

  ```
  S3 producer materializedNames: #[{ name := "W", slot := 2 }]
  S3 checkPreparedBindings on renamed: true
  S3 .ok  A = shape=[2] data=#[30.000000, 300.000000] (input A was shape=[2] #[10.0, 100.0])
  S3 .ok  W = <absent>
  ```

  `runPreparedDense` returns `.ok`, the caller's own input `A` is overwritten by the plan's output,
  and the declared output name `W` is simply absent from the returned environment. A caller that
  reads `env["W"]?` gets `none`; a caller that reads `env["A"]?` gets a value that looks like a
  legitimate tensor.
- **Note on scope:** this is not the out-of-range-slot defect the round-4 review already fixed. Slots
  are fully checked now (`slotOutOfRange`, `publicationSlots`, `storeArityMismatch` — all confirmed
  live in `AdapterTest`). It is the orthogonal *name* axis, which that fix did not touch.
- **Retire list — required if BND-01/BND-02 are ever fixed.** Landing a name-authenticity check for
  either axis turns currently-green documentation and a currently-green test red, and both must be
  retired in the same commit as the fix, not left for a later agent to discover. Cited here, not
  edited, per this audit's constraints:
  1. `test/Eval/Plan/CompileTest.lean` — the `#guard` asserting `checkPreparedBindings` accepts
     `materializedNames.map fun b => { b with name := "renamed" }`, and its comment above it ("Exact
     publication is structural slot identity, not name authentication … changing only names is
     valid"). The build goes red the moment a name check is added if this is not retired in the same
     commit.
  2. `Prepared.lean` — `checkPreparedBindings`'s doc sentence "Names remain deliberately
     unauthenticated: positional raw IR can prove slots and required-name uniqueness, not origins."
  3. `LeanNCD/Eval/AGENTS.md` — the `Prepared.lean` row's contract line "Raw plans prove slots but
     cannot authenticate names."
  4. `experiments/jax_bridge/README.md` — "raw IR cannot authenticate the user-visible names
     themselves."
  5. Re-grep for further siblings of (1) before assuming this list is complete — see §5 item 5.

### 4.4 BND-03 — four doc comments make a stale producer-discipline claim, and two misname the shared resolver (documentation defect, **outside the mechanical rule**)

- **Row:** A8 (`re-checked` / `loud typed error`). **Severity S4** (diagnostic-quality).
  **Scatter: direct.** Recorded despite not meeting the finding rule; see §4.1.
- **The stale claim.** Four doc comments state that alignment of `requiredInputs.inputSlots` against
  the enclosing `PreparedPlan.plan.raw.inputSlots` is producer discipline that the type does not
  enforce, and describe `packChecked`'s `| none => throw (.missingEnvBinding …)` arm as the loud
  fallback that catches a mismatch:
  1. `Adapter.lean`, `packChecked`'s doc comment;
  2. `Adapter.lean`, the inline comment inside `packChecked`'s slot loop;
  3. `Prepared.lean`, `RequiredBindings`' doc comment ("IMPORTANT SCOPE NOTE");
  4. `Error.lean`, `InputBindingError`'s doc comment ("If that coupling were ever broken by a
     hand-built `PreparedPlan`, `pack` still fails loud — a `.missingEnvBinding` naming the unmatched
     slot").
- **Why it is stale.** `checkPreparedBindings` re-runs `checkBindings` **against `raw.inputSlots`**,
  discarding `RequiredBindings`' own stored `inputSlots` field, and every path into `packChecked`
  goes through it. `S2` attempts exactly the construction those comments describe — a two-slot plan
  carrying a one-input plan's validly-checked `RequiredBindings` — and observes:

  ```
  S2 pack rejected with: LeanNCD.Eval.Plan.InputBindingError.invalidPreparedBindings
    (LeanNCD.Eval.Plan.PreparedBindingsError.requiredInputs
      (LeanNCD.Eval.Plan.BindingsError.notAPermutation #[0, 1] #[0]))
  ```

  The `missingEnvBinding` arm is dead code for this cause, and `checkBindings` is the identifier that
  blocks it.
- **Two further sites misname the shared resolver.** `Adapter.lean`'s `unpackChecked` doc and
  `Error.lean`'s `PlanRunCause.materialization` doc both say resolution goes "through the shared
  `PlanBindings.materializedWith`". No such function exists; it is
  `CheckedPreparedBindings.materializedWith`, and the difference is exactly the point of the round-4
  fix — resolution is reachable only *after* validation, not off a bare `PlanBindings`.
- **Corrected rationale for recording this at finding weight** (the first version of this fragment
  argued, wrongly, that the comments "say nothing about the name pairing"; they do — see below).
  `checkPreparedBindings`' own doc comment, ~100 lines further down the same file, states the name
  gap explicitly. The defect is not silence about the name axis but **misdirection about the slot
  axis**: an implementer reading `packChecked` or `InputBindingError` is told the slot alignment is
  the fragile, producer-discipline-only property and that `missingEnvBinding` is its safety net.
  Both halves are false, and the effort that claim invites — hardening a coupling that is already
  re-checked — is effort not spent on the axis that genuinely is unchecked. Four stale sites plus
  two misnamed ones, all in the seam Scatter will extend, is more than a stray comment.

### 4.5 BND-04 — `PreparedPlan.warnings` is unvalidated, so a real diagnostic can be dropped and a false one invented

- **Row:** D5. **Severity S4** (diagnostic-quality). **Scatter: none.**
- **What is unchecked:** `PreparedPlan.warnings : List EvalWarning` is a public field with no
  validator. `runPreparedDense` faithfully propagates whatever it finds through every outcome path
  — which is the documented, correct behavior for a producer-built plan, and exactly the wrong
  behavior for a hand-built one.
- **Construction and observed output** (`S10`), on `Y[i, j] := X[2 * i + j]` with a 6-element `X`
  (a genuine out-of-range read, so the producer records one real `paddedAccess` warning):

  ```
  S10 producer warnings count: 1 [padded-access warning: X[…] max-index 8 ≥ dim 6; out-of-range reads will be zero-padded]
  S10 checkPreparedBindings on silenced plan: true
  S10 silenced run .ok, warnings reported = 0 (a real paddedAccess warning was dropped, Y = shape=[4, 3] data=#[1.0, 2.0, 3.0, 3.0, 4.0, 5.0, 5.0, 6.0, 0.0, 0.0, 0.0, 0.0])
  S10 clean plan producer warnings: 0
  S10 fabricated run .ok, warnings reported = 1 [padded-access warning: X[…] max-index 8 ≥ dim 6; …]
  ```

  Both directions are silent. In the first, `Y`'s trailing zeros are genuinely zero-padded reads and
  the warning that would have explained them is gone. In the second, a plan with no padded read at
  all reports a padded-access warning about a read it does not contain.
- **Judgement:** real, reachable, and silent — hence a finding under the rule — but low severity.
  Warnings are outcome data, not correctness (`Eval/AGENTS.md`, Wave E 4i), and there is no obvious
  check to add short of making `warnings` a projection of the checked artifact rather than a field.
  Recorded so a fix wave can decide deliberately rather than discover it.

### 4.6 BND-05 — the plan-level JAX executable path discards `checkJaxAssignSupport`'s located cause

- **Row:** E10. **Severity S4** (diagnostic-quality). **Scatter: adjacent.**
- **What is unchecked:** `checkJaxAssignSupport` is carefully located — it takes a `nodeIndex` and
  every `JaxSupportError` constructor carries it, and it is correctly threaded at every real caller:
  `EvalPlanCodegen.requireJaxSupport` passes the real outer step index at its plan-level call site
  (`renderAffineNode`, and its `einsum`-mode sibling), and an explicit index at a standalone call.
  The locator loss is one layer up, in the plan-level validators: `jaxSupportOk` (the `Bool` view
  those validators use) hardcodes `checkJaxAssignSupport sigs 0` and discards the located cause down
  to a `Bool`; `validateAndConstructKernel` likewise hardcodes `checkJaxAssignSupport sigs 0` for its
  own single-candidate check — the correct convention there, see below, but it means nothing upstream
  of it ever receives a per-step index either; and `validateAndConstructExecutable` collapses every
  per-step tie or well-formedness failure — including `stepTiedToPreparedStep`'s own per-step
  `mapIdx` check, which does know which index failed — into a bare `invalidCandidate`, with no index
  and no cause.
- **`0` at a standalone entry is a documented convention, not a bug.** `requireJaxSupport`'s doc
  comment states it directly: "Located at `nodeIndex` — the real outer step index at a plan-level
  caller, `0` at a standalone one." `test/Eval/Plan/ExecutableTest.lean` pins exactly this: its
  `step1BoolAssign` fixture is commented as step **1** of the two-step `step1BoolRaw` plan, but the
  `#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))` that checks it validates it in
  isolation, through the standalone `affineOutcome`/`jaxOutcome`/`validateAndConstructKernel` path —
  and asserting index `0` there is intended and green. An earlier version of this finding read that
  `0` (from `validateAndConstructKernel`'s own hardcoded call) as evidence the locator is "wrong at
  every public entry"; it is not — a standalone entry has no outer step to report, `0` is its
  documented sentinel, and `checkJaxAssignSupport` itself is reached correctly-located by
  `requireJaxSupport` at the one production entry that is NOT standalone. A future reader should not
  re-derive this contrast as a defect.
- **Construction and observed output** (`S8`): a validated JAX kernel, built and validated at step 0
  of an assign/pointwise plan, reused at step 1 (a `.pointwise` step) is rejected as
  `JaxExecutableValidationError.invalidCandidate` — no step index, no underlying cause.
- **Judgement:** diagnostic-quality only — nothing incorrect executes, since every one of these paths
  correctly *rejects*. But `validateAndConstructExecutable`'s collapse throws away information
  `stepTiedToPreparedStep`/`JaxExecutableWellFormed` already compute, and it is the layer a Scatter
  lowering would extend with new rejection constructors.

### 4.7 Refuted candidate — input dtype at the runtime input boundaries

The brief's unconfirmed candidate was that a `predicate`-declared input bound to a tensor of `0.5`s
would pass `pack`, be fed to the Boolean `(min, max)` algebra, and give a silently wrong answer.
Investigated first, by construction, and refuted on three independent counts:

1. **Both backends agree.** `S4` runs `predicate P(i); P[i] := X[i] · Y[j]` (a Boolean-algebra
   destination, `admittedAlgebraBool` selected) over `X = [0.5, 0.25]`, `Y = [0.75, 0.1]`:
   `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]` — byte-identical. There is no
   checked/reference divergence to be silent about; literal Float `min`/`max` on non-binary data is
   the *specified* behavior (`Check.lean`'s `admittedAlgebraBool` doc comment, `Eval/AGENTS.md`
   Contract (c): "runtime values are NOT restricted to `0.0`/`1.0` … adding a truth check would
   create a checked/reference divergence").
2. **An input slot's dtype tag is behaviorally inert in the Dense path.** `S5` prepares the same
   program twice — once with the input declared `predicate` (slot signature `bool`), once
   undeclared (`f64`) — with identical Float data, and gets identical results
   (`Q = #[0.25, 9.0]` both times). So there is no invariant for `packChecked` or `runDensePlan` to
   re-establish here.
3. **The dtype invariant that *does* exist is re-checked, loudly, upstream.** The real obligation is
   "the external signature's dtype equals what the declaration commits the name to", and
   `prepareEvalPlan` Step B enforces it: `S6` shows the declaration-blind producer
   `InputSignature.ofDenseInputs` on a program declaring a `predicate` input failing with
   `InputSignatureError.dtypeMismatch "Z" bool f64`. `DenseTensor` has no dtype field to check
   against at run time, and by the time execution starts the signature has already been reconciled
   with the declaration.

Recorded as rows A7 and C6, verdict `assumed-unchecked` with failure mode `n/a (no invariant)` — the
stated departure from the closed vocabulary explained in §3's preamble and accounted for in §4.1.
Not a finding.

## 5. Open / unprobed

Named rather than omitted. (Two items from the first version of this fragment — `PreparedPlan.warnings`
and the JAX locator loss — have been promoted to BND-04 and BND-05 with construction evidence and are
no longer listed here.)

1. **`experiments/jax_bridge`'s own `PreparedPlan` consumers were not audited.** `EvalPlanCodegen.lean`
   (`generateForward`, `renderInputConstants`, `renderAffinePlanNamed`, `generateNamed`,
   `lowerCheckPlanToCandidate`), `EvalPlanAffineSmoke.lean`, and `EvalPlanAffineCorpus.lean` all take
   a `PreparedPlan` directly. Out of scope by the brief. BND-01/BND-02 reach them by construction
   (they consume the same name sidecar, and `experiments/jax_bridge/README.md` states the name gap as
   a known property), but which of them re-establish anything was not checked.
2. **Three `experiments/jax_bridge` entry points use the declaration-blind `InputSignature.ofDenseInputs`**
   (`EvalPlanAffineSmoke.lean`, `EvalPlanAffineCorpus.lean`, `EvalPlanSmoke.lean`). A corpus or
   fixture program that declares a `predicate` *input* would abort those runs at Step B with
   `dtypeMismatch` rather than mis-execute (S6), so this is loud — but it is a latent run-script
   breakage, not a silent one, and it was not exercised against the live corpus here.
3. **Two independent copies of the same shape/storage rule.** `packChecked` and `runDensePlan` each
   code `t.shape == sig.shape.toList` and `t.data.size == ∏ shape` separately;
   `Adapter.lean`'s own comment records why (the shared helper is private and typed to
   `PositionalInputError`). They agree today (S7 vs A4/A5). Not a finding — both check — but it is a
   two-copy rule at exactly the boundary Scatter will extend with destination-side geometry.
4. **`CheckedScanPlan`, `CheckedPlanBlock`, `CheckedPointwisePlan`, `CheckedAxiswisePlan`** appear in
   the type census as `private mk ::`-enforced and were not otherwise probed — `Scan.lean` is Task
   B's territory and the block/nonlinearity checkers were outside the five named families.
5. **Whether the `CompileTest.lean` rename `#guard` has siblings elsewhere in the suite** was not
   swept exhaustively; the one cited in §2 was found by grepping for `renamed`/`name authentication`
   and is the only hit, but a fix wave should re-grep rather than trust that.

## 6. Count reconciliation

**Row total: 41** (8 + 6 + 7 + 5 + 10 + 4 + 1 across §§3.1–3.7).

**`assumed-unchecked` rows: 8** — A6, A7, B4, C6, D4, D5, E8, E10.

**Findings under the brief's mechanical rule: 6 rows → 4 distinct defects.** A6 / D4 / E8 are one
defect seen from three consumers (BND-01); B4 / D4 are the materialized-name axis (BND-02, and D4
spans both name axes); D5 is BND-04; E10 is BND-05. A7 and C6 are `assumed-unchecked` but carry the
stated `n/a (no invariant)` failure mode and are not findings — §3's preamble and §4.1 explain why.
**BND-03 is a fifth listed entry that is explicitly outside the rule** (row A8 is
`re-checked`/`loud typed error`).

The brief predicted ~14–18 boundaries yielding ~10–12 `assumed-unchecked` cells needing 4–6
constructions. Actual: 41 rows, 8 `assumed-unchecked`, 11 construction fixtures. The
`assumed-unchecked` count is *lower* than predicted, which is itself a result: the 2026-09-05
consolidation (`0160f59`, `06604f2`) genuinely closed most of this surface. What it did not close is
a single axis — **names** — and that axis is unchecked at every one of the three places it appears,
by a decision recorded in four documents and pinned green by one test.

---

# Axis B — write-geometry predicate surface

Findings-only audit of the checked-plan write-geometry predicates, taken at `267976e` with a green
build (`lake build`, **8660 jobs**) [built]. No production code was changed.

Evidence tags: `[built]` = whole-project build, `[read]` = identifier inspected, `[snippet]` = a
construction spike with observed output. Two spike files, each committed with its captured output,
live in `leanncd/spikes/`, mirroring Task A's layout:

- `AxisBWriteGeometryProbe.lean` (+ `.output.txt`) — probes **S1–S13**
- `AxisBBaseBoundaryProbe.lean` (+ `.output.txt`) — probes **S14–S16** (S16 added in fix round 1)

Both are tracked in git via `leanncd/.gitignore` exceptions (alongside `BrNF.lean`). To re-run, run
`lake env lean spikes/<file>.lean` from `leanncd/`. Neither is in `lakefile.toml` or any default
build target. Note for whoever re-runs them: they import
`LeanNCD.Eval.Plan.Scan` rather than the `LeanNCD` umbrella *deliberately* — `LeanNCD/DSL/Syntax.lean`
declares `"bias"` as a syntax token, which makes `{ coeffs := …, bias := … }` a parse error in any
file that imports the umbrella [snippet].

---

## B1.1 — The inherited "F4 seven-predicate table" does not exist

**Finding B1-F1 (process; stale inherited obligation).** There is no required/forbidden/ignored table
over the write-geometry predicates anywhere in the repo.

Verification trail, re-run and restated in fix round 2 (the previous two narratives did not
reproduce). **Pass 1** — the exact commands, both run from the repository root, differing only in
case sensitivity:

```text
grep -rl  --include='*.md' --include='*.lean' forbidden papers/ docs/ leanncd/docs/ leanncd/experiments/ leanncd/LeanNCD/   → 19 files
grep -ril --include='*.md' --include='*.lean' forbidden papers/ docs/ leanncd/docs/ leanncd/experiments/ leanncd/LeanNCD/   → 20 files
```

**Case sensitivity is the real instability in this trail**, and it is the reason two earlier drafts
failed to reproduce: exactly one file carries the word capitalised as "Forbidden" and is therefore
invisible to the case-sensitive form — `leanncd/docs/superpowers/plans/2026-08-20-thread-4-nonlinearity.md`,
the last row of the table below. (A reviewer running these same two commands observed 18 and 19
rather than 19 and 20; the one-file difference in the *baseline* is a file that does not survive
pass 2, so it does not move the intersection. The baseline count is the environment-sensitive
number; the intersection is not.)

**Pass 2** — intersecting each pass-1 result with files that also mention any of
`classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`,
`pinnedLiteralsInRange`, `writesCollide` gives **6** files from the case-sensitive list and **7**
from the case-insensitive one — the same 6 plus the capitalised file. All 7 were opened and read
[snippet]:

| File | What it is |
|---|---|
| `papers/boolean_predicate_output_evalplan.md` | **presupposes** the artifact (Task 4.4, quoted below) |
| `papers/predicate_boolean_backend_parity.md` | **presupposes** the artifact (§9.4, quoted below) |
| `papers/wave_f_scanplan_proposal.md` | prose only; its sole `forbidden` hit is a cross-reference to "its §4.8 forbidden list" |
| `leanncd/docs/superpowers/plans/2026-08-26-nonlinearity-t1-logical-schedule.md` | prose only ("same shape as `baseWriteRowsOk` in Wave F F4") |
| `docs/superpowers/plans/2026-09-06-pre-scatter-backend-audit.md` | this audit's own plan |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean` | source, not a document |
| `leanncd/docs/superpowers/plans/2026-08-20-thread-4-nonlinearity.md` | **sibling case × class table, different predicate family** — reachable only case-insensitively. Does **not** falsify B1-F1: its axes are *case × {Pointwise, Axiswise} × class* over `checkPointwise`/`checkAxiswise`, so it has no row for any write-geometry predicate; it merely *cites* `baseWriteRowsOk`/`stepWriteRowsOk` as the defect family it argues it is not an instance of. See below |

So: no required/forbidden/ignored table over the **write-geometry** predicates in any of them. The
two **declining** documents quoted below appear in neither intersection, because neither contains the
word `forbidden` in any case — they were found by a separate grep for
`case-by-class|sibling audit|not required` [snippet].

What actually exists:

- A **completed** seven-row table in `papers/boolean_predicate_output_evalplan.md` whose axes are
  *assignment feature × {Dense checked plan, JAX render, JAX candidate evidence}* — mirrored in
  `leanncd/experiments/jax_bridge/README.md`. Not geometry predicates [read].
- An **instruction** in that same document (its Task 4.4 paragraph) reading: *"Task 4.4 must append a
  row to the existing write case-by-class audit. Re-read unchanged siblings `baseWriteRowsOk`,
  `stepWriteRowsOk`, `freeExtentsAgree`, `pinnedLiteralsInRange`, `writesCollide`, and their call
  sites. Record every cell as required, forbidden, or intentionally ignored."* The artifact it says to
  append to was never produced [read].
- **A second document presupposing the same artifact**, `papers/predicate_boolean_backend_parity.md`
  §9.4: *"Extend the existing write-predicate case table with block-output dtype versus state dtype.
  … If implementation touches `classifyWriteRow`, `baseWriteRowsOk`, `stepWriteRowsOk`, free extents,
  pins, or causality rows, stop and require the full write-geometry sibling audit rather than
  reviewing only the diff."* Same missing artifact, named differently [read].
- Two later documents that declined the obligation outright: `papers/max_min_aggregation.md` — *"no
  case × class sibling audit is required"* — and `papers/unary_factor_functions.md`, same wording
  [read].

So the "extend the existing table" instruction has been carried forward by at least two documents
against an artifact that does not exist, and twice explicitly declined.

**The closest existing precedent for the table in §B1.2, and why it is not that table.**
`2026-08-20-thread-4-nonlinearity.md` §4 is titled *"Case × class table —
`checkPointwise`/`checkAxiswise` geometry obligations"*, uses the Required/Forbidden vocabulary, and
introduces itself thus:

> Required per the slice-plan skill: a new geometry-checking predicate family gets this table as an
> explicit deliverable even though it is not an *instance* of the write-geometry defect family found
> four times in F3/F4 (free-extent, pinned-literal, write-map-rank, `stepWriteRowsOk`) — verified
> below, not assumed, since every `(c)` cell is a candidate instance *N+1* regardless of ancestry.

Its row 15 then discharges exactly that question — the nonlinearity family is not a fifth instance
because *"there is no second 'target' tensor addressed via an independently-boundable affine map the
way `commitWrite` (`Scan.lean`) has — this is the structural reason this family is not a 5th
instance … not merely an unexamined absence"* [read].

That is the same discipline §B1.2 applies, one predicate family over, and it is worth knowing three
things about it. First, it **confirms** B1-F1 rather than weakening it: it exists precisely because
the write-geometry table it defers to did not, and it never tabulates a write-geometry predicate.
Second, its `(c)`-cells-are-candidates-regardless-of-ancestry rule is the rule §B1.3 follows. Third,
it is the model for the appendability contract in §B1.2 — a case × class table whose classes stayed
stable while its rows grew.

The table in §B1.2 below is therefore built from scratch. It reuses only the JAX table's column
grammar and its closing gate sentence:

> Every forbidden cell needs a located test. No cell may be silently ignored.

---

## B1.2 — The write-geometry predicate table (current row kinds)

### Reading the table

A **row** is one write-map row *kind* sitting at one *dimension class* in one *phase*:

- kind ∈ {`pinned lit`, `free outputPos`, `advancing contextPos`} — the three current
  `WriteRowKind` constructors [read]
- dimension class ∈ {**adv** = the dimension is a member of `StateSlot.advancingDims`, **non-adv** =
  it is not}
- phase ∈ {**base** (`contextWidth = 0`), **step** (`contextWidth = advancingDims.size`)}

A **column** is one of the 14 audited sites. A **cell** answers: *does this site constrain such a
row?*

| Mark | Meaning |
|---|---|
| **a** | **required** — the site imposes a constraint on such a row and rejects the plan when it fails (including demanding the row's presence) |
| **b** | **forbidden** — the site rejects the plan when such a row is present at that dimension class in that phase |
| **c** | **silently ignored** — the site neither constrains nor rejects it; the row passes through unexamined. **Every `c` cell is a candidate gap** and is adjudicated in §B1.3 |
| **—** | the site is not reached in that phase (structural, not a classification) |
| **▷** | the site classifies *read* rows, a disjoint row vocabulary (see §B1.3, group G-READ) |
| **‡** | the mark holds only via an **unenforced call-site precondition** — a `c` cell in disguise; routed to the call-site sweep in §B1.4 |
| **§** | the mark holds for the row **class** but a sub-case inside the cell is unconstrained by this site. Do not read this `a` as stronger than it is — the named finding says which sub-case escapes |

Column keys: **1** `WriteRowKind` · **2** `classifyWriteRow` · **3** `writeRowKinds` ·
**4** `baseWriteRowsOk` · **5** `stepWriteRowsOk` · **6** `freeExtentsAgree` ·
**7** `pinnedLiteralsInRange` · **8** `writesCollide` · **9** `causalAdvancingRow` ·
**10** `stateReadCausal` · **11** `checkWrites` · **12** `checkScanPlan` · **13** `commitWrite` ·
**14** `runDenseScan`.

### The table

| # | row kind @ dim class @ phase | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R1 | `pinned` @ adv @ base | c | c | c | **a**§ | — | c | **a** | **a** | ▷ | ▷ | **a** | **a** | c | c |
| R2 | `pinned` @ non-adv @ base | c | c | c | **c** | — | c | **a** | **a** | ▷ | ▷ | **a** | **a** | c | c |
| R3 | `pinned` @ adv @ step | c | c | c | — | **b** | c | **a** | — | ▷ | ▷ | **b** | **b** | c | c |
| R4 | `pinned` @ non-adv @ step | c | c | c | — | **b** | c | **a** | — | ▷ | ▷ | **b** | **b** | c | c |
| R5 | `free` @ adv @ base | c | c | c | **c** | — | **a** | c | c | ▷ | ▷ | **c** | **c** | c | c |
| R6 | `free` @ non-adv @ base | c | c | c | **a** | — | **a** | c | c | ▷ | ▷ | **a** | **a** | c | c |
| R7 | `free` @ adv @ step | c | c | c | — | **b** | **a** | c | — | ▷ | ▷ | **b** | **b** | c | c |
| R8 | `free` @ non-adv @ step | c | c | c | — | **a** | **a** | c | — | ▷ | ▷ | **a** | **a** | c | c |
| R9 | `advancing` @ adv @ base | c | **b**‡ | **b**‡ | **c**‡ | — | **c**‡ | **c**‡ | c‡ | ▷ | ▷ | **c**‡ | **c**‡ | c | c |
| R10 | `advancing` @ non-adv @ base | c | **b**‡ | **b**‡ | **c**‡ | — | **c**‡ | **c**‡ | c‡ | ▷ | ▷ | **c**‡ | **c**‡ | c | c |
| R11 | `advancing` @ adv @ step | c | c | c | — | **a** | c | c | — | ▷ | ▷ | **a** | **a** | c | c |
| R12 | `advancing` @ non-adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |

### Cell census

168 cells (12 × 14): **24 a**, **16 b**, **86 c**, 18 —, 24 ▷.

**Updated by Task B2.** With the four appended `strided` rows R13–R16 (§B2.2) the table is
**224 cells (16 × 14): 24 a, 22 b, 122 c, 24 —, 32 ▷.** B2's four rows contribute 56 cells on their
own — **0 a, 6 b, 36 c, 6 —, 8 ▷** — and the absence of any `a` among them is itself a finding
(§B2.2, B2-F2): no audited site anywhere requires or demands the presence of a strided row.

**Reported divergence (the brief predicted ~40 adjudicable cells).** 86 `c` cells is a large
overshoot, and it is an artefact of the column list rather than of the code: three of the 14 columns
are *entirely* `c` by construction and account for 36 cells on their own — `WriteRowKind` (a closed
inductive cannot require or forbid anything), `commitWrite` (its own docstring states it "does NOT
call `inBoundsPerDim` before `flatIndex`: it performs no bounds recovery, trusting `checkScanPlan`"
[read]), and `runDenseScan` (validates the signature table and store arity, nothing per-row).
`classifyWriteRow` and `writeRowKinds` contribute 20 more, because both are structurally
dimension-class-blind. Excluding those five non-validating/blind columns leaves **30 `c` cells**
(4 in `baseWriteRowsOk`, 8 in `freeExtentsAgree`, 8 in `pinnedLiteralsInRange`, 4 in `writesCollide`,
3 each in `checkWrites` and `checkScanPlan`) — the same order as the prediction. The 86 collapse into
**17 adjudication groups** (§B1.3), so no group is closed by prose alone.

### How Task B2 appends a fourth row kind

The row axis is `kind × dim-class × phase` and the column axis is fixed. A fourth kind
(`strided`) appends **exactly four rows at the bottom** — `strided @ adv @ base`,
`strided @ non-adv @ base`, `strided @ adv @ step`, `strided @ non-adv @ step` — as R13–R16, with no
change to any column header, to any existing row, or to the legend.

**Two places outside the table itself must also be updated, and one of them sits BEFORE the append
marker**: the §B1.2 cell census (currently 168 cells / 24 a / 16 b / 86 c / 18 — / 24 ▷) and §B1.5's
gate summary, which restates the 16/86 split. Editing §B1.5 in place is expected and is not a
violation of the append boundary; the marker exists so B2's *new prose* lands after B1's, not to
freeze B1's counts.

Three facts B2 will need. **Facts 1 and 3 are measured here; fact 2 is a conditional forecast that
B2 must test, not inherit.**

1. **[measured] `classifyWriteRow` is the single chokepoint.** Every coefficient other than `1`, and
   every bias other than `0`/`1`, is `none` today: `classifyWriteRow 0 #[2] 0`,
   `classifyWriteRow 0 #[1,1] 0`, `classifyWriteRow 2 #[2,0] 1`, `classifyWriteRow 0 #[1] 5` all
   return `none` [snippet, S12]. A `strided` kind must be admitted there or nowhere.
2. **[CONDITIONAL — not measured; no `strided` constructor exists to measure]** *If* B2's strided
   branch of `classifyWriteRow` is **not** gated on `contextWidth` — which nothing in the current
   code forces either way, and which is a design choice B2 owns — then a strided row becomes
   emittable at **base**, unlike `advancing`. In that case: `baseWriteRowsOk`'s clause-2 `filterMap`
   is still the verbatim defect-instance-4 shape (B1-F2), so it would silently DROP the row from the
   positional cover; `freeExtentsAgree` matches only `.free` and `pinnedLiteralsInRange` only
   `.pinned`, so neither would look at it; and `commitWrite`'s `c·x + b` would then be bounded by
   nothing. The smallest shape that would exhibit it: rank-3 state, `advancingDims := #[0]`, dim0
   `.pinned 0`, dim1 strided, dim2 `.free 0`, `outputShapeSize = 1` — which passes clauses 1–3 today
   for any *new* dim1 kind that is `some` (one that is not among the three current `WriteRowKind`
   constructors: an existing kind, e.g. a `.free 1` at dim1, breaks clause 2's positional cover
   instead, since `[0,1] ≠ List.range 1`), as G16's `#[some (.pinned 0), some (.advancing 0), some
   (.free 0)]` construction demonstrates for the *advancing* kind at exactly those parameters
   [snippet, S16].

   **B2's first obligation is therefore to decide and record whether the strided branch is
   `contextWidth`-gated, and to build the construction either way** — if gated, the cell is latent
   like B1-F2 and the gate is a third unenforced precondition; if not gated, it is live, and this is
   the five-times defect recurring for the sixth time. Do not carry this paragraph forward as a
   finding; carry it forward as the test to run.
3. **[measured] `writesCollide`'s catch-all is conservative for a new kind.** `| _, _ => false` means
   a `strided` row can never separate two writes, so two strided base writes to one state would
   always be reported as colliding [snippet, S5]. That over-rejects rather than under-rejects — safe,
   but it makes strided-plus-strided base initialization inexpressible.

---

## B1.3 — Adjudication of every `c` cell

Order used throughout, per the audit's own rule: (1) name the catching site and quote its clause;
(2) if soundness rests on a caller rather than the predicate's text, mark `‡` and route to §B1.4;
(3) build the malformed `RawScanPlan`, run `checkScanPlan`, then `runDenseScan`, and record the
observed value verbatim. **No write-path cell below is closed as "backstopped by `gatherFactor`'s
`inBoundsPerDim`".**

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G1 | 12 | col 1 × R1–R12 | Closed structurally. `WriteRowKind` is a closed inductive `deriving DecidableEq, BEq` [read]; a type cannot require or forbid. Its derived structural equality is what makes `baseWriteRowsOk`'s `rows.getD d none == some (.pinned 0)` and `stepWriteRowsOk`'s `== some (.advancing i)` sound, so a payload-carrying fourth constructor inherits correct equality for free. |
| G2a | 18 | cols 2–3 × R1–R4, R6–R8, R11, R12 | Closed to G3, G6, G7, G8. Both functions are **dimension-class-blind by construction**: `classifyWriteRow`'s signature is `(contextWidth : Nat) (coeffRow : Array Int) (bias : Int)` — it receives no `advancingDims` and no dimension index at all [read]. The entire dim-class axis is therefore `c` at this column pair, which is precisely why every downstream site re-derives it. |
| **G2b** | 2 | cols 2–3 × R5 (`free` @ adv @ base) | **OPEN.** Same dimension-class blindness as G2a, but its only downstream catcher is `baseWriteRowsOk`, whose own cell for this row is G4 — itself open. A group cannot be closed by deferral to an open group, so these two cells are open too, folded into **Finding B1-F4**. |
| G3 | 1 | col 4 × R2 (`pinned` @ non-adv @ base) | Closed by `pinnedLiteralsInRange`: *"`some (.pinned lit) => 0 ≤ lit && lit.toNat < stateShape.getD d 0`"*. Confirmed live: `baseWriteRowsOk #[0] 0 #[some (.pinned 0), some (.pinned 99)] = true` [snippet, S2], and `pinnedLiteralsInRange #[3,3] #[some (.pinned 0), some (.pinned 5)] = false`, `… (.pinned (-1))] = false` [snippet, S4]. Pinning a non-advancing dimension is intended — `ScanTest`'s `pointWrite`/`outOfRangePointWrite` fixtures exercise both directions [read]. |
| **G4** | 1 | col 4 × R5 (`free` @ adv @ base) | **OPEN — Finding B1-F4.** See below. |
| **G5** | 2 | col 4 × R9, R10 (`advancing` @ base) | **`c`‡ — Finding B1-F2, candidate gap 1 CONFIRMED as latent.** See below. |
| G6 | 6 | col 6 × R1–R4, R11, R12 | Closed by kind partition. `freeExtentsAgree`'s `\| _ => true` arm ignores `.pinned` and `.advancing` — `freeExtentsAgree #[3,3] #[9] #[some (.pinned 0), some (.advancing 0)] = true` even at a wildly wrong output extent [snippet, S4]. Pinned rows are caught by `pinnedLiteralsInRange` (G3). Advancing rows at **step** are caught by `stepWriteRowsOk`'s clause 2 (`rows.getD d none == some (.advancing i)` at every advancing dimension) and clause 3 (every other dimension must be `.free`), plus `checkScanPlan`'s `advancingSizeMismatch`, which *"relates `stateShape[advancingDims[i]]` to `historyExtents[i]`"* [read]. **Advancing rows at BASE are NOT covered by that argument and are excluded from this group — see G16.** |
| G7 | 6 | col 7 × R5–R8, R11, R12 | Closed by the mirror-image partition. `pinnedLiteralsInRange #[3,3] #[some (.free 7), some (.advancing 9)] = true` [snippet, S4]. Free rows → `freeExtentsAgree` (G6's converse); advancing rows at **step** → as in G6. Its docstring's justification — *"`.free`/`.advancing` rows are vacuously fine (their range is already bounded by the checked output/context shapes elsewhere)"* — is accurate for the step phase and for `.free` rows generally, but **is false for an advancing row at base**, where there is no context shape at all; those cells are excluded from this group — see G16. |
| G8 | 2 | col 8 × R5, R6 (`free` @ base) | Closed as **documented and pinned intentional**. `writesCollide`'s docstring: *"`.free`/`.advancing` always range over their full domain and can never exclude the other write. This single rule is what makes 'two full free-axis faces never disjoint' (proposal §5.1) a structural consequence rather than an asserted claim"* [read]. Pinned by green `#guard`s in `ScanTest.lean`: `writesCollide faceRows pointRows == false`, `writesCollide faceRows colFaceRows == true` [read]. Confirmed: `writesCollide #[some (.free 0)] #[some (.free 0)] = true` [snippet, S5]. |
| G9 | 2 | col 8 × R9, R10 (`advancing` @ base) | `c`‡, closed as **vacuous today**. `writesCollide` is called only inside `checkWrites`' `if isBase then` branch and inside `Compile.lean`'s base-write loop [read], and no base row can be `.advancing` (G5). So the catch-all's treatment of advancing rows is unreachable in production — see §B1.2's B2 note 3 for why that stops being true with a fourth kind. |
| G10 | 1 | col 11 × R5 | Escalation of G4 — same finding, surviving to the orchestrator. |
| G11 | 2 | col 11 × R9, R10 | Escalation of G5. |
| G12 | 1 | col 12 × R5 | Escalation of G4, surviving to the **top-level** checked entry. `checkScanPlan` adds `advancingDimOutOfRange`, `duplicateAdvancingDim`, `advancingDimCountMismatch`, `advancingSizeMismatch` and the policy gates [read] — **none of which changes any cell in the table**. That is itself the point: the three base `c` cells reach the public entry point unchanged. |
| G13 | 2 | col 12 × R9, R10 | Escalation of G5, same remark. |
| G14 | 12 | col 13 × R1–R12 | Closed by design, with one docstring gap (Finding B1-F7). `commitWrite`'s docstring is a row-by-row soundness argument with **one bullet per current constructor** — `.free p`, `.advancing i`, `.pinned lit`, three bullets for three constructors, so the argument is complete over the constructor surface [read]. Its stated premise (`out.shape` runtime vs. `block.tensorSigs[…].shape` declared, resting on `checkNonlinIO`'s shape equality) is already flagged there as load-bearing. |
| G15 | 12 | col 14 × R1–R12 | Closed by evidence-carrying construction. `CheckedScanPlan` has `private mk ::`, so the only way to obtain one is `checkScanPlan`; `runDenseScan` then reads state shapes from `c.sigs` and rejects a differing caller table (`signatureContextMismatch`) and a differing store length (`storeArityMismatch`) before allocating [read]. No per-row obligation belongs here. |
| **G16** | 4 | cols 6–7 × R9, R10 (`advancing` @ base, both value predicates) | **OPEN — `c`‡ latent, folded into Finding B1-F2.** These four cells were initially misclosed inside G6/G7 by citing a catcher that cannot fire in this phase, which is exactly the failure this audit exists to prevent. `stepWriteRowsOk` is marked **—** at base in the table above, so its clauses 2 and 3 catch nothing here; `advancingSizeMismatch` relates `stateShape[advancingDims[i]]` to `historyExtents[i]` and says nothing about an advancing row's presence or placement at base; and `pinnedLiteralsInRange`'s docstring appeal to *"the checked output/context shapes"* has no referent, because `checkScanPlan` forces `raw.baseBlock.contextShape == #[]` — verified: `S16 (non-empty base block contextShape): checkScanPlan REJECTED: … baseBlockContextNotEmpty #[2]` [snippet, S16]. Both predicates pass such a row at **any** extents: on `#[some (.pinned 0), some (.advancing 0), some (.free 0)]`, `(freeExtentsAgree #[1,3,3] #[3], pinnedLiteralsInRange #[1,3,3], freeExtentsAgree #[1,1,3] #[3], pinnedLiteralsInRange #[1,1,3])` → `(true, true, true, true)` [snippet, S16]. Held up by the same two barriers as G5 — see B1-F2. |

The 17 groups above account for all 86 `c` cells: G1 12, G2a 18, G2b 2, G3 1, G4 1, G5 2, G6 6, G7 6,
G8 2, G9 2, G10 1, G11 2, G12 1, G13 2, G14 12, G15 12, G16 4.

- **9 groups closed, 71 cells**: G1, G2a, G3, G6, G7, G8, G9, G14, G15.
- **8 groups open, 15 cells**, collapsing to two findings:
  - **B1-F4** (`free` at an advancing dim in a base write) — G2b 2, G4 1, G10 1, G12 1 = **5 cells**;
  - **B1-F2** (`advancing` at base) — G5 2, G11 2, G13 2, G16 4 = **10 cells**.

**Updated by Task B2.** B2 appends **14 further groups, G17–G30 (§B2.3)**, covering its 36 new `c`
cells: G17 4, G18 4, G19 4, G20 2, G21 2, G22 2, G23 2, G24 2, G25 2, G26 2, G27 2, G28 2, G29 2,
G30 4. Of those, **7 groups / 20 cells are closed** (G17, G18, G21, G23, G25, G28, G30) and
**7 groups / 16 cells are open** (G19, G20, G22, G24, G26, G27, G29), collapsing to a single new
finding **B2-F1**. Combined totals across both tasks: **31 groups / 122 `c` cells — 16 groups /
91 cells closed, 15 groups / 31 cells open**, collapsing to three findings: **B1-F2** (10 cells),
**B1-F4** (5 cells), **B2-F1** (16 cells).

One further group is listed for completeness but is **not** a `c` group, because its 24 cells are
marked ▷ rather than `c`:

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G-READ | 24 (▷, not `c`) | cols 9–10 × R1–R12 | Not write-row cells. `causalAdvancingRow` and `stateReadCausal` classify a `ReadPlan`'s coefficient rows, a disjoint vocabulary. Their own `c` cell — `stateReadCausal` imposes no obligation on a read's **non-advancing** dimensions, per its docstring *"non-advancing dimensions are ordinary reads and carry no causality obligation"* [read] — **is** a read-path cell and **is** legitimately closed as backstopped by `gatherFactor`'s `inBoundsPerDim`. It is pinned by `ScanTest`'s `nonAdvancingScan` / `stepBlockGjWild` fixture pair, which asserts `checkScanPlan` still accepts a scan whose only irregularity is a non-advancing read [read]. |

### Finding B1-F2 — candidate gap 1: `baseWriteRowsOk`, CONFIRMED as latent, not live

`baseWriteRowsOk` still carries the verbatim defect-instance-4 shape:

```
((rows.toList.filterMap (fun r => match r with | some (.free p) => some p | _ => none))
  == List.range outputShapeSize)
```

It **admits** a hand-built `.advancing` row at both dimension classes:

- `baseWriteRowsOk #[0, 1] 0 #[some (.pinned 0), some (.advancing 0)]` → `true`
- `baseWriteRowsOk #[0]    0 #[some (.pinned 0), some (.advancing 0)]` → `true` [snippet, S2]

and nothing downstream examines such a row: `writesCollide`'s catch-all is `false` (G9), and **both
value predicates pass it at any extents whatsoever** (G16). On
`#[some (.pinned 0), some (.advancing 0), some (.free 0)]` — a rank-3 state, dim0 satisfying clause 3,
dim1 carrying the advancing row, dim2 the free cover — `baseWriteRowsOk` returns `true` at **both**
dimension classes (`baseWriteRowsOk #[0,1] 1 …` and `baseWriteRowsOk #[0] 1 …`, i.e. rows R9 and R10),
and `(freeExtentsAgree #[1,3,3] #[3], pinnedLiteralsInRange #[1,3,3],
freeExtentsAgree #[1,1,3] #[3], pinnedLiteralsInRange #[1,1,3])` → `(true, true, true, true)`
[snippet, S16].

**The consequence at the worker, worked out rather than argued.** At base `commitWrite` is called with
`ctx = []`, so `iter = oc` and `applyAffine` yields `oc[p] + 1` for the advancing row. For the map
those rows come from (`coeffs := #[#[0], #[1], #[1]]`, `bias := #[0, 1, 0]`) over an output of shape
`[3]`, the three coordinates are `([0,1,0], [0,2,1], [0,3,2])`; against a `[1,3,3]` state
`inBoundsPerDim` gives `(true, true, false)`, and `flatIndex` gives the addresses `(3, 7, 11)` on a
9-element store [snippet, S16]. `commitWrite` calls no `inBoundsPerDim`, so that is: two silent writes
into cells belonging to other coordinates, then an out-of-range `Array.set!` — the verbatim F4 failure
signature. **There is no base-phase bound to appeal to**: `checkScanPlan` forces
`raw.baseBlock.contextShape == #[]`, confirmed by `S16 (non-empty base block contextShape):
checkScanPlan REJECTED: … baseBlockContextNotEmpty #[2]` [snippet, S16].

**Two independent barriers hold it up today — not one.** The earlier draft of this fragment said
"solely" of the first; that was wrong, and the correction matters forward.

*Barrier 1 — `checkWrites`' one expression:*

```
let contextWidth := if isBase then 0 else st.advancingDims.size
```

which makes `classifyWriteRow`'s advancing branch — `if c == 1 && p < contextWidth && bias == 1` —
unsatisfiable, since no `p : Nat` is `< 0`. Measured:
`(classifyWriteRow 0 #[1] 1, classifyWriteRow 0 #[1,0] 1, classifyWriteRow 0 #[0,1] 1)` →
`(none, none, none)`, while the same rows at width 2 give
`(some (.advancing 0), some (.advancing 1))` [snippet, S1]. This barrier governs **every** plan,
hand-built or compiled.

*Barrier 2 — `Compile.lean`'s base-write construction loop, for compiled programs only.* That loop
can emit exactly two row shapes: an all-zero coefficient row with the literal as bias (from
`.iterAt _ lit`), or a single `1` at position `freeSeen` with bias `0` (from `.free`/`.freeNorm`)
[read]. The advancing shape is coefficient `1` **together with** bias `1`, which the loop has no arm
that produces — so a compiled base write could not carry an advancing row even if `contextWidth` were
nonzero. This barrier is independent of barrier 1 and makes "latent" more robust for source programs
than for hand-built ones.

**Where barrier 2 disappears.** That same loop's remaining arm is
`| .iterNext _ | .affine _ =>`, which currently throws `CapabilityError.unsupportedLhsSlot` [read].
`.affine` is precisely the slot Task B2's affine LHS writes must lower. **The moment B2 gives that arm
a real lowering, barrier 2 is gone for compiled programs, and barrier 1 — a single `if isBase then 0`
whose contract is stated only in two docstrings — becomes the whole defence.** B1-F6 notes the arm;
this is the connection to B1-F2 that the earlier draft left implicit.

**Construction attempt through the real entry (step 3 of the adjudication order).** A base write whose
dim-0 row is the advancing shape (`coeffs := #[#[1], #[1]]`, `bias := #[1, 0]`) on a `[3,3]` state:
`writeRowKinds 2 0` returns `#[none, some (.free 0)]`, and clause 1 (`rows.all Option.isSome`) fires:

```
S11 (advancing-shaped base row): checkScanPlan REJECTED:
LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
```

[snippet, S11]. So these cells are **`c`‡ — latent, not live**: unreachable today, and unreachable
only because of unenforced call-site values. The precondition is *stated* in `classifyWriteRow`'s and
`writeRowKinds`' docstrings (*"`contextWidth` is `0` for a base write"*) but is enforced by no
signature and no check, and `baseWriteRowsOk`'s own docstring does not mention it at all [read].

**Cell scope: 10 cells, not 6.** This finding covers rows R9 and R10 across columns 4, 6, 7, 11 and
12 — groups G5 (2), G11 (2), G13 (2) and G16 (4). The four G16 cells (both value predicates at base)
were added in fix round 1; the earlier draft misclosed them inside G6/G7 by citing `stepWriteRowsOk`
and `advancingSizeMismatch`, neither of which operates in the base phase. This is the
highest-confidence item in Axis B and it is the exact cell Task B2's new row kind may step into
(§B1.2, note 2).

### Finding B1-F3 — candidate gap 2: coeff-row WIDTH is unchecked but provably irrelevant (REFUTED)

Confirmed by reading: `checkWrites` guards the two **outer** dimensions only —
`writeCoeffRankMismatch` on `w.map.coeffs.size` and `writeBiasRankMismatch` on `w.map.bias.size`, both
against `stateShape.size` — and nothing anywhere compares an individual coefficient row's **length**
against `contextWidth + outputShape.size` [read].

It is nonetheless not a gap, for a three-step reason:

1. `classifyWriteRow` admits a non-pinned row only when it has **exactly one** nonzero coefficient
   **equal to 1**, and that coefficient's *index into the row* is the domain position `p` [read].
2. That position is bounded into the real domain by the geometry predicates themselves:
   `baseWriteRowsOk`'s clause 2 and `stepWriteRowsOk`'s clause 4 both require the free positions to
   equal `List.range outputShapeSize` exactly, and `stepWriteRowsOk`'s clause 2 requires an advancing
   row's position to be its own context index. So a free row's `p ∈ [contextWidth, contextWidth +
   outputShapeSize)` and an advancing row's `p ∈ [0, contextWidth)`.
3. `applyAffine`'s `(row.toList.zip iter)` drops exactly the coefficients at indices `≥ iter.length`,
   and by (1)+(2) every one of those is zero.

Measured at every step:

- `classifyWriteRow 1 #[1,0,0,0] 1` → `some (.advancing 0)`; `classifyWriteRow 1 #[0,0,0,1] 0` →
  `some (.free 2)` — over-wide rows *are* classified [snippet, S7].
- All three geometry predicates reject that out-of-domain free position:
  `(stepWriteRowsOk #[0] 0 #[some (.free 2)], stepWriteRowsOk #[0] 1 #[some (.advancing 0), some
  (.free 2)], baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 2)])` → `(false, false, false)`
  [snippet, S7].
- `applyAffine` truncation is a no-op: `applyAffine ⟨#[#[1,0,0,0]], #[1]⟩ [2]` → `[3]` and
  `applyAffine ⟨#[#[1]], #[1]⟩ [2,5,7]` → `[3]` [snippet, S7].
- Full-plan constructions agree byte-for-byte. A base write with 4-wide rows where the domain is
  1 wide, and a step write with 5-wide rows where the domain is 2 wide, both run and produce output
  identical to the correctly-widthed plan:
  - `S9 (over-wide base coeff rows): checkScanPlan .ok; dp = #[1,2,3, 0,1,1, 0,1,1]`
  - `S10 (over-wide step coeff rows): checkScanPlan .ok; dp = #[1,2,3, 0,1,1, 0,1,1]` [snippet]
- Moving the single `1` **outside** the real domain *is* rejected:
  `S9b (base coeff 1 outside the real domain): checkScanPlan REJECTED: … writeGeometryNotAdmitted
  true 0` [snippet].

**The free-position cover is the width guard.** The refutation carries one caveat that is not new:
step 3 relies on the declared-vs-runtime output-shape agreement that `commitWrite`'s own docstring
already names as load-bearing (`checkNonlinIO`'s shape equality plus every
`PointwiseFn.apply`/`AxiswiseFn.apply` arm being shape-preserving) [read]. A refuted candidate is a
valid audit result; recorded as refuted, with no remediation proposed.

### Finding B1-F4 — a `free` row may sit at an ADVANCING dimension in a base write (OPEN, memory-safe)

`baseWriteRowsOk` clause 2's `filterMap` records a free row's **position** and discards its
**dimension**; clause 3 demands `.pinned 0` at only *some* advancing dimension. With two advancing
dimensions a base write may therefore cover the entire extent of the second one.

Constructed and run end-to-end: state `dp` shape `#[3,3]`, `advancingDims := #[0,1]`,
`historyExtents := #[3,3]`, base write `dp[0, c] := ROWFACE[c]` (`coeffs := #[#[0],#[1]]`,
`bias := #[0,0]`), step write `dp[r+1, c+1] := T[r,c]`:

```
rows = #[some (.pinned 0), some (.free 0)]
baseWriteRowsOk #[0,1] 1 rows = true
freeExtentsAgree #[3,3] #[3] rows = true
S8 (free row at advancing dim, base): checkScanPlan .ok;
  dp = #[1.000000, 2.000000, 3.000000, 0.000000, 1.000000, 1.000000, 0.000000, 1.000000, 1.000000]
```

[snippet, S8]. **Memory-safe** — the free row's extent is bounded by `freeExtentsAgree`, which
returns `false` at any other extent (`freeExtentsAgree #[3,3] #[9] … = false`, [snippet, S4]) — and
the result is exactly what `ScanBoundaryPolicy.zeroThenBaseOverlay` specifies (*"How complete state
histories are initialized before base writes apply"* [read]): row 0 comes from the base overlay,
column 0 was never written and stays zero, the interior comes from the step block.

So this cell is **not closed** as backstopped (it is a write predicate) but **is** closed as
consistent with the declared boundary policy. What it lacks is a pin: `ScanTest.lean` exercises free
base faces only at *non-advancing* dimensions — `baseWriteRowsOk #[0] 1 faceRows` and
`baseWriteRowsOk #[1] 1 colFaceRows` [read] — so no fixture would notice if a future change started
rejecting or mis-executing this shape. Recommendation is a located pin, not a code change.

### Finding B1-F5 — base writes need touch the lower boundary of only ONE advancing dimension (OPEN, memory-safe)

**This is the finding the `§` mark on R1 × col 4 points at.** That cell is `a` for the row *class* —
`baseWriteRowsOk` genuinely demands a `.pinned 0` row at an advancing dimension and rejects its
absence — but the sub-case of *every other* advancing dimension's pinned row is unconstrained by this
site, range-checked only downstream by `pinnedLiteralsInRange`. Read the `a` as "required, but not of
every such row".

`baseWriteRowsOk`'s clause 3 is `advancingDims.any (fun d => rows.getD d none == some (.pinned 0))`.
Its docstring glosses this as *"at least one advancing dimension must be pinned to literal `0`
(touches the lower boundary)"* [read]. With more than one advancing axis that gloss is weaker than it
reads: every *other* advancing dimension's pinned literal need only be **in range**.

```
rows = #[some (.pinned 0), some (.pinned 1)]   -- dp[0,1] on a [3,3] state, advancingDims #[0,1]
baseWriteRowsOk #[0,1] 0 rows = true;  pinnedLiteralsInRange #[3,3] rows = true
S14  (base write off the boundary of advancing dim 1):  .ok; dp = #[0,7,0, 0,1,1, 0,1,1]
S14b (base write pinned to the FAR end of advancing dim 1): .ok; dp = #[0,0,7, 0,1,1, 0,1,1]
S14c (base write pinned OUT of range on advancing dim 1): REJECTED:
      ScanPlanError.writePinnedLiteralOutOfRange true 0 0 #[3, 3]
```

[snippet, S14]. Memory-safe, and the range boundary is exactly where `pinnedLiteralsInRange` puts it.
`Compile.lean`'s Phase 5 carries the **same** single-dimension rule (`baseWriteNotAtBoundary`), so a
source program inherits the same looseness — see B1-F6.

### Finding B1-F7 — `commitWrite`'s docstring is complete over constructors but STEP-scoped for `.advancing`

Treating the docstring as a predicate, per the audit's scope addition 2: it has one bullet per
current `WriteRowKind` constructor, so no row kind is missing an argument [read]. But the
`.advancing` bullet's argument is explicitly step-scoped — *"an `.advancing i` row is `ctx[i] + 1`,
with `ctx` from `mixedRadixUnrank c.stepExtents` and `stepExtents = historyExtents - 1`"* — and says
nothing about the base phase, where `commitWrite` is called with `ctx = []`. That is B1-F2's
unenforced precondition surfacing a third time: stated in `classifyWriteRow`'s docstring, absent from
`baseWriteRowsOk`'s, absent here.

---

## B1.4 — Call-site sweep

19 production call sites across the 14 audited identifiers, plus the type's own 11 signature
positions — close to the brief's ~21 estimate. Test-suite call sites are noted where they are the
only thing pinning a behavior, but are not counted. For each: how `contextWidth`, `stateRank`, and
`rows` are derived; the invariant assumed but absent from the callee's signature; and whether a new
row kind changes the answer.

| Site | Caller(s) | `contextWidth` / `stateRank` / `rows` derivation | Invariant assumed, absent from the signature | New row kind changes it? |
|---|---|---|---|---|
| `WriteRowKind` | **11** production signature positions: `classifyWriteRow`'s `Option WriteRowKind` return; `writeRowKinds`' `Array (Option WriteRowKind)` return; the `rows` parameter of `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree` and `pinnedLiteralsInRange`; `writesCollide`'s `rowsA` and `rowsB`; `checkWrites`' return type and its `rowsByState` annotation; `Compile.lean`'s `mine` annotation | n/a | Derived `DecidableEq`/`BEq` is relied on by two `==` comparisons against literal constructors | **Yes** — 14 columns of new obligations |
| `classifyWriteRow` | `writeRowKinds` (sole caller) | `contextWidth` passed through verbatim | **That `contextWidth = 0` means "base".** The function has no way to say so and no `advancingDims` at all | **Yes** — the sole chokepoint |
| `writeRowKinds` | `checkWrites`; `Compile.lean` ×2 (base-boundary loop; base-collision `mine` builder) | `checkWrites`: `stateShape.size` from `sigs[st.destSlot].shape`, `contextWidth` from `if isBase then 0 else st.advancingDims.size`. **`Compile.lean`: `stateShape.size` from `stateShapes[…]` (its own Phase 2 derivation) and `contextWidth` a hardcoded literal `0` at both sites** | `coeffs`/`bias` already length-checked against `stateRank` — true at the `checkWrites` site (the two rank guards run immediately before) and **assumed by construction** at both `Compile.lean` sites, which run no rank guard. What that assumption buys is visible when it fails: `getD` **manufactures** rows rather than rejecting. `writeRowKinds 3 0` on a write supplying one coefficient row returns `#[some (.free 0), some (.pinned 0), some (.pinned 0)]` — two `.pinned 0` rows invented from nothing — and `writeRowKinds 1 0` on a write supplying three drops rows 1–2 silently, returning `#[some (.free 0)]` [snippet, S6] | **Yes** |
| `baseWriteRowsOk` | `checkWrites` (`if isBase then` arm) — **sole caller** | `rows` from `writeRowKinds stateShape.size 0 w`; `advancingDims` from `st.advancingDims`; `outputShapeSize` from the **declared** `block.tensorSigs[w.outputSlot].shape.size` | **`contextWidth = 0`, hence no `.advancing` row can be present** — Finding B1-F2. `Compile.lean` does **not** call this function; it re-implements clause 3 only | **Yes** — §B1.2 note 2 |
| `stepWriteRowsOk` | `checkWrites` (`else` arm) — **sole caller** | as above with `contextWidth = st.advancingDims.size` | `advancingDims` in range and duplicate-free (established earlier, in `checkScanPlan`'s state loop, not here) | **Yes** — but this predicate is fully classified today (zero `c` cells), so a new kind needs one new clause, not a rewrite |
| `freeExtentsAgree` | `checkWrites` — **sole caller**; **no source-facing counterpart in `Compile.lean` at all** | `stateShape` from `sigs[st.destSlot].shape`; `outputShape` declared | Its docstring states it: *"At its only call site it runs AFTER `baseWriteRowsOk`/`stepWriteRowsOk` have admitted the geometry … so neither `getD` default is reachable there"* | No |
| `pinnedLiteralsInRange` | `checkWrites` — **sole caller**; re-implemented inline in `Compile.lean` | as above | same post-admission precondition as `freeExtentsAgree` | No |
| `writesCollide` | `checkWrites` (base pairwise loop); `Compile.lean` (base pairwise loop) | both arrays from `writeRowKinds` for the **same** state, so equal length | **Equal-length arrays.** `writesCollide` scans `List.range rowsA.size` and reads B via `getD d none`, so it is length-blind in both directions — see B1-F8 | **Yes** — §B1.2 note 3 |
| `causalAdvancingRow` | `stateReadCausal` (sole caller) | `row`/`bias` from `f.map` via `getD … #[]`/`getD … 0` | Read-row vocabulary; `advancingDims[i]` in range for the read's own map | No |
| `stateReadCausal` | `checkScanPlan` (causality loop); `Compile.lean` (Phase 5) | `advancingDims` from the state; `contextPos` from the term | `advancingDims.size == contextPos.size` is checked **inside** the predicate (its first conjunct) — unusually, not assumed | No |
| `checkWrites` | `checkScanPlan` ×2 (`… raw.baseBlock raw.baseWrites … true` and `… raw.stepBlock raw.stepWrites … false`) | `isBase` is the discriminator that produces `contextWidth` | Block already checked (`checkPlanBlock` runs before); state loop already validated dims and dtypes | **Yes** |
| `checkScanPlan` | `EvalPlan.lean`'s `checkPlan`, `.scan` arm — **sole production caller** | `sigs := raw.tensorSigs`, the outer graph's own table | None material: it validates its own inputs and stores `sigs` in the evidence | **Yes**, transitively |
| `commitWrite` | `runDenseScan` ×2 (base loop with `ctx = []`; step loop with `ctx = q.toList.map Int.ofNat`) | `target` from the allocated state; `w` from `raw.baseWrites`/`raw.stepWrites` | **Everything** — no bounds recovery, by design. Plus `checkNonlinIO`'s shape preservation, which its own docstring flags. Base call passes `ctx = []`, which the `.advancing` bullet does not cover (B1-F7) | **Yes** — needs a fourth bullet |
| `runDenseScan` | `EvalPlan.lean`'s `runDensePlan`, `.scan` arm — **sole production caller** | store built at exactly `raw.tensorSigs.size` and handed through unchanged | None: the signature tie and store-arity check make the caller's assertions checkable | No |

**Off-contract behaviour of the four standalone predicates.** Every row above records a precondition
of the form "`rows.size` equals the state's rank" or "`advancingDims` is in range", none of which
appears in any signature. Measured directly, all four **fail closed** when the precondition is
violated: `baseWriteRowsOk #[5] 1 #[some (.free 0)]` and `stepWriteRowsOk #[5] 1 #[some (.free 0)]`
are both `false` (an out-of-range `advancingDims` entry makes `rows.getD d none` yield `none`);
`freeExtentsAgree #[3] #[3,3,3] #[some (.free 0), some (.free 1), some (.free 2)]` is `false` (a short
`stateShape` defaults to extent `0`, which matches nothing); and
`pinnedLiteralsInRange #[] #[some (.pinned 0)]` is `false` (`lit.toNat < 0` is unsatisfiable)
[snippet, S13]. So a caller that breaches these preconditions gets a rejection rather than a silent
pass — the safe direction, and worth knowing before B2 adds a clause that could invert it.

Three known instances the brief asked to re-derive rather than trust, all re-derived above and each
confirmed:

1. **`checkWrites`' `if isBase then 0`** — confirmed verbatim. It is B1-F2's **barrier 1**, covering
   rows R9 and R10 across columns 4, 6, 7, 11 and 12 (groups G5, G11, G13, G16). It is *not* the sole
   support: `Compile.lean`'s base-write construction loop is an independent barrier 2 for compiled
   programs, and B1-F2 records where barrier 2 disappears.
2. **`Compile.lean`'s two literal `0`s** — confirmed at both `writeRowKinds` calls in Phase 5. See
   B1-F6.
3. **`commitWrite` trusting `checkNonlinIO`'s shape preservation** — confirmed; already documented in
   `commitWrite`'s own docstring as load-bearing, and it is the one caveat on B1-F3's refutation.

### Finding B1-F6 — `Compile.lean`'s second call site is a strict SUBSET of `Scan.lean`'s rules

Two hand-inlined duplicates confirmed [read]:

- the `baseWriteNotAtBoundary` guard re-implements `baseWriteRowsOk`'s **clause 3** —
  `unless (stateAdvDims.getD w.stateIndex #[]).any (fun d => rows.getD d none == some (.pinned 0))`
  — without calling `baseWriteRowsOk`;
- the loop immediately after re-implements `pinnedLiteralsInRange` —
  `unless 0 ≤ lit && lit.toNat < stateShape.getD d 0` — without calling it.

Beyond the duplication, the source-facing pass is a **strict subset**: it re-implements no counterpart
of `baseWriteRowsOk`'s clauses 1 and 2, none of `stepWriteRowsOk` at all, and none of
`freeExtentsAgree`. Those hold by construction of the base and step write loops (`.iterAt _ lit` →
an all-zero coefficient row with the literal as bias; `.free`/`.freeNorm` → a single `1` at
`freeSeen`, incremented in slot order, so the cover is `List.range` by construction) — but that
construction invariant is written down nowhere, and if it ever failed, the failure surfaces from
`checkScanPlan` as `PlanCompileCause.invalidPlan`, which `Eval/AGENTS.md` documents as *"`checkScanPlan`
rejected COMPILER output, which is a compiler bug, not a source problem"* [read] — i.e. with no source
locator, which is the exact outcome the source-facing pass exists to prevent.

This is the `scatterOutDim`/`scatterOutShape` drift shape one layer over. When `Scan.lean`'s
predicates gain a row kind, the two copies will not see it, and neither will the base/step write
construction loops. Both of those loops have a catch-all arm that currently throws
`CapabilityError.unsupportedLhsSlot`, and the two arms are **not** the same pattern: the base loop's
is `| .iterNext _ | .affine _ =>` and the step loop's is `| .iterAt .. | .affine _ =>` [read]. What
they share is `.affine` — precisely the slot Task B2's affine LHS writes must lower. **Giving the base
loop's arm a real lowering is what removes B1-F2's barrier 2**; see that finding's "Where barrier 2
disappears".

### Finding B1-F8 — `writesCollide` is length-blind in both directions (REFUTED as harmful)

`writesCollide` iterates `List.range rowsA.size` and reads the second array via `rowsB.getD d none`,
so a dimension present in only one argument can never separate the writes:

```
writesCollide #[some (.pinned 0)] #[some (.pinned 0), some (.pinned 1)] = true
writesCollide #[some (.pinned 0), some (.pinned 1)] #[some (.pinned 0)] = true
```

[snippet, S5] — dimension 1 pins `0` against `1` and *would* have separated them. The failure
direction is **conservative** (over-reports collision, therefore rejects), and at both call sites
both arrays come from `writeRowKinds stateShape.size …` for the same state, so the lengths are
always equal. `c`‡, refuted as harmful; recorded because the same `getD … none` catch-all is what
makes G9 and §B1.2 note 3 true.

### Finding B1-F9 — `DSL/Ast.lean` slot functions

The four functions in scope, all probed [snippet, S15]:

- **`toReadIdx`** — the `.affine _ => none` arm (defect instance 5's home) is intact and is still the
  only non-total arm across the five `LHSSlot` constructors:
  `((.free), (.freeNorm), (.iterAt), (.iterNext), (.affine))` → `(true, true, true, true, false)`.
  Its docstring's unreachability argument (`lowerArith` reclassifies every `slotsBecomeScatter`
  `.assign` into `Stmt.scatter` before `splitStmt` runs) is unchanged [read].
- **`slotsBecomeScatter`** — `([free i, free j], [free i, free i], [free i, freeNorm i],
  [affine (2·i)], [iterNext i, free j], [iterAt i 0, iterAt i 1])` →
  `(false, true, true, true, false, false)`. The `[.free a, .freeNorm a]` case is caught (the
  2026-08-27 "fourth class-6 door" fix), and the repeated-`iterAt` case deliberately is not, matching
  its docstring's *"NOT `axisUID?` (which also counts `iterAt`/`iterNext`, whose repeats mean
  something else)"* [read].
- **`outIdx`** — total over all five constructors [read]; it is the sole input to `outExtent`.
- **`outExtent`** — **new `c` cell.** Five distinct extent conventions coexist (`.axis a` → `size`;
  `.const n` → `n+1`; `.shift a c` → `size+c`; `.scale c a` → `c·size`; `.affine c0 xs` →
  `c0 + Σ cᵢ·sizeᵢ`), measured as `(some 4, some 6, some 5, some 8, some 9)` for
  `free i` / `iterAt i 5` / `iterNext i` / `2·i` / `1 + 2·i` at `size(i) = 4`. **Every
  negative-valued form collapses to extent `0` through `Int.toNat`, with no rejection:**
  `iterAt i (-5)`, `scale (-2) i`, `shift i (-9)`, `affine (-100) [(1,i)]` → `(some 0, some 0,
  some 0, some 0)`. Contrast an unsized axis, which correctly yields `none` and fails loud
  (`(none, none)`).

  Not documented as intentional, and not pinned: the only reasoning about a zero extent is in
  `Eval.scatterOutShape`'s own comment — *"An unsized axis means it is unbound by any read (an
  upstream sizing gap), so FAIL LOUD rather than defaulting its size to 0"* — which addresses the
  `none` case and is silent on `some 0` [read]. Both callers, `Eval.scatterOutShape` and
  `SizeInfer.scatterOutputShapes`, distinguish only `some n` from `none`, so a `some 0` flows straight
  through into a shape dimension [read]. This sits directly in Task B2's path (affine LHS writes) and
  inside the `scatterOutShape`/`outExtent` sync contract `Eval/AGENTS.md` names. **Flagged for B2, not
  closed** — whether a zero-extent scatter output is subsequently rejected on the scatter path was not
  chased here.

---

## B1.5 — Gate

> Every forbidden cell needs a located test. No cell may be silently ignored.

### Finding B1-F10 — 10 of the 16 `b` cells have no located test

Measured, not inferred. **Every `#guard` on either geometry predicate in the whole test suite is a
positive (an acceptance)** — all five of them: `baseWriteRowsOk #[0] 1 faceRows`,
`baseWriteRowsOk #[0,1] 0 pointRows`, `baseWriteRowsOk #[1] 1 colFaceRows`,
`stepWriteRowsOk #[0,1] 0 dpStepRows`, `baseWriteRowsOk #[0,1] 0 outOfRangePointRows`. There is no
negative `#guard` on `baseWriteRowsOk` or `stepWriteRowsOk` anywhere [read].

Located coverage therefore rests entirely on plan-level `writeGeometryNotAdmitted` fixtures, of which
there are exactly three [read]:

- `lookAheadStepWrite` (Part 2) — a step row with bias `2`, i.e. clause 1 (`rows.all Option.isSome`)
  rejecting an unrecognized row. Not one of the 16 `b` cells: it tests the `none` case.
- `advancingAtNonAdvancingScan` (Part 8) — covers **R12** (`advancing` @ non-adv @ step), asserting
  `writeGeometryNotAdmitted false 0`, with the review's original aliasing/panic account recorded
  alongside it.
- `pinnedAtNonAdvancingScan` (Part 8) — covers **R4** (`pinned` @ non-adv @ step), same assertion.

Plus `canonicalWScan`, an acceptance control proving clause 3 does not over-reject.

So of the 16 `b` cells: **6 are located** (R4 and R12, each across columns 5, 11, 12) and **10 are
not** —

- **R3** (`pinned` @ adv @ step) and **R7** (`free` @ adv @ step), 6 cells across columns 5, 11, 12.
  Both are rejections by `stepWriteRowsOk`'s clause 2 (`rows.getD d none == some (.advancing i)` at
  every advancing dimension). The only evidence they reject is this audit's [snippet, S3]:
  `stepWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 0)] = false` and
  `stepWriteRowsOk #[0] 1 #[some (.free 0), some (.free 1)] = false`.
- **R9, R10** (`advancing` @ base) at columns 2–3, 4 cells. Located only by [snippet, S1] and
  [snippet, S11] in this audit.

Clause 2 is the clause Task B2 is most likely to touch (a strided row at an advancing dimension has
to be classified against it), and it is currently the least-pinned clause in the file.

### Summary of state against the gate

> **Updated by Task B2** (see §B2.8 for the same accounting over the appended rows). The two bullets
> immediately below state B1's 12-row figures; with R13–R16 the table stands at **22 `b` cells** —
> 6 located by repo fixtures, 10 located only by B1's spikes, and **6 not locatable by any test that
> could exist today**, since the `strided` constructor they classify does not exist (B2-F5) — and
> **122 `c` cells** across **31 groups**, 16 closed / 91 cells and 15 open / 31 cells.

- **16 `b` cells**: 6 located by repo fixtures, 10 located only by this audit's spikes (B1-F10).
- **86 `c` cells**: all adjudicated in §B1.3 across 17 groups — **9 groups / 71 cells closed**
  (structurally, by kind partition, by a quoted sibling clause, or as documented-and-pinned
  intentional) and **8 groups / 15 cells open**, collapsing to two findings: **B1-F2** (latent,
  10 cells) and **B1-F4** (live and memory-safe, 5 cells). No `c` cell was softened to "unlikely" or
  "defensive", and no write-path cell was closed as backstopped by `gatherFactor`'s `inBoundsPerDim`.
  Fix round 1 moved 4 cells (both value predicates × `advancing` @ base) out of the closed column into
  B1-F2, because their stated catcher does not operate in the base phase — see G16.
- **Findings outside the cell grid**: **B1-F1** (the audit artifact this table was supposed to append
  to does not exist), **B1-F3** (candidate gap 2, refuted with mechanism), **B1-F5** (an `a` cell
  weaker than its own docstring says), **B1-F6** (`Compile.lean`'s inline duplicates are a strict
  subset), **B1-F7** (`commitWrite`'s `.advancing` bullet is step-scoped), **B1-F8** (`writesCollide`
  length-blindness, refuted as harmful), **B1-F9** (`DSL/Ast.lean`'s `outExtent` collapses negative
  affine forms to extent `0`; flagged for B2, not closed).

Every verdict above carries either a quoted clause from the code or a construction attempt with
verbatim observed output.

---

# Axis B / Task B2 — the `strided` row kind across the write-geometry surface

Findings-only, taken at `9680b92` with a green build (`cd leanncd && "$HOME/.elan/bin/lake" build`,
**8660 jobs**) [built]. No production code was changed: the diff over `leanncd/LeanNCD/`,
`leanncd/lakefile.toml` and `leanncd/test/` is empty, and **no `strided` constructor was added to any
committed file**.

Three further spike files, each committed with its captured output alongside B1's in
`leanncd/spikes/`:

- `AxisBStridedProbe.lean` (+ `.output.txt`) — probes **S17–S22**, the strided row across the
  write-geometry predicates and `LHSSlot.outExtent`. Imports `LeanNCD.Eval.Plan.Scan` only.
- `AxisBZeroExtentProbe.lean` (+ `.output.txt`) — probes **S23–S25**, B1-F9's declined question at
  both `outExtent` callers. Imports `LeanNCD.Eval.Eval` / `LeanNCD.Eval.SizeInfer`.
- `AxisBSurfaceZeroExtentProbe.lean` (+ `.output.txt`) — probe **S26**, the same question from real
  surface syntax. Imports the `LeanNCD` umbrella, so it deliberately contains no
  `{ coeffs := …, bias := … }` record literal (`DSL/Syntax.lean` declares `"bias"` as a token).

Re-run exactly as B1's: run `lake env lean spikes/<file>.lean` from `leanncd/`. None is in
`lakefile.toml` or any default build target.

**One extra evidence tag, used only in this section.** `[snippet, model]` marks an observation made
against a **transcribed model** rather than production code: a throwaway spike
(`spikes/AxisBStridedModelThrowaway.lean`) that declared a four-constructor `WRK` inductive and then
copied `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`, `pinnedLiteralsInRange` and
`writesCollide` **verbatim** from `Scan.lean` with no strided arm added, so that a genuinely new
constructor could be run through the current predicate text. It was **deleted before committing** and
is not in `leanncd/spikes/`; its observed output is reproduced inline below. A `[snippet, model]`
claim is weaker than a `[snippet]` one — it measures a faithful copy, not the shipped function.

**How each `[snippet, model]` claim is discharged, stated exactly rather than by a blanket rule.**
Most are paired with a `[snippet]` measurement of the real clause at the same parameters, with
`.pinned`/`.advancing` standing in for the fourth constructor — sound because the arms involved
(`| _ => none`, `| _ => true`, `| _, _ => false`) are constructor-blind by their own text, quoted at
each site. **Two are not so paired, and have no production counterpart in the committed spikes:**

- **G17's derived-`BEq` observation** (`(some (.strided 0 2 0) == some (.pinned 0), …)` →
  `(false, false, true, false)`). No production spike can compare against a constructor that does
  not exist. Re-derivable at source instead: `WriteRowKind` is `deriving DecidableEq, BEq` [read], and
  Lean's derived structural equality on a sum type is `false` between distinct constructors and
  compares payloads within one — so the observation restates the deriving handler's specification.
- **§B2.1 point 3's context-half row** (`classifyA 2 #[2,0,0] 0` → `none`). Re-derivable at source
  from `classifyWriteRow`'s singleton arm as it stands: with `c == 2`, both `c == 1` conjuncts fail,
  and a strided branch guarded on `p ≥ contextWidth` fails at `p = 0 < 2`, so every arm falls through
  to `else none` [read].

Neither carries a verdict of its own — G17 closes structurally and point 3 is a design argument — so
nothing in B2-F1 depends on the model. A reviewer who rejects the model-to-production transfer can
re-derive both at source by the two readings above.

---

## B2.1 — Fact 2 DECIDED: the strided branch is *not* phase-gated, and the base cell is LIVE

B1 tagged fact 2 `[CONDITIONAL — not measured; no strided constructor exists to measure]` and handed
the decision here. **Decision, with the assumption named.**

### The decision

> **Decision A (adopted).** `classifyWriteRow`'s strided branch carries the **domain-partition**
> guard `p ≥ contextWidth` — the identical guard `.free` already carries — and **no phase gate**. It
> is ordered **after** the advancing branch. In full:
>
> ```
> | [(c, p)] =>
>     if c == 1 && p < contextWidth && bias == 1 then some (.advancing p)
>     else if c == 1 && p ≥ contextWidth && bias == 0 then some (.free (p - contextWidth))
>     else if p ≥ contextWidth then some (.strided (p - contextWidth) c bias)
>     else none
> ```
>
> **Decision B (rejected).** The same branch additionally gated `&& contextWidth > 0`, i.e. step
> writes only — structurally the shape `.advancing`'s own `p < contextWidth` guard has.

**Consequence, stated plainly: the strided cell at base is LIVE, not latent.** Under decision A a
strided row is emittable at `contextWidth = 0`, so B1's fact-2 conditional resolves to its live
branch and this is the write-geometry defect family recurring for a **sixth** time (finding B2-F1).

### Why A and not B — the argument, and the assumption it rests on

1. **The feature wants base strided writes.** `Compile.lean` has **two** `.affine` arms to lower, not
   one: the base-write construction loop's `| .iterNext _ | .affine _ =>` and the step-write loop's
   `| .iterAt .. | .affine _ =>`, both throwing `CapabilityError.unsupportedLhsSlot` [read]. Decision
   B would leave the base arm permanently unlowerable, so a base initialization like
   `dp[0, 2*j] := ROWFACE[j]` would stay rejected — refusing half the feature to keep half a defect
   latent.
2. **A phase gate would not be a bound, only a deferral.** Barrier 1 (`checkWrites`' `if isBase then
   0`, plus `Compile.lean` Phase 5's two hard-coded `0`s — **two sites**, enumerated in §B2.7) is
   enforced by no signature and no check; B1 recorded it as an unenforced call-site precondition
   stated in two docstrings. Decision B would add a **third** row kind resting on that same
   unenforced value, i.e. it buys latency at the cost of one more `‡`.
3. **`p ≥ contextWidth` is required either way**, and for a reason independent of phase: the minimal
   shape the brief specifies is `strided (outputPos : Nat) (scale : Int) (offset : Int)`, coordinate
   `scale * out[outputPos] + offset`. Its payload names an **output-slice** position, so a nonzero
   coefficient sitting in the *context* half has no representation in it and must stay `none`.
   Measured on the model: a strided-shaped row at `p = 0 < contextWidth = 2` is `none` under **both**
   decisions — `(classifyA 2 #[2,0,0] 0, classifyB 2 #[2,0,0] 0)` → `(none, none)`
   [snippet, model].
4. **Ordering after the advancing branch is not cosmetic.** Coefficient `1` with bias `1` is
   `.advancing p` when `p < contextWidth` and unclassified today when `p ≥ contextWidth`; a strided
   branch placed *before* the advancing branch would swallow every advancing row. Measured on the
   real `classifyWriteRow`: `(classifyWriteRow 0 #[1] 1, classifyWriteRow 2 #[1,0,0] 1,
   classifyWriteRow 2 #[0,0,1] 1)` → `(none, some (.advancing 0), none)` [snippet, S17]; and on the
   model, with the branch ordered after, `.advancing` survives under both decisions —
   `(classifyA 2 #[1,0,0] 1, classifyB 2 #[1,0,0] 1)` → `(some (.advancing 0), some (.advancing 0))`
   [snippet, model].

**The assumption this rests on, named.** Decision A assumes the affine-LHS feature is wanted in
**base** blocks and not only in step blocks. That is an assumption about the feature's scope, not a
fact derivable from the code at `9680b92` — `Compile.lean`'s base `.affine` arm being *present and
throwing* shows only that the slot is reachable enough to need an arm, not that the feature intends
to lower it. **If the Scatter slice decides affine LHS writes are step-only, decision B is the right
one** and every `★`-marked row below becomes latent rather than live; §B2.3 gives decision B's mark
for each group that differs. This paragraph is the assumption; it is not presented as a measurement.

### The construction, built both ways

The construction the brief asked for, run under each decision so the Scatter slice inherits a tested
answer either way. Rows for the `dp[0, 2·oc₀, oc₀]` write (`coeffs := #[#[0], #[2], #[1]]`,
`bias := #[0, 0, 0]`) at base width 0:

```
decision A:  #[some (pinned 0), some (strided 0 2 0), some (free 0)]
decision B:  #[some (pinned 0), none,                 some (free 0)]

baseWriteRowsOk #[0] 1 (decision A's rows) = true      -- LIVE: admitted, strided row dropped
baseWriteRowsOk #[0] 1 (decision B's rows) = false     -- LATENT: clause 1 (rows.all Option.isSome)
```

[snippet, model]. And the same three coefficient/bias shapes at each phase:

```
decision A @ base (width 0): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
decision A @ step (width 2): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
decision B @ base (width 0): (none, none, none)
decision B @ step (width 2): (some (strided 0 2 0), some (strided 0 1 3), some (strided 0 2 3))
```

[snippet, model]. The corresponding **production** measurement — every one of those six shapes is
`none` at HEAD, confirming fact 1 over the exact rows the feature must admit rather than over B1's
generic `#[2]`:

```
classifyWriteRow 0 #[2] 0,  classifyWriteRow 0 #[1] 3,  classifyWriteRow 0 #[2] 3        -> (none, none, none)
classifyWriteRow 2 #[0,0,2] 0, classifyWriteRow 2 #[0,0,1] 3, classifyWriteRow 2 #[0,0,2] 3 -> (none, none, none)
```

[snippet, S17]. Through the real entry, a strided-shaped base row is rejected at HEAD by clause 1:

```
writeRowKinds 2 0 (coeffs #[#[0],#[2]], bias #[0,0]) = #[some (pinned 0), none]
baseWriteRowsOk #[0,1] 1 (those rows)                = false
S18 (strided-shaped base row, coefficient 2): checkScanPlan REJECTED:
  LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
S18b (strided-shaped base row, coefficient 1 bias 5): checkScanPlan REJECTED:
  LeanNCD.Eval.Plan.ScanPlanError.writeGeometryNotAdmitted true 0
```

[snippet, S18].

### One shape neither decision reaches

A **two-nonzero** coefficient row — `Out[i + j]`, i.e. `.affine 0 [(1,i),(1,j)]` — stays `none` under
both decisions, because `classifyWriteRow`'s `| _ => none` arm matches on the **length** of the
nonzero list and a one-`outputPos` strided payload cannot extend it. Measured on production:
`(classifyWriteRow 0 #[1,1] 0, classifyWriteRow 0 #[2,3] 5, classifyWriteRow 2 #[0,0,1,1] 0)` →
`(none, none, none)` [snippet, S17]; and on the model, `(classifyA 0 #[1,1] 0, classifyB 0 #[1,1] 0)`
→ `(none, none)` [snippet, model]. The slot nonetheless **has an extent**:
`LHSSlot.outExtent (.affine (.affine 0 [(1,i),(1,j)])) sz` → `some 7` at `size(i)=4, size(j)=3`
[snippet, S21]. So the minimal strided kind admits a strict subset of the affine LHS forms
`outExtent` already prices — recorded as **B2-F6** below.

---

## B2.2 — The `strided` row kind appended to the table (R13–R16)

Appended exactly as §B1.2 specified: four rows at the bottom, no change to any column header, to any
existing row, or to B1's legend.

**One B2-local mark, declared here rather than added to B1's legend** (which stays as B1 wrote it):

| Mark | Meaning |
|---|---|
| **★** | on a *row label*, not a cell: every mark in this row is the mark under §B2.1's **decision A**. The letter is **decision-invariant** for columns 1, 5, 9, 10, 13 and 14 — cols 1/13/14 because those sites classify nothing either way (G17, G29, G30), col 5 because `stepWriteRowsOk` is structurally `—` at base under both decisions, and cols 9–10 because they are `▷`, a disjoint read vocabulary. For the remaining eight cells of each row (cols 2, 3, 4, 6, 7, 8, 11, 12), §B2.3's group entry gives decision B's reading; **every** group covering an R13/R14 cell now carries one, and G29's entry additionally gives its decision-B open/closed *status*, which the letter alone does not settle. A row-label mark contributes nothing to the cell census |

### The appended rows

| # | row kind @ dim class @ phase | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R13 | `strided` @ adv @ base ★ | c | c | c | **c** | — | **c** | **c** | c | ▷ | ▷ | **c** | **c** | c | c |
| R14 | `strided` @ non-adv @ base ★ | c | c | c | **c** | — | **c** | **c** | c | ▷ | ▷ | **c** | **c** | c | c |
| R15 | `strided` @ adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |
| R16 | `strided` @ non-adv @ step | c | c | c | — | **b** | c | c | — | ▷ | ▷ | **b** | **b** | c | c |

### Cell census for the four appended rows

56 cells (4 × 14): **0 a**, **6 b**, **36 c**, 6 —, 8 ▷. Per row: R13 and R14 are 11 c / 1 — / 2 ▷
each; R15 and R16 are 7 c / 3 b / 2 — / 2 ▷ each. Whole table after the append: **224 cells (16 ×
14) — 24 a, 22 b, 122 c, 24 —, 32 ▷**, as restated in §B1.2's census and §B1.5's gate summary.

**Reported divergence (the brief predicted ~27 adjudicable cells).** 36 `c` cells, a 33% overshoot
— far smaller than B1's 86-against-40. The mechanism is the same one B1 identified and is not new
information about the code: the five non-validating / dimension-class-blind columns (`WriteRowKind`,
`classifyWriteRow`, `writeRowKinds`, `commitWrite`, `runDenseScan`) contribute 20 of the 36 by
construction. Excluding them leaves **16 `c` cells** — 2 in `baseWriteRowsOk`, 4 in
`freeExtentsAgree`, 4 in `pinnedLiteralsInRange`, 2 in `writesCollide`, 2 each in `checkWrites` and
`checkScanPlan` — below the estimate rather than above it.

### Finding B2-F2 — not one `a` cell among 56

**No audited site requires or demands the presence of a strided row, in either phase.** All 24 `a`
cells in the combined table belong to B1's rows R1–R12. Every site either forbids a strided row
(6 `b` cells, all at step) or ignores it (36 `c` cells). That asymmetry is worth naming because
`baseWriteRowsOk`'s clause 2 and `stepWriteRowsOk`'s clause 4 are *positional-cover* clauses — they
express "these dimensions must be covered" as an `a`-style demand on `.free` rows — and a strided row
is a cover row in every sense except that no clause counts it. §B2.4 is where that gap has to be
closed, and it is why B2-F1's cells are `c` rather than `b`.

---

## B2.3 — Adjudication of every new `c` cell (G17–G30)

Same order B1 used: (1) name the catching site and **quote its clause**; (2) if soundness rests on a
caller rather than the predicate's own text, mark `‡` and route to the call-site question; (3) build
the construction and record the observed value verbatim. **No write-path cell below is closed as
"backstopped by `gatherFactor`'s `inBoundsPerDim`", and no cell is closed by naming a catcher that
cannot fire in its own phase** — the failure that cost B1 a fix round (G16). Where a group's catcher
is `stepWriteRowsOk`, the group is a **step-phase** group and that predicate does run there.

| Group | Cells | Site × rows | Verdict |
|---|---|---|---|
| G17 | 4 | col 1 × R13–R16 | **Closed structurally**, extending G1. A closed inductive cannot require or forbid. G1 anticipated exactly this constructor: *"a payload-carrying fourth constructor inherits correct equality for free"* — verified rather than assumed, since two production clauses compare against literal constructors via derived `BEq` (`baseWriteRowsOk`'s `rows.getD d none == some (.pinned 0)` and `stepWriteRowsOk`'s `== some (.advancing i)`). On a four-constructor `deriving DecidableEq, BEq` inductive, `(some (.strided 0 2 0) == some (.pinned 0), == some (.advancing 0), == some (.strided 0 2 0), == some (.strided 0 2 1))` → `(false, false, true, false)` [snippet, model] — cross-constructor comparisons are `false` and payload discrimination is exact, so neither clause silently changes meaning. **Decision B**: unchanged, letter and status both. The gating decision is a `classifyWriteRow` branch condition; the inductive has no branch to gate, and the derived-`BEq` argument holds for a four-constructor type regardless of which rows are ever built. |
| G18 | 4 | cols 2–3 × R15, R16 | **Closed** to G-step (col 5). Both functions are dimension-class-blind by construction — `classifyWriteRow`'s signature is `(contextWidth : Nat) (coeffRow : Array Int) (bias : Int)`, no `advancingDims` and no dimension index [read] — so the whole dim-class axis is `c` here, exactly as G2a. Unlike G2b, the downstream catcher is **not** open: `stepWriteRowsOk` clause 2 (`advancingDims.toList.zipIdx.all (fun (d, i) => rows.getD d none == some (.advancing i))`) and clause 3 (`rows.toList.zipIdx.all (fun (r, d) => advancingDims.contains d \|\| (match r with \| some (.free _) => true \| _ => false))`) between them reject a strided row at every dimension, **in the step phase, which is this group's own phase**. Measured on the model at all three placements: `(stepWriteRowsOk #[0,1] 1 #[strided, advancing 1, free 0], stepWriteRowsOk #[0] 1 #[advancing 0, strided, free 0], stepWriteRowsOk #[0] 1 #[advancing 0, free 0, strided])` → `(false, false, false)` [snippet, model]. The real clauses' behaviour on a non-`.free` non-`.advancing` `some` row at the same parameters: `(stepWriteRowsOk #[0,1] 1 #[some (.pinned 0), some (.pinned 2), some (.free 0)], stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.pinned 2), some (.free 0)])` → `(false, false)` [snippet, S19]. **Decision B**: unchanged — `classifyWriteRow` admits strided at step under both decisions [snippet, model]. |
| **G19** | 4 | cols 2–3 × R13, R14 | **OPEN — B2-F1.** Same blindness as G18, but the only downstream catcher at base is `baseWriteRowsOk`, whose own cells for these rows (G20) are open. **A group cannot be closed by deferral to an open group** — B1 established that rule at G2b, and it applies unchanged. **Decision B**: these four cells become **`b`‡** instead, on barrier 1 (`checkWrites`' `if isBase then 0`), exactly as B1 marked R9/R10 at these columns. |
| **G20** | 2 | col 4 × R13, R14 | **OPEN — B2-F1, the sixth instance.** `baseWriteRowsOk` clause 2 is the verbatim defect-instance-4 shape and its `filterMap` arm is **constructor-blind**: `((rows.toList.filterMap (fun r => match r with \| some (.free p) => some p \| _ => none)) == List.range outputShapeSize)`. The `\| _ => none` arm drops every `some` row that is not `.free`, a fourth constructor included. Measured on the model at both dimension classes: `(baseWriteRowsOk #[0] 1 #[pinned 0, strided 0 2 0, free 0], baseWriteRowsOk #[0,1] 1 (same))` → `(true, true)` [snippet, model]. Measured on the **real** clause with the two non-`.free` constructors that exist, at the identical parameters: `(baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.pinned 2), some (.free 0)], … #[some (.pinned 0), some (.advancing 0), some (.free 0)], baseWriteRowsOk #[0,1] 1 (each of those))` → `(true, true, true, true)`, against the control in which dim 1 carries a genuine second `.free` row and the cover therefore breaks: `(baseWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 1), some (.free 0)], … #[some (.pinned 0), some (.free 0), some (.free 0)])` → `(false, false)` [snippet, S19]. That control is what makes the drop a *drop* rather than an accident of the parameters. **Decision B**: **`c`‡ latent** rather than live — the rows become `#[some (.pinned 0), none, some (.free 0)]` and clause 1 fires, `baseWriteRowsOk … = false` [snippet, model]. |
| G21 | 2 | col 6 × R15, R16 | **Closed** by an in-phase catcher, not by kind partition alone. `freeExtentsAgree`'s `\| _ => true` arm ignores a strided row exactly as it ignores `.pinned`/`.advancing` [read], so the cell is `c`. It is closed because `checkWrites` runs `unless admitted do throw (.writeGeometryNotAdmitted isBase wi)` **before** `freeExtentsAgree` [read], and at step `admitted` is `stepWriteRowsOk`, which rejects a strided row at every dimension (G18's measurement). So the row never reaches this predicate in this phase — a stronger closure than G6's, and one whose catcher demonstrably fires here. Marked `c` rather than `—` to keep B1's column convention (B1 marks col 6 `c` for R3/R4/R12, all `b` at col 5). **Decision B**: unchanged. |
| **G22** | 2 | col 6 × R13, R14 | **OPEN — B2-F1.** The same `\| _ => true` arm, in the **base** phase, where nothing rejects the row first: `baseWriteRowsOk` admits it (G20), so `checkWrites` proceeds to `freeExtentsAgree` and it passes at **any** extents. Measured on the model: `(freeExtentsAgree #[1,3,3] #[3] stridedRows, freeExtentsAgree #[1,1,3] #[3] stridedRows)` → `(true, true)` — the second with dim 1 at extent **1** [snippet, model]; and on the real predicate at the same parameters with `.advancing` standing in, `(freeExtentsAgree #[1,3,3] #[3] …, freeExtentsAgree #[1,1,3] #[3] …)` → `(true, true)` [snippet, S19]. **This is the load-bearing cell of the whole task**: `freeExtentsAgree` is the *one* predicate whose job is to bound a cover row's extent against the state's own dimension, and it is the predicate a strided row must extend (§B2.4). Not closed, and specifically **not** closed by citing `stepWriteRowsOk` or `advancingSizeMismatch` — neither operates at base, which is precisely G16's error. **Decision B**: **CLOSED**, and the cell letter becomes `c`‡. Under B the base rows are `#[some (.pinned 0), none, some (.free 0)]`, so `baseWriteRowsOk` clause 1 fires (G20's `false`) and `checkWrites` throws `writeGeometryNotAdmitted true wi` **before** it reaches `freeExtentsAgree` [read] — the G21 argument transposed to the base phase, with the same in-phase catcher. The `‡` records that this rests on barrier 1's unenforced `if isBase then 0`, so it is latent, not absent. |
| G23 | 2 | col 7 × R15, R16 | **Closed** by the same in-phase catcher as G21. `pinnedLiteralsInRange`'s `\| _ => true` arm ignores a strided row [read]; the row never reaches it at step, because `stepWriteRowsOk` rejects first and `checkWrites` throws before calling it [read]. Recorded alongside: the predicate's docstring justification — *"`.free`/`.advancing` rows are vacuously fine (their range is already bounded by the checked output/context shapes elsewhere)"* — **enumerates exactly two kinds and would not mention a strided row at all**. B1 already established that this sentence is false for an advancing row at base (G16); for a strided row it is not false so much as absent. See B2-F3. **Decision B**: unchanged. |
| **G24** | 2 | col 7 × R13, R14 | **OPEN — B2-F1.** As G22: reached in the base phase and passing. `pinnedLiteralsInRange #[1,3,3] stridedRows = true` and `pinnedLiteralsInRange #[1,1,3] stridedRows = true` [snippet, model]; the real predicate at the same parameters with `.advancing` standing in, `pinnedLiteralsInRange #[1,3,3] #[some (.pinned 0), some (.advancing 0), some (.free 0)]` → `true` [snippet, S19]. Not closed, and not closed by appeal to *"the checked output/context shapes"* — `checkScanPlan` forces `raw.baseBlock.contextShape == #[]`, so at base there is no context shape for that phrase to refer to (B1's S16 verified the rejection: `baseBlockContextNotEmpty #[2]`). **Decision B**: **CLOSED**, cell letter `c`‡ — identical to G22's decision-B note, since `checkWrites` throws on clause 1 before reaching `pinnedLiteralsInRange` too [read]. This is the G23 argument transposed to base. |
| G25 | 2 | col 8 × R13, R14 | **Closed as conservative** — fact 3, now measured on a real fourth constructor. `writesCollide`'s catch-all is `\| _, _ => false`, so *"a dimension forces the regions apart only when BOTH writes pin it to DIFFERENT literals"* [read] and a strided row can never separate two base writes. Measured: `(writesCollide #[strided 0 2 0] #[strided 0 2 1], writesCollide #[pinned 0, strided 0 2 0] #[pinned 0, strided 0 2 5], writesCollide #[pinned 0, strided 0 2 0] #[pinned 1, strided 0 2 0])` → `(true, true, false)` [snippet, model] — the third separates only via its `.pinned 0` vs `.pinned 1` row at dimension 0, which is the clause doing its declared job. Real-predicate counterpart on the existing non-`.pinned` constructors: `(writesCollide #[some (.free 0)] #[some (.free 0)], writesCollide #[some (.advancing 0)] #[some (.pinned 1)], writesCollide #[some (.pinned 0), some (.advancing 0)] #[some (.pinned 0), some (.pinned 1)])` → `(true, true, true)` [snippet, S19]. The failure direction is **over**-rejection, hence safe. Two differences from G9 are worth recording rather than inheriting: G9 closed these cells as *vacuous today* because no base row can be `.advancing`; under decision A that ground disappears, so this group is closed on conservatism alone. And the expressiveness cost is real — **two strided base writes to one state are always reported as colliding**, so `dp[0, 2*j] := A[j]` alongside `dp[0, 2*j+1] := B[j]` is inexpressible, and disjointly so (`baseWritesOverlap`, pinned by `ScanTest.lean`'s fixture at `baseWritesOverlap 0 0 1` and by `ScanCompileTest.lean`'s two `.scan (.baseWritesOverlap "sc2" "dp" 0 1)` assertions [read]). **Decision B**: vacuous, as G9. |
| **G26** | 2 | col 11 × R13, R14 | **OPEN.** Escalation of G20 to the orchestrator: `checkWrites` calls `baseWriteRowsOk` in its `if isBase then` arm as the **sole caller** [read] and adds no strided obligation. **Decision B**: **CLOSED**, cell letter `c`‡ — escalation of G20's decision-B note. `checkWrites` is the site that *throws* `writeGeometryNotAdmitted true wi` on clause 1, so under B it is the catcher rather than a pass-through, and it fires in the base phase. Latent on barrier 1, whose `if isBase then 0` is this very function's own expression — which is why the `‡` matters here more than anywhere: the catcher and the unenforced precondition are the same line of code. |
| **G27** | 2 | col 12 × R13, R14 | **OPEN.** Escalation of G20 to the **public** entry. `checkScanPlan`'s own additions — `advancingDimOutOfRange`, `duplicateAdvancingDim`, `advancingDimCountMismatch`, `advancingSizeMismatch`, `baseBlockContextNotEmpty`, the four policy gates, `stateDtypeNotAdmitted`, the causality loop [read] — **change no cell in these four rows**. `advancingSizeMismatch` in particular relates `stateShape[advancingDims[i]]` to `historyExtents[i]` and says nothing about a strided row's presence, placement, or scale, at either dimension class. So B2-F1's cells reach `checkScanPlan` unchanged, exactly as B1-F2's do. **Decision B**: **CLOSED**, cell letter `c`‡ — escalation of G26's decision-B note. `checkScanPlan` calls `checkWrites sigs raw.baseBlock raw.baseWrites raw.states true` and propagates its `ScanPlanError` unchanged [read], so under B the plan is rejected at the public entry with the located `writeGeometryNotAdmitted true wi`. Still latent rather than absent, on the same barrier 1. |
| G28 | 2 | col 13 × R15, R16 | **Closed** by evidence-carrying construction, in-phase. `CheckedScanPlan` has `private mk ::`, so the only way to obtain one is `checkScanPlan` [read]; a step write carrying a strided row makes `checkWrites` throw `writeGeometryNotAdmitted false wi` (G18), so no checked plan carrying such a row exists and `commitWrite` never receives one in the step phase. The missing docstring bullet is still an obligation — see B2-F3 — but it is a documentation finding, not an unclosed cell. **Decision B**: unchanged. |
| **G29** | 2 | col 13 × R13, R14 | **OPEN — B2-F1.** This is where B2-F1's cells become memory unsafety. `commitWrite`'s own docstring states the premise: it *"does NOT call `inBoundsPerDim` before `flatIndex`: it performs no bounds recovery, trusting `checkScanPlan`"* [read] — and at base, per G20/G22/G24, `checkScanPlan` checked nothing about this row. Worked out rather than argued, on the `dp[0, 2·oc₀, oc₀]` map (`coeffs := #[#[0],#[2],#[1]]`, `bias := #[0,0,0]`) over an output of shape `[3]` against a `[1,3,3]` state: `applyAffine` at `ctx = []` gives `([0,0,0], [0,2,1], [0,4,2])`; `inBoundsPerDim [1,3,3]` gives `(true, true, false)`; and `flatIndex` gives the addresses `(0, 7, 14)` on a **9-element** store [snippet, S20]. Since `commitWrite` calls no `inBoundsPerDim`, that is one correct write, one silent write into a cell belonging to another coordinate, then an out-of-range `Array.set!` — the verbatim F3/F4 failure signature, and strictly worse than B1-F2's `3/7/11`, which at least stayed within one element of the store. Two further arithmetic modes measured at the same site: a `.shift`-flavoured strided row (`bias := #[0,5,0]`) is out of range at **every** coordinate — `applyAffine → [0,5,0]`, `inBoundsPerDim → false`, `flatIndex → 15` [snippet, S20]; and a **negative** offset (`bias := #[0,-2,0]`) is collapsed by `commitWrite`'s own `.map Int.toNat` — `applyAffine → [0,-2,0]`, `inBoundsPerDim → false`, `(…).map Int.toNat → [0,0,0]`, `flatIndex → 0` — so it aliases silently onto the lower boundary **in range**, with no panic to notice it by [snippet, S20]. That third mode is new to this task: B1-F2's advancing row cannot produce a negative coordinate, because its bias is fixed at `1`. **Decision B**: the cell **letter** stays `c` (col 13 is decision-invariant per the `★` legend), but the **status** becomes **CLOSED**, on G28's ground transposed to base: `CheckedScanPlan` has `private mk ::`, so with `checkWrites` throwing on clause 1 no checked plan carrying a strided base row exists and `commitWrite` never receives one. The arithmetic measured above is then unreachable rather than wrong — which is exactly B1-F2's own situation, and exactly why decision B buys latency rather than a bound. |
| G30 | 4 | col 14 × R13–R16 | **Closed** by evidence-carrying construction, extending G15. `runDenseScan` reads state shapes from `c.sigs` — the table `checkScanPlan` validated the plan against — rejects a differing caller table (`signatureContextMismatch`) and a differing store length (`storeArityMismatch`) before allocating [read], and imposes no per-row obligation at all. Nothing in that argument mentions a row kind, so a fourth constructor changes none of it. **Not** offered as a bound on G29: the store-arity check fixes how long the store is, not where within it `commitWrite` writes. **Decision B**: unchanged, letter and status both — `signatureContextMismatch` and `storeArityMismatch` mention no row kind, so the argument is insensitive to which rows a checked plan can carry. |

The 14 groups above account for all 36 new `c` cells: G17 4, G18 4, G19 4, G20 2, G21 2, G22 2,
G23 2, G24 2, G25 2, G26 2, G27 2, G28 2, G29 2, G30 4.

- **7 groups closed, 20 cells**: G17, G18, G21, G23, G25, G28, G30.
- **7 groups open, 16 cells**: G19 4, G20 2, G22 2, G24 2, G26 2, G27 2, G29 2 — all one finding,
  **B2-F1**.

The 8 `▷` cells (cols 9–10 × R13–R16) fall under B1's **G-READ** unchanged: `causalAdvancingRow` and
`stateReadCausal` classify a `ReadPlan`'s coefficient rows, a disjoint vocabulary, and adding a
*write*-row kind changes neither. Worth one sentence because it is not quite symmetric:
`causalAdvancingRow`'s own shape test is `match nz with | [(c, p)] => c == 1 && p == ctxPos && bias ≤ 0
| _ => false` [read], so a **strided read** row (`c ≠ 1`) is already rejected there today, by a
clause that exists and fires. A strided read is therefore not a candidate gap N+1 on the read side —
recorded so the Scatter slice does not go looking for one.

### Finding B2-F1 — the write-geometry defect family recurs for a SIXTH time, LIVE at base

**16 cells: G19 (4), G20 (2), G22 (2), G24 (2), G26 (2), G27 (2), G29 (2).**

Under §B2.1's decision A a strided row is emittable at base, and at base **nothing looks at it**:

- `baseWriteRowsOk` clause 2's `filterMap` **drops** it from the positional cover (G20), while
  clauses 1 and 3 are satisfied by the other rows;
- `freeExtentsAgree` matches only `.free` and passes it at any extents, including a state dimension
  of extent 1 against a stride of 2 (G22);
- `pinnedLiteralsInRange` matches only `.pinned` and passes it likewise (G24);
- `writesCollide`'s catch-all can only over-reject, never bound anything (G25);
- `commitWrite` performs no bounds recovery and computes `scale · out[p] + offset` against a store
  bounded by nothing, reaching flat address **14 on a 9-element store** (G29).

**Why this is the same shape as F3/F4's four instances and B1-F2's fifth**, in the words
`stepWriteRowsOk`'s own docstring uses for the family: *"a geometry predicate that says which rows
MUST be a given kind without saying which rows MAY NOT be"* [read]. Clause 2 says the `.free` rows
must cover `List.range outputShapeSize`; it does not say that no other row may occupy an output
position. A strided row occupies one — in the construction above it shares output position `0` with
the `.free` row at dimension 2 — and is invisible to the cover for exactly the reason an
`.advancing` row at a non-advancing dimension was invisible to `stepWriteRowsOk`'s clause 4 before
F4's third clause was added.

**How it differs from B1-F2, and why that matters more than the similarity.** B1-F2 is *latent*: two
independent barriers hold it up, and B1 recorded that the second disappears when B2 lowers
`Compile.lean`'s base `.affine` arm. B2-F1 is **live from the moment `classifyWriteRow` gains a
non-phase-gated strided branch** — barrier 1 does not apply to it at all (§B2.7). It is therefore not
a thing to record and defer; it is a clause the Scatter slice must write.

**What the fix is, stated as an obligation rather than as code.** `baseWriteRowsOk` needs the
counterpart of `stepWriteRowsOk`'s third clause: a statement of which rows MAY occupy an output
position, so that a strided row is either counted into the cover or rejected. And `freeExtentsAgree`
needs a strided arm computing the extent the row actually spans — which is §B2.4's subject, and the
one place this finding touches the `outExtent` sync contract.

### Finding B2-F3 — four docstrings and one AGENTS.md node enumerate the constructor set exhaustively

B1's G14/B1-F7 established that `commitWrite`'s docstring is a row-by-row soundness argument with
**one bullet per current constructor** — verified again here, at `Scan.lean`'s
`- a \`.free p\` row …` / `- an \`.advancing i\` row …` / `- a \`.pinned lit\` row …`, three bullets
[read, via `grep -n "^    - a \`\.\|^    - an \`\." leanncd/LeanNCD/Eval/Plan/Scan.lean` → lines 544,
548, 558]. A fourth constructor makes that argument **incomplete**, not merely dated: the docstring's
value is that it is exhaustive over the surface.

The same sweep surfaces three further sites in `Scan.lean` whose prose names the constructor set as a
closed list, found with
`grep -n "pinned\`/\`\.free\|free\`/\`\.advancing\|pinned to a literal" leanncd/LeanNCD/Eval/Plan/Scan.lean`
→ 4 hits, lines 6, 95, 108, 109 [read]:

1. **`WriteRowKind`'s own docstring** — *"One recognized shape for a write-map row: pinned to a
   literal, an order-preserving projection of the block's own output slice, or bound to
   `context[p] + 1` (step writes only). Anything else is an unrecognized affine geometry and must be
   rejected."* The final sentence is what a strided constructor contradicts.
2. **`pinnedLiteralsInRange`** — *"`.free`/`.advancing` rows are vacuously fine (their range is
   already bounded by the checked output/context shapes elsewhere)."* Two kinds named; for a strided
   row the clause behaves identically and the sentence says nothing (G23/G24).
3. **`writesCollide`** — *"Since every row is `.pinned`/`.free`/`.advancing`, a dimension forces the
   regions apart only when BOTH writes pin it to DIFFERENT literals."* The premise is a literal
   three-way enumeration; the conclusion survives a fourth constructor (G25 measured it) but the
   stated reason does not.

And one node outside the source: `leanncd/LeanNCD/Eval/AGENTS.md`'s `Scan.lean` row describes the
file as owning the *"write-geometry classifier (`WriteRowKind`/`writeRowKinds`)"* with the
free/pinned/advancing vocabulary threaded through its `freeExtentsAgree` and `pinnedLiteralsInRange`
glosses [read]. A repo-wide sweep for files whose prose carries both `advancing` and `pinned` —
`grep -rln "advancing" --include='*.lean' --include='*.md' leanncd/LeanNCD/ | xargs grep -l "pinned"`
→ 6 files: `Eval/Scan.lean`, `Eval/AGENTS.md`, `Eval/Plan/Scan.lean`, `Eval/Plan/Error.lean`,
`Eval/Plan/Compile.lean`, `DSL/Ast.lean` [read] — is offered as the *located starting set* for the
Scatter slice's doc pass, not as a claim that these are the only affected sites.

### Finding B2-F6 — the minimal strided kind admits a strict subset of the affine LHS forms

`LHSSlot.outExtent` prices a two-axis affine slot (`.affine c0 xs` with `xs.length ≥ 2`) and
`slotsBecomeScatter` routes it to scatter, but `classifyWriteRow`'s `| _ => none` arm cannot classify
its coefficient row under a one-`outputPos` strided payload — measured both ways in §B2.1. So after
the Scatter slice lands, the checked scan backend will admit `Out[2*i]`, `Out[i+3]` and `Out[2*i+3]`
while still rejecting `Out[i+j]`, and the rejection will surface as `writeGeometryNotAdmitted` (a
positional-IR error) rather than as a source-locating capability error, because `checkScanLHSSlot`'s
`.affine` arm will by then have been lifted. **Recorded, not remediated**: whether the strided
payload should be a coefficient *list* rather than a single `outputPos` is a design question for the
Scatter slice, and the cheap alternative — keeping a `CapabilityError` for the multi-axis case at
preflight, where a source locator still exists — is the one this audit would flag if it were asked.

---

## B2.4 — Every strided cell tied to `LHSSlot.outExtent`'s arms

`LHSSlot.outExtent` (`DSL/Ast.lean`) is the single shared scatter-extent formula both
`Eval.scatterOutShape` and `SizeInfer.scatterOutputShapes` must call; a duplicate (`scatterOutDim`,
an upper-envelope `max index + 1`) drifted from it and shipped a soundness bug — a downstream reader
sized to 3 while the evaluator materialized 4 (fix `fc10d70`, duplicate deleted `6a26825`)
[read, `Eval/AGENTS.md` Contracts].

### Which arm is which row kind's image

`LHSSlot.outIdx` is total over all five `LHSSlot` constructors and `IdxExpr` has exactly five
constructors, so `outExtent`'s five arms are exhaustive over its own input [read — both inductives
counted at `DSL/Ast.lean`'s `inductive IdxExpr` and `def LHSSlot.outIdx`]. Measured at
`size(i) = 4`, all six forms in one probe: `(some 4, some 6, some 5, some 7, some 8, some 11)`
[snippet, S21].

| `outExtent` arm | Source slot it comes from | Extent | Checked-plan row kind |
|---|---|---|---|
| `.axis a` → `sz a.uid` | `.free a` / `.freeNorm a` | 4 | **`.free p`** (coeff 1, bias 0) |
| `.const n` → `(n+1).toNat` | `.iterAt a n` | 6 at `n = 5` | **`.pinned n`** (all-zero row, bias `n`) |
| `.shift a 1` → `(s+1).toNat` | `.iterNext a` | 5 | **`.advancing i`** (coeff 1, bias 1) |
| `.shift a c`, `c ≠ 1` → `(s+c).toNat` | `.affine (.shift a c)` | 7 at `c = 3` | **`strided p 1 c`** |
| `.scale c a` → `(c·s).toNat` | `.affine (.scale c a)` | 8 at `c = 2` | **`strided p c 0`** |
| `.affine c0 [(c,a)]` → `(c0 + c·s).toNat` | `.affine (.affine c0 [(c,a)])` | 11 at `c0=3, c=2` | **`strided p c c0`** |
| `.affine c0 xs`, `\|xs\| ≥ 2` | `.affine (.affine c0 xs)` | 7 at `[(1,i),(1,j)]` | **none** — B2-F6 |

So **each of R13–R16 is the checked-plan image of a three-arm family** — `.shift a c` with `c ≠ 1`,
`.scale c a`, and `.affine c0 [(c,a)]` — within which a **given row's `(scale, offset)` payload
selects exactly one arm**: `(1, c)` → `.shift`, `(c, 0)` → `.scale`, `(c, c0)` with `c ≠ 1` and
`c0 ≠ 0` → `.affine`. The row *kind* maps to the family; a row *instance* maps to one arm. The
remaining two arms are already taken: `.axis` is `.free`'s image and `.const` is `.pinned`'s.

**One collision inside the `.shift` arm, measured.** `.iterNext a` and `.affine (.shift a 1)` are the
**same** `outIdx` and therefore the same extent: `(LHSSlot.outIdx (.iterNext axI) ==
LHSSlot.outIdx (.affine (.shift axI 1)), LHSSlot.outExtent (.iterNext axI) sz == LHSSlot.outExtent
(.affine (.shift axI 1)) sz)` → `(true, true)` [snippet, S21]. That is the surface-level sibling of
`classifyWriteRow`'s coefficient-1-with-bias-1 ambiguity (§B2.1 point 4), and it is why the strided
branch's ordering is load-bearing at the row level too: the *same* `outExtent` arm feeds both
`.advancing` and `strided p 1 1`, distinguished only by whether the coefficient lands in the context
half or the output half.

### Would the site CALL the formula, or copy it?

**It could call it, and the obstruction is not the import graph.** Every S21 probe above compiled
under `import LeanNCD.Eval.Plan.Scan` **alone** — B1's S15 imported `LeanNCD.DSL.Ast` explicitly;
`AxisBStridedProbe.lean` does not, and `(LHSSlot.outExtent (.affine (.scale 2 axI)) sz).isSome` →
`true` there [snippet, S22]. `Eval/Plan/Kernel.lean` imports `LeanNCD.DSL.Ast` and `Scan.lean`
reaches it transitively via `Block → Dense → Check → Error → Kernel` [read, each file's `import`
lines].

The real obstruction is the **argument vocabulary**: `outExtent` takes an `LHSSlot` and a
`UID → Option Nat`, and the checked plan is positional and UID-free. A synthetic-`AxisSpec` adapter
closes that gap exactly, measured: with `syntheticAxis` at uid 0 and a lookup returning the block
output's extent 3, `(outExtent (.affine (.scale 2 syntheticAxis)) (synthetic 3),
outExtent (.affine (.shift syntheticAxis 3)) (synthetic 3),
outExtent (.affine (.affine 3 [(2, syntheticAxis)])) (synthetic 3))` → `(some 6, some 6, some 9)`
[snippet, S21] — the numbers `2·3`, `3+3`, `3+2·3`.

**Finding B2-F4 — `freeExtentsAgree`'s equality is the `scale = 1, offset = 0` special case of the
shared formula, and there is no arm supplying the general one.** The clause is
`| some (.free p) => stateShape.getD d 0 == outputShape.getD p 0` [read]. Under the arm mapping above
that is precisely `stateShape[d] == outExtent(.axis a)` with `outputShape[p]` standing in for
`sz a.uid`. The strided generalization is therefore `stateShape[d] == scale · outputShape[p] +
offset`, i.e. equality against the same three arms. Measured that the current clause returns the
**wrong** verdict for the strided numbers: `freeExtentsAgree #[6,3] #[3] #[some (.free 0), some
(.free 0)]` → `false` (the state dimension a stride-2 row needs is 6, and the clause rejects it),
against `freeExtentsAgree #[3,3] #[3] (same rows)` → `true` [snippet, S21].

**The decision this hands the Scatter slice, and the trap in it.** The write-side check can be
either:

- **equality against `outExtent`'s convention** — `stateShape[d] == scale·outputShape[p] + offset`
  (6 for a stride-2 row over a 3-element output), which keeps the write side numerically identical to
  the source side and is therefore drift-free by construction; or
- **the tighter sufficient bound** — `scale·(outputShape[p] - 1) + offset < stateShape[d]` (5 for the
  same row), which is memory-sufficient and **numerically different**.

The second is memory-safe but **is the `scatterOutDim` mistake in miniature**: a second extent
formula, disagreeing with `outExtent` by `scale - 1`, with no import enforcing agreement — exactly
what `Eval/AGENTS.md` warns of (*"no import enforces this beyond both depending on the same function;
a future second formula reintroduces the drift risk"* [read]). **The audit's recommendation is the
first**, via the synthetic-`AxisSpec` adapter measured above, so that `Scan.lean` *calls* the shared
formula rather than restating it. Recorded as a recommendation, not applied.

**One further copy to keep in view.** B1-F6 found `Compile.lean`'s Phase 5 already hand-inlines
`baseWriteRowsOk`'s clause 3 and `pinnedLiteralsInRange` without calling either, and re-implements no
counterpart of `freeExtentsAgree` at all. Whatever extent rule the Scatter slice writes into
`freeExtentsAgree`, the source-facing pass will not see it, and a violation will surface as
`PlanCompileCause.invalidPlan` — which `Eval/AGENTS.md` documents as *"`checkScanPlan` rejected
COMPILER output, which is a compiler bug, not a source problem"* [read], i.e. with no source
locator. That is now **two** formulas away from `outExtent`, not one.

---

## B2.5 — B1-F9 ANSWERED: a zero-extent scatter output is not rejected on the scatter path

B1 measured that `LHSSlot.outExtent` returns `some 0` for four distinct negative affine forms —
`iterAt i (-5)`, `scale (-2) i`, `shift i (-9)`, `affine (-100) [(1,i)]` → `(some 0, some 0, some 0,
some 0)` [snippet, S15] — and deliberately left the question *"is a zero-extent scatter output
rejected further down the scatter path?"* unanswered. **Answer: no, and the negative case is not even
the reachable one.** Both `outExtent` callers were measured, and the answer splits.

### Caller 1 — `Eval.scatterOutShape` → `evalScatter`: NOT rejected, at any point

`scatterOutShape` fails loud only on `none`; its own comment scopes itself to that case (*"An unsized
axis means it is unbound by any read (an upstream sizing gap), so FAIL LOUD rather than defaulting
its size to 0"* [read]), and `some 0` is not that case. Measured, all four negative forms plus the
positive control:

```
scatterOutShape sizesI [ .shift i (-9) / .scale (-2) i / .affine (-100) [(1,i)] / .iterAt i (-5) / .scale 2 i ]
  -> (ok: [0], (ok: [0], (ok: [0], (ok: [0], ok: [8]))))
scatterOutShape sizesI [.free k]   (k unsized)
  -> error: scatterOutShape: unsized axis in scatter output coordinate for slot …free {k}
```

[snippet, S23]. Then through `evalPlain`, which is the real dispatch (`scatterOutShape` followed by
`evalScatter`):

```
S23a (Out[i - 9], extent 0):            evalPlain .ok; Out shape = [0], data = #[]
S23b (Out[-2*i], extent 0):             evalPlain .ok; Out shape = [0], data = #[]
S23c (Out[-100 + i], extent 0):         evalPlain .ok; Out shape = [0], data = #[]
S23d (Out[iterAt i (-5)], extent 0):    evalPlain .ok; Out shape = [0], data = #[]
S23e (Out[2*i], extent 8 — CONTROL):    evalPlain .ok; Out shape = [8], data =
  #[1.000000, 0.000000, 2.000000, 0.000000, 3.000000, 0.000000, 4.000000, 0.000000]
```

[snippet, S23]. **The mechanism is `evalScatter`'s own bounds guard**, `if (outCoordZ.zip
outShape).all (fun (z, d) => 0 ≤ z && z < (d : Int))` [read]: with `d = 0` it is false at every source
coordinate, so every write is skipped by the same rule that exists for genuine overspill
(*"Out-of-range output coordinates are skipped"* [read]). Isolated: `S23f (evalScatter at outShape
[0]): .ok; Out = [0]/#[]` [snippet, S23]. **The collision policy cannot fire either**, because
`.rejectCollisions` is only reached *inside* that guard — four source coordinates all "landing on" a
zero-extent output collide with nothing: `S23g (zero extent + rejectCollisions): .ok; Out = [0]`
[snippet, S23]. And the two gates that *do* still fire are both ordered before the shape is looked
at, so neither helps: `S25a (zero extent + relu): ERROR: evalScatter: non-identity nonlinearity on
scatter Out is unsupported` and `S25b (zero extent + UNSIZED source axis): ERROR: evalScatter:
unsized source axis uid 1` [snippet, S25].

### Caller 2 — `SizeInfer.scatterOutputShapes` → the sizing fixpoint: rejected, but only if READ

`scatterOutputShapes` publishes `some dims` and drops only `none`, so a zero dimension becomes a
downstream-readable shape: `((scatterOutputShapes sizesI [negShift])["Out"]?,
(… [control])["Out"]?, (… [unsizedAxis])["Out"]?)` → `(some [0], some [8], none)` [snippet, S24].
When something reads it, the solver **does** fail loud:

```
S24a (zero-extent scatter out, read downstream): inferAxisSizes ERROR: affine size system
  non-positive (uid 2) (value=0, reduced row=0, col=0); sources: [Out[…axis k] (scatter-out)];
  actions: [increase effective input extent or reduce negative shifts, ensure inferred output
  window size stays strictly positive]; ml-hints: [ml-hint: offset/window yields non-positive extent]
S24b (extent-8 scatter out, read downstream — CONTROL): .ok; i = some 4, k = some 8, warnings = 0
```

[snippet, S24] — `SolveFailureKind.nonPositive`, with remediation text that names the cause
correctly. **But the diagnostic blames the reader, not the writer**: `uid 2` is the *downstream* axis
`k`, and the source list names `Out[axis k] (scatter-out)`. The zero-coefficient or negative-offset
slot that produced the extent is one statement away and unmentioned.

### The case that is actually reachable from surface syntax is a ZERO coefficient, and it is LIVE

`DSL/Elab.lean`'s `elabTLLHSSlot` has four affine arms, and **no** arm can produce a negative
coefficient or offset, by two distinct mechanisms [read]:

- three arms — `$n * $x + $m`, `$n * $x`, `$x + $n` — build every coefficient and offset as
  `Int.ofNat n.getNat` from a `num` literal, so the value is a natural number cast to `Int`;
- the fourth, `$x +1`, is **stronger still**: it does not read a `num` at all but returns
  `.affine (.shift (idxAxis (identStr x)) 1)`, i.e. the literal `1` **hardcoded** in the arm body,
  so the sign is fixed by the source text rather than by a cast.

`.iterAt` (the `$n:num` arm) likewise uses `Int.ofNat n.getNat`. **So none of the four negative forms
B1 measured is surface-reachable** — they require a programmatic `Stmt`, as B1's S15 and this task's
S23 both used. A **zero** coefficient is a different matter, reachable through the two `$n * $x…`
arms, and `outExtent`'s `.scale` arm then yields `(0 · s).toNat = 0`. Measured end-to-end through
`tlprog!{ … }` and `TLProgram.eval`:

```
S26a (Out[0*i] := X[i]):                  eval .ok; Out shape = [0], data = #[]
S26b (Out[0*i + 0] := X[i]):              eval .ok; Out shape = [0], data = #[]
S26c (Out[2*i] := X[i] — CONTROL):        eval .ok; Out shape = [8], data =
  #[1.000000, 0.000000, 2.000000, 0.000000, 3.000000, 0.000000, 4.000000, 0.000000]
  (slots: [[LHSSlot.affine (IdxExpr.scale 0 {i})]] and [[LHSSlot.affine (IdxExpr.scale 2 {i})]])
S26d (Out[0*i], then Y[k] := Out[k]):     eval FAILED: affine size system non-positive (uid 2) …
S26e (Out[2*i], then Y[k] := Out[k]):     eval .ok; Out = some [8], Y = some [8]
```

[snippet, S26]. So `Out[0*i] := X[i]` — four words of ordinary surface syntax, with `axis i : ℕ = 4`
— compiles, evaluates `.ok`, and returns an **empty** `Out` with all four writes silently dropped and
no diagnostic. That is **live at `9680b92`**, not latent.

### Verdict on B1-F9

**Not rejected on the scatter path.** The rejection that exists lives in the *sizing solver*, fires
only when the zero-extent output is read downstream, and attributes the failure to the reader's axis.
A zero-extent scatter output that is a program's final output evaluates `.ok` to an empty tensor with
every write dropped. Reachable from surface syntax via a zero coefficient (S26a/S26b), and from a
programmatic `Stmt` via any of B1's four negative forms (S23a–S23d).

**Cell status.** B1 recorded `outExtent` as a `c` cell outside the 14-column grid; it stays outside
the grid and is now **adjudicated rather than flagged**: `c`, **not closed**, because the catcher
(the solver's `nonPositive`) fires in only one of the two consumer paths and never in `evalScatter`
itself — the same disqualification G22/G24 face. It is not a write-path cell of the scan surface, so
it is not part of B2-F1's 16.

**Scope note, so this is not read as more than it is.** The checked-plan backend does not see a
scatter at all today: `Compile.lean` throws `scatterOrAffineLhs` at three sites and
`checkScanLHSSlot` rejects `.affine` in every scan-block statement [read]. Every measurement above is
of the **legacy** evaluator. What makes it Task B2's business is that the Scatter slice is precisely
what carries `.affine` into the checked backend, at which point `outExtent`'s `some 0` becomes a
checked-plan `outputShape` dimension and a strided row's `scale = 0` degenerate case reaches
`classifyWriteRow` — where a zero coefficient is not a singleton nonzero at all and classifies as
`.pinned bias`, which is the `.const` arm's image, not the strided one. That reclassification is
worth a fixture and is named in §B2.6.

---

## B2.6 — B1-F10 ANSWERED: the negative coverage the Scatter slice must add first

B1-F10's baseline reproduces exactly. Commands, run from `leanncd/`:

```text
grep -rn "#guard.*baseWriteRowsOk\|#guard.*stepWriteRowsOk" test/       → 5 hits, all in
                                                                          test/Eval/Plan/ScanTest.lean
grep -rn "#guard *!.*WriteRowsOk\|#guard *¬.*WriteRowsOk" test/         → 0 hits
grep -rn "baseWriteRowsOk\|stepWriteRowsOk" test/ | grep -i false       → 0 hits
grep -rn "writeGeometryNotAdmitted" test/                               → 3 assertions, all
                                                                          `.writeGeometryNotAdmitted false 0`
```

[read]. So: all five geometry `#guard`s are acceptances, there is no negated `#guard` and no
`== false` on either predicate, and every plan-level `writeGeometryNotAdmitted` assertion carries
`isBase = false` — **zero base-phase geometry-admission fixtures**, which is the phase B2-F1 lives in.

One sharpening, so B1-F10 is not read wider than it is: the *value*-predicate siblings **do** have
base-phase negative fixtures — `writeFreeExtentMismatch true 0 0 #[2,2] #[5]`,
`writePinnedLiteralOutOfRange true 1 0 #[2,2]` and `baseWritesOverlap 0 0 1` in `ScanTest.lean`, plus
two `.scan (.baseWritesOverlap "sc2" "dp" 0 1)` assertions in `ScanCompileTest.lean`
[read, `grep -rn "writeFreeExtentMismatch\|writePinnedLiteralOutOfRange\|baseWritesOverlap" test/`].
The gap is specific to **geometry admission** at base.

### Finding B2-F5 — the 6 new `b` cells are not locatable by any test that could exist today

R15 and R16 across columns 5, 11 and 12 are `b` on `stepWriteRowsOk`'s clauses 2 and 3, and **no test
can locate them at `9680b92`**, because the constructor they classify does not exist: there is no way
to write `#guard stepWriteRowsOk … #[some (.strided …)] == false`, and no source program can produce
such a row while `checkScanLHSSlot` rejects `.affine`. This is a different status from B1-F10's 10
unlocated cells (which *could* be pinned today and simply are not), and it is why these six are
counted separately in §B1.5's updated gate line.

### The negative coverage to add BEFORE touching `stepWriteRowsOk`'s clause 2

Named, not written — the brief's instruction. Ordered so that each item is a prerequisite of the
next, and each names the assertion it must make.

**Tier 1 — predicate-level `#guard`s, the first negative `#guard`s either predicate has ever had.**
These are the ones that must exist *before* clause 2 is edited, because they are what would catch a
clause-2 edit that widens acceptance:

1. `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.strided 0 2 0), some (.free 0)] == false`
   — a strided row at a **non-advancing** dimension, rejected by clause 3 (R16).
2. `stepWriteRowsOk #[0,1] 1 #[some (.strided 0 2 0), some (.advancing 1), some (.free 0)] == false`
   — a strided row at an **advancing** dimension, rejected by clause 2 (R15).
3. `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0), some (.strided 0 2 0)] == false`
   — a strided row at the **cover** position, i.e. where clause 4's `filterMap` would silently drop
   it; asserts the rejection comes from clause 3 rather than from an accidental cover mismatch.
4. **The three positive controls those three would otherwise pass vacuously**:
   `stepWriteRowsOk #[0] 1 #[some (.advancing 0), some (.free 0)]`,
   `stepWriteRowsOk #[0,1] 1 #[some (.advancing 0), some (.advancing 1), some (.free 0)]`, and one
   acceptance of whatever strided placement the slice *does* admit at step, if any.
5. **Retrofit for B1-F10's own 10 unlocated cells while the file is open**, since they need no new
   constructor: `stepWriteRowsOk #[0] 1 #[some (.pinned 0), some (.free 0)] == false` (R3) and
   `stepWriteRowsOk #[0] 1 #[some (.free 0), some (.free 1)] == false` (R7), currently evidenced only
   by B1's S3.

**Tier 2 — base-phase geometry-admission fixtures, the family with zero members.** Each asserts
`checkScanPlan` returns `.writeGeometryNotAdmitted true wi` — the `isBase = true` form no fixture
carries:

6. A base write carrying a strided row that the slice's `baseWriteRowsOk` clause **rejects**
   (whichever way B2-F1 is fixed). This is the fixture that pins the fix.
7. **The acceptance control it needs**: the same base write with the strided row's extent agreeing
   with the state dimension per §B2.4's formula — `checkScanPlan .ok`, and `runDenseScan` producing
   the *stride-spaced* data, not merely `.ok`. Without a data assertion this fixture cannot
   distinguish "wrote the right cells" from "skipped every write", which is exactly the failure mode
   B2.5 found on the legacy scatter path.
8. A base write whose strided row's extent **disagrees** — asserting
   `writeFreeExtentMismatch true …`, joining the existing base-phase fixture for the `.free` case.
9. A base write whose strided row's coordinate would leave the state dimension at some coordinate but
   not at coordinate 0 — the `(0, 7, 14)` shape of G29. Its point is that a fixture asserting only
   the *first* coordinate lands in bounds would pass a broken clause.
10. A **negative-offset** strided base row, asserting rejection rather than the silent
    `Int.toNat` collapse onto the lower boundary that G29 measured. This one has no `.free`/
    `.advancing` analogue anywhere, because neither kind can produce a negative coordinate.

**Tier 3 — the two boundary cases §B2.1 and §B2.5 turned up, each a one-line assertion:**

11. `scale = 0` reclassification: a strided-shaped row with coefficient `0` is **not** a singleton
    nonzero and classifies as `.pinned bias` (the `.const` arm's image). Assert that, so a future
    strided branch cannot quietly claim it.
12. `scale = 1, offset = 1` at a **context** position stays `.advancing`, and at an **output**
    position becomes strided — the ordering obligation of §B2.1 point 4, and the one assertion that
    would fail if the strided branch were placed before the advancing branch.

**Tier 4 — differential, not predicate-level.** `test/Eval/Plan/DifferentialTest.lean`'s
`scanParityCheck` and `test/Eval/PropertyOracle/ScanUnroll.lean`'s `independentRun` are the
three-way gate, and `ScanUnroll.lean` *deliberately* calls no `writeRowKinds`/`applyAffine`/scan-write
helper (plan §4.8) [read]. A strided base write must be added to the oracle's own rewrite by hand for
the third leg to stay a differential — noting it here because it is the item most likely to be
skipped, and skipping it silently converts a three-way gate into a two-way one.

---

## B2.7 — Where barrier 2 disappears, and what barrier 1 alone does NOT cover

B1 established two independent barriers holding the `.advancing`-at-base case latent, and recorded
that the second disappears when B2 lowers `Compile.lean`'s base `.affine` arm. Both halves confirmed
here, and the conclusion for a **strided** row is different from the conclusion for an advancing one.

**Barrier 2, re-read and confirmed.** `Compile.lean`'s base-write construction loop emits exactly two
row shapes — an all-zero coefficient row with the literal as bias, from `.iterAt _ lit`; and a single
`1` at position `freeSeen` with bias `0`, from `.free`/`.freeNorm` — with the remaining arm
`| .iterNext _ | .affine _ =>` throwing `CapabilityError.unsupportedLhsSlot` [read]. The step loop's
catch-all is the differently-shaped `| .iterAt .. | .affine _ =>`, same throw [read]. **Lowering the
base loop's `.affine` arm is exactly what the Scatter feature must do, and it is what removes
barrier 2.**

**A third barrier B1's case did not have.** For a strided row there is also a **preflight** barrier:
`checkScanLHSSlot`'s `| .affine _ => throw (.scatterOrAffineLhs s!"{stmtName}: affine LHS slot")`
rejects an affine LHS slot in *every* base and recurrence statement of an admitted `.scan`, before
sizes exist [read]. Call it barrier 0. It is not a barrier for B1-F2, because `.iterNext` and
`.iterAt` are both *admitted* at preflight — so B1's "two independent barriers" is correct for its own
case and is not being corrected here. But the Scatter slice must lift barrier 0 **and** barrier 2 to
lower an affine LHS write at all, and lifting barrier 0 is also what turns B2-F6's multi-axis
rejection from a source-locating capability error into a positional `writeGeometryNotAdmitted`.

**What barrier 1 alone then covers, and what it does not.** First a correction to how B1 and §B2.1
describe it: **barrier 1 is two sites, not one expression.**

1. `checkWrites`' `let contextWidth := if isBase then 0 else st.advancingDims.size` [read] — the
   internal checker, governing **every** plan, hand-built or compiled.
2. **`Compile.lean`'s Phase 5 source-facing pass, which hard-codes the same `0` twice** —
   `let rows := writeRowKinds stateShape.size 0 w` in the base-boundary loop and
   `writeRowKinds stateShape.size 0 w` in the base-collision `mine` builder [read]. B1-F6 recorded
   these two literal `0`s; what §B2.1 and §B2.4 did not say is that they are barrier 1's *second*
   site, so the barrier's contract is asserted in two files.

Site 2 is **equally no defence for a strided row under decision A**, and for a second reason beyond
the polarity argument below: Phase 5's hand-inlined pinned-literal check is
`match rows[d] with | some (.pinned lit) => … | _ => pure ()` [read], whose `| _ => pure ()` arm is
**constructor-blind** in exactly the way `pinnedLiteralsInRange`'s `| _ => true` is (G24). Its
`baseWriteNotAtBoundary` guard is satisfied by whichever other row carries `.pinned 0`, and
`writesCollide` can only over-reject (G25). So under decision A a strided base row passes the
**source-facing** pass silently too — which matters because that pass exists precisely to produce a
source locator, and B1-F6 already recorded that its absence surfaces as
`PlanCompileCause.invalidPlan`, documented as *"a compiler bug, not a source problem"*.

Barrier 1's whole force, at either site, is that it makes a `p < contextWidth` test unsatisfiable,
since no `p : Nat` is `< 0`. Therefore:

- **It covers exactly the `.advancing` kind** — the only current branch of `classifyWriteRow` whose
  guard is `p < contextWidth`. Measured by B1: `(classifyWriteRow 0 #[1] 1, classifyWriteRow 0 #[1,0]
  1, classifyWriteRow 0 #[0,1] 1)` → `(none, none, none)` [snippet, S1].
- **It does not cover a strided row at all**, under §B2.1's decision A. The strided guard is
  `p ≥ contextWidth`, which at `contextWidth = 0` is *satisfied by every* `p` — the opposite polarity.
  Barrier 1 is not a weakened defence for B2-F1; it is **no defence**. Measured on the model:
  `classifyA 0 #[2] 0` → `some (.strided 0 2 0)`, and the resulting rows pass `baseWriteRowsOk`
  [snippet, model].
- **It does not cover a `.free` row at an advancing dimension either** — B1-F4, live and memory-safe
  today, independent of any of this.

So after the Scatter slice lands, the base-phase picture is: `.advancing` stays latent behind barrier
1 alone (B1-F2, 10 cells, the *"single `if isBase then 0`"* B1 warned becomes the whole defence);
`.free` at an advancing dimension stays live-and-safe (B1-F4, 5 cells); and **strided becomes live
and unsafe with no barrier of any kind** (B2-F1, 16 cells). The three are independent, and only the
third is created by the feature.

---

## B2.8 — Gate, over the appended rows

> Every forbidden cell needs a located test. No cell may be silently ignored.

- **6 new `b` cells** (R15, R16 × cols 5, 11, 12): **0 located, and 0 locatable at `9680b92`** — the
  `strided` constructor they classify does not exist, so no `#guard` and no plan fixture can name
  them (B2-F5). §B2.6 items 1–4 are the tests that must exist the moment it does. Combined with B1's
  16: **22 `b` cells — 6 located by repo fixtures, 10 located only by B1's spikes, 6 not locatable.**
- **36 new `c` cells**: all adjudicated in §B2.3 across 14 groups — **7 groups / 20 cells closed**
  (structurally, by an **in-phase** catcher whose clause is quoted, by evidence-carrying
  construction, or as conservative-and-measured) and **7 groups / 16 cells open**, collapsing to one
  finding, **B2-F1**. No `c` cell was softened to "unlikely" or "defensive"; no write-path cell was
  closed as backstopped by `gatherFactor`'s `inBoundsPerDim`; and no cell was closed by naming a
  catcher that cannot fire in its own phase — every closure whose catcher is `stepWriteRowsOk` is a
  step-phase group, and the two base-phase value-predicate groups (G22, G24) are **open** for exactly
  the reason G16 was reopened.
- **0 new `a` cells** — B2-F2, a finding in its own right.
- **Findings outside the cell grid**: **B2-F2** (no site requires a strided row), **B2-F3** (four
  docstrings plus one AGENTS.md node enumerate the constructor set exhaustively and go stale),
  **B2-F4** (`freeExtentsAgree`'s equality is the shared formula's `scale=1, offset=0` case, and the
  tempting tighter bound is the `scatterOutDim` drift shape), **B2-F5** (6 `b` cells not locatable),
  **B2-F6** (the minimal strided kind admits a strict subset of the affine LHS forms `outExtent`
  prices). Plus two inherited findings **answered**: **B1-F9** (§B2.5 — not rejected on the scatter
  path; live from surface syntax via a zero coefficient) and **B1-F10** (§B2.6 — the negative
  coverage named, in four tiers).

Every verdict above carries either a quoted clause from the code, a construction with verbatim
observed output, or — where a fourth constructor was unavoidable — a `[snippet, model]` observation
against a verbatim transcription. Of those model observations, all but **two** are paired with a
`[snippet]` measurement of the real clause; the two exceptions (G17's derived-`BEq` result and
§B2.1 point 3's context-half row) are enumerated at the top of §B2 with the source reading that
re-derives each, and neither carries a verdict. The one claim that is **not** a measurement at all
is §B2.1's scope assumption, and it is labelled as such there.

