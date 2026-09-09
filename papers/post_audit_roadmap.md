# Post-audit roadmap — hardening, Scatter, and the binding surface

Successor to `pre_scatter_backend_audit.md`. That document says what is wrong; this one says what to
do about it, in what order, and who should do which parts.

## Contents

- [How this document is scoped](#how-this-document-is-scoped)
- [Section 0 — DECIDED: Decision A (base and step)](#section-0--decided-decision-a-base-and-step)
- [Section A — Slice 1: write-geometry hardening (implementable now)](#section-a--slice-1-write-geometry-hardening-implementable-now)
- [Section B — Slice 2: Scatter + affine LHS writes (scoped, not detailed)](#section-b--slice-2-scatter--affine-lhs-writes-scoped-not-detailed)
- [Section C — the binding surface (independent of Scatter)](#section-c--the-binding-surface-independent-of-scatter)
- [Section D — work carved out for external (GPT) execution](#section-d--work-carved-out-for-external-gpt-execution)
- [Section E — simplification and dead-code opportunities](#section-e--simplification-and-dead-code-opportunities)
- [Section F — deliberately not in this roadmap](#section-f--deliberately-not-in-this-roadmap)

## How this document is scoped

The root `CLAUDE.md` Rule 13 says **one implementation plan per slice, not one spanning several**,
and to write the next slice's plan only once the previous has landed. This document was requested as
a plan for all the next steps, which is in tension with that rule. The resolution:

- **Section A is a real implementation plan.** It is specified to the standard of
  `.claude/skills/slice-plan/`, and can be executed as-is.
- **Sections B and C are scoped, not detailed**, on purpose. Slice 2's task list is *not derivable
  today*: it depended on Section 0's decision (now settled — Decision A) and still depends on the
  compile errors Slice 1's tripwire produces —
  which are the actual work list and do not exist yet. Writing tasks against them now would be
  invention, and invented plan detail is what the audit spent three fix rounds correcting.
- **When Slice 1 lands, Section B gets promoted into its own plan document**, authored from the
  compile-error list rather than from this prose.

**Provenance of the claims below.** Every count, site, and code claim in this document was
**re-measured against `main` at `89cd767` while authoring it**, not restated from the audit. Two
counts were re-derived and matched exactly (five geometry `#guard`s; three
`writeGeometryNotAdmitted` assertions, all `false 0`); the `Compile.lean` duplication, the
`PlanBindings` non-use, and the `splitStmt` off-chain status were each re-verified by grep. This
matters because the slice-plan skill's most-repeated failure is a plan restating an inherited claim
instead of re-measuring it.

**This document ships no Lean code blocks, deliberately.** The skill's first rule is that every Lean
block in a plan must be compiled before it ships, and its cited failures are all plans that shipped
plausible-but-uncompilable code. Slice 1's changes are mechanical enumerations over a behaviour table
that is better specified *as a table*; the implementer writes the Lean and compiles it. The
`check-snippet.sh` obligation therefore sits with the implementer, and Section A says so explicitly.

## Section 0 — DECIDED: Decision A (base and step)

### What the question actually was

**Within a checked scan, may a strided write row appear in the `base` (initialization) block, or only
in the `step` (recurrence) block?**

This is **scan-scoped**, and an earlier draft of this section did not say so — worth stating plainly
because the narrower reading changes how limiting the alternative looks. `writeRowKinds` has exactly
three call sites, all scan machinery (`Scan.lean`'s `checkWrites`, and `Compile.lean`'s Phase 5
scan-plan construction), and it operates on a `StateWriteMap` — a write into *scan state*. "Base" and
"step" are a scan's two blocks, not two halves of scatter in general.

**What the decision was never about:** whether the backend admits a plain top-level `Out[2*i] = …`.
That path is gated by its own `scatterOrAffineLhs` throw sites in `Compile.lean` (seven of them,
re-counted while authoring), and Slice 2 must open it under either decision. Neither option
restricted it.

### The decision, and why

**Decision A: strided rows are admitted in both the base and step blocks of a scan.**

Rationale, recorded for whoever reads this after the fact:

- **Excluding base is an arbitrary boundary.** "Affine LHS writes, except when initializing" is not a
  natural restriction to bake into a capability surface.
- **The use cases are real.** A strided base write initialises every *k*-th slot and leaves the rest
  at the zero-fill `zeroThenBaseOverlay` already guarantees: upsample-then-recur (seed even
  positions, let the recurrence fill the odd ones); interleaving two streams into one state at
  alternating offsets; dilated/strided convolution state seeding; coarse-to-fine boundary conditions.
  Under decision B each of these has to seed densely and push the striding into the recurrence —
  sometimes fine, sometimes contorted.
- **The cost was accepted knowingly**, see below.

Decision B was the conservative, reversible option — ship step-only, admit base later, with
`pre_scatter_backend_audit.md` §B2.3's decision-B reading for all fourteen groups G17–G30 making the
switch a re-read rather than a re-analysis. It was rejected because the asymmetry is not worth
carrying and because the hardening that makes A safe is work worth doing regardless.

### What Decision A costs — and the consequence for sequencing

| | Under Decision A |
|---|---|
| `B2-F1` | **16 live, unsafe cells** — not latent |
| Table census | `24 a / 22 b / 122 c` (the audit's headline figures) |
| Slice 2 scope | both lowering arms — a base arm *and* a step arm |
| Barrier 1 | **no defence at all** — the strided guard has the opposite polarity (`p ≥ contextWidth`), satisfied by every `p` when `contextWidth = 0` |

**Therefore Slice 1 is a blocking prerequisite for Slice 2, not a parallel nicety.** Under decision B
it would have been prudent; under decision A the 16 cells of `B2-F1` must actually be *closed*, not
documented, and there is no barrier left to fall back on. Section A's status is promoted accordingly.

## Section A — Slice 1: write-geometry hardening (implementable now)

**Status: BLOCKING PREREQUISITE for Slice 2**, promoted from "prudent" once Section 0 settled on
Decision A. Under Decision A `B2-F1`'s 16 cells are live and barrier 1 provides no fallback, so this
slice is what makes Scatter safe rather than merely tidier.

**Goal.** Make the write-geometry surface fail loudly when a new row kind is added, and give it tests
that can fail — *before* Scatter extends it. No new capability; no behaviour change except where a
test is added.

**Why before Scatter, not with it.** An earlier draft of this recommendation said to remove the
catch-alls *when* the constructor arrives. That was wrong and is revised here: done first, this is a
behaviour-preserving refactor the existing suite proves, and it installs the tripwire so Scatter's
constructor addition produces compile errors instead of silence. Done simultaneously, the compile
errors appear inside a larger diff and cannot be separated from the new-kind work. Bundling of
exactly this shape is what made the Boolean/predicate slice cost six review rounds.

### Global constraints

- **Build stays green at exactly 8660 jobs** (`cd leanncd && "$HOME/.elan/bin/lake" build`). Any
  other number must be explained, not asserted.
- **No behaviour change in Tasks 1 and 3.** The existing suite is the oracle: it must pass unchanged,
  before and after.
- **No `strided` constructor is COMMITTED in this slice.** That is Slice 2's.
  ⚠️ **Corrected mechanism (an earlier draft of this constraint named an impossible one).** Task 1's
  tripwire proof does need a fourth constructor temporarily, but it cannot live in a throwaway
  `leanncd/spikes/` file: **Lean inductives cannot be reopened from another module**, so no spike can
  add a constructor to `WriteRowKind`. The real method is **in-place mutation of
  `Eval/Plan/Scan.lean` itself** — add the constructor, rebuild, capture the error list verbatim,
  revert, and *verify* the revert (`shasum` against a pre-recorded manifest, plus
  `git grep -i strided` clean) before doing anything else. `leanncd/scripts/mutation-cycle.sh` is
  built for exactly this shape and fails the cycle if restoration does not verify; prefer it to a
  hand mutate/restore, which is how a mutation gets left in the tree.
- **No line numbers in shipped text** — completion records, `AGENTS.md` rows and doc comments cite
  identifiers only. A later commit in the same slice invalidates line references.
- Every Lean snippet the implementer writes is compiled via
  `bash .claude/skills/slice-plan/check-snippet.sh` before it goes in a commit.
- The twelve tracked spikes under `leanncd/spikes/` are **evidence, not scratch** — they must still
  reproduce byte-identically against their `.output.txt` at the end of the slice. Nothing in CI
  compiles them, so this is a manual gate.

### Task 1 — the exhaustiveness tripwire

Replace every catch-all in the write-geometry predicates with arms explicit over
`WriteRowKind`'s three constructors and `Option`'s `none`, preserving today's result in every case.

**Sites** (named by identifier, per the constraint above), all in `Eval/Plan/Scan.lean`:

| Predicate | Catch-all today | Preserve |
|---|---|---|
| `classifyWriteRow` | `| _ => none` (multi-nonzero / non-unit coefficient) | `none` |
| `baseWriteRowsOk` | cover `filterMap`'s `| _ => none` | drop from cover |
| `stepWriteRowsOk` | clause 3's `| _ => false`, and cover `filterMap`'s `| _ => none` | as today |
| `freeExtentsAgree` | `| _ => true` | `true` for `.pinned`/`.advancing`/`none` |
| `pinnedLiteralsInRange` | `| _ => true` | `true` for `.free`/`.advancing`/`none` |
| `writesCollide` | `| _, _ => false` | `false` |
| `causalAdvancingRow` | `| _ => false` | `false` |

`pre_scatter_backend_audit.md`'s 224-cell table is the authority for what each arm's value must be —
**this task consumes that table, it does not rebuild it.** (The slice-plan skill requires a
case × class table as a deliverable when fixing instance *N* of a recurring defect family; here the
audit already produced it over the full predicate surface, which is why this task is small.)

**The deliverable that matters is not the refactor — it is the proof the tripwire works.** Add a
fourth `WriteRowKind` constructor **in place in `Eval/Plan/Scan.lean`** (a spike cannot do it — see
the corrected constraint above), rebuild, record the failing sites verbatim, and revert.

⚠️ **Expected: five of the seven rows above, not all seven.** An earlier draft of this task said
"every site in the table above", which is wrong for two rows and would have reported a missed
catch-all where none exists. `classifyWriteRow` and `causalAdvancingRow` scrutinise
`nz : List (Int × Nat)`, **not** a `WriteRowKind`, and Lean imposes no exhaustiveness obligation on a
function's **range** — so neither can ever be tripwired, however its arms are written. Concretely the
build reports **six errors over five rows**: `baseWriteRowsOk`'s cover, *both* of
`stepWriteRowsOk`'s non-advancing clauses, `freeExtentsAgree`, `pinnedLiteralsInRange`, and
`writesCollide`. **Any of those six that still compiles is a catch-all that was missed, and is the
finding.** The two un-tripwirable rows convert into a *documentation* obligation at the type
(`WriteRowKind`'s own docstring must say that a new kind has to be admitted in `classifyWriteRow`
deliberately, because nothing will remind you) — not a compile error to hunt for.

- **Files:** `leanncd/LeanNCD/Eval/Plan/Scan.lean` only — the mutation is applied to and reverted in
  that same file, and no new file is created.
- **Risk:** low-moderate. **0 new fixtures, 1 mutation cycle** (the fourth-constructor proof). The
  cost is in the mutation cycle and the rebuild, not the diff.
- **Rollback unit:** yes — independently revertible.

### Task 2 — the negative coverage that does not exist

This is the slice's real work, and `B1-F10` is why: **re-measured on `main` at `89cd767`**, there are
exactly **five** `#guard`s exercising `baseWriteRowsOk`/`stepWriteRowsOk` in the whole suite, **all
five are positive acceptances**, none is negated, and there are exactly **three**
`writeGeometryNotAdmitted` assertions, **all of them `false 0`** — the `false` being the `isBase`
flag. So **no base-phase geometry rejection is pinned anywhere.** One existing guard even asserts
that an out-of-range pinned point *is* admitted, documenting the gap rather than closing it.

> **⚠️ SUPERSEDED BASELINE — Slice 1 has landed and closed it.** The paragraph above is the premise
> the task was written against and is left intact for that reason, but it no longer describes the
> tree. Re-measured after Slice 1: **14** `#guard`s exercise `baseWriteRowsOk`/`stepWriteRowsOk`, of
> which **9 are negations** (`== false`), plus **3** negative guards on the `classifyWriteRow`
> chokepoint upstream of both — 12 negative assertions where there were none. And there are now
> **6** plan-level `writeGeometryNotAdmitted` assertions, three `isBase = false` and three
> `isBase = true` (`true 0`, `true 0`, `true 1`), so the base-phase locator is pinned in both
> directions. Do not quote the pre-slice figures as current; `pre_scatter_backend_audit.md`'s
> `B1-F10` carries the same stale measurement and now has a superseding banner of its own.

Add the Tier 1 coverage named in `pre_scatter_backend_audit.md` §B2.6.

> **⚠️ THE FOUR-FIXTURE TABLE BELOW IS DEFECTIVE — corrected here, and superseded by what Slice 1
> actually built.** Two of its four rows cannot be built as written and a third asks for coverage
> that already existed; the table is retained only so the corrections have something to point at.
> Row by row:
>
> 1. *base-phase geometry rejection, assert `true 0`* — **sound, and landed three times over**, one
>    per clause of `baseWriteRowsOk`, reached through `checkScanPlan`: `true 0`, `true 0`, `true 1`.
>    All three clauses turned out to be plan-level constructible, because nothing upstream of the
>    geometry check inspects a coefficient row's WIDTH.
> 2. *`.advancing` row rejected at base, from `pointRows`* — **not constructible through the
>    compiler's own path.** `checkWrites` sets `contextWidth := 0` for a base write and
>    `classifyWriteRow`'s `.advancing` arm requires `p < contextWidth`, which no `p : Nat` satisfies,
>    so no base-phase row `writeRowKinds` can produce is ever `.advancing` (this is the audit's
>    barrier 1). Slice 1 pinned that clause with a reachable row instead — a non-unit coefficient,
>    which `classifyWriteRow` refuses — and hand-assembled rows arrays only where the point is the
>    row *sequence*, each kind in them one a base write can really produce.
> 3. *out-of-range pinned literal rejected at base, "flip the existing acceptance"* — **this
>    instruction would have asserted something FALSE.** `baseWriteRowsOk` is *correct* to admit an
>    out-of-range pinned point: geometry admission recognises a row as `.pinned lit` without ever
>    looking at `lit`'s value, and range-checking is `pinnedLiteralsInRange`'s job, already pinned by
>    its own negative guards (including the negative-literal case). The existing acceptance guard
>    documents that division of labour and **must stay green**. Flipping it would have made the suite
>    assert the opposite of the design.
> 4. *free-extent disagreement at base, from `faceRows`* — **already existed at `89cd767`**, verbatim
>    and with the exact donor named: `#guard freeExtentsAgree #[2,2] #[5] faceRows == false`. Nothing
>    to add. (`freeExtentsAgree` is also a separate check from the two geometry predicates this task
>    is about, so it was never part of the gap the opening paragraph measures.)
>
> **What replaced the table:** one negated guard per clause of *both* predicates — three for
> `baseWriteRowsOk`, four for `stepWriteRowsOk`, plus an order-half and a position-swap guard — three
> `classifyWriteRow` chokepoint guards, three plan-level base-phase rejections, and a frozen
> `stepWriteRowsOkNoClause1` oracle with a 588-case agreement check for the one clause no fixture can
> isolate. Broader than four fixtures, and derived from the clause structure rather than from a
> selected list.

Each fixture below names its donor, so the implementer clones rather than rediscovers — but read the
correction above before cloning any of them:

| Fixture | Donor | Change |
|---|---|---|
| base-phase geometry rejection | the `writeGeometryNotAdmitted false 0` assertion in `ScanTest.lean` | assert `true 0` — a base write, not a step write |
| `.advancing` row rejected at base | `pointRows` (`ScanTest.lean`) | one row `.pinned 0` → `.advancing 0` |
| out-of-range pinned literal rejected at base | `outOfRangePointRows` | flip the existing acceptance to the rejection it should be, at base |
| free-extent disagreement at base | `faceRows` | widen the free face past the state's own dimension |

**Every one of these must be mutation-tested**: break the predicate it targets, confirm the fixture
fails, restore, confirm it passes. Record both observations. A fixture that passes either way reports
safety it does not provide — the failure mode the skill names for `C1`'s parity fixtures.

**A warning specific to this task.** `B1-F10`'s subject is partly a *locator* requirement (`isBase`
being `true` rather than `false`). Per the skill, a locator requirement is invisible to every
value-comparing test: an `isBase` flag flip changes no accept/reject verdict and no computed value.
**The first fixture above is the one that pins it**, and its construction must actually distinguish
the two readings — a fixture whose write is admissible at both phases pins nothing.

- **Files:** `leanncd/test/Eval/Plan/ScanTest.lean` (primary),
  `leanncd/test/Eval/Plan/ScanCompileTest.lean` if a plan-level leg is needed.
- **Risk:** **highest in the slice. 4 fixtures × 1 mutation cycle each.** Size this by the fixture
  count, not the diff — Wave F F4's comparable task ran ~200k tokens on 6 fixtures × 3 cycles.

### Task 3 — de-duplicate `Compile.lean`'s inlined geometry rules

**Re-verified while authoring** (not inherited): `Eval/Plan/Compile.lean`'s base-write loop contains
a hand-inlined re-implementation of `baseWriteRowsOk`'s advancing-pin clause, and a second
hand-inlined re-implementation of `pinnedLiteralsInRange` whose fall-through arm is
`| _ => pure ()` — constructor-blind, exactly like the predicates Task 1 hardens. Neither calls the
shared function. It also computes `writeRowKinds` twice over the same states in one pass.

This is the `scatterOutDim` drift shape one layer over: when `Scan.lean`'s predicates change, these
copies do not see it. Two real call sites of the same logic is the threshold `leanncd/AGENTS.md`'s own
reuse pattern names — and duplicated logic is where correctness bugs hide precisely because nothing
forces the copies to stay in sync.

Replace both copies with calls to the shared predicates. Where the diagnostics differ (the inlined
versions throw located `baseWriteNotAtBoundary` / `baseWritePinOutOfRange` errors that the shared
predicates do not produce), keep the located diagnostics — **preserve the error payloads exactly**;
this task changes where the *rule* lives, not what a rejection reports.

**Deliverable proving the call replaced the copy:** break a shared predicate and confirm the
`Compile.lean` path now fails too. Before this task, breaking `baseWriteRowsOk` leaves the inlined
copy happily accepting; after it, both must fail. Record both observations.

- **Files:** `leanncd/LeanNCD/Eval/Plan/Compile.lean`.
- **Risk:** moderate. **0 new fixtures, 1 mutation cycle**, but it touches production code with
  dependents and its own diagnostics — its own blast radius, hence its own task.
- **Rollback unit:** yes.

### Process weight for Slice 1

Three tasks, each independently rejectable — they pass the skill's reviewer test (a reviewer could
approve the tripwire and reject the de-duplication, or vice versa).

**Two independent final reviewers with different lenses**, not one. The skill's measured F4 split
(five per-task reviews → 1 Important; one whole-branch review → 1 Critical) says the whole-branch
tier is where soundness findings come from, and this slice's whole subject is a soundness surface.
Fund the second lens by running per-task review of Tasks 1 and 3 at mid tier — they are mechanical
against a specified table — and keeping Task 2's review at full tier, since fixture *shape* is where
its failure mode lives.

### Slice 1 completion record

**Status: LANDED**, all three tasks, on `worktree-slice1-write-geometry-hardening` from base
`89cd767`. Two independent whole-branch reviews, both recommending merge; the soundness lens found
no Critical and no Important. Build green at **8660 jobs**; all twelve tracked `leanncd/spikes/`
files still reproduce byte-identically; **no `strided` constructor in any committed file**. The
corrections above (the impossible spike mechanism, "every site in the table", the four-fixture table,
the superseded `B1-F10` baseline) were all found while executing this section and are folded into it
rather than left in a workspace document — this section is the durable spec, and the plan file the
slice was executed from is gitignored.

**Task 1 — the exhaustiveness tripwire** (`03c6cb1`, plus `b5099bf`/`cedbe77` scoping the shipped
claims). Every catch-all in the write-geometry predicates replaced by arms explicit over
`WriteRowKind`'s three constructors plus `Option`'s `none`, result-preserving in every case.
**Nine tripwired sites, seven of them production**, verified by adding a fourth constructor in place:
six in `Eval/Plan/Scan.lean` (`baseWriteRowsOk`'s cover, both of `stepWriteRowsOk`'s non-advancing
clauses, `freeExtentsAgree`, `pinnedLiteralsInRange`, `writesCollide`), one in `Eval/Plan/Compile.lean`
(its base-write placement loop, closed by Task 3), and two in `test/Eval/Plan/ScanTest.lean`'s frozen
`stepWriteRowsOkNoClause1` oracle. Only the six in `Scan.lean` appear in the first build; the other
three surface as those are discharged. `classifyWriteRow` and `causalAdvancingRow` remain
structurally un-tripwirable and are documented as such at the type.

**Task 2 — the negative coverage** (`10e6ded`, `9d900da`). `ScanTest.lean` gained **Part 9: 24
assertions** (20 `#guard` + 4 `run_cmd`), of which **9 are negated clause guards, each carrying its
own mutation cycle**. Three results worth carrying:

- **The `isBase` locator is shown failing.** Replacing `writeGeometryNotAdmitted isBase wi` with a
  constant `false` breaks the build with **exactly and only** the three new base-phase fixtures
  (`true 0`, `true 0`, `true 1`) — no pre-existing assertion fires, so that mutant was previously
  undetectable and each new fixture is individually load-bearing. Reproduced by the reviewer against
  the full default target.
- **A live unpinned weakening was found and closed**: dropping `c == 1` from `classifyWriteRow`'s
  free branch survived the entire suite, admitting a stride-k row as `.free 0`. Three chokepoint
  guards now pin both coefficient tests, with disjoint failure sets.
- **`stepWriteRowsOk`'s clause 1 is logically redundant** given clauses 2 and 3 (proved, two lines,
  for arbitrary rank and `advancingDims`), so its mutation survives by design. Rather than ship a
  fixture that passes either way, the redundancy itself is checked: a frozen local oracle minus
  clause 1, plus a 588-case agreement `run_cmd`. Ruling recorded: KEEP, because the copy is never
  called by production, so divergence *fails the build* rather than drifting silently.

**Task 3 — de-duplicating `Compile.lean`'s inlined geometry rules** (`76ace2e`). Two items:

- The hand-inlined **`pinnedLiteralsInRange` duplicate is now a real call** —
  `pinnedLiteralsInRange #[extent] #[row]`, one row at a time so the located
  `baseWritePinOutOfRange` diagnostic (dimension, literal, extent) is preserved exactly, with only
  the LOCATOR left at the call site and the RULE in `Scan.lean`. Mutation-verified: deleting the
  predicate's pinned-row rule now breaks `ScanCompileTest`'s two `baseWritePinOutOfRange` guards,
  which the former inlined copy survived unchanged. Its `| _ => pure ()` arm became a tripwire site
  in the same commit.
- **`writeRowKinds` is hoisted**: the placement loop and the base-collision `mine` builder used to
  compute it twice over the same writes and state shapes in one pass; there is now a single
  `baseWriteRows` both consume. `writeRowKinds` is total, so this cannot change which rejection fires
  first. Side effect worth knowing: the audit's barrier 1 was *"two sites, not one expression"*, whose
  second site was these two literal `0`s — now one.

**The one deliberate non-replacement, and its owner.** `Compile.lean`'s `baseWriteNotAtBoundary`
guard still restates `baseWriteRowsOk`'s advancing-pin clause inline. Calling the *whole* predicate
there compiles and passes the full suite — the reviewer tried it — so nothing blocks it
mechanically; the objection is diagnostic, and it is recorded in `leanncd/LeanNCD/Eval/AGENTS.md`'s
write-geometry contract row as well as in Section B's first inherited item. **Owner: Slice 2**, which
reopens `baseWriteRowsOk` anyway; the fix is to lift that clause alone into a named `Scan.lean`
predicate both sites call, not to call `baseWriteRowsOk` from `compileScan`.

**What Slice 1 deliberately did NOT close**, carried into Section B: the free branch's `bias == 0`
test and `classifyWriteRow`'s multi-nonzero arm are both genuinely unpinned (measured — see Section
B's firing-set table), and `ScanTest.lean`'s `allRowKinds` literal is not tripwired.

## Section B — Slice 2: Scatter + affine LHS writes (scoped, not detailed)

**Not planned here, on purpose.** Section 0 is now settled — **Decision A**, so *both* lowering arms
are in scope (base and step) and `B2-F1`'s 16 cells are live. What is still not derivable is the
other half of this slice's task list: the compile-error list Slice 1's Task 1 produces. Write this
plan from that list, once it exists.

What is already settled and must be carried into that plan when it is written:

- **⚠️ ENTRY OBLIGATION, discovered by Slice 1 and not present in the audit: the chokepoint has no
  compile-time guard, and the fix has to be a witness function.** Slice 1's tripwire makes **nine
  sites** fail to compile when a fourth `WriteRowKind` constructor appears — **seven production and
  two test.** This is Slice 2's expected compile-error list, so both the split and the arrival order
  matter:

  | Where | Sites |
  |---|---|
  | `Eval/Plan/Scan.lean` (production) | **six** — `baseWriteRowsOk`'s positional cover; *both* of `stepWriteRowsOk`'s non-advancing clauses; `freeExtentsAgree`; `pinnedLiteralsInRange`; `writesCollide` |
  | `Eval/Plan/Compile.lean` (production) | **one** — the base-write placement loop's pinned-literal match |
  | `test/Eval/Plan/ScanTest.lean` (test) | **two** — both matches inside the frozen `stepWriteRowsOkNoClause1` oracle |

  **They do not all appear in one build**, and a plan that expects nine errors at once will read the
  first round as two sites missing. Re-measured in this slice's final fix wave by adding a throwaway
  fourth constructor in place (Lean inductives cannot be reopened from another file, so there is no
  way to do this from a spike): the build reported `Scan.lean`'s **six, and only those six**, because
  a module that fails to compile blocks its dependents. `Compile.lean`'s one and `ScanTest.lean`'s
  two surface only once the six are discharged. Expect three rounds.

  The tripwire's residual limit belongs in the same breath, since it is the whole of what the
  mechanism buys: **it forces a decision at each value check, it does not constrain the decision.**
  Discharging all nine with `| some (.strided ..) => true`, mirroring the neighbouring arms, compiles
  clean and reproduces the historical defect exactly — the new kind exempt from every value check,
  just deliberately this time. Each arm's value comes from `pre_scatter_backend_audit.md`'s cell
  table, not from its neighbours.

  Two sites are worse than that: `classifyWriteRow` and `causalAdvancingRow` **structurally cannot**
  be tripwired at all. Their catch-alls
  scrutinise `nz : List (Int × Nat)`, not a `WriteRowKind`, and Lean imposes no exhaustiveness
  obligation on a function's **range**. `classifyWriteRow` is the audit's single chokepoint — the
  only place a strided kind can be *admitted* — so **Slice 2's first edit lands in the one position
  with no guard rail.**

  Two readings, and only one is dangerous. If Slice 2 forgets the producing branch entirely, the
  result is **fail-closed**: a `c == 2` row yields `nz = [(2, p)]`, both `c == 1` tests fail, the
  result is `none`, `rows.all Option.isSome` then fails in both geometry predicates and `checkWrites`
  throws `writeGeometryNotAdmitted`. Loud, and every acceptance fixture fails. **The dangerous
  reading is the `contextWidth` gating**: the `.advancing`/`.free` branches discriminate on
  `p < contextWidth` vs `p ≥ contextWidth` and subtract `contextWidth` for the output position. A
  strided branch written without that discrimination yields a *well-formed* `.strided` whose
  `outputPos` is off by `contextWidth` — which every one of the seven tripwired production consumers
  happily accepts. Silently wrong geometry, which is this defect family's exact shape.

  **The mechanism that closes it — use this one, not the obvious one.** A `#guard` set asserting
  each existing constructor is producible does **not** work: naming `pinned`/`free`/`advancing` never
  mentions `.strided`, so it compiles and passes unchanged when the constructor is added. What works
  is a **witness function matching exhaustively over the type** — e.g.
  `classifyWitness : WriteRowKind → (Nat × Array Int × Int)` with one
  `#guard classifyWriteRow (witness k) == some k` per constructor. Adding `.strided` then breaks
  `classifyWitness`'s own exhaustiveness, which is a compile error.

  **What that compile error does and does not buy — corrected, because an earlier draft of this
  bullet over-claimed on exactly the point the mechanism is sold on.** It forces the author to
  *supply* a `contextWidth` value; it does **not** force the author to *exercise the
  discrimination*. And a single witness does not close the dangerous reading this section itself
  names. `contextWidth = 0` is the natural first choice and the base-phase value, and there
  `outputPos = p - contextWidth` and a broken `outputPos = p` **coincide** — so a lone
  `contextWidth = 0` witness passes under both the correct branch and the branch that omits the
  `p < contextWidth` / `p ≥ contextWidth` split, and the off-by-`contextWidth` bug ships with a green
  guard. **Requirement, therefore: at least one `contextWidth = 0` witness AND at least one
  `contextWidth > 0` witness per constructor.** Only the second one can separate the two readings.

  Slice 1 demonstrated this one layer down, and its fixtures are the precedent to copy: its three
  `classifyWriteRow` guards are deliberately split across phases — one at `contextWidth = 0` and two
  at `contextWidth = 2`, one of those with the nonzero coefficient in the OUTPUT half of the domain
  (`p ≥ contextWidth`) — precisely so no base-phase guard can stand in for the step-phase rule.
  Build the witness set before, or as, the strided branch is written.

  **Slice 1 also pinned part of this surface, and left a named remainder.** Slice 1's Task 2 landed
  three `classifyWriteRow` guards after its reviewer found a **live** unpinned weakening: dropping
  `c == 1` from the free branch survived the entire 8660-job suite, admitting a stride-k row as
  `.free 0` — invisible to `freeExtentsAgree` and `pinnedLiteralsInRange`, and exactly this defect
  family's shape on exactly the constructor this slice adds. Both coefficient tests
  (free branch and advancing branch) are now pinned, by two mutation cycles with **disjoint** failure
  sets — which is what makes the third guard non-redundant. The failure sets are not one guard each,
  and an earlier draft of this bullet said they were: dropping `c == 1` from the free branch fires
  *both* free-branch guards, and dropping it from the advancing branch fires **three** assertions —
  the advancing-branch guard plus `unrecognizedStepRows`' row-shape guard and its
  `stepWriteRowsOk` rejection. Both re-measured against the full default target in this slice's final
  fix wave. **A useful side effect: `classifyWriteRow`'s current rejection of non-unit coefficients is
  now asserted, so this slice must consciously edit a test to admit strided rows** — the change
  appears in a diff instead of happening silently.

  **The remainder, deliberately not closed by Slice 1** (out of its brief's scope, and the guards
  belong with the branch edits rather than ahead of them): the `bias == 0` / `bias == 1` tests in
  those same two branches, and the multi-nonzero arm, still have **no dedicated guard**. Same defect
  family. Close them as part of writing the strided branch — this slice is the one that touches them.

  **"No dedicated guard" is not the same as "undetected", and this bullet used to conflate them.**
  An earlier draft said a weakening of any of the three *would today go undetected*. That is false
  for one of them, and the correction matters because as written it told Slice 2 a hole exists where
  none does — and would have made a real fixture failure look like collateral damage. Each of the
  three was weakened in place and rebuilt against the full default target during Slice 1's final fix
  wave; the observed firing sets:

  | Weakening | Observed | Firing set |
  |---|---|---|
  | advancing branch, drop `bias == 1` | **build FAILS** | exactly one assertion — the pre-existing `lookAheadStepWrite` plan-level fixture in `ScanTest.lean` Part 2 (`writeGeometryNotAdmitted false 0`). With `bias == 1` gone, `stepWriteS` at bias `2` classifies `.advancing 0` instead of `none` and the look-ahead write is admitted, so that fixture throws. Pinned incidentally, by a fixture whose stated subject is the look-ahead shape rather than the bias test — hence still *no dedicated* guard |
  | free branch, drop `bias == 0` | **build PASSES, 8660 jobs** | **empty** — genuinely unpinned |
  | multi-nonzero arm, route length-≥2 rows through the free-branch logic on their leading nonzero | **build PASSES, 8660 jobs** | **empty** — genuinely unpinned |

  So the accurate scope for Slice 2 is: **two unpinned value checks, not three** — the free branch's
  `bias == 0` and the multi-nonzero arm. Add a dedicated guard for the advancing branch's `bias == 1`
  too if it is cheap (an incidental pin in an unrelated fixture is a poor place for a load-bearing
  rule to live), but do not plan it as coverage of a live hole.

- **⚠️ `allRowKinds` must be extended when the constructor lands, and NOTHING will tell you.**
  `ScanTest.lean`'s 588-case agreement check (`stepWriteRowsOk` vs the frozen
  `stepWriteRowsOkNoClause1` oracle, over all rank-2 rows arrays × four `advancingDims` subsets ×
  output ranks 0–2) enumerates its row kinds from `allRowKinds`, a **plain list literal** — not
  tripwired, and its docstring claims "every row classification reachable in a rank-2 write". Once
  the oracle's two arms are added to discharge its compile errors, the check goes on passing over a
  window that no longer contains the new kind, while still reading as an exhaustive result. The thing
  it exists to notice is exactly what a narrowed window hides: clause 1 ceasing to be redundant
  because clause 3's new arm admits the strided kind. **This is the silent-narrowing shape Slice 1
  exists to prevent, reappearing in Slice 1's own test scaffolding** — extend the literal in the same
  commit as the oracle's arms, and re-check the two-line redundancy argument in the oracle's
  docstring rather than assuming it survives.

- **Inherited from Slice 1 Task 3: extract `baseWriteRowsOk`'s clause 3 into its own named
  predicate.** `Compile.lean`'s base-write loop still hand-inlines that one clause (the
  advancing-pin boundary check), the last surviving duplicate of a `Scan.lean` rule — which is why
  `leanncd/LeanNCD/Eval/AGENTS.md` calls it *"the one surviving duplicate"*. Precisely what Slice 1
  did to the other items, since an earlier draft here said "closed the other two duplicates" and
  overstated it: `B1-F6` named **two** hand-inlined duplicated *rules*, and Slice 1 closed **one** of
  them — the pinned-literal check, now a real `pinnedLiteralsInRange` call with only the locator left
  in `Compile.lean`. Separately it hoisted a duplicated *computation* (`writeRowKinds`, previously
  run twice over the same states in one pass, now one `baseWriteRows` shared by the placement and
  collision loops). One rule closed, one computation hoisted — not two duplicates closed. This one
  was deliberately left, and the reason is worth carrying because
  the obvious reading is wrong: calling the *whole* `baseWriteRowsOk` there **compiles and passes the
  full suite** — Slice 1's reviewer tried it — so nothing blocks the replacement mechanically. The
  objection is diagnostic: clauses 1–2 hold at that point only by a **non-local invariant spanning
  Phases 1–3**, so asserting them would convert a hypothetical *compiler bug* from the `invalidPlan`
  channel (Step E's `writeGeometryNotAdmitted`/`writeCoeffRankMismatch`, which exists as exactly that
  net) into a source-facing `baseWriteNotAtBoundary` naming a boundary fault that is not the real
  fault. The clean fix is to lift clause 3 alone into a named `Scan.lean` predicate both sites call.
  **This slice reopens `baseWriteRowsOk` anyway, so it is the natural owner.**

- **The extent rule is not free to invent.** Every strided cell must be the checked-plan image of an
  `LHSSlot.outExtent` arm, and must **call** that shared formula rather than copy it. A duplicate
  formula (`scatterOutDim`) previously drifted from it and shipped a soundness bug — a downstream
  reader sized to 3 while the evaluator materialised 4 (fix `fc10d70`, duplicate deleted `6a26825`).
- **Barrier 2 disappears in this slice.** `Compile.lean`'s base-write loop currently cannot emit
  coefficient 1 *with* bias 1, which is half of what keeps `B1-F2` latent. Lowering its `.affine` arm
  is precisely what removes that. The plan must state what barrier 1 alone then does and does not
  cover — under decision A, per §B2.7, nothing.
- **`B2-F3` breaks by construction.** Four docstrings and one `AGENTS.md` node enumerate
  `WriteRowKind`'s constructor set exhaustively; adding a fourth falsifies all five. Mechanical, and
  carved out for GPT in Section D.
- **`B2-F4` is a simplification this slice should take, not defer.** `freeExtentsAgree`'s equality is
  the `scale = 1, offset = 0` special case of the general strided extent rule — so the general check
  can *subsume* it rather than sit alongside it. See Section E.
- **`B1-F9`'s live trigger.** A zero-extent scatter output is not rejected downstream, reachable via
  a **zero coefficient** from four words of surface syntax. (The four *negative* affine forms are
  surface-unreachable — the elaborator builds coefficients through `Int.ofNat`.)
- **Value-grep before declaring the doc sweep done.** This slice moves a capability boundary, so
  grep the whole repo for the numbers that moved — the stale values themselves, not the surrounding
  vocabulary — including `papers/backend_missing_functionality.md`, whose "Hard" row for
  `scatterOrAffineLhs` this slice closes, and `papers/wave_f_capability_manifest.md`.

## Section C — the binding surface (independent of Scatter)

Different surface (`Adapter`/`Prepared`/`Executable`), no dependency in either direction with
Sections A and B. Parallelisable.

### C1 — the name-authentication policy decision (`BND-01`, `BND-02`)

**This is a decision, not a fix, and it must not be done as a drive-by.** The checked plan
deliberately proves *slot* identity and never *name* identity. That choice is documented in four
places and **pinned by a live green `#guard`** asserting a wholesale rename of every
`materializedNames` entry is accepted as valid.

What the audit adds is that the choice has a **reachable, silent, wrong-answer path through the
public API** — `BND-01` returns `.ok` with the wrong tensors in the wrong slots; `BND-02` publishes
an output under an input's name and drops the declared output. Both were reproduced independently
with two different fixtures.

Deciding to authenticate names means retiring: the `CompileTest.lean` `#guard`, the
`checkPreparedBindings` doc sentence, the `leanncd/LeanNCD/Eval/AGENTS.md` contract line, and the
`leanncd/experiments/jax_bridge/README.md` line — the retire list is in the audit at §4.3. Deciding *not* to
means recording that the silent path is accepted, and saying where a caller is expected to establish
name correctness instead. **Either is defensible; leaving it undecided is not**, because Scatter is
tagged `direct` on both findings and will inherit whichever answer is implicit.

### C2 — the two narrow fixes (`BND-04`, `BND-05`)

Unblocked by C1 and much smaller:

- **`BND-04`** — `PreparedPlan.warnings` is unvalidated, so a real `paddedAccess` diagnostic can be
  dropped and a fabricated one reported. Both directions were constructed.
- **`BND-05`** — the plan-level JAX executable path discards `checkJaxAssignSupport`'s located
  cause: `jaxSupportOk` hardcodes `0` and reduces the cause to a `Bool`, and
  `validateAndConstructExecutable`'s final branch throws a bare `invalidCandidate`. Note the audit's
  own first framing of this was **refuted** — `0` at an index-less standalone entry is the documented
  convention, not a defect. The defect is confined to the plan-level path, where a real index exists
  and is discarded. Do not re-derive the refuted version.

## Section D — work carved out for external (GPT) execution

Criteria: mechanical, little judgement, independently verifiable, no design decision embedded.

### D1 — `BND-03`'s stale doc comments (available now)

Four doc comments make a stale producer-discipline claim, and two misname the shared resolver as
`PlanBindings.materializedWith` when the function is `CheckedPreparedBindings.materializedWith`.
Sites: `Eval/Plan/Adapter.lean`, `Eval/Plan/Error.lean`, `Eval/Plan/Prepared.lean`. Pure text; zero
logic; the audit's §4.4 names each site and what it should say.

### D2 — `B2-F3`'s constructor enumerations (only once Slice 2 adds the constructor)

Four docstrings plus one `AGENTS.md` node enumerate `WriteRowKind`'s constructors exhaustively and
become false the moment a fourth exists. Updating them is mechanical, but it is **only correct after**
the constructor lands — so this is a queued carve-out, not an available one.

### Required brief contract for any GPT dispatch

External agents on this repo have produced sound content while **unreliably following
output-location instructions** — this has bitten twice. Therefore every brief must:

1. Name the exact file paths to edit and forbid creating any new file.
2. Forbid touching anything under `leanncd/LeanNCD/`'s logic, `lakefile.toml`, or `test/` for D1.
3. Carry a **mechanical git self-check the agent must run and paste**:
   `git diff --stat` must show only the named files, and
   `git diff -- leanncd/LeanNCD/Eval/Plan/Scan.lean` must be empty.
4. Require the build job count from a real run (**8660**), not an assertion that it is unchanged.

**The controller re-runs the self-check independently before trusting "done".** A pasted self-check
is evidence the agent ran something, not evidence it landed where it said.

## Section E — simplification and dead-code opportunities

Per the root `CLAUDE.md`'s surgical-changes rule, **pre-existing dead code is mentioned here, not
deleted** — none of these is authorised by this roadmap alone except where a task above claims it.

| # | Opportunity | Status | Verified how |
|---|---|---|---|
| E1 | `Compile.lean`'s two hand-inlined copies of `baseWriteRowsOk`'s pin clause and `pinnedLiteralsInRange` → call the shared predicates | **claimed by Slice 1 Task 3** | read at authoring time |
| E2 | `Compile.lean` computes `writeRowKinds` twice over the same states in one pass — hoistable | fold into Task 3 if free; otherwise mention | read at authoring time |
| E3 | `Adapter.lean`'s **slot-name** `missingEnvBinding` throw is unreachable — `checkPreparedBindings`' `Perm` against `raw.inputSlots` guarantees every iterated slot has a name. (The sibling arm, a name absent from `env`, is live.) | dead arm; removal optional and needs its own unreachability mutation | audit §4.4, arms re-confirmed by grep |
| E4 | `PlanBindings` is **never a parameter anywhere** — exactly one non-definition occurrence, a field of `PreparedPlan`. Candidate for inlining or privatising | mention; touches a public type, so not a drive-by | `grep ": PlanBindings"` → one field hit |
| E5 | `freeExtentsAgree` is the `scale = 1, offset = 0` special case of the general strided extent rule — subsume rather than keep alongside | **Slice 2 should take this**, not defer it | audit `B2-F4` |
| E6 | `splitStmt`/`splitNonlins` are off the production chain — every occurrence outside `Pipeline/Lowering.lean` is a doc comment or a test reference | **not dead**: deliberately retained as the old-leg regression comparator. Do **not** remove | `grep` across `LeanNCD/` and `test/` |
| E7 | `ScalarConst.f32`/`.bool` are documented inert inside any checked plan | mention only; already doc-commented by the C6 audit | audit provenance |

**A further opportunity Task 1 will create.** Making the matches exhaustive frequently exposes arms
whose bodies are identical across several constructors — those collapse into a single alternation
pattern, which is *smaller* than today's wildcard while still failing to compile when a constructor
is added. Expect Task 1's diff to shrink some predicates rather than grow them; if every predicate
grows, the arms were probably written more verbosely than needed.

## Section F — deliberately not in this roadmap

- **Semantic-payload finding #6** — the four boundary decoders (`realizeStMat`, `realizeBrBaseP`,
  `AcsetCodec`, `realizeSBr`). Still flagged UNAUDITED in `leanncd/AGENTS.md`; the audit explicitly
  did not close it, and this roadmap does not either. Different subsystem, `noncomputable`, so the
  construction-attempt evidence bar used throughout the audit is unavailable there.
- **Scatter collision Gap 2** — a sound symbolic over-approximation of non-injective scatter maps. No
  concrete axis sizes exist at compile time, so Python's enumerate-all-coordinates approach cannot be
  ported; this needs its own scoping pass.
- **Decomposing `DSL/Pipeline/Structural.lean` (1199 lines) or `Eval/Plan/Compile.lean` (1324)** —
  the two size outliers. Both are structural hubs and deliberately out of scope; cf. Spike 5,
  deferred repeatedly.
- **Whether a nonlinearity activates before or after collision reduction** — a Scatter design
  question, deferred by policy long before the audit.
- **Pushing to `origin`.** `main` is currently 13 commits ahead and unpushed by standing preference.
