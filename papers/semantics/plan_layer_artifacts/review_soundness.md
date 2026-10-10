# Soundness review (lens 1 of 2): Plan-layer slice 1 package

Reviewer: read-only soundness lens. Worktree HEAD 465af455. Written incrementally.

## Q4. Equivalent-mutant claims

### F-1 (Minor) A2-e "transactional vs sequential commit EQUIVALENT" holds only on Valid plans; the plan states it unqualified

- Where: plan §5.2 row "`execAcc` | transactional vs sequential commit | EQUIVALENT (A2-e, N5) |
  `semFail` carries no memory; `readPub` hides prefix commits"; manifest label
  "A2-e EQUIVALENT (N5): non-transactional acc"; mutant body in
  `plan_layer_mutations_post.json` (per member: scan `[x]` on `readPub pc M₁`, then `addAt`, `none` -> `.stuck`).
- Claim: no fixture can distinguish the mutant.
- Why it is too strong: "`readPub` hides prefix commits" needs every member destination to be
  unpublished at `pc`, which is `dest_not_pub` (needs R plus Order4/PubFresh, i.e. a valid plan).
  `runPlan` is total on invalid plans and fixtures observe it (`earlyStep`, `dupGroup`, ... print
  outcomes), so the claim is false as stated. Two concrete distinguishing plans:
  1. Published destination read in the same group (violates `pubOrder`):
     `unitPlan [[.initZero cAll], [.pub cAll], [.acc [cOcc 0, cOcc 1]]]` over `routed chainBody`
     (occ 0 writes point 1, occ 1 reads point 1; `chainPlan` gives `[0,3,4]`). Shipped kernel: occ 1
     reads point 1 from the pre-step view (0). Mutant: `readPub 2 M₁` shows occ 0's commit (3), so
     occ 1 reads 3. Final memory differs at point 2.
  2. Uninitialised destination before an undefined member (violates `accMat`): group `[x1, x2]` with
     x1's destination slot `none` and x2 undefined (`failureAfterBody`-style). Shipped: scan reaches
     x2 -> `failed x2 pc M`. Mutant: x1's `addAt` returns `none` -> `stuck pc M`.
- On Valid plans the equivalence does hold (destinations unpublished and materialised by
  `dest_not_pub` / `acc_slot_isSome`), so no theorem is affected.
- Fix: qualify the §5.2 row and the manifest label as "equivalent on `checkPlan`-valid plans"; the
  justification should cite `dest_not_pub` and `acc_slot_isSome`, not only "semFail carries no
  memory". Optionally add plan 1 as a fixture that kills A2-e outside the valid domain.

### Note on N5 wording (Minor, folded into F-1)

N5 says "`PlanFailed` carries no state". In the shipped Lean `PlanOutcome.failed o pc M` DOES carry
memory; what carries no memory is `StepResult.semFail`, and `runFrom` always reports the PRE-step
`M` regardless of what `execAcc` did. Consequence: the Global Constraint "transactional failure ...
reports `failed o pc M` with the PRE-step memory" and fixture `step-failure-after` do not test
transactionality; the pre-step memory comes from `runFrom`'s structure. The decision text should say so.

### A2-b (raw commit view): equivalence CONFIRMED, universally (not only on Valid plans)

The mutant keeps the scan on `readPub pc M`. A successful scan means `checkReads` passed on every
member footprint (Readiness.lean `evalReady`), so every footprint address has `readPub pc M a` =
`some`, hence `Pub pc a`, hence raw = `readPub` there; `evalWith_stable` then gives equal values.
No plan, valid or not, distinguishes it. No finding.

### A3a-a (checkCov1Complete trivially true): equivalence CONFIRMED at `checkPlan`

For every plan: `checkSingleton && checkCov2Complete && checkSteps` already forces every occurrence
into `accFlat` (each occurrence's target is in `addrList` ⊆ `pubFlat`; `checkPubOrder` at that pub's
pc puts the occurrence in `consList pc` ⊆ `accFlat`). This is `accFlat_complete`. The mutant is
killed only by the `checkPlan_sound` proof (Validity.lean:193), as the manifest expects. No finding.

F-1 concrete numbers for plan 1 (from `chainPlan` = `[0,3,4]` and the A2-f / A3b-3 observation
`chainEarly` -> `[0,3,1]`, i.e. occ 1 contributes point1 + 1): shipped kernel ends `[0,3,1]`, the
A2-e mutant ends `[0,3,4]`. Not built here (read-only); derived from the shipped definitions and
the recorded fixture values.

### F-2 (Important) §8.1 would write "`PlanFailed(o)` carries no state" into the spec, contradicting the Lean

- Where: plan §8.1 table, row "failure matching": "`PlanFailed(o)` carries no state, so raw-vs-view
  commit values and transactional-vs-sequential commit are unobservable (N5)"; also §2 N5.
- Lean: `PlanOutcome.failed (o) (pc) (M)` (Step.lean:34) carries the memory, and fixture
  `step-failure-after` (PlanStepTest.lean:75) and the failureAfter row in PlanCorrectnessTest.lean:74-76
  print it (`slot 0 = some 0`). §1's goal is to restate the
  spec "to match what is proved"; this sentence does not.
- Also "unobservable" is only true on valid plans (F-1).
- Fix: "`StepResult.semFail` carries no memory and `runFrom` reports the pre-command memory, so on
  valid plans raw-vs-view commit values (any plan) and transactional-vs-sequential commit (valid plans,
  via `dest_not_pub`, `acc_slot_isSome`) are unobservable."

## Q1. Theorem-statement strength

Read: `batch_execution` (Batch.lean:117), `step_R`, `step_failed` (Simulation.lean:549, 567),
`checkPlan_sound` (Validity.lean:187), `run_R`, `runPlan_R` (Run.lean:109, 154), and all of
Correctness.lean. Hypotheses are `hv : π.Valid`, `η : P.Input`, instances `[DecidableEq σ.Tensor]`,
`[∀ t : P.Defined, AddCommMonoid …]`, and `ops`. None is contradictory: `Valid` is inhabited by
`plan_valid := plan.checkPlan_sound (by decide)` and `sPlan_bad_valid` (PlanRunTest.lean:11, 25), and
`done_correct`, `failed_correct`, `done_iff_model` are each instantiated on a concrete run
(PlanCorrectnessTest.lean:88, 93, 99), so (a) and (b) are not vacuous. Statements match §1/§2/P7/P8 and
the a3b notes: (a) unique model + Decode + denotation; (b) no model only (D5); (c) `done_or_failed`
(never stuck) and `done_of_model`. The plan prose claims nothing stronger, apart from F-3.

### F-3 (Minor) `cov1_of_cov2_pubOrder` is vacuous as stated; N6 is cited to it

- Where: Correctness.lean:32 `theorem cov1_of_cov2_pubOrder (hv : π.Valid) (x) : x ∈ π.accFlat`.
  Plan §2 N6 ("proved (`cov1_of_cov2_pubOrder`)"), §5.1 row `checkCov1Complete`, §8.1 Definition 31.1
  row ("cite `cov1_of_cov2_pubOrder`"), §10 item 2.
- Claim: N6, "covering half of condition 1 follows from condition 2 + condition 4".
- Problem: the hypothesis `π.Valid` already contains `coverage1`, so the statement is a one-liner
  (`hv.coverage1.2 x`) and does not show redundancy. The proof happens not to use `coverage1`, but the
  statement does not record that. The real result is `accFlat_complete` (Simulation.lean:83:
  `Singleton → (∀ y, y ∈ pubFlat) → Order4 → x ∈ accFlat`), which is correct and not vacuous. So N6
  is true, but the cited name does not establish it. `Valid.order4` has the same shape, since it takes
  all of `Valid` but uses only `pubOK`.
- Effect: the spec would cite a theorem whose statement is trivial for the claim it supports. A
  reader deciding Open item 2 (drop the check) cannot read the soundness of the drop from the
  statement.
- Fix: cite `accFlat_complete` in N6, §5.1 and §8.1. Alternatively, restate `cov1_of_cov2_pubOrder` over
  `(single : π.Singleton) (cov2 : π.Coverage2) (pubOK : ∀ pc B, … → π.PubOK pc B)`. That changes a
  patch, so take the citation route for this slice.

## Q2. Relation R and Valid: no finding

- `R` (Memory.lean:213) relates `M` to a reference `c` through R1 (`P.Reaches` from `P.initial η`,
  which is reference semantics), R2 (bookkeeping against the static command prefix), R3 (slots at
  `place`), and R4. None of it is defined by running the plan side. `refState` is the reference
  contracts (`postAcc`/`postPub` on `c.published`, independent of `M`) folded along the prefix.
  `refState_execution` gives a real `Execution`.
- `run_R` uses `R ∧ refState pc = some c`. That is consistent with P3 and is not circular.
- `checkPlan_sound : checkPlan = true → Valid` goes in the soundness direction. Completeness is
  disclaimed in §1 Global Constraints ("only soundness ... is proved") and in "does NOT do". It is not
  claimed anywhere else I read. The §5.1 "Required (accept)" column is fixture-level (`decide` on six
  plans), which is correct.

## Q3. §5 case × class cells

Verified against the test sources. Each `#eval check` throws on mismatch, the same as `checkSmoke` in
ExecutableReferenceTest.lean:108-112, so it fails the build.

| cell | claim | evidence found | verdict |
|---|---|---|---|
| R: `checkPlan` accepts the six valid plans | `(true, [])` ×6 | PlanValidityTest.lean:32-43 (`#eval` + `decide`) | backed |
| F: `checkReady` / `chainEarly` | `ready@1`, run stuck 1 | PlanValidityTest:52; PlanStepTest:134-136 `("stuck",1,…)` | backed |
| F: `checkPubOrder` / `earlyStep`, `earlyHalf` | `pubOrder@1`, `pubOrder@2`, both done | PlanValidityTest:47, 74-75; PlanStepTest:143-145 | backed |
| F: `checkInit` / `reinitMid` | `initFresh@2`, done 5 `[0,10,0]` | PlanValidityTest:83-89 | backed (consumed-target half only, as stated) |
| F: `checkCov1Complete` / `missingOcc` | `cov1Complete`, `pubOrder@2` | PlanValidityTest:64-73 | backed; EQUIVALENT is correct (Q4) |
| F: `checkCov2Complete` / `missingPub` | `(false,["cov2Complete"])`, done 3, Decode none | PlanCorrectnessTest:105-114 | backed |
| I: `execInit` target live | `reinitMid` returns `[0,10,0]` | PlanValidityTest:87-89 | backed |
| I: `execAcc` duplicate / consumed | `dupGroup` done 4 `[0,16,0]` | PlanStepTest:158-162 | **partial**: see F-4 |
| I: `execPub` contributions pending | `earlyStep` done 3, `refState 2 isSome = false` | PlanStepTest:142-145 | backed |
| I: `execPub` already published | OPEN | none | honest |
| I: `checkSteps` non-singleton | by design | `fused` | backed |
| R: `stepCommand` fused **or empty** | stuck | `fused` only (PlanStepTest:165-167) | **partial**: see F-4 |
| OPEN: `checkCov1Nodup`, `checkCov2Nodup`, `checkPubFresh`, `checkInit` not-published half, `stepPlan` pc ≥ m | OPEN | none | honest. See note below. |

### F-4 (Minor) Two cells claim more case coverage than their fixture gives

- §5.2 `execAcc` "duplicate / already-consumed member": `dupGroup` puts occ 0 0 in two DIFFERENT
  groups (`[.acc group], [.acc [occ 0 0]]`), so only the already-consumed case is exercised. No fixture
  has a within-group duplicate (`G` not `Nodup`). §5.1 `checkAccFresh` says "second clause", which is
  honest. §5.2 lumps both cases under one piece of evidence.
- §5.2 `stepCommand` "fused or empty command": only `fused` exists. No fixture has an empty command
  `[]`. By code (`stepCommand | _ => .stuck`; `checkSingleton` uses `length == 1`) the empty case is
  correct, but the table presents it as evidenced.
- Fix: split each row, or mark the uncovered half "by code inspection, no fixture".

### Note on the OPEN cells (not a finding; affects Open item 3's cost estimate)

- `checkCov1Nodup` and `checkCov2Nodup` are equivalent at `checkPlan`, not just candidates, in
  the singleton profile:
  - Two groups at pc1 < pc2 are disjoint, because `checkAccFresh` at pc2 rejects any member in
    `consList pc2` ⊇ G1. Within a group, `G.Nodup` holds.
  - Likewise `checkPubFresh` rejects a member whose address is in `Pub pc` ⊇ earlier blocks
    (Syntax.lean:105), and `DefAddr.addr_injective` finishes the argument.
  - So no fixture can ever kill a "drop cov*Nodup" mutant. Open item 3's "3 fixtures + 3 cycles"
    cannot back these two cells; they need the (short) A2-conjecture proof instead.
- The `checkInit` not-published half CAN be backed at checker level. Example:
  `[[.initZero block], [.acc group], [.pub block], [.initZero [addr 0]]]` gives `initFresh@3` today and
  `true` under the mutant. It is observationally redundant on outcomes, though: a published address
  with a non-empty fiber is already caught by the consumed-target half via `pubOrder`, and an
  empty-fiber one gets 0 written over 0. So the §5.1 role "safety" overstates it. That affects §8.1
  N7 wording only.

## Q5. Slice-1 profile restrictions vs theorem hypotheses: no finding

- The theorems assume only `Valid`, a validated `η : P.Input`, `[DecidableEq σ.Tensor]`, an
  `AddCommMonoid` per defined sort, and `ops`.
- The restrictions in the profile live in two places:
  - in `Valid`: `singleton`, `initFresh` (N2), `pubOK` materialisation (N1), and full `coverage2`;
  - in the model: fixed injective `place`, dense memory, `StepResult` without implementation errors.
  All of these are listed in Global Constraints or §2.
- The theorems are generic in `S`/`K`. "Single sort Q" restricts only the fixtures, so the theorems
  assume less than stated, not more.
- The plan-carried `tensors`/`tensors_complete` (P4) is a structural requirement of `P.Plan`, and it
  is stated.
- The plan-layer `addVal` uses the same `AddCommMonoid` instance as the reference `consume`. I did
  not check whether that instance coheres with `ops`'s scalar addition. That question belongs to the
  reference layer, not this slice.

## Q6. Execution safety

- Nothing in §3, §4, §8 or §9 pushes. §9.5 and §10.9 explicitly say no push.
- Each task is gated by `sha256` = manifest, then `apply --check`, then `apply --index`, then a
  module build, so a wrongly applied patch fails `--check` or the hash. T1-T4 build only their
  modules. Tests build first in T5 (`defaultTargets = ["LeanNCD","Tests"]`), and a failing `#eval
  check` errors the build. That is sufficient for mechanical patches.

### F-5 (Minor) §3.1 commits in the primary checkout without checking which branch is current, and without an empty-status gate

- §3.1 says "From the primary checkout on `main` (tree clean)". It runs `status --short` but states
  no "must print nothing" gate, and there is no `branch --show-current` (or `symbolic-ref`) check
  before the `commit`. If the primary checkout is on another branch, or has staged work, the docs
  commit lands there, or sweeps up the staged work. The only gate (`diff --cached --stat`) comes
  after `checkout -- paths`, which would reveal extra staged paths, so the residual risk is the
  branch. The commit message also lacks the repo's Co-Authored-By trailer.
- Fix: add `/usr/bin/git -C <primary> branch --show-current` (must print `main`), and make
  `status --short` empty an explicit gate.

### F-6 (Minor) §9.5 deletes the unmerged prototype branch and worktree; consequences are not stated

- `worktree-plan-layer-slice1` is never merged (§3.1: "must NOT be merged"). Deleting it needs
  `git branch -D` and discards the prototype commit history (A1-A3b proto commits, code HEAD
  11dd4c17). Only the tree content survives, via the patches.
- `git worktree remove` will refuse because of untracked files in the prototype worktree. This review
  file and the fidelity lens's file live there, untracked. The plan does not say to commit or copy
  them before §3.1 copies the docs. A file written after §3.1 never reaches `main`.
- CLAUDE.md Rule 13 lists deleting other branches and worktrees as ask-first. The prototype branch is
  arguably this initiative's own work, but the plan should say which reading it takes.
- Fix: in §9.5, tag the prototype head (for example
  `/usr/bin/git -C <primary> tag proto/plan-layer-slice1 <sha>`) before `branch -D`. Also land the
  review files on the branch before §3.1, or copy them into `<exec>`.
