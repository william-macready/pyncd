# Part V buffer retirement (slice 3): design

Status: design approved in conversation 2026-10-11; this file awaits user review before `writing-plans`.
Path: architectural (new `Ann` constructor, new `Valid` clause, new `R` field).
Scope: **retirement only**. Reuse/aliasing and scan liveness are later slices (see Out of scope).

## 1. Goal

Spec 30.3 lists "Retire a published resource that is not needed by any remaining contribution, output
decoding, or remaining concrete storage operation". The slice-1/2 profile has no retirement: `Pub(pc)`
serves both as the logical published set and as the set of readable slots. This slice separates the two.
The reference state keeps a retired address in `dom σ` (ghost history); only its physical representation
goes away.

Success criteria:

- `Valid`, `checkPlan_iff`, `step_R`, `step_failed`, `step_not_stuck`, `done_correct`, `failed_correct`,
  `done_iff_model`, and the fused (`FValid`) and fault-oracle (`Faults`) theorems all hold for plans that
  contain `retire`, with their statements unchanged except where listed in section 5.
- All 180 existing fixture rows stay green; no existing mutation manifest regresses.
- Reading a retired slot is a plan defect, not an implementation error: the checker rejects it and the
  run is `stuck`, exactly like reading an uninitialised slot. A failing retire step could only be a
  fault, and the existing `Faults` oracle already covers that.

## 2. Decisions taken (user, 2026-10-11)

| # | Decision | Chosen | Rejected |
|---|----------|--------|----------|
| D1 | Slice scope | Retirement only, dense injective `place` | Retirement + reuse together |
| D2 | Effect of `retire` on memory | Clears each member's slot to `none` | View-only no-op |
| D3 | Retirement targets | Defined addresses only (`DefAddr P`) | Any published address, inputs included |
| D4 | "No remaining reader" | Enforced at the reader (`ReadyOK` over `Live`) | Also stated locally in `RetOK` |

Rejected design alternative: replace `Pub` by `Live` everywhere. It forces `R2` and the 29.3
conditions to re-derive the logical set from the commands, a much larger ripple for no gain.

## 3. Design

### 3.1 Syntax (`Plan/Syntax.lean`)

- `Ann.retire (B : List (DefAddr P))`.
- `groups`, `blocks`, `inits`, `keys` are empty on `retire`; new `Ann.rets : Ann P → List (DefAddr P)`.
  `Coverage1`, `Coverage2`, `coverage_iff_schedule`, `flatKeys_perm` are unaffected apart from a new
  case arm in `keys_perm_aux`.
- `retList pc := (π.prefixAnn pc).flatMap Ann.rets`; `Ret pc a := a ∈ (π.retList pc).map DefAddr.addr`;
  `Live pc a := Pub pc a ∧ ¬ Ret pc a`. Decidable instances alongside `Pub`/`Mat`.
- `Pub` is unchanged and remains the logical published set.
- Inputs are always live: `Ret` only mentions defined addresses (`P.input t = false` for `t : P.Defined`).
- Lemmas mirroring `pub_succ`/`mat_succ`: `ret_succ`, `ret_zero`, `live_input`.

### 3.2 Execution (`Plan/Memory.lean`, `Plan/Step.lean`)

- `readPub` and `SlotView .pub` use `Live` instead of `Pub`. `SlotView .acc` is unchanged
  (`Mat ∧ ¬ Pub`).
- `execRet B M` sets `place x.addr` to `none` for each `x ∈ B`. It is total (cannot be `stuck`), like
  `execInit`.
- `execAnn _ _ _ (.retire B) = .ok (execRet B M)`.
- `postAnn _ c (.retire _) = some c` (the reference state does not change).
- `slotView_injective` still holds (`Live ⊆ Pub`; the pub and acc cases are separated by `¬ Pub`).

### 3.3 Validity (`Plan/Simulation.lean` side conditions, `Plan/Validity.lean`)

- New `RetOK pc B := ∀ x ∈ B, π.Live pc x.addr ∧ P.output x.1.val = false`; added to `AnnOK`, `StepOK`
  and `Valid` (field `retOK`).
- `ReadyOK` is stated over `Live pc` instead of `Pub pc`. This is what enforces spec 30.3's "no
  remaining reader" (D4): an unconsumed occurrence whose footprint contains a retired address fails
  `ReadyOK` at its own `acc` command.
- No duplicate check inside a retire block: clearing is idempotent.
- Clause roles (extends the spec 31.1 role table):
  - Live, the `Pub` half: *safety* (a retire of an unpublished address would clear a live accumulator).
  - Live, the `¬ Ret` half: *diagnostic* (re-retiring is harmless).
  - not-an-output: *terminal* (`Decode` at `pc = m` needs every output live).
  - `ReadyOK` over `Live`: *progress*.
- Checker: `checkRet pc B`, wired into `checkAnn`; `checkPlan_sound`, `checkPlan_complete`,
  `checkPlan_iff` extended; `checkReady` uses `Live`. Fused: `FValid`/`checkPlanF` are `Valid`/`checkPlan`
  of `π.expand`, so a retire inside a fused command is covered by expansion.

### 3.4 Simulation (`Plan/Simulation.lean`, `Plan/Memory.lean` for `R`)

- `R3` (`pubSlot`) is stated over `Live`.
- New `R5` (`dead`): `∀ a, Pub pc a → ¬ Live pc a → M (place a) = none` ("a retired slot is free").
  It gives D2 a theorem, and is the invariant the reuse slice starts from.
- `R_start`: `R5` holds vacuously (`Ret 0` is empty).
- New `step_retire`: advances `R` using `place_injective` (retired and surviving slots are distinct) and the
  fact that retired addresses are published, so they are distinct from every accumulator address.
- `step_init`, `step_acc`, `step_pub` each need a small `R5` preservation argument: they write only
  unpublished slots (`dest_not_pub`, `place_injective`), so they never touch a dead slot; `step_pub` makes
  new members live, which is consistent with `R5`.
- `step_not_stuck`, `step_failed`, `step_failed_no_model`, `execAnns_R`, `execAnns_failed`, `R_transport`
  get a `retire` arm or the extra `Ret` equality; their statements do not change.
- `terminal_adequacy` needs one new lemma: for a valid plan, `Live m` holds at every output address
  (no member of any retire annotation is an output, so `Ret m` excludes outputs).
- `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model`, the fused
  corollaries and the `Faults` (`_E`, `_FE`) theorems keep their statements.

### 3.5 Testing

- All 180 existing fixture rows stay green with no row edited.
- New `PlanRetireTest` (checked against both `checkPlan` and `runPlan`; fixtures are authored from the
  plan in `PlanFixtures.lean` style):
  1. valid retire after the last reader: `done`, final memory has `none` at the retired slot;
  2. read after retire: `checkPlan` false, run is `stuck`;
  3. retire of an output: `checkPlan` false;
  4. retire of an unpublished accumulator: `checkPlan` false;
  5. fused command, retire after a read (valid) and retire before a read (rejected);
  6. retire under a fault oracle (`Faults`): the `_E` outcome is consistent with the fault-free run
     before the fault position.
- Mutation manifest, about 8 cycles. Planned mutants: `execRet` clears the wrong slot; `execRet` does not
  clear; `checkRet` drops the live clause; `checkRet` drops the output clause; `ReadyOK` over `Pub`;
  `SlotView.pub` over `Pub`; `R5` weakened; `step_retire` omitted from `execAnns_R`.
- Known equivalent mutant at the behaviour level: `readPub` ignoring `Ret`. Under `R5` a retired slot is
  already `none`, so the read is the same; the guard matters only to the proofs. It is recorded as an
  equivalent mutant, not chased.
- Per `slice-plan`: each mutation `expect` string carries a line number; any edit shifting lines in a mutated
  file needs a manifest re-run.

### 3.6 Docs

Updated inside the implementation plan (not as a post-hoc audit):
spec 30.2/30.3/30.4/31.1 "As formalized" notes (the header "no retirement" becomes "retirement of defined
published addresses, dense injective `place`"), the 33.2 note, the proof-status rows, and the
`Plan/AGENTS.md` node.

## 4. Out of scope (parked, not part of this slice)

- Reuse/aliasing: a `place` that is not injective in time, `place_injective`/`slotView_injective` reworked.
- Scan liveness (spec 33.2-33.4), and a plan that exhibits the two-buffer example.
- Retiring inputs (needs an ownership story for caller memory).
- Copy and relocate storage operations; in-kernel read-before-write.
- Concrete implementation-error sources beyond the abstract `Faults` oracle.

## 5. Statements that change

| Item | Change |
|------|--------|
| `Ann` | new constructor `retire` (about 24 constructor-case sites gain an arm) |
| `Plan.Valid` | new field `retOK`; `ReadyOK` over `Live` |
| `R` | `pubSlot` over `Live`; new field `dead` |
| `readPub`, `SlotView .pub` | guard `Live` instead of `Pub` |
| `checkAnn`, `checkReady` | new `checkRet`; `checkReady` over `Live` |

Everything else (coverage, `refState`, `postAnn` results, theorem statements of section 3.4) is unchanged.

## 6. Risks

- The `R5` preservation arguments touch the three largest step proofs (`step_init`, `step_acc`, `step_pub`).
  If `R5` turns out disproportionate it can be dropped; D2 then has fixture-level content only and the
  reuse slice adds it.
- The about 24 constructor-case sites include `Faults` and the fusion modules; per the Lean pitfalls memory,
  grep callers before changing signatures.
- The `Valid` change shifts line numbers in mutated files, so the slice-1 and slice-2 manifests need a
  re-run and `expect` repair.
