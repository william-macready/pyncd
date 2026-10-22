# Part V slice 4 (typed buffer reuse): independent review

Audience: the repo owner (William) and whoever fixes the findings below.
Subject: the slice documented in `plan_layer_slice4_plan.md` and `plan_layer_slice4_record.md`, merged
locally as `c44f8a21` (range `4ffdc342..84b1cc1c`, 10 commits, not pushed). Reviewed 2026-10-12 by a
different agent from the one that wrote the slice.

## Verdict

**The Lean change looks sound. The tests, manifests and some documents are weaker than the record says.**
Two independent soundness passes (one of them a full old-versus-new read of `Simulation`, `Validity`,
`Step` and `Memory`) found no defect. There are three Important findings, all about evidence and status
rather than about the semantics, and a set of Minor ones. I recommend fixing the three Important ones
before pushing.

## What was verified independently (not taken from the record)

| claim in the record | independent result |
|---|---|
| full default build, 8796 jobs | reproduced: `Build completed successfully (8796 jobs)`, no `^error`, four pre-existing `declaration uses sorry` warnings outside Plan |
| axiom audit, 5992 constants, standard axioms only | reproduced in the same build (`Semantics.AxiomAudit`) |
| 354 fixtures = 174 `#eval check` rows + 180 `example`/`theorem` items | reproduced with the `rg -c` method; new modules 26, 22, 25 (`PlanReuseTest`, `PlanReuseStorageTest`, `PlanReuseWrapperTest`) |
| no `sorry`/`admit`/`axiom`/`native_decide` in Plan files | reproduced (`rg` finds none) |
| 64 mutation verdicts pass (20 + 15 + 9 + 10 + 10) | **partly reproduced.** Re-run in an isolated worktree, one manifest after another: slice-4 10/10, slice-3 10/10, D7 9/9. Slice-2 and slice-1 were still running when this report was written; see "Open items" |
| `mutation-manifest.sh --check` clean | reproduced for all five manifests (20, 15, 9, 10, 10 entries, every old-string unique) |
| all baseline assertions preserved | reproduced by a script comparison of the 13 migrated test modules: all 141 `#eval check` names remain and every expected value is byte-identical; no theorem or example deleted or weakened (details below) |
| patch replay verified | **not re-checked** |
| 8796 jobs and 5992 constants | each reproduced; the docs agree with each other |

## Soundness (0 Critical, 0 Important)

Method: read the contract (`plan_layer_slice4_plan.md`, the design spec decisions D1-D6), then the code and
the old-versus-new diffs. Evidence is by identifier.

- **Placement is typed.** `Slot` is `InputSlot` plus `BufferSlot`. `locate` returns a bounded index with a
  sort certificate, and `place` sends defined addresses only to buffer slots. A defined address cannot land
  in input storage, outside capacity, or in a buffer of another sort.
- **The layout checker is exact.** `mem_resourceList` shows every resource is enumerated (every address as a
  published resource, inputs included, plus every defined address as an accumulator). `checkLayoutAt` checks
  every ordered pair. `checkLayouts` covers boundaries `0` through `commands.length` inclusive, which is
  exactly `LayoutOK` at each `pc ≤ commands.length`; there is no off-by-one at the final boundary.
  `checkPlan_iff` follows from the sound and complete theorems, and `checkPlanF` is `checkPlan` of the
  expansion, so fused plans are checked at their internal boundaries.
- **Premise placement is right.** `step_init` needs the post-boundary layout; `step_acc` and `step_retire`
  need the pre-boundary layout; `step_pub` and `step_failed` need none; `step_R` carries both. Every call
  site obtains them from `Valid.layout_boundary` (singleton) or the expansion's layout (fused).
- **Kernels.** Argued case by case from `LayoutOK` at the boundary each proof uses: a retire followed by an
  init into the same slot in the next command (accepted and correct); a fused retire-then-init (accepted)
  and the reversed order (rejected at an internal boundary); two members of one `initZero`, `acc` or
  `retire` block sharing a slot (rejected); an accumulator materialised into a slot a live published
  address occupies (rejected); an address's accumulator slot differing from its published slot (impossible,
  both come from `place` of the same address); an output sharing a slot with an internal tensor (rejected
  while both are represented, allowed once the internal one is retired).
- **`R.dead` changed meaning**, from "a retired address's slot is `none`" to "every physical slot that no
  resource currently maps is `none`" (including unused capacity). This is a necessary generalisation,
  because the old form is false once a slot is reassigned. It is established by `R_start` and re-proved by
  init, pub and retire.
- **Statement changes.** The only added hypotheses are the layout premises above plus allocation equalities
  on the prefix-transport lemmas (`execAnn_prefix`, `R_transport`, `decode_prefix_congr`); every call passes
  `rfl` (`expand` keeps the allocation). All are derivable from `Valid`/`FValid`. No hypothesis was removed
  and no conclusion weakened. `step_pub`, `step_failed`, `step_failed_no_model`, the `refState_*` lemmas, the
  `*OK` predicates and `checkPlan_iff` are unchanged apart from the memory type. The casts are justified
  only by the allocation's own sort certificate and no cast leaks into a downstream statement.
- **Computability.** The checker definitions are plain computable `def`s and run under `#eval`.

## Important findings (each confirmed by hand by the reviewer of this report)

### I1. The inherited mutation manifests lost their failure locations

All 55 line-anchored `expect` strings in the slice-1, slice-2 and slice-3 manifests (20, 15 and 20) were
reduced to a bare file name followed by a colon. Measured with `rg` on the manifests before (`4ffdc342`)
and after: line-anchored strings 20 to 0, 15 to 0, 20 to 0 (the D7 manifest never had any).

Concrete example, `S3-M3` (`checkRet` always true). Before: the build had to fail at both the soundness
proof and the completeness proof of `checkRet`, each with `Type mismatch`. After: the strings are
`Validity.lean:` and `Type mismatch`, so any `Type mismatch` in a log that mentions `Validity.lean`
satisfies it. `S3-M1` and `S3-M2` were reduced the same way. `mutation-manifest.sh` only checks that each
string occurs somewhere in the mutated build log, so a mutant that breaks one of the two intended sites, or
that breaks for an unrelated reason in the same file, still passes. Multi-site entries pin fewer sites than
before; `A1-b` now has the same expect list as `A1-a`.

The brief this slice was given said to repair only the line and column part when line numbers shift. The
record states that five anchors were repaired; in fact all of them were stripped.

Fix: restore the multi-site anchors with their new locations, taken from an unfiltered re-run's first
error lines per cycle (the slice-3 follow-up did exactly this for slices 1 and 2, keeping the message text).
The independent re-run logs made while writing this report contain the observed locations.

### I2. Five live documents still say the slice's gates are pending

The slice landed and its record and plan header say all 64 verdicts pass, both reviews are adjudicated and
the merge is `c44f8a21`. These still say otherwise: the spec intro paragraph before the proof-status table
("mutation, fresh review and integration gates remain pending"); `leanncd/LeanNCD/Semantics/AGENTS.md`
("Current artifact"); `leanncd/LeanNCD/Semantics/Plan/AGENTS.md` (Purpose, and the Pitfalls manifest bullet:
"Slice-4 rerun results are pending"); the path doc section "Slices 1-4 profile, fixtures and mutations"
("Actual rerun kills ... remain pending"), which contradicts the path doc's own snapshot; and
`plan_layer_slice4_plan.md` (section 3 "mutation kills are not yet observed for this branch", and section 4
still titled "Remaining execution tasks" although every task in it is complete). The close-out commit
(`84b1cc1c`) touched only the design spec, path doc, plan and record.

Fix: replace each sentence with the landed status (64/64, reviews adjudicated, merge `c44f8a21`, local and
unpushed).

### I3. Two of the three "retention" rejections would pass without any buffer reuse

In `PlanReuseStorageTest`, the row `storage-retention-rejections` combines three plans. `retireOutput`
appends a retire of the output, which `RetOK`'s not-an-output rule already rejects. `overwriteOutput`
re-initialises an already published address, which the old initZero freshness rule rejects. Both would be
rejected identically under the default allocation, and the row prints only `checkPlan` for them (not
`checkLayouts`). Only `retainedInternal` exercises the new layout clause. The fixture comment ("output
storage cannot be cleared or claimed again") claims more than is tested: nothing shows a later internal
tensor being refused a live output's slot, or the corruption an unchecked run would produce.

Fix: add a fixture where the output is computed first and an internal tensor placed in the same slot is
computed second (checker false at the layout clause, unchecked run corrupts the output), with a
default-allocation twin that passes.

## Minor findings

Library
- The theorem that plans using the canonical allocation satisfy the new layout clause
  (`checkPlan_of_canonical`) exists only in the test file `PlanFixtures.lean`. The library has its two
  ingredients (`place_injective`, `layoutOK_of_place_injective`) but no combined theorem. A short lemma in
  `Validity.lean` with a `#print axioms` line would make "old plans stay valid" a library fact.
- `execAnn_prefix`, `stepCommand_single`, `place_sort`, `start_read` and `cast_option_none` have no
  `#print axioms` line of their own; the design (section 7.5) asks for one per new theorem. Not an axiom gap
  (the theorems that use them are printed).
- `slotView_injective` gained a hypothesis `hinj`; its only caller supplies it and the old unconditional form
  is false under reuse, so the change is required. `execAnn_prefix` now states its result with casts; its
  only caller passes `rfl`.

Documents
- The path doc calls slice 4 "compiled" in a heading, its TOC entry, the roadmap line, the 4.9 intro and the
  snapshot, while also saying it "landed locally". Rename heading and TOC anchor together to "landed
  (local, unpushed)".
- `leanncd/AGENTS.md` still says "Part V slice 1-3 plan layer" in the "Semantic explorations" row.
- A `Plan/AGENTS.md` pitfall ("Retiring an output or retiring twice still runs to `done`") holds only for
  the canonical allocation; under reuse a second retire can clear a slot's new occupant. The Contracts line
  "outputs cannot be retired" holds only because the checker rejects it, not the runner.
- The docstring of `structure R` in `Memory.lean` still says "slice-1 to slice-3 profile".
- The record says the live plan is 244 lines; it is 254 (add "at authoring time" or drop the number).

Tests and manifests
- The `A2-e` equivalence-control mutant now fails inside `Step.lean` ("split failed") instead of in the
  Simulation proofs, so what it exercises changed. The other retargeted mutants keep their meaning.
- `S4-M6` (a `dead` mutation with `∨ True`) dies only because `R_start` uses `rfl`; in the library `dead` is
  used only to re-prove itself, and the theorems that depend on it are test theorems the manifest does not
  target.
- `reuse-good-empty-output` cannot fail on layout: `routed chainBody` has no output, so the bad twin also
  prints `some []`. Real decode under reuse is covered by the storage fixture.
- No reuse fixture retires point 0 again after point 2 has taken its slot, although the record says the
  no-second-retire rule now protects the new occupant.
- The D7 manifest has no `expect` strings, and `Faults.lean` changed in this slice, so its 9 passes only
  show the build broke somewhere.
- One concrete `rfl` in `PlanFusionCorrectnessTest` is now derived from the library theorem `runPlan_agree`:
  still sound, no longer an independent check.
- Capacity zero is tested only through the default allocation of an empty tensor, not a custom buffer.

## What the new tests do well (so the findings are in proportion)

- Preserved baseline: 13 migrated modules, all 141 check names present with byte-identical expected values;
  proofs of `checkPlan = true` now go through a proved lemma plus `decide`, proofs of `= false` are still a
  full `decide`; nothing passes vacuously.
- Accepted reuse plan (`rtInitAfter` donor): row `[4,3,4]` against the canonical `[none,3,4]`; `R` at every
  boundary; the shared slot reads `[none,0,4,4]` at pc 4 to 7, so the test writes into the reused slot and
  reads the new occupant back.
- Rejecting twin: checker false, unchecked run `done` with point 1 reading 1 where its true value is 3.
- Collision classes pub/pub, pub/acc and acc/acc each separated from a legal separate-buffer neighbour; the
  final boundary has its own discriminator (clean at pc 0, collision at pc 1); fused plans have every outer
  boundary clean and only an internal expanded boundary false.
- Fault-oracle rows land after the write to the reused slot, with `R` at the error state.
- New clauses covered by mutants: omitting the layout check, skipping the final boundary, dropping pub or acc
  resources, the role guard, retirement clearing. Covered only by proofs or fixtures: premise placement of
  `step_init` versus `step_acc`, internal fused boundaries, empty unused capacity, input-slot separation and
  sort checking (both by construction).

## Process note

Partway through this review the reviewer entered an isolated worktree to run the mutation manifests, and the
harness then blocked the review agents' access to the main checkout. The soundness reviewer could not diff
`Simulation`, `Validity`, `Step` and `Memory` and inferred their old statements from call sites, so that part
was re-run afterwards with access restored and reached the same conclusion. The documents and tests reviewers
recovered access and re-ran their checks. Lesson for the next review: run the mutation re-runs after the
read-only lenses finish, or from a separate session.

## Open items at the time of writing

- Independent re-run of the older manifests: slice-4, slice-3 and D7 passed (10/10, 10/10, 9/9); slice-2 and
  slice-1 were still running. The result of the remaining two should be appended here or in the slice record.
- The patch replay was not re-checked.
- Recommended before pushing (11 commits ahead of `origin/main`): fix I1, I2 and I3; the Minor items are
  optional and can ride in the same pass.
