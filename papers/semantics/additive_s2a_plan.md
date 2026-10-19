# S2a: affine write slots in the Source oracle and the Source-level proofs: implementation plan

Status: prototype complete and mechanically replayed; this plan executes it by applying verified per-task patches.
Base: local `main` at `6fad5161` (B3 prepare-time guard landed; S1 landed earlier).
Branch / worktree: `worktree-additive-s2a-affine-write-slots` at
`/Users/williammacready/code/python/pyncd/.claude/worktrees/additive-s2a-affine-write-slots`
(Lean project `<wt>/leanncd`). This branch IS the execution branch: the plan, manifest and patches are already
committed on it. The prototype chain ends at scratch branch `proto-s2a-p3` (tip `ddbd82c5`); do not merge it.
Rationale: `papers/semantics/oracle_extension_s2_design.md` (§2 decisions, §4 S2a, item 7 probe result).
Authoring evidence (costs, dispatch table, survivors, deviations, checklist gaps) is in
`papers/semantics/additive_s2a_record.md`, not here.
Artifacts: `papers/semantics/additive_s2a_artifacts/` (`p0_extent_probe.md`, `p1_findings.md`, `p2a_findings.md`,
`p2b_findings.md`, `p2c_findings.md`, `p3_findings.md`, `p3_observed.md`, `p3b_findings.md`, the four mutation
drafts, the prototype's own `p*_patches/` directories: historical, NOT the shipped series).
Shipped patches: `papers/semantics/additive_s2a_files/patches/` (19 files, `leanncd/` paths only; `T4-07`/`T4-08` are the
review-driven additions A2/A1, prototyped on `proto-s2a-p4` after the independent review).
Manifest: `papers/additive_s2a_mutations_post.json` (32 cycles).

## 0. Goal, process weight, fixed decisions

**Goal.** The Source differential's exact oracle and the Source-level correspondence proofs cover writes whose LHS
slots are integer-affine forms over the statement's axes (`Y[2*a]`, `Y[a+1]`, `Y[a+b]`, `Y[2, a]`, `Y[3]`, diagonals)
and scatters with `fill = 0`, `reduce in {sum, rejectCollisions}`, so that S3a has an independent reference for
scatter-collision semantics. What is ASSERTED: four-leg parity on non-colliding affine `.assign` writes (rows a, b, c),
oracle-vs-executed-core parity on collisions (T3), and, after the review-driven addition T4-A2, legacy-vs-oracle value
agreement on the collision-sum scatters (legacy only: the checked plan refuses those slots by capability). Before A2 the
collision-sum agreement was only a comment and `p3_observed.md`. Concretely:
1. `AdmittedOutput` carries a virtual write shape and a destination map `dest`; the fiber/correspondence/program
   theorems are stated through `dest` (T1).
2. A second admission entry `admitSourceAffine` admits affine and policy-checked scatter writes and refuses
   out-of-range images statically (`writeOutOfRange`) and other scatter policies (`scatterPolicy`) (T2).
3. The oracle evaluates write forms, never `dest`; `Observation` derives executor-comparable occurrences from the
   oracle's own assignments (T3).
4. The differential's reference leg uses `admitSourceAffine`; three new structural known-difference conditions
   cover the divergences observed against production (T4).

**Process weight: Full.** Soundness surface (core proofs, raw-chain gating), new capability, 4 code tasks, 19
patches, 32 mutation cycles (`slice-plan` §0).

**Fixed decisions (do not reopen).** Design note §2 and §4, plus the prototype's resolutions:
- Cut: S2a is sum only. S2b (tropical carriers) is a separate plan written after this slice lands (Rule 13).
- Proof depth is the middle path: Program/fiber theorems and the executed core leg generalise; the raw-parse chain
  keeps its bare-slot hypotheses. Affine statements get NO raw-parse theorem, by construction.
- Scatter options (oracle and admission): `fill = 0` and `reduce in {sum, rejectCollisions}`; anything else is
  `.unsupported .scatterPolicy`.
- Reads stay bare: an affine READ slot is `.unsupported .affine` under both entries. Scan slots and `freeNorm` stay
  refused.
- The default entry `admitSource` and everything proved about it (`admitStatement`, `StatementFields`,
  `admitStatement_fields`, `admitSource_fields`, `admitRawSource`, RawCorrespondence/RawSemanticConnection/Provenance
  theorems) are unchanged in behaviour; they still refuse affine LHS slots and every scatter.
- `IsBare` is a witness (`exists bare : Slots source.axes (signature axes), bare.uids = indices and dest
  (sourceSlots.project w) = bare.project w`), not the structural equation `shape = signature axes and dest = id`;
  the structural form is the separate lemma `admitOutput_identity` with `isBare_of_identity` bridging them.
- Forms are DATA on `AdmittedOutput` (`forms : List WriteForm`, one per destination axis); their agreement with
  `dest` is the Prop `AdmittedOutput.FormsSpec`, proved for each of the two output builders, NOT a structure field
  (a stored proof would break retargeting `{ o with tensor := t, dest := d }` used by `SourceAffineDestinationTest`).
- The oracle's independence from `dest` is by construction (its code never mentions `dest`, `sourceSlots` or the
  admitted `shape`; it uses the destination TABLE ENTRY's extents). No fixture can distinguish a `dest`-based oracle
  (they are equal by `FormsSpec`); the observable variant is mutation (i) of T3. SCOPE OF THAT CLAIM (review F2, F3):
  it is independence from `dest` ONLY. The forms are extracted by `idxAffineForm`, which the oracle's input
  (`AdmittedOutput.forms`, via `Admission`) shares with production's lowering, compile and scan code, so a defect in
  `idxAffineForm` is invisible to every differential row; only the T3 hand-valued fixtures pin it, and they cover
  `.scale`, a two-unit-axis `.affine` and `.const` only (no `.shift` value fixture, no negative coefficient). Also,
  `FormsSpec` is a Prop proved for the two output builders only: a hand-built or retargeted `AdmittedOutput` (the T1 test's
  `retarget` builds one whose `forms` and `dest` disagree) carries no agreement and must never reach the oracle,
  `Observation` or `NumericalProfile`; today only T1's proof test builds one.
- f32 is the default dtype; the oracle and reference evaluator are f64-only. Every differential fixture in this slice
  declares f64 through the donor `snap` helpers (`SourceOracleAffineTest.snap`); no checked-plan f32 fixture is in
  scope (the Source differential's native legs are the checked plan and legacy evaluator on f64 programs).
- Models: Sonnet 5.5 high for implementers and per-task reviewers. Opus 5.5 high only for the T1 review and BOTH
  final whole-branch reviews.

## 1. Execution protocol

**Brief preamble (copy verbatim into EVERY brief):**

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command, no pipelines into git.
> Use absolute paths and `/usr/bin/git -C <worktree>`. Build only with
> `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`; never run `lake` from
> the worktree root. Use the Read tool for file windows and `rg -n` for search (pass FILE paths, not the
> directory named Source, to rg; no -g globs; no shell variables). Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and say so in the report if you breach it.

Plus per brief: "Budget: see the task's cap; run builds that may exceed 2 minutes with `run_in_background` and wait
for the notification; window-read (40-60 lines), never whole-file-read a file over ~20k characters; do NOT run the
full `Tests` target." Execution preamble source: `.claude/skills/new-slice/SKILL.md` (worktree already exists here;
skip its creation step, but its `prepare-worktree.sh` has already been run: check `ls <wt>/leanncd/.lake` before the
first build, and stop if Mathlib would cold-build).

**Applying a task.** Patches are `git diff <hash>^ <hash> -- leanncd` of the compiled prototype commits, applied in
TASK order (not the prototype's chronological order). The full 17-patch chain was applied on this branch and the
resulting `leanncd/` tree equals `proto-s2a-p3` (`git diff --cached --stat proto-s2a-p3 -- leanncd` empty).
Intermediate task states are NOT separately built by the author; the first build of each is the task's own.
Per task:
1. `/usr/bin/git -C <wt> apply --check --index <patch>` for each listed patch in order; then the same without `--check`.
   If one fails, STOP and report (base mismatch; do not hand-merge).
2. Build the task's targets (below), in the background when the task touches `Admission.lean`.
3. Read the task's production hunks and fixtures (windows) and tick the task's checklist and its §3 table rows.
4. Commit once per task (patches are already staged by `--index`), message per task, ending with
   `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.
5. Report: commit hash, targets built, turns/context. Write the ledger line before the next dispatch.

**Controller steps per task (not the implementer):**
`bash <wt>/leanncd/scripts/mutation-manifest.sh --task <Tn> <wt>/leanncd <wt>/papers/additive_s2a_mutations_post.json`
and read the table. A mutation that does not fail with its `expect` strings is a finding, never a pass. NOTE: the
`expect` positions in the manifest are the FINAL-state positions of the test files; T2's manifest entries are valid
after T2 only if no later task edits the same test file (none does: each test file is created and finished within
its own task) and Admission.lean positions (`T2-M7` expects an Admission position) are valid after T2 because T3/T4
do not edit `Admission.lean`.

**Reviews.** Per task: one mid-tier review of the task's commit diff plus the §3 table rows owned by the task
(reviewer appends findings to `papers/semantics/additive_s2a_review_<Tn>.md` as it goes; windows of 40-60 lines).
Final whole-branch review: TWO Opus lenses (§5). One fix dispatch per finding group, given only the relevant section.

## 2. Global constraints (exact values)

- **Baseline (measured).** `LeanNCD Tests` on main `6fad5161` before the slice: 8814 jobs, green. Expected after all
  four tasks: **8818 jobs**. The prototype measured the full `Tests` at its tip: 8818 jobs, "Build completed
  successfully", `Semantics.AxiomAudit` prints only `propext`, `Classical.choice`, `Quot.sound`. The prototype's own
  series was 8816 (T1 state, one new module: +2), 8817 (T2 + T4-01), 8818 (T3 state), 8818 (tip, although T4 registers a
  fourth module: increments 2, 1, 1, 0 are unexplained). So the total is the check, NOT a per-module count of one: the
  executor confirms that all four new test modules appear BUILT in the final `Tests` log by grepping their names. The
  controller separately built the T1..T3 task state (all five Lake targets, 8508-8584 jobs, listed in the record);
  other intermediate states were not built.
- **New test modules (lakefile.toml registration, one per task).** `Semantics.SourceAffineDestinationTest` (T1),
  `Semantics.SourceAdmissionAffineTest` (T2), `Semantics.SourceOracleAffineTest` (T3),
  `Semantics.SourceDifferentialScatterTest` (T4). No existing test is semantically edited; the single forced edit is
  two lines in `SourceRawCorrespondenceTest` (T1: the conjunct now takes `.1`).
- **Fixture and cycle counts (counted with `rg -c "^#guard" <file>` on the final tree; `example`/`theorem` counted with
  `rg -c "^(example|theorem)" <file>`).**

  | Task | Test file | `#guard` | example/theorem | Manifest cycles |
  |---|---|---|---|---|
  | T1 | `SourceAffineDestinationTest.lean` | 3 | 2 | 3 (all PROOF kills) |
  | T2 | `SourceAdmissionAffineTest.lean` | 46 (28 from the patches + 18 appended by `c9c86181` after the T2 review: negative and mixed-sign image, bare-slot `scatterPolicy`, `freeNorm`/scan refusal) | 0 | 10 (6 guard kills, 2 proof kills `T2-M2`/`T2-M7`, 2 guard kills `T2-M1`/`T2-M10` that the `6d35f5cd` survivor fixtures made possible) |
  | T3 | `SourceOracleAffineTest.lean` | 16 | 0 | 9 |
  | T4 | `SourceDifferentialScatterTest.lean` | 38 (17 + 21 from T4-07/T4-08) | 0 | 10 |

  Total manifest: 32 entries (T1 3, T2 10, T3 9, T4 10); `mutation-manifest.sh --check` on the final tree prints
  `manifest OK: 32 entries, 32 selected, every old-string unique`. `--check` verifies old-string uniqueness only; the
  `expect` strings are verified only by running the cycles (controller step above). The controller ran `--task T4` on
  the final applied tree: 10/10 PASS (record §11), including the six older cycles on `Differential.lean` after A1 rewrote
  `confirms`.
- **Exact shipped fixed values the fixtures observe:** inputs `X[a] = [1,2,3,4]`, `W[b] = [1,10,100]`, `|a| = 4`,
  `|b| = 3` (T3); `Y[2*a]` over `|k| = 7` gives `[1,0,2,0,3,0,4]`; `Y[a+b]` over `|k| = 6` gives
  `[1,12,123,234,340,400]`; `Y[2]` (constant slot) over `|k| = 4` gives `[0,0,111,0]`. Every value was observed from a
  run (`p2b_findings.md` §3), not derived.
- **Scatter extent (P0).** Production ignores the declared pinned shape of a scatter destination (always the derived
  stride-aligned extent, e.g. `S[2*i]` with `|i| = 4` is shape `[8]`); the oracle uses the DECLARED shape. This is the
  `scatterExtentOverridesDeclared` condition (T4). Table: `additive_s2a_artifacts/p0_extent_probe.md`.
- **Diagonal fact (P2a).** `Y[a, a] := X[a]` is ALREADY admitted by today's `admitSource` (bare path: `firstUIDs`
  dedups); S2a only adds a regression fixture (T2) and an oracle fixture (T3, fixture 5).

### Deliberately NOT done, with owner (Rule 14)

| Item | Owner / disposition |
|---|---|
| Tropical carriers (min-plus, max-plus), `mixedSorts` | S2b (own plan after this lands) |
| Scatter-collision semantics change, deletion of `CollisionReduce`/`ScatterOpts.fill`, range-error in production, checked plan honouring the declared shape | S3a |
| Tropical sorts, casts, constants in production | S3b |
| Affine READ slots (convolution/padding): still `.unsupported .affine` | out of S2 scope (design §4.3); unowned |
| Raw-parse theorem for affine statements (raw entry refuses affine statements by construction; `RawStatementFields`/`StatementFields` require `IsBare`) | documented gap (decision §2.2); unowned |
| Checked-plan capability refusals of multi-axis and constant affine slots (observed rows d, d', f): not conditions | unowned; with them no scatter-sum collision fixture reaches four-leg parity (legacy-only agreement) |
| `usedDType` can still mask a native divergence (decided in `checkRunProfile` before any native leg is read; pre-existing) | unowned; flagged in `p3b_findings.md` |
| `Provenance.admitIdentifiedSourceAffine` reports a misleading `.duplicateTensor "statement originals not unique"` on an unreachable runtime-`Nodup` branch (no accurate `SourceCause`; a new constructor touches `Adapter.lean` and its renderers) | unowned; cost ~1 small dispatch; needs `admitSourceAffine_originals` to remove the runtime check |
| `multiWriterScatter` encodes the single observed pair (`scanAxisNotIter` on both legs), not the design's `multiWriterScatter` refusal text; other multi-writer shapes (two hand-built scatters) not run | S3a |
| Constant slot under `.assign` fails at compile with `overlappingScatter` whatever the RHS (P0's scan error did not reproduce; cause undetermined) | S3a |
| Scatter parity fixture on the ORACLE leg (the oracle never runs a `.scatter` statement in a four-leg parity fixture; scatter appears in admission fixtures and differential rows) | unowned |
| JAX/other backends: unprobed | out of scope |
| `admitAffineWrite` duplicates the ~15-line write body of `admitStatement`'s `.assign` arm; `admitSourceAffine` duplicates the 4-line `admitSource` | cleanup candidate once both entries have proofs |
| Unproved/untested paths (`p2a_findings.md` "Not done"): (1) no statement/source-level `FormsSpec` theorem for `admitSourceAffine`; (2) no `admitSourceAffine_originals`; (3) no fixture for an all-`.const` write at admission level (empty support, `shape = []`); (4) no fixture for an RHS reading an axis the LHS does not mention (the T3 fixture 6/9 cover it at oracle level only); (5) `writeOutOfRange` slot index tested only at slot 0 before the T2 survivor fixtures, now also slot 1; (6) the `.rank` mismatch path (closed by the T2 survivor fixture) | listed; items 1-3 unowned |
| Known limitation: an executor occurrence whose contracted fiber is EMPTY (extent-0 contracted axis) leaves no oracle occurrence for non-bare rows | unowned; no fixture |
| Differential renderer does not print `ComparisonRun.conditions` | unowned |
| Unmeasured guards (review F8): the T2 range accept-neighbours and the affine-READ refusal guards are killed by no cycle (`T2-M2`, `T2-M7` stop the build at a proof; a proof-compatible STRICTER range check such as `writeValue f v + 1 < a.extent` is the mutation they exist for and is not in the manifest) | unowned; add that cycle if the guards are ever relied on |
| Over-detection and under-confirmation of the T4 conditions (review F9): `writeCollides` counts every term's read axes (a multi-term `Y[2*a] := X[a] + W[b]` reads as colliding because of `b`); two single-writer extent conditions on DIFFERENT tensors are never confirmed (`shapeOnly` needs every binding issue to belong to the head's declaration: safe direction, a generic divergence); `derivedShape` with a negative coefficient goes through `Int.toNat` and is unprobed | unowned |
| Enumeration cost: admission's range check (`coordAll` over the support box), the oracle and `writeCollides` (`eraseDups`, quadratic in the box) enumerate the whole box; fixture-sized only. Empty extents behave (vacuous check, no occurrence) | unowned |
| Bare-slot `.scatter` with `reduce := rejectCollisions` and a CONTRACTED axis (review F11): `admitAffineStatement` sends it to the bare path, the oracle sums over the contracted axis, `detectConditions` skips it (`nonBareWrite` false), and production DOES reject it (probed by A1: legacy `evalScatter Z: collision`, checked runtime `scatterCollision`), so it classifies as `nativeFailure` with no condition explaining it (pinned as `fF11`) | detection of the contracted-axis collision: parked, ~1 dispatch |
| T4-08 residuals: the checked RUNTIME collision and the multi-writer `scanAxisNotIter` carry no tensor identity and stay cause-only (a same-kind failure from another statement on those legs is still absorbed); binding is per tensor, not per statement; the checked arm's tightening to the two affine-slot capability constructors has no cycle or fixture; the reverse statement orders of `fOriginL`/`fOriginC` were not pinned | locator in `PlanRunFailure` (out of scope); the rest ~0.5 dispatch |
| EXTENT-CONDITION MASKING (review T4AB Major, verified): while `scatterExtentOverridesDeclared` is confirmed, `compareNative` returns the binding issues before `compareValues`, so no tensor's value in that program is compared and an unrelated value divergence in the same program is absorbed (before S2a the same program was a loud native discrepancy) | unowned; fix = per-tensor binding in `compareNative`, ~1-2 dispatches |
| T4-C review Minor (extends the F9 row): with head-only confirmation plus origin binding, two detected collisions where the head `Y` is single-axis and a later `Z` is multi-axis classify `nativeFailure` (checked preflight refuses `Z` first), not `known:collision`: safe direction | unowned; ~0.5 dispatch |
| T4AB review Minors: the both-legs requirement of `confirms` is half-tested (survivors: `checkedCollision := true`, dropping the checked `scanAxisNotIter` clause of the multi-writer condition, dropping either `shapeOnly` conjunct); `multiWriterScatter` confirms on an incidental `scanAxisNotIter`; the `fF'` comment says no condition although `detectConditions` emits the extent condition unconfirmed; only the head condition is tried | unowned; ~1 dispatch (guards/cycles) |
| T1 review Minors: `T1-M3` is guard-unkillable (one-term fixture); `AdmittedStatement.destination` is never evaluated by a guard; `IsBare` holds vacuously for any `dest` when a declared axis has extent 0 (the identity fact is `admitOutput_identity`); the `output_projection` conclusion is generalised through `dest` though its hypotheses are unchanged (T1 checklist (e) reworded accordingly) | unowned; ~0.5 dispatch |
| T3 review Minors: no negative-coefficient fixture, no two-term affine statement fixture, only slot 0 of a rank-1 destination tested | unowned; ~0.5 dispatch |
| T2 review Minors: `admitAffineWrite` copies of the nonSum/nonIdentity/undeclaredTensor/role-input checks are unexercised; `AxiomAudit` does not mention the new theorems | unowned; ~0.5 dispatch |

## 3. Sibling audit (case x class): deliverable of T2 and T4

Rows are consumers of `AdmittedOutput` fields and of the admission entry. Classes: R = required (the consumer needs
the field generalised), F = forbidden (the consumer must refuse/never see a non-bare output), S = SILENTLY IGNORED
(the consumer compiles and runs but does not look at the field). Every S cell is a candidate defect instance; cells
marked `*` have no guarding fixture. Derived from the findings files and a `rg` of `leanncd/LeanNCD` and
`leanncd/test` on the applied tree (`rg -n "admitSourceAffine|admitSource\b|admitIdentifiedSource"` and `rg -n` for
`.dest|.forms|.indices|.shape|.slots|.sourceSlots` over `leanncd/LeanNCD/Semantics`).

| Consumer | `dest` | `slots`/`sourceSlots` | `indices` | `shape` | `forms` |
|---|---|---|---|---|---|
| `AdmittedStatement.destination`, `Term.globalDestination`, `Term.fiber_partition`, `collectedBody*`, `empty_fiber`, `AdmittedStatement.fiber_partition` (T1) | R (composes `dest`) | R (at virtual `shape`) | S (not used) | R (types) | S (not used) |
| `Permutation`/`Program.destination`/collection theorems via `statement.destination` | R (through `destination`, unfolded nowhere) | S | S | S | S |
| Raw chain: `StatementFields`, `RawStatementFields`, `CertifiedRawStatement.output_projection`, `RawOutputSlots` | R under `IsBare` (pairs with `IsBare`; the destination equation holds for every output) | R under `IsBare` (reads `sourceSlots.uids`/`.project` through the bare witness; review F5: not "forbidden") | R (`RawOutputSlots raw memo slots output.indices`) | F | S* (no raw reading of forms) |
| `AdmittedStatement.destination_pullback` (statement CHANGED in T1-01), `destination_bare` (new), `pure_correspondence`, `Term.output_global_support`, `Term.globalFiber_reenumerate`, `Observation.sourceDebugFrom`/`sourceDebugAffine` (entry consumers) | R (through `destination`) | R | S | R (types) | S |
| `admitStatement` / `admitSource` (default) | R (builds identity `dest`) | R | R | R (signature axes) | R (`indices.map single`) |
| `admitAffineWrite`, `admitAffineStatement`, `admitSourceAffine` | R (builds `dest` from `hfit`) | R | R (`formsSupport`) | R (`supportShape`) | R |
| `Oracle.termFiber` / `destination` | S BY DESIGN (never mentions `dest`) | S (reads use `slots`; output does not) | S | S BY DESIGN (uses table-entry extents) | R |
| `Observation.normalizeOracleContribution` | S | S | R (bare: inversion over indices) | S | F (throws `nonBareWrite` unless forms == `indices.map single`) |
| `Observation.oracleOccurrences` / `normalizeOracleRow` | S | S | S | S | R (non-bare: restriction to `output.context.axes` uids, valued by sums) |
| `NumericalProfile.checkFiber` | S | S | R (bare support) | S | R (non-bare: forms uids, `formsAt`; occurrence-count check restored in T4) |
| `Differential.detectConditions` (`nonBareWrite`, `derivedShape`, `writeCollides`) | S | S | R (`nonBareWrite` is `forms != indices.map single`; review F5) | S | R |
| `Diagnostics.oracleContributions` (`flatMap occurrences`) | S | S | S | S | S (identical on bare rows) |
| `Provenance.admitIdentifiedSource` (default entry) | S | S | S | S | S (admission refuses affine first) |
| `Provenance.admitIdentifiedSourceAffine` | S* (runtime `Nodup` only; misleading cause) | S | S | S | S |
| `NativeSource.admission` / `runNative` (T4-01) | S (no library proof consumes `NativeSource.admission`) | S | S | S | S |

| Admission entry | Used by | Affine LHS | Scatter | Affine READ |
|---|---|---|---|---|
| `admitSource` | default `sourceDebug`, `admitIdentifiedSource`, the whole raw chain, all pre-existing tests | F: `.unsupported .affine` | F: `.unsupported .scatter` | F |
| `admitSourceAffine` | `compareSource` (via `sourceDebugAffine`), `NativeSource`, `admitIdentifiedSourceAffine`, T2/T3/T4 fixtures | R (admitted if image in range; else `writeOutOfRange`) | R (policy-checked; else `scatterPolicy`) | F |

Silently-ignored cells that are deliberate (oracle independence from `dest`/`shape`; reads using `slots`) need no
fixture. The starred cells are the findings to carry: raw-chain forms (S*), identified-source affine entry (S*).
**T2 deliverable:** the reviewer confirms the `admitSource`/`admitSourceAffine` rows by running
`rg -n "admitSourceAffine|admitSource\b" <each consumer file>` over the files below and records any consumer not in
this table in the review file. **T4 deliverable:** the same for `.forms` consumers (`rg -n "\.forms" <file>` for
`Oracle.lean`, `Observation.lean`, `NumericalProfile.lean`, `Differential.lean`, `Diagnostics.lean`).
Files: `leanncd/LeanNCD/Semantics/Source/{Admission,Statement,Fiber,Correspondence,ProgramCorrespondence,
RawCorrespondence,RawSemanticConnection,Provenance,Observation,NumericalProfile,Differential,Diagnostics,Oracle,NativeLegs}.lean`
(pass each as a FILE path to rg).

## 4. Tasks

Dependencies: T2 needs T1; T3 needs T2; T4 needs T2 and T3. T5 (docs) runs after T4. All Lake targets below are
`LeanNCD.Semantics.Source.<Module>` for modules and `Semantics.<TestName>` for test modules, as in `lakefile.toml`.

Risk/cost table (author-measured, harness turns from `token-report.py`; the prototype authors' self-reports differ
and are noted in the record):

| Task | Patches | Fixtures (guard/example) | Cycles | Prototype turns (measured; self-reported) | Cap, split |
|---|---|---|---|---|---|
| T1 | 5 | 3 / 2 | 3 | P1: 77 (self-report 104) | 60 turns, 250k; SPLIT FLAGGED: dispatch A = T1-01..T1-03 (core proofs) then dispatch B = T1-04, T1-05 (gating + test) |
| T2 | 3 | 46 / 0 (28 + 18 review guards) | 10 | P2a: 52 (self 60-75), P2c: 30 | 60 turns, 250k; no split (apply + build; cycles are the controller's); `Admission.lean` rebuild is the long step |
| T3 | 3 | 16 / 0 | 9 | P2b: 35 (self 74) | 60 turns, 250k; no split |
| T4 | 8 | 38 / 0 | 10 | P3: 34 + P3b: 60 = 94 (self 57 + ~80, controller figure 156); A2 45 harness tool calls (self 35); A1 57 (self ~46) | 60 turns, 250k; THREE dispatches: A = T4-01..T4-04 (production + the `T4-03` test scaffold), B = T4-05, T4-06 (fixtures AND the head-only `confirms` change in `Differential.lean`: its reviewer must read `classification`/`confirms`, review F6), C = `T4-07` (A2 guards) and `T4-08` (A1 origin binding; Opus review of the diff). A1 and A2 are PROTOTYPED (patches shipped, cycles run). Mutation cycles are ALWAYS the controller's step (§1), never inside an implementer dispatch |

Execution should cost less than prototyping (it applies patches), but this is a hope, not a measurement: the
prototype figures above are what was measured. Surface any breach.

### T1. Core generalisation to a destination map (Semantics proofs, no Eval)

Patches, in order: `T1-01-admitted-output-shape-dest.patch`, `T1-02-fiber-correspondence-dest.patch`,
`T1-03-program-correspondence-fiber-partition.patch`, `T1-04-raw-chain-isbare-gate.patch`,
`T1-05-affine-destination-test.patch`.
Prototype commits (verbatim from `git log --oneline --reverse 6fad5161..proto-s2a-p3 -- leanncd`):
`a3e89af6`, `42b495ae`, `c6de3d98`, `979e5ca3`, `a5fc0677`.
Files (from the patches): `leanncd/LeanNCD/Semantics/Source/{Admission,Statement,Fiber,Correspondence,
ProgramCorrespondence,RawCorrespondence,RawSemanticConnection}.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/SourceAffineDestinationTest.lean` (new), `leanncd/test/Semantics/SourceRawCorrespondenceTest.lean`.
Lake targets: `LeanNCD.Semantics.Source.RawSemanticConnection`, `LeanNCD.Semantics.Source.ProgramCorrespondence`,
`Semantics.SourceAffineDestinationTest`, `Semantics.SourceRawCorrespondenceTest`.
Commit message: `feat(semantics): AdmittedOutput destination map; fiber and program correspondence through dest (S2a T1)`.
Mutation cycles: `--task T1` runs 3 (`T1-M1 globalFiber ignores destination`, `T1-M2 collectedBody empty fibers read 1`,
`T1-M3 statement fiber keeps only first term`): ALL are PROOF kills (the mutated build fails at a theorem), so the
`#guard`s of this task are UNMEASURED, not shown strong. State this in the review.
Expected: all targets green; no existing test edited except two lines in `SourceRawCorrespondenceTest`; no `sorry`.
Checklist: (a) `AdmittedOutput` gains `shape`, `dest`, `slots`/`sourceSlots` at `shape`; (b) `IsBare` is the witness
form; `admitOutput_identity`/`admitOutput_bare` exist; (c) theorem NAMES unchanged and none weakened to bare-only
(`Term.fiber_partition`, `Term.globalDestination_partition`, `Term.collectedBody_correspondence`, `Term.empty_fiber`,
`AdmittedStatement.fiber_partition`); (d) `StatementFields`/`RawStatementFields` pair the bare-slot conjunct with
`IsBare` (left-nested in position 7, so positional `obtain` sites are unchanged); (e) `CertifiedRawStatement.output_projection`
keeps its hypotheses (no new one), while its conclusion is generalised through `dest` (reworded after the T1 review); (f) CONSEQUENCE: `admitStatement_fields` cannot prove `StatementFields` for
affine statements: check the raw entry still refuses them.
Reviewer lens: proof soundness. Is `IsBare` the right gate (does the raw chain need the witness or the equation)? Does
every theorem that formerly talked about the bare destination still say something strictly stronger? Opus review.
Patch-vs-tree note: `T1-04` and `T1-05` are independent of `T1-01..03`'s files except `Admission.lean`.

### T2. Admission of affine writes and scatter policy (+ survivor fixtures)

Patches, in order: `T2-01-admit-source-affine.patch`, `T2-02-admission-affine-fixtures.patch`,
`T2-03-survivor-fixtures.patch`.
Prototype commits: `ba33df5e`, `fb8311a0`, `6d35f5cd`.
Files: `leanncd/LeanNCD/Semantics/Source/{Admission,Adapter}.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/SourceAdmissionAffineTest.lean` (new).
Lake targets: `LeanNCD.Semantics.Source.Admission`, `Semantics.SourceAdmissionAffineTest`,
`Semantics.SourceAdmissionAcceptanceTest` (the pre-existing affine-refusal guard must still pass unchanged).
Commit message: `feat(semantics): admitSourceAffine admits affine writes and policy-checked scatter (S2a T2)`.
Fixtures: 28 `#guard` from the patches, 46 on the final tree (18 more appended by `c9c86181` after the T2 review: negative/mixed-sign image, bare-slot `scatterPolicy`, `freeNorm`/scan refusal) (donor: `SourceAdmissionAcceptanceTest` snapshot helpers; accept-neighbours throughout: e.g.
`snap 3 [k]` admits where `snap 2 [k]` refuses). Cases: flip (`Y[a+1]` refused `writeOutOfRange` under the new entry,
`.unsupported .affine` under `admitSource`); neighbour; `Y[2*a]`; `Y[2, a]`; `Y[a+b]`; diagonal; scatter `sum`,
`rejectCollisions` admitted and `max`/`min`/`overwrite`/`fill := 1` refused `scatterPolicy`; affine READ refused under both;
survivor fixtures from P2c (blamed slot 1 of `[a, k]`; `.rank 1 2` at slot 1).
Mutation cycles: `--task T2` runs 10: 6 killed by guards (`T2-M3`, `M4`, `M5`, `M6`, `M8`, `M9`), 2 by proofs
(`T2-M2`, `T2-M7`), and 2 more guard kills, labels `T2-M1 range-error slot forced to 0` and `T2-M10 rank check removed`.
Those two were SURVIVORS in P2c (no fixture noticed them); `T2-03-survivor-fixtures.patch` adds the fixtures that kill
them (blamed slot 1 of `Y` over `[a, k]`; `.rank 1 2` at slot 1), and the manifest records the observed killing
positions. Slot-blame and rank-check fixtures are therefore load-bearing: do not drop `T2-03`.
Unmeasured (review F8): `T2-M2` and `T2-M7` stop the build at a proof, so NO cycle exercises the range accept-neighbour
guards or the affine-READ refusal guards; `T2-M9`'s `expect` list (line 89 only, recorded before `T2-03`) is a subset
and omits the new slot-1 guard at line 148 (`mutation-manifest.sh` checks that every listed string appears, so this is
harmless; do not add 148 without observing it).
Expected: targets green; no existing test flipped; `NativeSource` unchanged in this task (it switches in T4-01).
Deliverable: §3 table rows for `admitSource` vs `admitSourceAffine` confirmed (see §3).
Reviewer lens: refusal completeness. Does any program that `admitSource` refused and `admitSourceAffine` now admits
carry a statement the correspondence theorems cannot handle? Is the image check exhaustive (box enumeration)? Is a
`.freeNorm`/scan slot still refused under the new entry?

### T3. Oracle forms, Observation, parity fixtures

Patches, in order: `T3-01-oracle-forms-observation.patch`, `T3-02-oracle-affine-parity-fixtures.patch`,
`T3-03-fixture-9-axis-in-form-unread.patch`.
Prototype commits: `eccc3676`, `923542dd`, `d1dfd0e4`.
Files: `leanncd/LeanNCD/Semantics/Source/{Oracle,Observation}.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/SourceOracleAffineTest.lean` (new).
Lake targets: `LeanNCD.Semantics.Source.Oracle`, `LeanNCD.Semantics.Source.Observation`,
`Semantics.SourceOracleAffineTest`, `Semantics.SourceOracleTest` (bare behaviour must be byte-identical).
Commit message: `feat(semantics): oracle evaluates write forms; Observation derives affine occurrences (S2a T3)`.
Fixtures: 16 `#guard` (donors: `SourceOracleTest`, `SourceProgramCollectionTest`, `SourceAdmissionAffineTest`,
`SourceDifferentialGeometryTest`; ONE shared bare neighbour `Y[a] := X[a]` through the same `parity` helper for all
fixtures, not one per fixture). Parity asserts: oracle `Y` equals hand value; executor completed and its tensors equal
the oracle's; executor `canonicalContributions` equal the oracle-derived occurrences; executor contribution values
equal hand `occ`. Out-of-range: tampered forms give `.writeOutOfRange 0 4 4` and `.writeOutOfRange 0 (-1) 4`.
Mutation cycles: `--task T3` runs 9 (all killed). Cycles (i), (iii), (vi) printed exactly 10 positions; the script may
truncate its listing, so those `expect` lists may be incomplete (the check passes on the listed ones).
Expected: targets green; existing oracle/observation tests unchanged.
Reviewer lens: independence and silent wrongness. Fixture 9 (axis in the form but not read) is the ONLY killer of
`support := [] ++ reads`; fixtures 6 and 8 are the only killers of `(g.1, o.value)`. Check non-symmetric inputs make
the readings differ (X and W are distinct-valued).

### T4. Differential for affine/scatter and structural conditions

Patches, in order: `T4-01-native-source-affine-admission.patch`, `T4-02-differential-oracle-occurrences.patch`,
`T4-03-differential-scatter-scaffold.patch`, `T4-04-scatter-structural-conditions.patch`,
`T4-05-differential-guards-fixtures.patch`, `T4-06-drop-redundant-legacy-phase-check.patch`,
`T4-07-legacy-vs-oracle-collision-guards.patch` (A2), `T4-08-origin-bound-condition-confirmation.patch` (A1).
Prototype commits: `b6e39e58`, `39fe34cc`, `cbfe630d`, `7aebc2dd`, `ff7a2172`, `11e92575`, then (scratch branch
`proto-s2a-p4`) `820bebab` (A2), `1b90ad0e` (A1).
Files: `leanncd/LeanNCD/Semantics/Source/{NativeLegs,Diagnostics,Differential,NumericalProfile,Observation,Provenance}.lean`,
`leanncd/lakefile.toml`, `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` (new).
Lake targets: `LeanNCD.Semantics.Source.Differential`, `LeanNCD.Semantics.Source.NativeLegs`,
`Semantics.SourceDifferentialScatterTest`, and the existing differential tests `Semantics.SourceDifferentialPolicyTest`,
`Semantics.SourceDifferentialGeometryTest`, `Semantics.SourceDifferentialIdentityTest`.
Commit message: `feat(semantics): differential covers affine and scatter writes with structural conditions (S2a T4)`.
Fixtures: 38 `#guard` in total (17 from `T4-03`..`T4-06`, 21 from `T4-07`/`T4-08`) plus tamper guards (donor: `SourceOracleAffineTest.snap`); rows (a)(b)(c) four-leg parity; (d)(d') legacy sums,
checked plan refuses by capability; (e)(f) production collides; (g) refuses at compile with `scanAxisNotIter "a"`;
(h6) oracle `writeOutOfRange`; (h9) both native legs value with shape issues 9 vs 8; (i) constant slot compile failure;
masking negative `fMask`; tamper `dropOccurrence true/false` (expect `occurrences 3 2`). Accept-neighbours: E vs A,
F vs F', G vs single writer, H9 vs A. Full table: `p3_observed.md`.
Conditions (detected from source, native-confirmed, ordered by pipeline stage, only the head confirmed):
`scatterCollisionRejected`, `multiWriterScatter`, `scatterExtentOverridesDeclared`.
Mutation cycles: `--task T4` runs 10 (P3b-M1..M6, A2-M1/M2, A1-M1/M2; the equivalent mutant M7 was NOT added: it was
removed as redundant code in `T4-06`). The controller ran all 10 on the final applied tree: 10/10 PASS. P3b-M6
(`oracleOccurrences` to `[]`) and A2-M1 printed 10 lines: possibly truncated (A2-M1's `expect` is only the three new
guards observed). The legacy-evaluator cycle A2-M3 (`Eval/Scatter.lean` `.sum` branch to `out.set! oc val`, fails exactly
the legacy-value guards 235, 237, 239, 241 and none of the collision-free neighbours) was run by hand once and is NOT in
the manifest (it rebuilds the `Eval` chain).
Expected: targets green; every existing differential test green with NO edit (the `compareSource` switch to affine
admission changes no existing refusal: checked in the prototype by the full `Tests` run).
Deliverable: §3 `.forms` rows confirmed (see §3).
Known corrections to carry: the `usedDType` path decides before any native leg is read, the new conditions are
stricter (decided after the native legs and only when `confirms` holds); `usedDType` can still mask a native
divergence (parked).
Reviewer lens: no masking. For each condition, does an unrelated native failure still classify as `nativeFailure`
(fixture `fMask`)? Does `confirms` need BOTH native legs? Is the count check restored for non-bare rows (tamper guard)?
After `T4-04`..`T4-06` alone the prototype did NOT satisfy this lens (independent review F1, Major): `confirms` was
cause-only (the legacy leg matched ANY `.scatterCollision`, the checked leg ANY runtime `scatterCollision` OR ANY
preparation `.capability _`, the multi-writer condition ANY `scanAxisNotIter`, and only the HEAD condition is confirmed),
so a native failure from a DIFFERENT tensor of the same source was absorbed; `fMask` differs only in error KIND. `T4-08`
(A1) closes it where the native error carries an identity:

**T4-A1 = `T4-08` (review-driven; PROTOTYPED on `proto-s2a-p4` as `1b90ad0e`; Opus review of the diff).** Observed
(`p4a1_findings.md`): the legacy `scatterCollision` names the destination tensor and the checked preparation refusal
(`multiAxisScatterLhs`/`scatterOrAffineLhs`) carries a context string `"Y: affine LHS slot"`: both are now bound to the
condition's tensor (the checked arm also now accepts only those two affine-slot capability constructors instead of any
`.capability _`: NOT covered by a cycle or fixture, parked ~0.5 dispatch). The checked RUNTIME collision
(`PositionalInputError.scatterCollision`: coordinates only) and the multi-writer `scanAxisNotIter` (axis name only, both
legs) carry NO tensor identity and stay CAUSE-ONLY (docstrings say so); binding is per TENSOR, not per statement, because no
native error carries a statement index. Probe F11: production DOES reject a bare-slot contracted-axis `rejectCollisions`
scatter (legacy `evalScatter Z: collision`, checked runtime `scatterCollision`), while the oracle sums it and
`detectConditions` skips it, so it classifies as `nativeFailure` with no condition (an undetected divergence, pinned as
`fF11`, detection parked ~1 dispatch). Negative fixtures `fOriginL` and `fOriginC` (same kind, different tensor) moved
from the wrong `known:collision` to `nativeFailure`; their accept-neighbours (Z gets a plain write) stay
`known:collision`. Cycles A1-M1 (legacy binding reverted: fails exactly `tag fOriginL`) and A1-M2 (checked binding
reverted: fails exactly `tag fOriginC`). The original specification, kept for the executor's checklist:
 1. FIRST observe (do not guess) with the `observe` helper of `SourceDifferentialScatterTest.lean`: which native errors
    carry a tensor or statement identity (`scatterCollision` carries a destination name; check whether the checked
    plan's `capability` refusal and the legacy `scanAxisNotIter` compile error name one) and what production does on a
    bare-slot `.scatter` with `reduce := rejectCollisions` and a CONTRACTED axis (`S[i] := X[i, j]`, review F11).
    Record the observed table in `papers/semantics/additive_s2a_record.md`.
 2. Negative fixture (donor: `fMask`, change: make both statements raise the SAME error KIND from different tensors):
    statement S1 = the detected collision `Y[a+b] := X[a]*W[b]`; statement S0 = a second, undetected failure of the same
    kind on another tensor (a bare-slot `rejectCollisions` scatter with a contracted axis if the probe shows production
    rejects it, else another undetected same-kind failure the implementer constructs). Expected: NOT
    `knownContractDifference` for the S1 condition; the classification stays a native failure. The implementer pins the
    OBSERVED classification, and the fixture must fail on the prototype's cause-only `confirms`.
 3. Production change in `Differential.lean` (`confirms` and the per-leg predicates): compare the native error's
    tensor/statement with the condition's. Where a native error carries NO identity (report which legs/causes), leave that
    leg cause-only, say so in a docstring and in the §2 table, and keep the other leg origin-bound.
 4. Manifest: add one cycle per bound leg (confirmation reverted to cause-only; expect = the new negative fixture's
    line, copied from the observed failure). The controller runs them; a surviving cycle is a finding.
**T4-A2 = `T4-07` (review-driven; PROTOTYPED on `proto-s2a-p4` as `820bebab`).** Result (`p4a2_findings.md`): guards at the
end of the test file assert, by exact bits and against hand-computed cells written beside them, that the LEGACY leg
equals the oracle for `fD` (`[1,12,123,234,340,400,0]`) and `fD'` (`[0,0,0,10]`) (no `ComparisonRun` field means exactly
that: `legacyComparison` is a tolerance-profile comparison used as one conjunct), with collision-free accept-neighbours
`fN` (`Y[a+4b]`, declared extent 16: production derives 16 for that form, a declared 12 gives a shape issue) and `fN'`.
The original specification, kept as a checklist: add to
`SourceDifferentialScatterTest.lean` (append at the END of the file) guards asserting that the LEGACY leg's output tensors
equal the oracle's for the collision-sum scatters `fD` and `fD'`, named and commented as LEGACY-ONLY agreement (the checked
plan refuses those slots by capability, so four-leg parity is impossible), plus an accept-neighbour (a collision-free
scatter whose legacy values equal the oracle's). Cycle: one mutation of the ORACLE's collision handling that makes
the legacy-vs-oracle guards fail (cheap: `Oracle.lean` only). An optional second cycle mutating legacy `Eval/Scatter.lean`'s
`.sum` branch (`prev + val` to `val`) is EXPENSIVE (it rebuilds the `Eval` chain); run it once by hand and record the
result in the record rather than shipping it in the manifest.

### T5. Documentation sweep (no code)

Edit, by value-grep (commands; each hit is either updated or recorded as unchanged with reason):
1. Job counts: `rg -n "8814|8816|8817|8818" <files>` over `leanncd/LeanNCD/Semantics/AGENTS.md`,
   `leanncd/AGENTS.md`, `papers/semantics/lean_executable_semantics_path.md`, `papers/semantics/additive_production_decision_note.md`,
   `papers/semantics/additive_collection_slice1_record.md` (historical records are NOT edited; they keep their dated counts).
2. Fixture counts and module lists in the Semantics node: `rg -n "Test.lean|guards|fixtures" leanncd/LeanNCD/Semantics/AGENTS.md`;
   add the four new test modules and the discoverability entry below.
3. Path doc: `rg -n "affine|scatter|S2a|S2|oracle" papers/semantics/lean_executable_semantics_path.md` (additive sections).
4. Gap audit: `rg -n "G04|F01" papers/semantics/tensor_logic_semantic_gap_audit.md`: state what S2a closes (affine
   LHS/scatter in the oracle) and what remains (S2b, S3).
5. Design note and decision note §E rows: `rg -n "S2a|S2b|S3a" papers/semantics/oracle_extension_s2_design.md papers/semantics/additive_production_decision_note.md`;
   mark S2a landed with the merge hash after merge. There is no separate master-plan blockquote for this lineage
   (`rg -c master` over the docs listed in this task finds none; review F10): the decision note §E rows and the design note
   §7 are the places. Step 1 is expected to find nothing in the two AGENTS.md files (0 hits for the job counts there);
   the real edits are steps 2-6 and the discoverability entry.
6. Oracle statements in the Source modules: `rg -n "bare-slot fragment|bare slot|BareOutputSlots|crossStatement|refuses.*affine|\.affine" <file>` for
   each of `leanncd/LeanNCD/Semantics/Source/{Oracle,Admission,Observation,Differential,NumericalProfile,Adapter}.lean`.
   Any docstring saying the oracle is limited to a bare-slot fragment is rewritten to the affine fragment with sum-only scatter.
**Discoverability (the deliverable):** a new reader finds the affine fragment in `leanncd/LeanNCD/Semantics/AGENTS.md`,
Source section: the two admission entries (`admitSource` default, `admitSourceAffine` differential), `AdmittedOutput.forms`
vs `dest`, `FormsSpec`, `IsBare` as a witness, the explicit gap "affine statements have no raw-parse theorem", and the
three conditions. Keep any hook-injected section of that node under ~3k characters (trim before editing if over).
No `File.lean:NNN` in any shipped text; cite identifiers. Docs only: no builds needed, but run
`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd LeanNCD.Semantics.Source.Oracle` if a Lean docstring is edited.

## 5. Final reviews and merge (Rule 13)

After T4 and T5: the controller runs the manifest UNFILTERED (not `--check`):
`bash <wt>/leanncd/scripts/mutation-manifest.sh <wt>/leanncd <wt>/papers/additive_s2a_mutations_post.json`, then the full
`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd Tests` in the background (~25 minutes), expecting
**8818 jobs, Build completed successfully** and `Semantics.AxiomAudit` standard axioms only. Both Opus whole-branch
reviews run in parallel, each appending findings to `papers/semantics/additive_s2a_review_final_<lens>.md`:
(a) semantics/proof soundness: the `IsBare`/`FormsSpec` design (witness vs equation; why `FormsSpec` is not a field),
raw-chain gating (the raw entry still refuses affine; nothing proves a raw reading of forms; `output_projection`
unchanged signature), the independence-by-construction claim of the oracle;
(b) regression/differential: no pre-existing test edited beyond the two forced lines; `compareSource` switch cannot
wrongly refuse a program; no condition masks a native divergence (including the same-kind/different-origin case closed
by T4-A1) and legacy-vs-oracle collision sums are asserted (T4-A2); the §3 starred cells.
One fix dispatch per finding group.

Merge: `ExitWorktree` keep, then `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff worktree-additive-s2a-affine-write-slots`
(local `main` only), confirm `git diff --stat main worktree-additive-s2a-affine-write-slots` is empty, remove the worktree,
`git branch -d`. Do NOT push; say that `main` is ahead of `origin/main`. The prototype scratch branches
(`proto-s2a-*`) remain: ask before `-D`. Record the measured execution total in the record (target <= ~175M, Rule 6).

## 6. Parked (one line each; see §2 table for owners)

S2b tropical carriers; S3a/S3b; affine READ slots; `admitSourceAffine_originals` + a proved `Nodup`; statement/source-level
`FormsSpec` theorem; all-const write admission fixture; `usedDType` masking; `admitAffineWrite` body dedup; conditions
for the checked plan's capability refusals; scatter parity fixture on the oracle leg; extent-0 contracted fiber under
non-bare rows; renderer printing `conditions`; JAX unprobed; a hand-valued `.shift`/negative-coefficient fixture for
`idxAffineForm`; a stricter-range-check mutation for the T2 accept-neighbours; the `writeCollides`/`derivedShape`/
multi-tensor-extent limits (§2 table).
The review Minors and the extent-condition masking Major recorded in the last six rows of the §2 table (T1, T2, T3, T4-A/B/C reviews) are parked there, not here.
