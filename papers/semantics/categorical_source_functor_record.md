# Source-category functor — authoring and execution record

This is provenance/accounting, not a second live plan. Execute
[categorical_source_functor_plan.md](categorical_source_functor_plan.md).
The [prototype record](categorical_source_functor_prototype_record.md) remains
unchanged historical authoring-(a) evidence. The handoff is a goal brief.

## Authoring (b): bounded fresh synthesis

Date: 2026-11-08. Worktree:
`/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update`.
Frozen base: `19c9d6446552c4f4c507c89be94c3561a94ec5ea`.
Branch: `agents/categorical-source-functor-update`.
Session: `37386608-c5a8-4c82-a88b-0d50cc6e834c`.
Process Full: new source presentation/category/functor soundness surface.

This fresh dispatch read the handoff, slice-plan discipline, prototype record,
package/receipt/control/snippet/replay artifacts and inspected verification
scripts. Patch windows audited the exact design claims; no target/source
module re-exploration or new design/code was undertaken. Current synthesis
and Lean entry-point windows/greps located directly stale documentation for
later controller edits. All reads used bounded windows.

Only the live plan and this record were added. Existing verification commands
regenerated module snippet logs/snippets.json and replay.json; those are
verification outputs, not prototype source changes. No reconstruction, source
edits, real-index staging, commits, deletes of prototype files, merge, push,
primary-file access/edit or other-worktree operations occurred. The replay's
private index was removed by its existing finally handler; snippet scratch
was removed by the existing wrapper. No files were written to system temporary
directories. Worktree metadata was read via git in this worktree only.

### Compact evidence/provenance ledger

| Item | Historical authoring (a) | Fresh authoring (b) |
|---|---|---|
| Base identity | Recorded full base in package | Actual HEAD equals package base |
| Source/patch/wiring/copy identity | Frozen compiled hashes | `package.py --audit` PASS: 8 files, 3 patches, final lakefile, 3 identical copy bodies |
| Ordered patch replay | Alternate index applied task1, task2, task3; all bytes equal | `--replay-check` PASS; real worktree/index untouched |
| Module snippets | Eight final real-module snippets exit 0 | `--snippets` PASS: all eight real-split modules |
| Universe/API snippet | Compiled after repairing noncomputable example | Recompiled frozen `universe_check.lean`; Object/WholeInterface/Term/Hom `Type 1`, actual functor and both category instances accepted |
| Manifest schema/old strings | Populated ten entries, unfiltered check passed | Unfiltered `--check`: 10 entries, 10 selected, every old string unique |
| Actual mutation execution | Populated unfiltered 10/10 expected failures, identical restores, restored builds green | Not rerun: would mutate source, outside this authoring objective |
| Full release-target build | Final 8,919 jobs, exit 0, preserved log | Not rerun: no source edits; controller release build remains mandatory |
| Source/copy/namespace audit | Standard axioms, no proof shortcuts; exact copied maps | Source shortcut scan clear; exact-copy audit and regenerated namespace output checked |
| All receipt identities | Fourteen frozen identity entries | Every artifact SHA256 in prototype receipt matched before output regeneration |
| Plan code blocks | Compiled patches supply Lean | No inline Lean blocks introduced |
| Plan review/release/integration | Not performed by prototype | Pending controller gates; not represented as green |

### Immutable identity anchors

All full source hashes and final wiring/copy hashes are in `package.json`.
The prototype receipt is historical and must not be regenerated to erase its
scope/overrun evidence.

| Artifact under `papers/semantics/categorical_source_functor_artifacts/` | SHA256 observed in authoring (b) |
|---|---|
| `package.json` | `f31075967efdcf68d491d6ef3c4bf1dccf33871b4cd46b23982bd232e010df31` |
| `package.py` | `07854051010e08c59ea59b6a78cb9b457483bf237555fbcb6f42fc9612ad3adb` |
| `verification_receipt.json` | `9d35d450060560ef93d5fd4ab92067c1a8d3fcc9498125a30f93e8b15ead9d04` |
| `task1.patch` | `a089ffe7b6753cce0be4b7c812e792650d4b8a01f5e92a62a3e6554c3fba6c03` |
| `task2.patch` | `cd9bdc1196bacab0d21bfd901389b4069e4239be3c77fa1271bc3a43d2377fad` |
| `task3.patch` | `a81bdf2b10ac7fb4a784bd8face150a8b9518e7fe223c64f058e23063861d671` |

Receipt checks covered these patches plus package.py/json, snippets.json,
replay.json, observed_controls.json, mutations_verified.log/md,
universe_check.lean/log, the populated mutations_post.json and the preserved
full-build log. Snippet log names contain fresh scratch identifiers, so
regenerated logs are fresh verification evidence, not immutable log identities.

### Exact fresh verification commands and observed outcomes

Each command was invoked separately, with absolute paths:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --audit
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --replay-check
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --snippets
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/universe_check.lean
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/token-report.py 37386608-c5a8-4c82-a88b-0d50cc6e834c
```

First five commands exited 0 with the PASS results above. Token-report exited
0 but printed `no transcript for session 37386608-c5a8-4c82-a88b-0d50cc6e834c`:
not a measured budget pass. Inline read-only Python assertions also checked
the fourteen receipt identities, exact HEAD, absence of sorry/admit/new-axiom/
unsafe tokens in the eight source files, and the exact namespace audit messages.

Fresh snippet audits observed:

| Namespace | Constants | Observation |
|---|---|---|
| `IndexedSource` | 130 | Only standard axioms |
| `IndexedSourceTest` | 14 | Only standard axioms |
| `IndexedSourceObservationProbe` | 4 | Only standard axioms |
| `IndexedSourceObservationProbeTest` | 27 | Only standard axioms |
| `IndexedSourceObservationParity` | 4 | Only standard axioms |

These are namespace constants, not fixture counts. Fixture risk is five donor
families/ten cycles/four universal parities. M1–M7 are decide observation
controls on test-only computations/donors. M8–M10 are theorem-level donor
substitutions, not mutations of generic source/model/target proofs and not
numeric model observations. Exact failure expectations are copied from
`observed_controls.json`/the populated observed manifest; the initial
expectation-free run is only historical break/restore evidence.

Strict undefinedness remains the exact scalar-profile-0 negated-domain theorem;
the total neighbour is profile 4, not an inferred model count. Hidden complete
witnesses remain distinct with equal outputs; the selected private cell is 1.
Empty wrapped interfaces remain unequal and reconstructed input presence is
true even with an empty coordinate carrier. Explicit UID renaming is allowed
by wires; roster order and UID equality are not additional constraints.
No new core rejection or independent model-gluing verification is claimed.

### Prose/path assertions and conflicts

Patch windows confirmed the wrapper, contravariant port/domain geometry,
certified inverse, exact input/boundary/output equations, all `Rel` schemas,
quotient category, actual functor fields and unchanged componentSpan leaf.
Binary soundness calls composition_hom; boundary schemas call their existing
squares; bracket soundness uses rebased graph spans and bracket_hom.
Both source nested terms derive equality to the triple without using
Rel.bracket. Public entry imports the functor; task 2/3 list wiring matches
the final tracked lakefile delta. ProbeTest and parity imports are separate.

Current documentation sweep found directly stale source-law claims in the
synthesis's introduction, evidence/perspective rows, 6.6, 6.10, 10.2, 10.3 and
the Lean entry. A.9 needs the source presentation/functor step, not replacement
of its target-category/partial-map material. Historical witness records/plans/
reviews are not rewritten. Primary README remains excluded.

Read-only own-worktree git metadata showed main at
`c1e91e065b4700c472a8ad84f31b85e1e1f2bd31`, not the frozen base, in
`/Users/williammacready/code/python/pyncd`. This does not invalidate replay onto
the frozen base or authoring verification. It does prevent a claim that final
main-versus-branch diffs must be empty; the plan requires ancestry/deliverable
verification and task-only integration conflict adjudication. No primary
contents were opened and no integration occurred.

The designated Patterns and Global Pitfalls sections of leanncd/AGENTS.md were
measured at 426 and 2,525 characters (2,951 combined), below the approximately
3k hook-section budget. No unrelated instruction-trimming edit was made.

Final plan/path/expectation assertions and final status verification are
recorded below. Both documents contain no inline Lean or unstable Lean
line-number citations.

### Accounting

Authoring (a) exceeded its 55-turn aim during compiled-prototype iterations;
its exact peak/cumulative-token measurement was unavailable. This fresh
authoring (b) aims at most 40 turns and below 250k peak context, with no nested
delegation. Token-report has no Copilot transcript, so numerical cumulative
input/peak and the approximately 50M total-authoring target are unmeasured,
not fabricated or declared satisfied. This fresh dispatch remained below its
40-turn aim by direct interaction count; no new turn-aim breach was observed.
Execution's 175M cap remains a
controller measurement obligation using its actual session IDs.

## Authoring verification close-out

Post-edit assertions passed: live plan 477 lines (below 800), 48 referenced
existing file paths checked (including `ls`), two explicit future execution/
release result paths identified rather than asserted to exist, 55 plain
commands parsed, all ten
diagnostic/fixture expectations equal the observed controls and manifest,
all three patch identities present/matching, and both documents free of
inline Lean, unstable line citations and trailing whitespace.
The first local documentation-assertion run had a checker column-indexing
error; the checker was corrected and rerun to PASS before accepting results.
It did not reveal a prototype mismatch and changed no source or tooling file.

Post-authoring package audit again passed; all fourteen prototype receipt
identities still matched; the only tracked edit remained the original
lakefile wiring, and the real index was empty. Final `--replay-check` passed
with ordered byte equality. Final unfiltered manifest `--check` reported
10 entries, 10 selected, every old string unique. Final status showed only
the two requested documents added to the original untracked prototype/
artifact/manifest/history state; no prototype source changes or staging.
No load-bearing design mismatch has been observed. No authoring finding
remains unresolved, apart from the explicitly unavailable token measurement.
Independent plan reviews, reconstruction and every execution/release/
integration item below remain pending, including advanced-main integration
and primary dirty-state preservation.

## Execution ledger — controller fills, never predeclare success

| Checkpoint | Status | Required persistent evidence |
|---|---|---|
| Independent plan findings/adjudication | PASS | Controller reviewed the full live plan independently of both authors; frozen scope, exact commands, donor/control limits, reconstruction footprint and advanced-main integration agree with verified artifacts. No unresolved findings. |
| Reconstruction gate | PASS | Frozen eight-file/three-patch audit and replay passed; apply_patch deleted only the eight new prototype modules and reversed the exact lakefile addition. Status and empty lakefile diff confirmed the baseline; artifacts remained intact. |
| Task 1 | PASS | Commit 86aed9d1; exact task1 patch applied after --check; wire snippet compiled and hash matched. Controller geometry review clean. |
| Task 2 | PASS | Commit 3c4bb32a; exact task2 patch applied after --check; all three source hashes matched. Targeted build exited 0 (2,985 jobs); universe/API snippet compiled. Controller presentation/soundness review clean. |
| Task 3 | PASS | Commit cc612d4a; exact task3 patch applied after --check; test/parity build exited 0 (8,646 jobs); namespace audits use only standard axioms. All ten actual unfiltered expected controls passed with byte-identical restores and green restored builds; mutations_execution.md/log preserve the run. Post-cycle package audit passed; controller observation review clean. |
| Direct documentation sweep | Repaired after final review | Initial sweep missed the introductory strongest-conclusion quotation's unqualified source-law gap; both reviewers found it. The quotation now explicitly acknowledges the specified source category/functor and limits remaining obligations to broader source interpretations and rank/process work. Relative paths and whitespace passed; historical records/handoffs and primary README unchanged. |
| Controller release | PASS | Fresh unfiltered release controls 10/10, expected diagnostics, exact restores and restored builds; mutations_release.md/log. Eight module snippets, universe/API, exact-copy/source/namespace audits and ordered replay passed. Full LeanNCD Tests IndexedExecutionExperiment build exited 0 (8,919 jobs); full_build_release.log. No proof-shortcut tokens; namespace audits only standard axioms. |
| Final soundness lens | CLEAN, documentation finding repaired | review_soundness.md traces every source schema and both actual nested comparisons. No load-bearing defect; its P3 stale-summary finding is accepted and repaired with DOC-1. |
| Final integration/observation lens | DOC-1 accepted and repaired | review_integration.md independently checks whole-branch observation/import/artifact boundaries; no additional implementation/integration defect. P2 DOC-1 is the same stale summary, now repaired without Lean changes. |
| Local integration/task-only cleanup | PASS | Merge a67bee5693a13cdd112d2ce573141f3c3405248a into local main completed without conflicts. Topic ancestry and frozen source/copy/wiring hashes passed; merged-main full build passed 8,919 jobs. Primary README remained byte-identical; unrelated JAX changes preserved. After the user confirmed moving this chat to primary, the clean completed worktree was removed and its fully merged branch deleted. Other worktrees were untouched. No push. |
| Budget close-out | Measurement unavailable | Controller token-report again returned no transcript for the actual Copilot session. Authoring/execution cumulative input and peak cannot be measured by this repository's Claude-transcript tool; no numerical compliance claimed. Prototype 55-turn aim overrun remains disclosed; fresh author stayed within its 40-turn aim. Final-review accounting remains to record. |

### Per-task review findings

Controller plan review: no executable-plan defect found. Source/patch identity
audit, ordered alternate-index replay and unfiltered ten-entry old-string
check all exited 0 before reconstruction. Latest main's concurrent delta is
confined to JAX-bridge files and its record; it does not overlap source modules
or the proposed two-document sweep. The primary's dirty semantics README is
not an edit target.

Task 1 review: the contravariant port pairing and coordinate map agree with
environment direction, preserve rational values and retain certified raw/axis
coherence. Inversion eliminates dependent port equality explicitly and proves
the inverse environment equivalence; the three constructor transport proofs
identify the actual input, boundary and output maps. No target or original
transport declarations were edited. No findings. Task 2 remains next.

Task 2 review: the inductive relation supplies source equivalence and typed
congruence independently of denotation. The quotient category uses those
source generators, not target equality; the actual Mathlib functor descends
only through the proof covering every generator. Leaves use the unchanged
complete-witness componentSpan. Binary assembly invokes composition_hom
with the exact three wire maps. Both nested-to-triple derivations use assembly,
boundary-square schemas, wire composition and source associativity, without
the redundant bracket generator; its separate soundness proof uses
rebaseGraphs and bracket_hom. No fresh UID/program equality is asserted.
Type 1 objects/homs and the actual functor API compiled; no findings.

Task 3 review: Axis values distinguish the reversed adapter; Triple's
nonconstant input independently checks exterior tagging. Source binary
assembly and both actual nested-to-triple comparisons are instantiated;
private stores and distinct nested UIDs remain checked. Hidden equal-output
witnesses remain distinct and the leaf is explicitly the complete component
span; strict/total neighbours and empty metadata/input presence are retained.
The three exact copied maps have separate universal parity and ProbeTest
does not import it. M1-M7 detect specified test-copy/donor observation defects;
M8-M10 are theorem-level donor controls, not independent model semantics
or production-proof mutations. Every expected diagnostic was observed.
No findings. Controller release rerun and both final lenses remain mandatory.

### Final soundness review findings

Candidate 94f7bc8f: reviewer found no load-bearing source/functor issue and
reported P3 stale unqualified source-law status in the introductory quotation.
Accepted, grouped with DOC-1 and repaired by explicitly acknowledging the
specified proved presentation before listing broader source/rank/process work.
Report preserves the original finding. Reviewer used 21 tool-bearing rounds;
exact tokens/peak unavailable, no measured budget-compliance claim.

### Final integration/observation review findings

Candidate 94f7bc8f: P2 DOC-1 identifies the same stale quotation and the initial
sweep's false no-current-gap conclusion. Accepted; quotation and this record
are corrected. No other implementation/integration issue. Review remains
historical evidence, not overwritten as an originally clean candidate.
Reviewer stayed below its 35-turn aim; exact tokens/peak unavailable.
After the documentation-only correction, controller repeats all release
gates and checks current remaining-obligation claims before integration.

Post-repair controller gates actually passed again: exact DOC-1 quotation
assertion; eight real-module snippets; universe/API; standard-axiom namespaces;
package/copy audit and ordered replay; unfiltered manifest check and actual
10/10 expected cycles with byte-identical restores and restored builds; full
LeanNCD Tests IndexedExecutionExperiment build (8,919 jobs, exit 0); whitespace.
No Lean source or frozen compiled patch changed. The review finding is fully
adjudicated, not waived. Current main is c1e91e06 with only unrelated JAX deltas
since the frozen base; the primary README SHA256 before merge is
467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25.

### Final proved boundary and remaining obligations

Controller execution and its separate release gates now pass, independently
of historical prototype evidence. Object retains the whole interface; typed
identity, wire, matched leaf and composition syntax is quotiented by the
generated equivalence/congruence described above. The genuine semantics
functor preserves identities/composition, maps certified wires to graph
arrows and matched leaves to all-input complete-model spans. Actual binary
assembly and both nested constructor bracketings compare after the exact
inherited interface transports, not raw UID/program equality.

Assumptions remain finite decidable Declarations Unit, exact rationals,
supplied local matches and explicit certified boundaries; leaves require
neither model existence nor uniqueness, rank or successful execution.
No output-only collapse, event-free core identity, process/phase/trace law,
broader source structure, faithfulness or backend refinement is claimed.
The ten controls have the observational/theorem-donor limits stated above.
Final whole-branch reviews are complete and their sole documentation finding
is repaired and verified. Local integration, merged-main verification and
task-only branch/worktree cleanup passed. The verified plan, frozen patches,
reviews and separate execution/release/integration evidence remain on local
main. No task was skipped or parked; process/backend extensions remain
explicitly excluded. Token totals and context peaks remain unavailable rather
than declared compliant, and the prototype turn-aim overrun remains recorded.
