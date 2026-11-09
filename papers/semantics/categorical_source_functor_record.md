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
| Task 1 | PASS, committing | Exact task1 patch applied after --check; reconstructed wire snippet compiled. Controller geometry review clean; source SHA256 is the frozen package identity. |
| Task 2 | Pending | Patch/file hashes, targeted build/universe, soundness review, commit, usage |
| Task 3 | Pending | Patch/file hashes, tests/audits/parities, actual 10-cycle table, observation review, commit, usage |
| Direct documentation sweep | Pending | Current-value/prose/path checks, split source/process ledger, entry point, commit |
| Controller release | Pending | Fresh unfiltered manifest execution, byte restores, source/copy/namespace audits, eight snippets, universe, full three-target build, exit/job observations |
| Final soundness lens | Pending | Whole-branch findings and disposition |
| Final integration/observation lens | Pending | Whole-branch findings and disposition |
| Local integration/task-only cleanup | Pending | Primary dirty preservation, ancestry/deliverables, merge and cleanup results; no push |
| Budget close-out | Pending | Controller/all-dispatch measured totals or unavailable-data disclosure, breaches |

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

### Final soundness review findings

Pending.

### Final integration/observation review findings

Pending.

### Final proved boundary and remaining obligations

Pending execution. Do not convert compiled-prototype/authoring evidence into
a release receipt. Close-out must retain the denotational scope and the open
rank/process/backend boundaries, plus every skipped/blocked item.
