# Witness semantics: authoring verification and execution record

## Status and provenance

**Implementation and release gates complete.**
The integration receipt is authoritative for the final local merge,
merged-main rebuild and task-only cleanup, and is written only after those
operations actually succeed.
The authoring section below records the earlier artifact-only write-up.
The fresh artifact-only writer edited only this record, the plan and
`categorical_witness_semantics_record.md`. No production Lean, prototype,
scripts, manifest, package or git state was modified; no nested agents ran.

Process weight is Full: a new denotational categorical interpretation with a
soundness surface. The prototype/verification phase preceded this independent
write-up phase. The exact frozen package is
`categorical_witness_semantics_artifacts/package.json`.

| Identity | Frozen value |
| --- | --- |
| Base | `a9c9a647a04e260e21c8e5c624a0bac3fa13ef20` |
| Final compiled prototype HEAD | `0e49e37020b848d9a88da1daa7b95b5eef8260a7` |
| Final compiled tree | `ac03d2b330b355cc4632a2f3371e11f2081d81fd` |
| Patch groups | 7, with exact per-group targets/files/SHA-256 in package |
| Primary `papers/semantics/README.md` protected SHA-256 | `467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25` |

The controller supplied the following completed verification facts. They
were read as handoff evidence, **not rerun by this writer**:

- `package.py --emit` froze seven compiled task groups.
- `package.py --check` passed every patch/intermediate source SHA and the exact
  final tree using a private index; no ordinary index/worktree was modified.
- Prototype full wrapper build `LeanNCD Tests IndexedExecutionExperiment`
  passed, 8,911 jobs. All requested individual modules had targeted greens.
- Seven generic exact-copied-body `rfl` parities built. Seven body-copy checks,
  generated scaffold and three authoritative source hashes passed.
- Final **unfiltered actual** populated `_post` manifest: 10/10 cycles passed,
  with both expected strings, byte-identical file restoration and restored
  green. Authoritative table:
  `categorical_witness_semantics_artifacts/authoring_verified_mutations.md`.

No Lean code blocks were introduced: execution consumes reviewed compiled
patches. Post-application checks of every changed `.lean` are still required
through `check-snippet.sh`; inherited prototype evidence does not replace them.

## Historical failures retained, not upgraded to semantic evidence

The design audit was a design-only pass with no prototype/build. Task 1 was
only the first compiled group; its then-open boundary/coherence/partial-map
work is now proved in the final prototype, not still a current gap.

Task 2 initially left `toWired_fromWired` uncompiled. The controller repaired
the dependent inverse using actual pullback compatibilities, input inverse
laws and store restriction/gluing; the packaged task 2 is compiled. Its
original failure remains documented in `categorical_witness_semantics_task2_record.md`.
Task 3 initially had no concrete triple fixture; task 5 supplies the actual
nonconstant three-source scenario. These are chronological snapshots.

Task 6's record describes its proposal stage, not final observed diagnostics.
It named original commit `91721bc0`; final packaged group 6 source commit is
`1348a295bc833a9083b85cecaf8479f20649415c`, including controller repairs.
Do not replay the older proposal commit instead of the package.

The first ten-cycle attempt had two invalid proposals: a boundary type
mismatch and external-input computability failure. The runner's unqualified
10/10 table in `authoring_mutations.md` had no checked `expect` strings; it
shows break/restore mechanics, **not intended semantic discrimination**.
The controller identified the defects, repaired both and individually
reobserved them (`authoring_mutation_repairs.md`, also before populated
expectations). Only the final unfiltered populated manifest/table establishes
the stated expected observations. Initial attempts are not erased or counted
as successful numeric semantic evidence.

Final controls: six valid typed copied-map changes, then four transparent
donor controls. The last strict/total donor is theorem-level `Type mismatch`,
not numeric and not a production-map defect. Generic parity is mutation-free
and built independently; ProbeTest never imports Parity. `toWiredCopy` has
exact baseline parity and donor observations, but no independent mutation of
its embedded proof-carrying decomposition. No broader mutation claim is made.
All cycles concern newly added code; there is no pre-code empty manifest.

## Controller pre-execution review

The controller inspected the frozen implementations at the relevant symbols,
not just agent receipts. The following invariants were accepted before replay:

| Task | Direct review |
| --- | --- |
| 1 | Role subtypes retain complete signatures and UIDs; input presence is independent of coordinate inhabitedness. The setoid and quotient use apex equivalences with both legs; pullback congruence and units/associator explicitly map witnesses. |
| 2 | Boundary direction is downstream-coordinate to upstream-coordinate, hence upstream-output to downstream-input environments. The all-input inverse uses compatibility, both input inverses and both store restrictions/gluing laws; both exterior legs are proved. |
| 3 | Actual derived nested boundaries use input/output index equivalences. Both bracket spans rebase to the original endpoints and map to the same complete compatible triple; no raw UID/program equality premise occurs. |
| 4 | Existential domain and domain-indexed value are separated. Extraction is quotient-invariant only under injective left legs; both component at-most-one hypotheses remain on authoritative composite domain/value laws. |
| 5 | Hidden private 0/1, empty metadata, nonconstant boundary cells and actual bracket/private observations discriminate output-only and flattening readings. The scalar 14 alone is explicitly not treated as a boundary oracle. |
| 6 | Copied declarations are mechanically identical modulo names. Parity is separate from mutated observations; numeric failures and donor substitutions are distinguished. Two invalid proposals were repaired rather than credited. |
| 7 | The aggregate remains nondefault; ledger distinguishes target identities and witness coherence from unprovided source/process laws. The related stale summary statements were swept. |

No load-bearing finding was identified in these controller task reviews.
They are not substitutes for the two required independent final whole-branch
lenses. The artifact checker default was made repository-relative so it remains
usable after cleanup; all frozen body/source hashes and explicit execution
commands are unchanged. The protected hash belongs to the primary semantics
contents file, not the repository-root README.

## Authoring checks and direct scope decisions

Inputs read: handoff; design audit; task records 1–6; interface design
Sections 6–7; synthesis Sections 9.2–9.3/10; package; artifact-script usage;
initial, repaired and final mutation tables; actual `_post` entries.
No production Lean exploration or remeasurement of controller facts occurred.

The plan derives every task Files list and build target from the package,
and identifiers/donors/deltas from the task records. Deterministic authoring
checks verify package-file inclusion, seven patch groups, manifest count and
expectation pairs, absence of unstable `.lean:NN` locators in shipped witness
records, and the plan size limit. These are document checks, not code review.
Observed document check: **PASS** — seven exact task file lists and existing
patch paths, ten task-6 entries with two expectation strings each and only
ProbeTest targets, no Lean blocks, no unstable locators in any witness record.
The live plan is within the requested 200–400-line range.
Final post-edit document validation also **PASS**: each task's exact Files
set and targets match the package; shell blocks parse with `bash -n` and
contain neither shell-variable expansion nor chained commands. The final
plan is **359 lines**. No release commands were executed by these checks.
No invented numeric values, model counts, evaluation printouts or diagnostics.

The plan explicitly names: Type 1 objects/homs, Type 0 Env/apex; span-iso
quotient and pullback congruence; identity/unit/associativity; all validated η
and whole Models stores; explicit boundary/exterior transports and both legs;
one compatible complete triple for actual source bracketings; injective-left
restriction without existence; authoritative domain/value connection.
Core identity/source Category/functor/process laws remain excluded.

Relevant automatically injected AGENTS hooks were measured by the controller:
Patterns 426 characters + Global Pitfalls 2,525 = **2,951** combined (~3k).
The large narrative build guide is not those hook sections. The task 1
suggestion to trim is historical and not a required scope extension.
No existing core defect or mutation-manifest repair was needed outside the
new copied probes. Scope did not widen.

`package.py` uses a private-index workspace. The execution plan binds its
workspace root to a support directory inside the project with explicit
`TMPDIR` in an `env` invocation, avoiding system temporary paths without
changing the verified script. This invocation is prescribed, not rerun here.
Replay's checkpoint `controller_review` string is not a review verdict;
the controller must record actual task invariants and both final lenses.

## Budget and accounting disclosure

Target: authoring roughly 20 turns; hard limit 40 turns / ~250k retained
context. This fresh writer finished the artifact-only document/check work in
fewer than 20 conversation turns, with no builds or nested dispatches.
No conversation-turn breach was observed; this is not measured token-budget
compliance. Tool leaf calls and parallel envelopes are not conversation turns.

Prior costs, faithfully carried forward:
- Design audit: 44 tool calls versus 20 aim.
- Task 2: 40-turn aim and hard 60-turn budget breached.
- Task 3: approximately 70 tool actions, exceeding its action limits.
- Task 4: approximately 70 leaf calls; fewer than 40 conversation turns.
- Task 5: over 40-turn aim, within reported hard 60-turn limit.
- Task 6: exactly 60 leaf actions plus 7 batching envelopes (67 under that
  interpretation); action-cap breach, conversation cap not reached.
- Controller also exceeded the short-dispatch action guideline; scope did
  not widen.

Prescribed reporter for Copilot session
`de983171-486d-493b-8e86-068461660c5c` returned
`no transcript for session de983171-486d-493b-8e86-068461660c5c`.
Peak/cumulative token measurements are unavailable. Do not claim measured
250k compliance, attainment of the authoring 50M target, or compliance with
the execution 175M cap. Report any independently observed breach explicitly.

## Actual controller release gates and adjudication

These are controller outcomes, not upgraded prototype or authoring receipts:

| Gate | Actual outcome |
| --- | --- |
| Seven patch groups | Applied, built, post-edit snippet/hash checked and committed; `execution_replay.json` |
| Final unfiltered mutations | 10/10 with both expected strings, byte-identical restoration and restored green; `execution_verified_mutations.md` |
| Exact copies and Parity | Seven complete name-only copies, scaffold and source hashes pass before/after cycles; separate mutation-free Parity build passes |
| Source/import/axiom audit | No forbidden shortcuts or ProbeTest import of Parity; compiled namespace audits admit only standard axioms |
| Integrated full build | `LeanNCD Tests IndexedExecutionExperiment` passes 8,911 jobs; `release_receipt.json` |
| Whole-branch soundness | Clean for `e7102517..72888777`; `review_soundness.md` |
| Whole-branch integration | R1 stale documentation status repaired in `8d8a45ab`; original reviewer confirms clean, R1 closed |

No Lean code changed after the final reviewed/build-tested candidate. R1
changed only the interface design's opening/recommendation/remaining-work
claims. It now distinguishes proved model gluing, target category laws and
denotational coherence from open source/process/ranked obligations.
No required task, build target, snippet, manifest entry or final review was
silently skipped. Accounting remains explicitly unsupported.

The final [integration receipt](categorical_witness_semantics_artifacts/integration_receipt.json)
records the actual local-main merge, merged-main build, preserved contents
hash, owned worktree/branch cleanup and no-push outcome after they succeed.

## Actual seven-task execution

The controller ran the packaged `--replay` on the clean plan-package branch.
All seven patches actually applied, built their exact named targets, passed
every changed Lean file through `check-snippet.sh` in its post-edit form,
matched the intermediate source hashes, and were committed. The copied-source
checks passed at tasks 6 and 7. `execution_replay.json` contains the actual
seven receipts; the last execution commit is `fc45891c`.

The controller's scoped Git comparison with the frozen prototype HEAD
`0e49e370` was empty for the complete experiment source, lakefile, AGENTS and
two edited design documents. The substantive pre-execution task reviews
therefore apply to the executed bytes without a new source modification.
The script's checkpoint labels are not independent review verdicts.
No task, named build, post-edit snippet, or source-copy check was skipped.

Local main advanced concurrently to `e7102517`. Its only overlapping file
is the lakefile: the added JAX refusal-test glob is in a separate library,
not the witness experiment. The controller will integrate this current-main
change before final release checks and whole-branch reviews. The primary
semantics contents hash is still the original protected value.

The current-main merge completed without conflicts; both libraries' lakefile
globs were preserved. A controller `merge-tree` comparison checked all 17
task-owned paths against the exact merge of current main and the frozen
prototype source, rather than assuming disjoint edits were harmless.
`integration_source_check.json` records the hashes and checked paths.
The integrated candidate subsequently passed the release gates and both
review lenses as recorded above.
