# Whole-branch review: integration, fixtures, and claim fidelity

Review base: `2212263c`; reviewed head: `e1553bb7fd45eb5f9111c06aba736e74935b6400`.
Scope: nondefault package/discovery, seven model fixtures, runtime-versus-proof
claims, artifact/replay integrity, scoped documentation, and release gates.
The separate soundness review owns the full core-theorem trace.

## Checkpoint 1 — scope and evidence contract

Read handoff sections 4–6, plan sections 1–3, initial record/accounting,
package emission/check logic, and initial manifest entries. The plan correctly
distinguishes source dependencies from sequential Lake-registration patches;
release replay/build/reviews are not claimed completed by authoring readiness.
Protected README/synthesis files are outside the branch diff.

No findings established yet. Review is in progress. No builds, mutations,
staging, commits, delegation, or source edits are being performed.
Accounting: review targets 25–35 turns with a hard return at 40 turns/150k
retained context; exact cumulative-input accounting is currently unavailable.

## Checkpoint 2 — local/geometry fixtures and discovery

Read the complete local and geometry fixture/test modules, aggregate imports,
Lake/AGENTS/interface-design diff, plan through section 6, and corresponding
record windows. Cases 1–5 have meaningful complete-model proofs: strict absence
ranges over all stores/inputs; total private audit is retained; zero-writer
equations constrain every model. Generic empty input presence is tested at the
binding level, and empty output index identity is explicit. The axis oracle
checks actual restricted input `(5, 2)` against flattening `(3, 4)`, explicitly
showing both output sums remain `14`.

All added modules are registered in the existing nondefault experiment.
The aggregate imports the denotation API and all fixture tests, with audits for
all new namespaces. Scoped documentation names the explicit import entrypoints
and limits denotation to both `AtMostOneModels` premises.
No findings established so far; cycle fixtures and mechanical artifact/release
evidence remain to inspect.

## Checkpoint 3 — cycles, mutation classification, exact package bytes

Read both complete cycle modules. `cycle_upstream_models_cases` derives the
exhaustive store classification from both whole-store equations; composite
uniqueness ranges over every candidate and then uses generic store recovery.
The zero witness is excluded, one extends, and upstream non-`AdmInput` is
retained. Hidden stores retain private `0/1`, the same boundary `0`, and equal
whole final outputs `1`; both full witnesses round-trip and their compatible
pairs are proved distinct.

A read-only independent unified-diff reconstruction checked all eight patch
SHA-256 values, every intermediate file hash, and every checkpoint commit.
All 14 final packaged files exactly match REVIEWHEAD and working source.
No generated patch bodies were dumped or patches applied to any Git index.
A second read-only check confirmed all 12 manifest replacements occur exactly
once, labels/expectations/task mappings are valid, all 11 module registrations
are exclusively nondefault, and task order respects actual new-module imports.

Manifest labels match proof-elaboration/model-counterexample evidence, not
runtime kills. Final M9 retains the store parameter via read-times-zero; the
older M9/M10 `n/a` table is explicitly superseded. Authoring evidence reports
12 restored/green cycles; replay release cycles/probes remain external gates.
No findings established so far.

## Checkpoint 4 — integration and release fidelity

Inspected immediate donor bodies: the producer's `1 + (-1)` collected equation
forces zero; the consumer evaluates the whole strict reciprocal array before
selecting its first coordinate. Changing only `other` to `4` retains private
definedness and `Audit = 1/2`. The axis producer's six actual literals and
consumer's repeated point reads match the fixture values.

For claim fidelity, inspected the generic occurrence/collection surface:
`admEnv_components` covers every actual occurrence, while both collection
lemmas preserve the unchanged occurrence sum with `Finset.sum_congr`.
Guard-excluded valuations are not occurrences; duplicate contributions and
zero fibers are generic obligations, not invented extra dedicated fixtures.
Input/output APIs separately preserve binding presence and output indices.
Public denotation signatures require both at-most-one hypotheses and assert
values only on composite `AdmInput`; all these claims match scoped docs.

The aggregate's axiom audit actually fails on forbidden dependencies; it is
not merely a `#print` observation. A source sweep found no prohibited proof
shortcuts in the 11 new experiment modules. `#eval` probes observe stores or
bodies, and reports correctly avoid executor-completion claims.

Package subprocess failures abort (`check=True`), per-task progress is recorded
only after build/snippets/hash checks and commit, and replay is gated on a clean
base checkout. The final-index reconstruction verifies actual registration
bytes, not just package metadata. Existing manifest helpers require a failed
mutated build, successful restored build, byte-identical SHA-256 restoration,
and every expected string in the actual mutated build log. Release commands
correctly use the prototype-owned manifest while targeting replay source;
the code patches do not pretend to copy bookkeeping artifacts into replay.
Task-owned temporary package indices are isolated and automatically cleaned.

Stored replay logs corroborate all eight successful task builds and the exact
source-copy check counts, including the reported local/axis/cycle observations.
Execution head `cbd52ddf` is a parent of REVIEWHEAD, and its packaged source/docs
are byte-identical to REVIEWHEAD. Protected README/synthesis/settings paths
occur in neither the final diff nor any branch commit; both protected document
blobs are unchanged from the base. No source constructor, default library,
runner, registry, or numerical operation is changed.

## Final assessment

**No actionable integration, fixture, or claim-fidelity findings.**
Coverage includes all seven acceptance cases, nondefault discovery/imports,
manifest classification and exact replacements, patch bytes/intermediate
hashes/replay commits, complete-model versus runtime observations, scoped
design/docs, and authoring/execution/release distinctions. The 490-line plan
and 313-line record were read in bounded windows. Full core-theorem soundness
was deliberately left to the separate required review.

Remaining external gates at this review's snapshot:

- Controller's actual replay release mutation/probe completion and recording;
  untracked controller evidence was not treated as completed release evidence.
- Separate final soundness review and controller adjudication of both lenses.
- Final protected-primary-working-copy hash/scope checks, release close-out,
  and authorized local integration/cleanup. No push is inferred or performed.

The full required `LeanNCD Tests IndexedExecutionExperiment` build is reported
green by the controller (8,898 jobs); this review intentionally reran no builds
or mutations. Pending release boxes are honest, not false completed claims.
Rank stitching, execution phases/projections/traces, and categorical
associativity/units remain explicitly open.

Review budget: 25 tool rounds, approximately 26 assistant turns including the
final response; retained context estimated below 150k. No known review-budget
breach. Exact cumulative token accounting remains unavailable and is not
asserted; the record faithfully surfaces earlier controller/cyclic-donor
overruns and unmeasured accounting. The only file written by this reviewer is
this report; no source edits, staging, commits, builds, mutations, or delegation.
