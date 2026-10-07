# Collection/model plan authoring record

## Status and authorization

Dispatch B is a fresh write-up from verified artifacts, not an implementation.
Authorization: **PREPARE AND VERIFY PLAN ONLY**.
The [live plan](collection_model_plan.md) has completed controller verification and
both final review lenses. This record is not an execution completion log.
The following dispatch-B observations describe its artifact-only authoring work:
No source patch was applied, no implementation/config/guidance source was edited,
no build or mutation was run by Dispatch B, and no agent was launched.
No commit, merge, push, rebase, or worktree removal was performed.
At dispatch B's handoff, the two documents were left untracked for controller
review/publication. The controller publishes only the verified plan artifacts.

Work was confined to `/Users/williammacready/code/python/pyncd.worktrees/collection-model-plan`.
Protected `f32-flip-slice2-proto` / `f32-flip-slice2` worktrees and branches were
not read, built, touched, rebased, or removed.
Initial status contained only the supplied artifact directory, patch directory,
and post manifest as untracked entries. Those are controller-owned inputs,
not modifications by this author.

## Provenance: code, emission, and controller observations

Primary authority: [evidence.json](collection_model_artifacts/evidence.json).
Compiled code source of truth: [01](collection_model_patches/01-finite-pushforward.patch),
[02](collection_model_patches/02-program-models.patch),
[03](collection_model_patches/03-fixtures-integration.patch).
No Lean code has been copied/reformatted into either authored document.
Consequently the snippet-compilation checklist is not applicable here;
the controller/prototype compilation evidence concerns the actual patch code.

| Item | Observed/provided value | Authority and interpretation |
| --- | --- | --- |
| Baseline | `26fcfe6b8b209b8bd05b871705f6b731b1caba0a` | Supplied execution/source-guard base |
| Task 1 prototype commit | `067a26416040ca0050a12c1a0405ed029a85ef8b` | Evidence / emission script |
| Task 2 prototype commits | `c4181f60ad3e90005e22cb5a8f29fe203bd1b6e2`, `53034be98e6af24fda8e26699386784e317a8f04` | Models plus final input proof fix bundled in patch 02 |
| Candidate / Task 3 commit | `8c377721298a18d57906f1412fa9703efbd0b4a8` | Prototype only; NEVER merge |
| Exact final tree | `3bc1200f3083e62dc86f23983857e185287af67d` | Temporary-index replay equalled compiled candidate |
| Refreshed baseline full build | exit 0, `8686` jobs | Controller report, not Dispatch B execution |
| Prototype targeted build | exit 0 | Evidence's targeted-build observation |
| Prototype full default build | exit 0, `8690` jobs | Evidence; includes final input proof adjustment |
| Prototype manifest check | exit 0, 12 entries/selected, unique anchors | Evidence; check is not the actual suite |
| Controller initial full suite | 12/12 passed | Controller report/evidence, every failure/restored pass observed |
| Controller pinned replay | 12/12 passed, every expect seen | Copied result table: byte-identical restores and green restored builds |
| Controller post-mutation source diff | Empty tracked-source diff against candidate | Updated `controller_verification` observation |
| Controller candidate full default build | Passed, `8690` jobs | Independent controller verification; existing warnings retained |
| Controller all-13-theorem axiom audit | Compiled; only `propext`, `Quot.sound`, `Classical.choice`; no `sorryAx` | Controller `check-snippet.sh` audit, not Dispatch B execution |
| Final categorical/semantic/model review | Clean | Independent lens A, no actionable findings |
| Final artifact/type/admission/execution review | No open findings | Independent lens B; preparation restriction finding resolved and confirmed |

The controller independently reran mechanical patch emission and all three ordered
temporary-index apply checks with exact final-tree comparison. Dispatch B read
the resulting patches; it did not repeat git-object emission or apply checks.
[emit-patches.py](collection_model_artifacts/emit-patches.py) diffs compiled
commit pairs with full-index/binary output and replays them in a temporary index.
It needs prototype git objects, so it is provenance code, not an execution
dependency. Execution consumes the published patches and checks actual sources.

The prototype full build reports existing baseline sorry/linter warnings.
Evidence says no new sorry/axiom in the new modules and no silently skipped tests;
Dispatch B does not relabel these as its own independent build observations.
Likewise `8686` and `8690` are historical observations, not future numeric gates.

## Bounded inspection performed

All three patches were reviewed in consecutive approximately 40-60-line windows,
located by `rg -n` headers/symbols, including complete production/test patch bodies
and the import, test-glob, guidance, and scoped semantics-note hunks.
The evidence was read in bounded windows for counts, exact hypotheses, fixtures,
observations, mutation provenance, known limitations, and budget disclosures.
The post manifest was searched by label/task/file/old/new/target/expect anchors.
All 12 verification task IDs are 3; the anchors include observed expectations.

Only the supplied specification reference windows were used:
- [NaperianTyping.md](../NaperianTyping.md): representability caveat and
  "Fiber semantics and reindexing", window 284-334.
- [tensor_logic_boundary_policies.md](tensor_logic_boundary_policies.md):
  Section 8.4.4 and immediate drop-timing boundary, window 1205-1255.
- [tensor_logic_semantics.md](tensor_logic_semantics.md):
  Sections 19-20, windows 2335-2385, 2386-2436, 2437-2487, 2488-2543, 2544-2599.

Repository execution preamble, preparation options/ledger behavior, and manifest
CLI contract were inspected in bounded helper windows. This author did not
rediscover the specifications, read the entire specs, inspect protected branches,
or re-explore prototype sources. Existence of artifact, wrapper, prior-art,
integration, and historical-record paths was checked by explicit absolute paths.
New Collection/Program/Models/test production paths remain planned code paths,
represented as monospaced names with links to their creating patches.

Baseline hook sizes are supplied observations: 2882 characters for the root
injected sections and 2642 for semantic guidance. The root guidance file is
larger than its injected sections; do not confuse total file size with hook size.
No shrink patch was made. No modified Task 3 guidance-hook measurement is claimed.
The plan makes remeasurement a controller gate before asserting a modified size.

## Semantic and categorical observations supported by the patches

Collection's representation is a plain function family; `pullback` is
precomposition. `pushforward` is a finite conditional sum over tagged occurrences.
Generic zero/add/identity/composition/relabeling/grouping proofs are substantive,
and Program's collector calls this generic pushforward directly.
The additive homomorphism is packaged by `pushforwardHom`.
This supports finite Naperian read/write algebra, not a completed categorical
interpretation, D-graded PROP integration, or Kan-extension/adjunction theorem.
Strong monoidality does not establish representability; the explicit family
representation does not prove the general lifted-object isomorphism.

`AddCommMonoid` is required only for participating defined carriers in Program/
Models. Body `ScalarOps` and primitive registry operations remain data, without
fake machine-float algebra laws or assumptions that nonlinear maps preserve sums.
The program has finite declared tensor roles, per-target statement/guard-valuation
sigma tags, already bounded defined destinations, and strict demanded outcomes.
Admission is encoded in types/predicates, not a source/runtime boundary checker.
No raw write policy or source-level substitution is implemented.

Input bindings are optional COMPLETE typed tensor families, with exact presence
equality. Empty input presence is independent of vacuous coordinate agreement.
Declared defined extras are rejected; undeclared IDs are unrepresentable.
Models require input agreement, admission and every defined equation.
The equation operator needs an admission witness and returns a plain store;
fixed-point equivalence is not iteration. Unique-model denotation uses
`Classical.choose`, projects outputs, and supplies no general solver/existence
or uniqueness theorem.

## Exact inventory, fixture observations, and mutation attribution

13 production theorems, not fixture assertions:
- Collection (6): `pushforward_zero`, `pushforward_add`, `pushforward_id`,
  `pushforward_comp`, `pushforward_relabel`, `pushforward_grouped`.
- Program (3): `collect_grouped`, `collect_relabel`, `admEnv_relabel`.
- Models (4): `models_fixedpoint`, `models_relabel`, `models_grouped`,
  `denotation_of_model`.

18 fixture assertions comprise 9 guards and 9 theorems; five `def` proof helpers
and one evaluation command are not counted. The plan preserves the evidence's
F01-F18 donor/mutation map, rather than deriving replacement values.
Observed evaluation output: `4`, `9`, `0`, `0`, `9`, `5`, `14`, `3 / 4`.
Additional compiled guard observations include no implicit prior seed with
candidate `99`, legal active body `some 0`, and reciprocal-after-sum `some 1/6`.
Theorem observations cover excluded undefined demand, active undefined rejection,
present/missing/extra input bindings, nonoutput model rejection, admission without
equations, the legal zero model, and its fixed point.

The [post manifest](collection_model_mutations_post.json) has 12 unique anchors:
5 source/invariant mutations and 7 fixture contrasts, ALL after Task 3 lands.
There is no pre manifest, and no cycle is scheduled before test/config integration.
Prototype directly observed M01/M03/M05; it originally left nine expectations
absent rather than invent diagnostics. The controller observed all nine in the
initial complete successful suite and copied expectations from actual failures.
The supplied evidence distinguishes that initial run from the strengthened replay.
Controller subsequently completed the pinned replay successfully: all 12 expects
were seen, files restored byte-identically, and every restored build was green.
The copied [result table](collection_model_artifacts/mutation_results.md) was read
by Dispatch B and agrees with the updated evidence's `controller_verification`.
The older `mutation_evidence.suite_run: false` describes the prototype dispatch,
not the later controller suite; the explicit controller verification and final
table are authoritative for that later observation. The evidence was not edited.

M01 multiplicity and M04 prior seed can fail generic collection proof obligations
before fixture guards execute. M02 fails the dependent definedness/admission
invariant needed by contribution extraction; it is not evidence for a runtime
guard checker. M03 directly breaks undefined-body rejection and numeric guards;
M05 breaks empty-input rejection. M06-M12 are contrasts in fixture construction/
expectations, not seven additional source regressions.
Exact error lines are permitted in JSON expectations but are not used as
`File.lean:NNN` prose citations. The plan links symbols and source paths instead.

## Limitations deliberately preserved

- No full representability/coherence, categorical interpretation, D-graded
  PROP/Functor/Kan-extension integration, or arbitrary nonlinear sum law.
- No source elaboration/pure-einsum correspondence, capture-avoiding substitution,
  raw writes/drop/evaluate-only decisions, operational machines/ranks/publication,
  solver/convergence/least-fixed-point selection, or backend/precision refinement.
- No general unique-model existence/uniqueness guarantee.
- No dedicated fixture demonstrating an equation-operator result outside AdmEnv.
  The codomain allows it; the spec example is not a new tested fixture.
- No Boolean OR collection fixture and no XOR instance.
- Existing independent ExpressionTest fixture 14 is a heterogeneous primitive
  donor only; new collection F10 is not a multi-sort whole-program oracle.
- Old Expr/readiness/completeness and legacy evaluator contracts remain unchanged.
  The plan does not claim the current evaluator implements additive program models.
- Historical spike gaps are not rewritten as a current inventory.

## Completed controller gates and publication distinction

At the initial artifact-existence check, final `mutation_results.md` was absent.
The controller subsequently copied it and supplied completed independent gates:
the strengthened suite, empty post-mutation source diff, full candidate build,
and all-13-theorem compiled axiom audit. These are now recorded as actual
controller verification, distinct from the earlier prototype-only observations.
The separate publication baseline remains code-unchanged with its green `8686`
full build. Both final plan review lenses are complete; passing these candidate
and authoring checks does not implement or release the plan.

The controller independently checked artifact integrity: 13 production proofs,
18 assertions, 12 task-3 anchors with observed expectations, exact nine delivered
candidate paths, and byte-identical copied patches. The publication worktree and
local main still passed the protected-input diff guards before publication.
The publication set is plan documents, three patches, manifest, evidence,
mutation results, and authoring emitter; no candidate implementation source.

Lens A confirmed finite-family categorical organization and full model fidelity,
without additional findings. Lens B found that the draft had accidentally
widened the user's protection from no modification/rebase/build/removal to a
blanket no-read rule, conflicting with the mandatory preparation helper.
The controller restored the actual user restriction and explicitly documented
read-only cache discovery/copy into the new worktree, prohibited donor writes/
builds and protected-source inspection, and required STOP before preparation
if a later authorization also prohibits protected-cache reads. The reviewer
confirmed this bounded correction resolves the finding; no helper/code change
or permission workaround was introduced. There are no open final findings.

Future implementation gates are separate: clean prepared execution source,
baseline ancestry/protected-source diff, actual ordered apply checks, per-task
reviews/commits, actual manifest check AND complete suite with `--out`, controller
full default build, two final whole-branch review lenses, then local integration.
No prototype merge and no remote push. Current plan publication is NOT execution
or implementation release; no future task is falsely marked complete here.

## Budget and candid telemetry

Read-only document/artifact validation passed:
- Live plan length remains within the 350-500 target and 800-line ceiling.
- Mechanical patch counts: 13 production theorems, 9 fixture theorems,
  9 guards, 5 named proof helpers, and 1 evaluation command.
- Manifest metadata: 12 distinct labels, all task 3, all with nonempty observed
  expectations, all targeting `Semantics.CollectionModelTest`.
- Every authored relative Markdown link resolves; neither document contains a
  Lean fenced block or a numeric Lean-file line citation.
- Post-edit status adds exactly the two requested documents to the preexisting
  untracked controller artifacts; there are no tracked-source modifications.

These checks do not execute mutations, prove unique old-string occurrences on
future sources, validate actual apply checks, or replace controller reviews.

Authoring was split into prototype/verification A and fresh artifact-only B.
Prototype estimates approximately 45 turns plus five alignment follow-ups:
above its approximately 45 target, below its 60 absolute cap; no known absolute
60-turn/approximately 250k context breach. These are estimates, not measurements.
Evidence's token-report result is "no transcript for session" for the SDK session;
aggregate cumulative input tokens are unavailable. The approximately 50M authoring
target therefore cannot be reported as measured compliance or a measured overrun.
Likewise do not fabricate a measured context peak or aggregate slice cost.

Dispatch B target is approximately 40 turns, absolute 60/approximately 250k.
Bounded parallel reads and one coherent two-document creation kept the dispatch
well within its turn target; no absolute breach is known. A precise aggregate
token total remains unavailable, so no inferred compliance is asserted.
Final reviewer estimates: lens A 13 tool-bearing rounds, lens B 17 including its
bounded confirmation; both below the approximately 60-round cap, with no known
context-cap breach. These are estimates, not a measured aggregate token total.
The repository token-report tool still has no matching SDK transcript.

Authored paths only:
- [collection_model_plan.md](collection_model_plan.md)
- [collection_model_authoring_record.md](collection_model_authoring_record.md)

No implementation was executed or released by this dispatch.
