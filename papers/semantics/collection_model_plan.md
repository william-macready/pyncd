# Finite Naperian collection and simultaneous program models

## 1. Authority, process weight, and release boundary

**Full path:** a new typed program/model capability with a soundness surface.
This is ONE slice, implemented by THREE ordered task patches, not several slices.
Current authorization is **PREPARE AND VERIFY PLAN ONLY**. Nothing below authorizes
this authoring dispatch to apply patches, edit implementation sources, build,
commit, merge, push, or launch agents. Controller authoring verification is complete.
This is an execution-ready plan, not a released implementation.

The code source of truth is the mechanically emitted, compiled patch set:
[01](collection_model_patches/01-finite-pushforward.patch),
[02](collection_model_patches/02-program-models.patch), and
[03](collection_model_patches/03-fixtures-integration.patch).
There are no transcribed Lean blocks to compile or keep synchronized here.
[Evidence](collection_model_artifacts/evidence.json) supplies observed values,
theorem/fixture/donor maps, limitations, and provenance.
The [authoring record](collection_model_authoring_record.md) separates observations
from future execution gates; it is not an implementation completion record.

Execution base: `26fcfe6b8b209b8bd05b871705f6b731b1caba0a`.
Prototype candidate: `8c377721298a18d57906f1412fa9703efbd0b4a8`.
Exact replayed candidate tree: `3bc1200f3083e62dc86f23983857e185287af67d`.
The candidate is provenance, NEVER a branch to merge or an execution-HEAD condition.
Execution starts from future local published-main or an artifact-only descendant,
subject to the source guards below, not by checking out the prototype candidate.
Do not modify or rebase `f32-flip-slice2-proto` / `f32-flip-slice2`, build in
their worktrees, or remove either branch or worktree. These are the user's
protected-work restrictions; they do not prohibit read-only cache discovery
by the required preparation helper.

## 2. Organizing principle and exact semantic contract

Finite function families are the explicit Naperian representation: `Family I K`
is `I -> K`; existing `Coord`, declarations, and typed stores supply the indices.
Contravariant reads are pullback `f^*`, implemented by precomposition.
Covariant finite ADDITIVE writes are fiber pushforward `d_!`: sum every tagged
occurrence whose destination is the selected coordinate; an empty fiber is zero.
This is the organizing algebra used directly by `Program.collect`, not a
categorical sidecar attached to an unrelated imperative collector.

The generic production deliverables are `pushforward_zero`, `pushforward_add`,
`pushforward_id`, `pushforward_comp`, `pushforward_relabel`, and
`pushforward_grouped`, together with `pushforwardHom`.
Identity/composition establish the covariant finite-family algebra; zero/add
preservation packages its additive homomorphism. Relabeling preserves tagged
fibers, and sigma grouping justifies collection by statement.
Pullback is defined as precomposition; do not invent extra named pullback proofs
in the 13-theorem inventory or claim an adjunction/naturality theorem.

Hypotheses matter: generic pushforward needs finite occurrences, decidable
destination equality, and `AddCommMonoid K`. Composition additionally needs a
finite intermediate index type and decidable equalities; relabeling needs a
finite alternate occurrence type; grouping needs finite base and dependent fibers.
Program/model collection needs additive commutative monoids ONLY on carriers
of participating defined tensors. `ScalarOps` and registry body operations remain
explicit data. Their addition/multiplication are not silently identified with
collection laws; no fake `Float` semiring/additive-law instances are introduced.
No arbitrary nonlinear primitive is assumed to commute with finite sums.

Alignment anchors: [Naperian typing](../NaperianTyping.md), "Fiber semantics and
reindexing" / its reformulated D-graded view; [boundary policies](tensor_logic_boundary_policies.md)
Section 8.4.4; [semantics](tensor_logic_semantics.md) Sections 19-20.
Strong monoidality alone does NOT imply representability. Function representation
here is explicit; this slice does not derive it from a categorical strong
monoidal action or instantiate the full Naperian categorical interface.
This is finite-family algebra, NOT full D-graded PROP integration, a
Cat/Functor/Kan-extension construction, or a representability/coherence theorem.

### Program, admission, and collection

- Finite declared tensors are partitioned by `input : Tensor -> Bool`.
  `Defined` is the false subtype; `output_defined` makes outputs a subset of it.
- Each defined target has local statement tags and finite valuations.
  `Occurrence` is a sigma of statement tag and guard-admitted valuation subtype.
  Equal bodies and colliding destinations do not identify occurrence tags.
- Destinations are already bounded coordinates of defined targets.
  Noninjectivity is permitted. Structural typed admission is NOT source/runtime
  validation and supplies no raw-write/drop/evaluate-only boundary policies.
- `outcome` uses existing strict `interpret`. `AdmEnv` demands a successful
  result for EVERY actual occurrence, even zero-valued or non-output bodies.
  Guards remove excluded valuations before this demand; no undefined summand
  becomes zero. `contribution` extracts the value using the admission witness.
- `collect` directly uses generic pushforward. Empty fibers and zero-statement
  defined tensors yield zero. The prior candidate tensor value is not a seed;
  it matters only through an explicit body read.
- `collect_grouped`, `collect_relabel`, and `admEnv_relabel` establish the
  statement-grouped and equivalent-occurrence presentations. These are not
  source-parser permutation or capture-avoiding substitution theorems.

### Inputs, models, equation operator, and denotation

- `InputBinding` is an optional typed COMPLETE tensor family for each declared
  identifier. `ValidInput` requires exact `isSome = input` presence equality.
  A declared EMPTY input must be present, despite having no cells.
- Bindings for declared defined tensors are rejected by that predicate.
  Undeclared identifiers are structurally unrepresentable, not a runtime diagnostic.
- `Models` requires input agreement, `AdmEnv`, and EVERY defined coordinate
  equation, including internal nonoutputs. Admissibility alone is not a model.
- `equationOperator` preserves candidate inputs and replaces defined tensors
  by collection. Its domain requires an `AdmEnv` witness; its codomain is `Store`,
  not an admissible-store subtype. It may leave `AdmEnv`.
- `models_fixedpoint` characterizes models by input agreement and existence
  of an admission witness whose equation operator fixes the candidate.
  This is NOT an iterative solver, convergence claim, or least-fixed-point rule.
- `models_relabel` and `models_grouped` transfer the equivalent collection
  presentations to the full model relation.
- `AdmInput` means exactly one COMPLETE model, not merely unique output values.
  `denotation` uses `Classical.choose` and projects outputs;
  `denotation_of_model` relates it to any model under that uniqueness hypothesis.
  There is no executable solver or general existence/uniqueness guarantee.

### Explicit exclusions and uncovered cases

Source elaboration/pure-einsum correspondence, capture-avoiding substitution,
operational machines, ranks, scheduling/publication, backend/precision refinement,
and the boundary decision register are deferred. Do not implement them here.
The historical spike gap document remains historical, not a current inventory.
There is NO dedicated fixture where `equationOperator` produces a nonadmissible
result. Its codomain permits this; Section 20.2 supplies the mathematical example.
Boolean OR collection is NOT fixture-covered; no XOR instance is introduced.
Existing ExpressionTest fixture 14 supplies a heterogeneous primitive donor;
new F10 reuses that primitive, not a multi-sort whole-program oracle.

## 3. Execution preparation and immutable-source guards

Controller owns preflight, actual mutations/full builds, final reviews, and release.
Use a newly isolated execution worktree with the published artifacts tracked.
`<execution-worktree>`, `<execution-base-branch>`, and
`<controller-session-artifacts>` below are absolute-path/branch templates:
substitute literal values, never shell variables. The execution session's working
directory must already be that worktree; an absolute script path does not change it.

Run the preparation helper against the controller-selected local published base,
not an assumed remote head. Omit `--plan`: the published plan is already tracked,
so no copy from a primary checkout may overwrite it.
The helper enumerates registered worktree caches read-only and copies a donor's
cache into the NEW execution worktree. It must not build in or write to a donor.
Do not inspect protected source code or use a protected worktree as the execution
checkout. If a later authorization also prohibits reading protected caches,
STOP before preparation: the current helper has no donor allowlist.

```bash
bash <execution-worktree>/.claude/skills/new-slice/prepare-worktree.sh --base <execution-base-branch>
```

If preparation has left an untracked ledger, move only that resolved ledger into
controller session artifacts; do not stage it or delete unrelated work.
For the standard plan ledger location, the separate command is:

```bash
mv <execution-worktree>/.superpowers/sdd/collection_model_plan <controller-session-artifacts>/collection_model_preparation_ledger
```

Run that move only if the ledger exists and its destination is available.
The post-preparation status must be EMPTY, including untracked files.
Recheck ancestry and protected sources AFTER preparation before any source build
or patch application; a preparation fast-forward must not bypass the guard.

```bash
/usr/bin/git -C <execution-worktree> status --short
/usr/bin/git -C <execution-worktree> merge-base --is-ancestor 26fcfe6b8b209b8bd05b871705f6b731b1caba0a HEAD
/usr/bin/git -C <execution-worktree> diff --exit-code 26fcfe6b8b209b8bd05b871705f6b731b1caba0a HEAD -- leanncd papers/semantics/tensor_logic_semantics.md papers/semantics/tensor_logic_boundary_policies.md papers/NaperianTyping.md papers/semantics/tensor_logic_semantic_core_spike_record.md
```

Any nonempty status, failed ancestry, meaningful protected-source difference,
or patch conflict is a STOP for controller adjudication. Do not passively port,
rebase, shrink, or merge around it. Artifact-only publication descendants can
pass these guards without matching the candidate HEAD.
Then refresh project oleans over the warm Mathlib cache:

```bash
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD
```

Stop if Mathlib cold-builds. Current observed baseline hook-injected root sections
are 2882 characters; semantic guidance is 2642, both below approximately 3k.
No preflight shrink patch belongs to this slice. Task 3 changes guidance: controller
must remeasure before claiming its modified hook size; an over-budget result
needs explicit adjudication, not an invented inherited measurement.

Apply checks are against the actual execution source in task order. Check/apply
01 before checking/applying 02; check/apply 02 before checking/applying 03.
Temporary-index exact-tree evidence is provenance, not a substitute for these
actual-source checks. Do not regenerate patches during execution:
[emit-patches.py](collection_model_artifacts/emit-patches.py) needs prototype git
objects and is an authoring provenance tool, NOT an execution dependency.

## 4. Shared actor brief, budget, and task sizing

Open EACH actor brief with this repository preamble verbatim:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Use `rg -n` to locate the listed symbols, then read approximately 40-60-line
windows. New production paths below are deliberately monospaced, paired with
their patch link, not links to nonexistent production files.
Do not rediscover specifications or read large AGENTS/spec files wholesale.
Each task has at most THREE coherent work items. Budget by fixtures/cycles:

| Task | Production proofs | New assertions | Cycles now | Deferred cycles / risk |
| --- | ---: | ---: | ---: | --- |
| 1: finite pushforward | 6 | 0 | 0 | Generic algebra/type hypotheses; mutation suite at T3 |
| 2: typed program + models | 3 + 4 | 0 | 0 | One coupled admission/model boundary; suite at T3 |
| 3: fixtures + integration | 0 | 18 (9 guards, 9 theorems) | 12 | 5 source/invariant mutations, 7 fixture contrasts |

The 13 production proofs are NOT additional fixture assertions.
Five fixture proof helpers defined with `def` and one `#eval` are NOT assertions.
Use about 40 turns per implementation dispatch as a target, absolute 60 turns
and approximately 250k context peak; report any breach. Split a predicted breach
into production then fixture/cycle dispatches using the repository handoff pattern.
No heavyweight docs-only dispatch; Task 3 owns its bounded documentation sweep.
Slice execution cap is approximately 175M cumulative input tokens.
Authoring target is approximately 50M; these are not inferred compliance claims.
Token-report found no matching SDK transcript for the prototype session:
aggregate total is unavailable. Preserve that disclosure in close-out.

## 5. Task 1 -- generic finite additive pushforward

**Prerequisites:** source guards passed; warm preparation and `LeanNCD` refresh.
**Brief:** begin with Section 4's verbatim preamble; use 40-60-line windows.
**Files:** `leanncd/LeanNCD/Semantics/Collection.lean`, created by [patch 01](collection_model_patches/01-finite-pushforward.patch).
Symbols: `Family`, `pullback`, `pushforward`, `pushforwardHom`,
`pushforward_zero`, `pushforward_add`, `pushforward_id`, `pushforward_comp`,
`pushforward_relabel`, `pushforward_grouped` @ that production file.
Patch reading windows: 1-45 and 46-81; locate headers/symbols with `rg -n`.
Prior art: `Coord`, `Declarations`, `Store` @ [Types.lean](../../leanncd/LeanNCD/Semantics/Types.lean).
Immediate future callers: `Program.collect`, `collect_grouped`,
`relabeledCollect`, `collect_relabel` @ Task 2's `Program.lean`.
Mathlib finite sums/equivalence/sigma grouping are the patch's existing tools.

Three work items:
1. Land explicit function-family representation, contravariant precomposition,
   finite additive fiber pushforward, with exactly the compiled hypotheses.
2. Land zero/add/identity/composition proofs and the additive homomorphism.
3. Land occurrence-equivalence invariance and sigma grouping.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/collection_model_patches/01-finite-pushforward.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/collection_model_patches/01-finite-pushforward.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Collection
```

Gate: controller per-task review checks variance, all finite/additive hypotheses,
and absence of a full categorical interpretation claim. Six production theorems,
zero new assertions, zero cycles yet. Do not run the post manifest here.
After review, stage ONLY the task file and commit:

```bash
/usr/bin/git -C <execution-worktree> add leanncd/LeanNCD/Semantics/Collection.lean
/usr/bin/git -C <execution-worktree> commit -m "feat(semantics): prove finite additive pushforward laws" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 6. Task 2 -- one typed admission and simultaneous-model boundary

**Prerequisites:** Task 1 reviewed/committed. Begin with Section 4's preamble.
**Files:** `leanncd/LeanNCD/Semantics/Program.lean` and
`leanncd/LeanNCD/Semantics/Models.lean`, both from [patch 02](collection_model_patches/02-program-models.patch).
Patch windows: 1-52, 53-103, 104-155, 156-204; keep source windows 40-60 lines.
Symbols @ `Program.lean`: `coordDecidableEq`, `Program`, `Defined`, `Occurrence`,
`outcome`, `AdmEnv`, `contribution`, `collect`, `collect_grouped`,
`relabeledCollect`, `collect_relabel`, `admEnv_relabel`.
Symbols @ `Models.lean`: `InputBinding`, `ValidInput`, `Input`, `InputAgreement`,
`Models`, `equationOperator`, `models_fixedpoint`, `RelabeledModels`,
`models_relabel`, `GroupedModels`, `models_grouped`, `AdmInput`, `Output`,
`outputProjection`, `denotation`, `denotation_of_model`.
Prior art: `interpret` @ [Interpret.lean](../../leanncd/LeanNCD/Semantics/Interpret.lean),
typed `Expr` @ [Expr.lean](../../leanncd/LeanNCD/Semantics/Expr.lean), and Task 1 laws.
Immediate callers: Task 3 collection fixtures and the semantic umbrella import.

Three work items:
1. Finite tensor roles, tagged guard-valuation occurrences, bounded defined
   destinations, strict body outcomes, and witness-backed defined contributions.
2. Pushforward-backed collection and grouped/relabelled admission/value laws.
3. Tensor-presence inputs, ALL defined equations, fixed-point characterization,
   model presentation invariance, and nonconstructive unique-model projection.

Program and Models stay together: changing admission changes the model boundary.
Do not split into an input-only patch that temporarily misstates complete models.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/collection_model_patches/02-program-models.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/collection_model_patches/02-program-models.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd LeanNCD.Semantics.Models
```

`LeanNCD.Semantics.Models` is the task's import-umbrella proof target; it imports
Program and Collection. The public semantic umbrella is wired only in Task 3.
Gate: controller reviews typed versus runtime admission, duplicate tags, strict
zero demand, empty input presence, all nonoutput equations, and the partial
operator/unique-model distinctions. Seven production theorems, no new fixtures
or mutation execution yet. Stage both files explicitly after review:

```bash
/usr/bin/git -C <execution-worktree> add leanncd/LeanNCD/Semantics/Program.lean leanncd/LeanNCD/Semantics/Models.lean
/usr/bin/git -C <execution-worktree> commit -m "feat(semantics): define finite collection program models" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 7. Task 3 -- bounded fixtures, discovery, and verification

**Prerequisites:** Tasks 1-2 reviewed/committed. Begin with Section 4's preamble.
**Files:** [patch 03](collection_model_patches/03-fixtures-integration.patch) creates
`leanncd/test/Semantics/CollectionModelTest.lean` and modifies
[Semantics.lean](../../leanncd/LeanNCD/Semantics.lean),
[lakefile.toml](../../leanncd/lakefile.toml),
[root guidance](../../leanncd/AGENTS.md),
[semantic guidance](../../leanncd/LeanNCD/Semantics/AGENTS.md), and
[tensor_logic_semantics.md](tensor_logic_semantics.md).
The already published [post manifest](collection_model_mutations_post.json)
is consumed, not recreated; there is NO pre manifest.
Patch windows: 1-48, 49-96, 97-145, 146-193, 194-241, 242-290.
Symbols @ new test file: `expressionProgram`, `vectorProgram`, `duplicate`,
`collision`, `noStatements`, `occurrenceSwap`, `partialProgram`, `mixedProgram`,
`reciprocalProgram`, `roleDeclarations`, `roleProgram`, `presentEmpty`,
`omittedEmpty`, `extraDefined`, `internalNonzero`, `zeroStore`, and F07-F18 names.
Prior art/donors @ [ExpressionTest.lean](../../leanncd/test/Semantics/ExpressionTest.lean):
`Fixtures.ops`, `point`, `zeroStrict`, `bad`, `heterogeneous`, `registry`, `emptyShape`.
Immediate callers: default `Tests` glob and `LeanNCD.Semantics` through `LeanNCD`.

Three work items:
1. Land the exact 18 assertion fixtures with their legal/rejected neighbors.
2. Wire discovery/guidance and perform the value-based documentation/sibling audit.
3. AFTER the ENTIRE patch including configuration lands, controller runs the
   manifest check, all 12 cycles with `--out`, targeted checks, and full default build.

```bash
/usr/bin/git -C <execution-worktree> apply --check <execution-worktree>/papers/semantics/collection_model_patches/03-fixtures-integration.patch
/usr/bin/git -C <execution-worktree> apply <execution-worktree>/papers/semantics/collection_model_patches/03-fixtures-integration.patch
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd Semantics.CollectionModelTest
```

### Assertions and observed contrasts

All symbols in this table live in the new test file from patch 03.
Values are copied from evidence, not hand-derived. Each donor identifies the
construction that should be reused; "NEW" means no prior whole-program fixture.

| ID / kind | Intent and observation | Donor / change | Mutation links |
| --- | --- | --- | --- |
| F01 guard | Duplicate statements collect `4` | NEW `vectorProgram`; `Fixtures.ops/point` | M01, M06 |
| F02 guard | Distinct colliding tags collect `9` | Clone vector; `collision` asymmetric values/destinations | M01 |
| F03 guard | Untargeted coordinate is `0` | Clone collision, observe point 1 | M04 |
| F04 guard | Zero-statement defined tensor is `0` | Clone vector with count 0, `noStatements` | M04 |
| F05 guard | Prior `99` is NOT a seed; guard true | Clone duplicate; NEW `prior` | M04 |
| F06 guard | Relabel preserves lanes `9` and `5` | Clone collision; NEW sigma `occurrenceSwap` | M11 |
| F07 theorem `excluded_undefined` | False guard excludes undefined demand; proof compiled | Clone `Fixtures.zeroStrict/bad`, admitted subtype | M02, M07 |
| F08 theorem `active_zero_undefined` | Active nonoutput zero-times-undefined rejected | Clone partial program, keep true/legal false | M02, M03, M08 |
| F09 guard | Active legal zero body returns `some 0` | Clone partial program, legal true | M08 |
| F10 guard | Boolean primitive argument collects rational `14` | Clone `Fixtures.heterogeneous`, `Op.mixed` | M03 |
| F11 guard | Before-sum reciprocal `3 / 4`; after-sum `some 1/6` | `Fixtures.registry Op.recip`; NEW reciprocal program | M03, M10 |
| F12 theorem `present_valid` | Empty input present and valid; proof compiled | NEW roles; donor `Fixtures.emptyShape` | M09 |
| F13 theorem `omitted_empty_rejected` | Missing empty input rejected; proof compiled | Clone present binding, replace by none | M05 |
| F14 theorem `defined_binding_rejected` | Declared defined extras rejected; proof compiled | Clone present binding, supply defined families | M09 |
| F15 theorem `nonoutput_not_model` | Internal `7` violates zero equation; proof compiled | NEW internal store; zero-statement role tensor | M12 |
| F16 theorem `admissible_not_model` | Admission does not imply equations; proof compiled | Clone F15 plus `role_admitted` | M12 |
| F17 theorem `zero_model` | Legal zero store satisfies all equations | Clone internal store with zero store | M12 |
| F18 theorem `zero_fixedpoint` | Zero model fixes equation operator | Clone F17, apply `models_fixedpoint` | M12 |

The single evaluation output was `4, 9, 0, 0, 9, 5, 14, 3 / 4`.
F06 uses unequal lane values; preserving one lane cannot conceal a bad relabel.
F07/F08/F09 distinguish excluded undefined, active undefined, and active legal
zero bodies. F12-F14 distinguish presence from vacuous cell agreement.
F15-F18 distinguish admission, nonoutput equations, a model, and a fixed point.

### Unchanged siblings and case x class audit

Name these unchanged siblings in the controller task review: `Expr` admission,
strict `interpret` binary/primitive evaluation, expression `Readiness` and
`Completeness`, existing Expression/Native/Contract tests, the historical core
spike, and legacy [Eval/](../../leanncd/LeanNCD/Eval) contracts.
Their behavior is not replaced. Do NOT claim the current legacy evaluator
implements this additive program semantics. Preserve old expression/readiness
claims and prior non-default spike discovery while adding the new layer.

| Case / class | Required | Forbidden | Silently ignored / absent |
| --- | --- | --- | --- |
| Active output / nonoutput occurrence | Every body defined | Treat undefined as zero | None |
| Guard-excluded valuation | Remove before demand | Evaluate its body anyway | Its body and contribution |
| Active zero body | Strict definedness | Zero-times-undefined shortcut | None |
| Duplicate / colliding tags | Sum every fiber member | Deduplication, overwrite, injectivity demand | None |
| Empty fiber / no statements | Additive zero | Automatic prior seed | None |
| Defined candidate prior | Explicit body read only | Implicit update seed | Prior value as extra summand |
| Declared input, including empty | Present complete family | Missing input default | Empty cells only, never presence |
| Declared defined input binding | Exact absence | Extra supplied binding | None |
| Undeclared ID / input destination | Structural unrepresentability | Runtime rejection claim | Not a silently accepted raw API |
| Nonoutput defined equation | Every coordinate equation | Output-only model check | None |
| Nonlinear body primitive | Evaluate before collection | Unproved commutation across sum | None |
| Raw write/drop/source program | Explicitly deferred | Inventing a policy/checker | Not silently ignored supported syntax |

Classify any additional silently ignored cell found by review; do not expand
scope without controller adjudication. This table audits unchanged neighbors
that a patch-only review cannot see; it is not a source checker implementation.

### Documentation value sweep (same task, no docs-only dispatch)

Run these separate value-grep commands over the execution tree and classify
every hit, including documents outside the patch. Read only 40-60-line windows
around relevant hits; do not rewrite a historical completion record as inventory.

```bash
rg -n '8686|8690|13 production|18 assertions|9 guards|9 theorem|12.*mutation' <execution-worktree>
rg -n 'not additive program models|no additive program|collection.*deferred|models.*deferred|writes.*deferred' <execution-worktree>
rg -n 'empty input|input presence|omitted input|defined bindings|non-output|nonoutput|AdmEnv|AdmInput|unique.model|fixed.point|Classical.choose' <execution-worktree>
rg -n 'Float|semiring|Boolean OR|XOR|heterogeneous|source checker|runtime|drop|publication|solver|backend|precision|categorical|Kan|representability' <execution-worktree>
```

`8686` is the historical refreshed baseline observation; `8690` is the prototype
candidate full build observation, not a permanent job-count requirement.
Retain both with provenance; record actual execution counts separately.
Current scoped guidance may acknowledge the new collection/model layer, but
must retain all input/model/backend exclusions in Section 2.
Review Section 19's bounded validation note, semantic guidance, umbrella and
default test reachability. Historical spike/readiness records stay historical.
Any further necessary prose correction is controller-adjudicated and re-reviewed,
not silently folded into the verified patch or delegated as a heavyweight task.

## 8. Mutation gate, task commit, and future release protocol

All 12 post-manifest entries have verification task `"3"` and target
`Semantics.CollectionModelTest`. Only run them after all Task 3 sources/config land.
M01-M05 are five source/invariant mutations; M06-M12 are seven fixture contrasts.
M01 multiplicity and M04 prior seed can die in generic collection-law proofs
before numerical guards run. M02 rejects a dependent contribution-definedness/
admission invariant statically; it is NOT a runtime guard-checker bug.
M03 replaces outcomes by zero; M05 bypasses empty-input presence.
M06 deletes a duplicate; M07 activates an excluded body; M08 legalizes an undefined
body; M09 repairs extra bindings; M10 asserts nonlinear commutation; M11 changes
the asymmetric lane expectation; M12 repairs a nonoutput equation counterexample.
These are 12 cycles, not 12 independent runtime regression executions.
Every `expect` is copied from an actual failure; exact diagnostic line numbers
belong only in the JSON anchors, not prose citations.

Controller must execute BOTH commands, with no prefix filter or silent skips:

```bash
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --check <execution-worktree>/leanncd <execution-worktree>/papers/semantics/collection_model_mutations_post.json
bash <execution-worktree>/leanncd/scripts/mutation-manifest.sh --out <controller-session-artifacts>/collection_model_mutation_results.md <execution-worktree>/leanncd <execution-worktree>/papers/semantics/collection_model_mutations_post.json
bash <execution-worktree>/leanncd/scripts/lake-build.sh <execution-worktree>/leanncd
```

`--check` alone is NOT the suite. Require all 12 selected/PASS, expected failures,
restored builds, and byte-identical restoration. Full default build follows the
actual manifest check AND actual suite; preserve existing warnings honestly.
Prototype targeted/full builds passed, full `8690` jobs; controller baseline
passed `8686` in the separate code-unchanged publication tree. Controller initial
suite and strengthened pinned replay both passed 12/12. The copied
[result table](collection_model_artifacts/mutation_results.md) confirms every
expectation, byte-identical restore, and green restored build. Controller's
post-mutation tracked-source diff was empty and full candidate build passed
`8690` jobs. Its compiled axiom audit of ALL 13 production theorems found only
`propext`, `Quot.sound`, and `Classical.choice`, with no `sorryAx`.
These are actual controller verification, not Dispatch B build claims.
Both final plan review lenses are complete, with no open findings after the
confirmed preparation-restriction correction. Authoring verification is complete;
publication of these artifacts is not an implementation release.
For future execution the controller reruns its own full suite/build, regardless
of those prototype observations.

Task 3 gate: controller reviews fixtures, exclusions, sibling table, discovery,
documentation classification, and actual mutation/full-build outputs, then commits:

```bash
/usr/bin/git -C <execution-worktree> add leanncd/test/Semantics/CollectionModelTest.lean leanncd/LeanNCD/Semantics.lean leanncd/lakefile.toml leanncd/LeanNCD/Semantics/AGENTS.md leanncd/AGENTS.md papers/semantics/tensor_logic_semantics.md
/usr/bin/git -C <execution-worktree> commit -m "test(semantics): cover collection models and wire discovery" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Future final whole-branch review has TWO independent lenses:
1. Categorical/semantic/model fidelity: finite-family variance and laws,
   nonlinear boundaries, presence, all equations, fixed points and uniqueness.
2. Artifact/type/admission/execution fidelity: actual patch replay, import/default
   reachability, structural versus runtime claims, mutation kills/restoration,
   source guards, untouched siblings and scoped documentation.
Reviewers preserve findings incrementally in controller session artifacts;
give them exact symbols and 40-60-line windows, not a fresh broad exploration.
Controller adjudicates every load-bearing finding; stop on unfixable blockers.

A future implementation release requires the controller's green full build and
clean/adjudicated whole-branch reviews. Only then merge the implementation branch
to local main and remove THAT execution branch/worktree under the repository
finish protocol. Do not merge the prototype, touch protected worktrees, or push.
Current PLAN-ONLY publication is a separate controller-owned artifact commit;
it must not be reported as an implemented/released collection/model slice.
Close-out records actual commands/counts, skipped items (none silently), review
dispositions, measured budget or unavailable telemetry, and remaining limitations.
