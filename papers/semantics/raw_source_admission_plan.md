# Raw-source/admission correspondence: execution recipe

**EXECUTION-READY. Controller verification complete; implementation not landed.**

Date: 2026-10-09. Process: **Full**, a new soundness surface; proof discovery is complete.
Base: `3d721f9631de8642163446f98b4efc8fe1d078d5`.
Recipe checkout: `/Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4`.
Authoring and verification are complete. The controller restored prototype source to the stated
base; only the plan, patches and evidence remain. This recipe is released for a separately
authorized implementation execution. No implementation commit, merge or push occurred.

## 1. Package and front gate

[readiness.json](raw_source_admission_artifacts/readiness.json) records the four new patches,
ten installed compiled file hashes, dependencies, targets, theorem/fixture contracts and receipt hashes.
[emit_ready_patches.py](raw_source_admission_artifacts/emit_ready_patches.py) captures via an isolated
temporary git index: `read-tree HEAD`, explicit-path `add`, path-scoped `diff --cached HEAD`.
A second temporary index checks and applies patches in order and compares every resulting SHA256
with the installed compiled bytes. Neither operation changes source files or the real index.
Cached replay, all four per-stage builds, both final manifests and the full default build
**passed**. See [controller-readiness.json](raw_source_admission_artifacts/controller-readiness.json).

| Task | New final patch | Dependency | Files |
|---|---|---|---|
| 1 | [01-certified-binding.patch](raw_source_admission_patches/01-certified-binding.patch) | entry gate | Traverse, Structural, Adapter |
| 2 | [02-resolved-occurrences.patch](raw_source_admission_patches/02-resolved-occurrences.patch) | 1 | Admission |
| 3 | [03-raw-correspondence.patch](raw_source_admission_patches/03-raw-correspondence.patch) | 2 | new RawCorrespondence |
| 4 | [04-semantic-fixtures.patch](raw_source_admission_patches/04-semantic-fixtures.patch) | 3 | new RawSemanticConnection, Source umbrella, new raw test, admission test, lakefile |

The original [evidence.json](raw_source_admission_artifacts/evidence.json) and
[task-1.patch](raw_source_admission_patches/task-1.patch),
[task-2.patch](raw_source_admission_patches/task-2.patch),
[task-3.patch](raw_source_admission_patches/task-3.patch) remain **partial seed history**.
Do not apply them, overwrite them, or count their observations as final package readiness.
The structural/endpoint candidate manifests are historical design evidence; only the two
[existing-text](raw_source_admission_mutations.json) / [post-text](raw_source_admission_mutations_post.json)
manifests are current execution authority.

The controller appended dated receipts to the [record](raw_source_admission_record.md):
ordered **stage builds**, final targets/full default build, both final manifest checks
**and all 17 cycles**, byte-identical restorations and restored green.
Source soundness/fidelity reviews are clean within their explicit scope, not plan-staging approval.
Direct controller package verification completed the staging gate. The package is ready, not landed.
Runtime documentation and execution whole-branch reviews are still task/execution obligations.

Reproducible packaging commands (capture requires the installed compiled prototype at the base;
verify also works after controller restoration):

```sh
python3 /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/emit_ready_patches.py --consolidate
python3 /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/emit_ready_patches.py --capture
python3 /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/emit_ready_patches.py --verify
```

Re-capture resets status to pending controller checks; never use it to manufacture a ready status.
Consolidation preserves stable M/S/E prefixes and exact old/new text, partitions by whether the old
text occurs at base, and copies verified error substrings from the observed controller logs.
Final targets/task tags differ from historical logs; the controller reran all final controls.
Do not invoke capture on the restored base without first reinstalling the prototype.
[verify_ready_package.py](raw_source_admission_artifacts/verify_ready_package.py) records the full
controller sequence and requires the installed exact prototype bytes before it starts.

## 2. Exact theorem contract and non-claims

For actual `admitRawSource raw specs inputs = .ok admitted`, the compiled endpoint supplies:

- **A:** the actual resolver memo covers every occurring axis name; the existing name-keyed,
  UID-only map preserves names/kinds and binds same-name occurrences regardless of initial UIDs.
  Successful `checkAxes` preserves ordered pinned UID/extents, including zero. Every table entry
  has its original declaration lookup, tensor-bearing classification, name/type, ordered declared
  slots and successful `sourceAxis`, actual matching spec, role and exact extent shape.
  Original declaration index is never the compact tensor-table position.
- **B:** original raw declarations and exact indexed raw statements/terms/factors/slots connect
  pointwise to the actual mapped and admitted occurrences. `List.Forall₂` and indexed getters
  retain names, metadata, origins, repeated occurrences and empty sums/products, not just counts.
- **C:** certified raw occurrences instantiate existing checked/global UID read/output projections,
  body/footprint/fiber, Program collection/model, and rational reached-success results.
  Coordinate witnesses use the original raw name's actual memo lookup at the same slot position.

Authoritative contracts:
[declaration_invariants.json](raw_source_admission_artifacts/declaration_invariants.json),
[resolver_binding.json](raw_source_admission_artifacts/resolver_binding.json),
[raw_bridge.json](raw_source_admission_artifacts/raw_bridge.json),
[semantic_connection.json](raw_source_admission_artifacts/semantic_connection.json).
The [soundness](raw_source_admission_artifacts/soundness_review.json) and
[fidelity](raw_source_admission_artifacts/fidelity_review.json) reports found no scoped load-bearing defect.
They review the installed source, not revised staging/docs or future whole-branch integration.

Runtime bodies are unchanged except `assignUIDs`' memo/relabel extraction, covered generically by
`assignUIDs_eq_inline`: equality of the entire FreshM computation, including errors/final state.
The existing `axisSpecs` collector is newly public with unchanged body; reusable mapping/list
lemmas live in Traverse. No parallel runtime mapper/checker/interpreter was added.

Generic body/fiber/collection results require total stores and existing semiring premises.
Reached results require an `ActualValidatedResult admitted` and its actual complete outcome.
Their equations/input agreement/uniqueness are **relative to result.input**, not automatically the
source's stored input buffers. Canonical donor results use `sourceInput` through their actual
source run; their named theorems still explicitly consume the complete-outcome equality.
Denotation applicability is the existing **output-restricted** checked API; all-defined-coordinate
equations are supplied separately. Observed donor completion is not unconditional kernel completion.

Not claimed: independently specified raw denotation, parser/string correctness, global mint
freshness/injectivity, unconditional successful runs, input-buffer certification, oracle equality,
native/float/backend refinement, arbitrary substitution, re-admitted source permutations or rank
synthesis. Scans, affine/marked slots, guards/Iverson/unary/nonlinear bodies remain outside admission.
Production cross-statement additive divergence remains separate and unchanged.

## 3. Common executor brief and sequencing

Every future brief opens with the shell-harness preamble in
[new-slice](../../.claude/skills/new-slice/SKILL.md), plus these restrictions:
plain separate commands; no shell variable references, `cd x && y`, or pipelines into git;
absolute paths and `/usr/bin/git -C <absolute-worktree>`; explicit stage paths; never stage/commit
`.claude/settings.json`; build only the target checkout's `lake-build.sh` with its `leanncd` directory.
Read/view **40–60-line windows**, search with `rg -n`. Do not rediscover or transcribe proof bodies.
Use an isolated, warm execution worktree at the exact base; if its path differs, replace each literal
checkout prefix in the recipe before running commands. Do not apply onto the still-installed prototype.

Tasks apply complete compiled patches, then build, run available controls and obtain per-task
proof/fidelity review. No proof discovery is expected; an unfixable load-bearing finding blocks the chain.
Dependencies are strictly **1 → 2 → 3 → 4**.
The raw test source and its umbrella registration arrive only in task 4.
Tasks 1–3 verify production proofs and prefix-available mutations, **not runtime fixtures**.
All ten actual runtime/donor families are centralized in task 4; their logical contract ownership
does not make them available earlier. Task 3 imports base Provenance/ProgramCorrespondence through
modified Admission; it must not depend on a future umbrella import or test target.

| Stage | Contract-owned families; actual run stage | Cycles at stage | Risk / bounded work |
|---|---|---:|---|
| 1 | 4 structural families, all run at 4 | 7 proof rejections: M1,S1,S2,S3,S6,S7,S8 | resolver fidelity + context/table invariants + traversal helpers |
| 2 | ErrorOrder/OutputTargetNames, run at 4 | 7 proof rejections: M2,M3,S4,S5,E1,E2,E3 | resolved output, term/factor order, slot/origin proofs |
| 3 | RawIndexedOccurrences/RawSentinelNames, run at 4 | 0 new cycles | raw declaration, AST, slot transport; prior proof pins remain |
| 4 | 2 semantic families + all earlier 8 | E4 proof rejection; M4,E5 fixture contrasts | semantic applicability + integration/fixtures + small docs sweep |

Seven controls per early stage are runner work, not seven proof-discovery assignments.
Prefer one bounded apply/build/review dispatch per stage; cap approximately 60 turns / 250k context.
If necessary split review or long validation from application, retaining the exact patch/hash handoff.

### Task 1 — actual binding and original declaration invariants (A)

Files: [Traverse.lean](../../leanncd/LeanNCD/DSL/Traverse.lean),
[Structural.lean](../../leanncd/LeanNCD/DSL/Pipeline/Structural.lean),
[Adapter.lean](../../leanncd/LeanNCD/Semantics/Source/Adapter.lean).
Symbols (window-read, not whole-file):
`AxisSpec.mapUID_metadata`, `traverseAxes_list_id`, `traverseAxes_list_collect`,
`ProdTerm.mapUID_factors`, `RHSExpr.mapUID_terms`, `TLProgram.mapUID_lists` @ Traverse;
`TLProgram.axisSpecs`, `TLProgram.axisNames`, `TLProgram.mem_axisNames_iff`,
`forIn_insert_coverage`, `assignUIDMemo_covers`, `sourceUIDRelabel`,
`assignUIDs_mapUID_covered`, `assignUIDs_eq_inline` @ Structural;
`resolveSource_mapUID_covered`, `checkAxes_declarations`, `checkTable_declarations`,
`DeclaredAxisSlots`, `TableDeclarations.entry`, `adaptSource_declarations`,
`adaptSource_entry_declaration`, `TensorTable.find_name` @ Adapter.

Apply patch 01; check actual memo coverage and full computation equality, ordered pin/table proofs,
all original declaration forms and specs, and generic traversal reuse. No tests from task 4 yet.
Exit: Adapter target green, seven prefix-available controls restored green, per-task review adjudicated.

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/01-certified-binding.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/01-certified-binding.patch
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.Adapter
```

### Task 2 — resolved occurrence certificate

File: [Admission.lean](../../leanncd/LeanNCD/Semantics/Source/Admission.lean).
Symbols: `mapM_success_forall2`, `admitRead_fields`, `admitTerm_reads`, `BareReadSlots`,
`BareOutputSlots`, `FactorFields`, `TermFields`, `StatementFields`,
`admitStatement_fields`, `admitSource_fields` @ Admission.
Apply patch 02; retain exact output name/declaration, ordered resolved statement/term/factor/slot
relations and origins. Exit: Admission target green, seven task-2 controls restored green and review
adjudicated. M2/M3 and E1–E3 are proof coverage, not earlier runtime ErrorOrder fixture runs.

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/02-resolved-occurrences.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/02-resolved-occurrences.patch
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.Admission
```

### Task 3 — original raw transport and correspondence (B)

File: new [RawCorrespondence.lean](../../leanncd/LeanNCD/Semantics/Source/RawCorrespondence.lean).
Symbols: `RawAxisFields`, `RawDeclaredAxisSlots.slot`, `RawReadSlots.slot`, `RawOutputSlots.slot`,
`RawTermFields.factor`, `RawStatementFields.term`, `RawCorrespondence.tensor`,
`RawCorrespondence.pinned`, `RawCorrespondence.statement`, `RawCorrespondence.read`,
`RawCorrespondence.output`, `RawAdmissionFields`, `admitRawSource_fields` @ RawCorrespondence.
Apply patch 03; verify actual-success A/B composition and every original indexed occurrence.
Exit: direct module target green and axiom output reviewed; no test/umbrella dependency.
The module's compiled `#print axioms` receipts audit generic endpoints; accept only the recorded
standard dependencies (`propext`, `Classical.choice`, `Quot.sound`) or none, never `sorryAx`.
If a reviewer supplies a scratch Lean audit block, compile its exact file with the existing
[check-snippet.sh](../../.claude/skills/slice-plan/check-snippet.sh) wrapper; do not hand-roll Lake.
No Lean block is transcribed into this recipe.

Only if supplied by a reviewer, the scratch audit file below is a **future temporary file**,
not a package dependency. From the recipe checkout, standardize its typecheck as:

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/spikes/raw-source-axiom-audit.lean
```

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/03-raw-correspondence.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/03-raw-correspondence.patch
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.RawCorrespondence
```

### Task 4 — semantic applicability, fixtures, discoverability and docs (C)

Files: new [RawSemanticConnection.lean](../../leanncd/LeanNCD/Semantics/Source/RawSemanticConnection.lean),
[Source.lean](../../leanncd/LeanNCD/Semantics/Source.lean), new
[SourceRawCorrespondenceTest.lean](../../leanncd/test/Semantics/SourceRawCorrespondenceTest.lean),
[SourceAdmissionTest.lean](../../leanncd/test/Semantics/SourceAdmissionTest.lean),
[lakefile.toml](../../leanncd/lakefile.toml), runtime docs in §6.
Symbols: `RawReadSlots.coordinate`, `RawOutputSlots.coordinate`,
`RawCorrespondence.certifiedStatement`, `CertifiedRawStatement.term`,
`CertifiedRawTerm.read_projection`, `CertifiedRawStatement.output_projection`,
`CertifiedRawTerm.semantics`, `CertifiedRawStatement.semantics`, `CertifiedRawSource`,
`CertifiedRawSource.collect`, `CertifiedRawSource.models`, `admitRawSource_certified`,
`admitRawSource_reached`, `admitRawSource_reached_denotation` @ RawSemanticConnection.
Dependencies: `Term.read_projection`, `AdmittedOutput.projection` @ Admission;
`AdmittedStatement.footprint_body`, `AdmittedStatement.destination_pullback` @
[Statement.lean](../../leanncd/LeanNCD/Semantics/Source/Statement.lean);
`Term.body_correspondence`, `Term.collectedBody_correspondence` @
[Correspondence.lean](../../leanncd/LeanNCD/Semantics/Source/Correspondence.lean);
`AdmittedSource.collect_correspondence`, `AdmittedSource.models_iff_global`,
`sourceResult_globalModel`, `sourceResult_globalEquations`, `sourceResult_globalUnique`,
`sourceResult_globalDenotation` @ [ProgramCorrespondence.lean](../../leanncd/LeanNCD/Semantics/Source/ProgramCorrespondence.lean).
Fixture identifiers are in §4, all @ SourceRawCorrespondenceTest.
Apply patch 04; build modules/tests/umbrella, run three controls, perform the docs sweep.
Both new modules must be reachable through plain `LeanNCD`; Tests registration and admission test
import are in the patch. Runtime docs are **not** already updated by this prototype.

```sh
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/04-semantic-fixtures.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4 apply /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_patches/04-semantic-fixtures.patch
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd LeanNCD.Semantics.Source.RawCorrespondence LeanNCD.Semantics.Source.RawSemanticConnection Semantics.SourceRawCorrespondenceTest Semantics.SourceAdmissionTest Semantics.SourceAdmissionAcceptanceTest LeanNCD
```

## 4. Ten observed families, donors and distinguishing pins

All observed true in [structural_fixtures.json](raw_source_admission_artifacts/structural_fixtures.json)
and [endpoint_fixtures.json](raw_source_admission_artifacts/endpoint_fixtures.json).
These are ten contract families, not ten separate modules or a new acceptance count.
Donors: `snapshot` @ [SourceAdmissionFixtures.lean](../../leanncd/test/Semantics/SourceAdmissionFixtures.lean);
`RealLinearSumProduct` @ [SourceAdmissionAcceptanceTest.lean](../../leanncd/test/Semantics/SourceAdmissionAcceptanceTest.lean);
parsed/asymmetric/refusal variants and symbols below @ SourceRawCorrespondenceTest.

| Family | Installed fixture | Exact donor contrast / observed pin | Controls |
|---|---|---|---|
| DeclLocatorInterleaved | `Structural.DeclarationIdentity` | Clone snapshot; insert spacer axis after declaration3, increment later spec/input IDs. B table1 is declaration5, not1; original raw and mapped lookups certified. | S1,M2 |
| DeclarationForms | `Structural.DeclarationForms` | Recreate RealLinearSumProduct's X*X+X with rational inputs 1/3,5/7; tensor/linear, typed/untyped f32/f64, bias/nonbias and nat declarations/real use leaves. | S3,S7,S8 |
| EqualExtentAxes | `Structural.DeclarationIdentity` | Clone snapshot; equal bounds2, legal A[k,i] read retained. A declaration [i,k], [k,i], [i,i] have distinct UID lists despite equal shapes; all neighbors accepted. | S2,S3 |
| ResolverMetadataFidelity | `Structural.ResolverMetadataFidelity` | Clone parsed and inconsistentUIDs; initial same-name UID/kind differences do not alter resolved reads. Metadata and zero pins retained. | M1,S6 |
| ErrorOrder | `ExactErrorOrder`, original `ErrorOrder` | Clone refusal: max + relu + Missing simultaneously. refusalSum gives nonIdentity; refusalIdentity gives undeclared Missing; exact stage/side/statement and absent other origins. | E1,E2,E5 |
| OutputTargetNames | `Endpoint.OutputTargetNames` | Clone interleaved; same-shape writable Y/Z. Output Y table2/declaration6 vs Z table5/declaration9, with exact output origins; both accepted. | E3 |
| RawIndexedOccurrences | `Structural.IndexedOccurrences` | Clone asymmetric; B,A,B then A then empty product; append copied statement0 and Diagonal[i,i] read/write. Distinct ordinals, repeated factors/slots, empty sum and duplicate writes retained. | M3,S4,S5,M4 |
| RawSentinelNames | `Structural.RawSentinelNames` | Clone parsed; distinct a/b names both raw UID0, f64 X(a,b), read X[b,a], adjusted declarations/specs/shape. Name-keyed bindings and order differ from sentinel aliasing. | M1,S6 |
| CertifiedParsedSemantics | `Endpoint.CertifiedParsedSemantics`, `Endpoint.parsed_certified_execution` | Fixed parsed source and actual sourceInput run; observed complete,4 events,X/Y [3,5]. Kernel theorem explicitly requires actual complete outcome. | E4 plus structural pins |
| CertifiedAsymmetricSemantics | `Endpoint.CertifiedAsymmetricSemantics`, `Endpoint.asymmetric_certified_execution` | Fixed asymmetric run, observed complete,12 events,Y [607,6016],Diagonal [1,0,0,1],empty buffer; original ordered witnesses retained. Not a native/differential oracle. | E4,M4 |

The declaration/slot sibling audit in the fidelity report is authoritative. Preserve this matrix
under actual call-site premises (`checkAxes` precedes `checkTable`; `sourceAxis` checks resolved UID):

| Class | Required | Forbidden by existing checks | Intentionally silently ignored |
|---|---|---|---|
| pinned nat/real axis, zero allowed | ordered UID/pin | duplicate UID | tensorDecl skips axes; no name/kind guard |
| unpinned axis / iteration | existing missingDomain / iteration refusal | success classification | tensorDecl alone skips unpinned axis; prior pass rejects |
| tensor / typedTensor f32,f64 | original name/type/ordered slots, spec | duplicate name, unbound slot, missing/bad spec | checkAxes skips tensor |
| linear / typedLinear, both bias bits | same supported matrix | no added linear-specific guard | bias irrelevant; checkAxes skips |
| complex/predicate | existing refusal | tensor selection | axis pass alone skips |
| bare read/output slots, same-size distinct or repeated UIDs | resolved UID, rank/extent and ordered provenance | unbound/wrong rank/extent | names/kinds post-resolution; support dedup is not occurrence dedup |
| nonbare slots / iverson / unary / scatter / recurMorphism | existing located refusal | admitted fragment | none at rejecting seam |
| output/defined vs input role | exact name lookup, writable output/defined | input writes | external-name classification does not set role |
| input bindings, unused/zero-size included | original ID/shape/length/values checks | missing/duplicate/unexpected/bad bindings | noninputs need no buffer |

Do not widen scope to "fix" ignored cells: each is explained by the unchanged fragment.

## 5. Mutation receipts and execution runner

Observed controller receipts: [existing](raw_source_admission_artifacts/controller-existing.md),
[post](raw_source_admission_artifacts/controller-post.md),
[structural](raw_source_admission_artifacts/controller-structural.md),
[endpoint](raw_source_admission_artifacts/controller-endpoint.md), with matching `.log` artifacts.
All 17 observed cycles broke, restored byte-identically and rebuilt green.
Exactly **15 proof-protected rejections + 2 fixture contrasts + 0 runtime kills**.
M1 now fails Structural proofs, not five runtime tests. E1/E2/E3 fail Admission proofs before tests;
E4 fails coordinate proof linkage. M4/E5 change test oracle/donor, not production runtime.
The current manifests have 11 base-existing old strings and 6 post-added old strings, classified
mechanically. `expect` includes the exact file error prefix plus observed diagnostic text:
Application type mismatch, unsolved goals, `simp` made no progress, or Expression as appropriate.
Historical CANDIDATE/PENDING labels map by stable prefix; final labels/targets have fresh receipts.
Packaging `--check` passed for both consolidated manifests (11/6 entries, every old text unique).
Controller final-target cycles also passed: [11 existing-text](raw_source_admission_artifacts/final-manifest-existing.md)
and [6 post-text](raw_source_admission_artifacts/final-manifest-post.md), with byte-identical
restoration and restored green. Classification remains 15 proof rejections and 2 fixture contrasts.

The runner validates **all entries before filtering**, including on `--check`. Therefore early
stages use generated exact task projections, hashed in readiness.json, not the full post manifest.
These projections are derived execution inputs, not a third authority; capture regenerates them.
At tasks1/2 use both projections; at task4 use its post projection only; task3 has no new entries.
Commands below supply the runner's working directory explicitly; receipt names are new, preserving
historical observations. Schema/unique-text checks are separate from actual cycles.

```sh
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_mutations.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --task 1 --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/execution-task1-existing.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/stage-1-existing.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --task 1 --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/execution-task1-post.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/stage-1-post.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --task 2 --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/execution-task2-existing.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/stage-2-existing.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --task 2 --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/execution-task2-post.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/stage-2-post.json
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/mutation-manifest.sh --cd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd --task 4 --out /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/execution-task4-post.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics/raw_source_admission_artifacts/stage-4-post.json
```

The task4 existing selection is empty; do not invoke it (runner refuses zero selected).
The two unfiltered `--check` commands above are final-stage checks, not early-prefix commands.
At earlier stages run `--check` on the same **projection** used for that stage's cycles.
After task4 controller reruns both unfiltered manifests with new `--out` paths and retained logs.

## 6. Task4 runtime documentation sweep and final exit

Edit [lean_executable_semantics_path.md](lean_executable_semantics_path.md) §4.7/§5.1:
replace "raw link open/by construction" with actual-success `admitRawSource_fields` and
`admitRawSource_certified` structural correspondence and existing-semantic applicability.
Update [tensor_logic_semantics.md](tensor_logic_semantics.md)'s Proposition19.1 status row likewise,
preserving out-of-fragment limits. Explain result.input/complete-outcome/output-restricted denotation.
Append a dated follow-up to [source_correspondence_record.md](source_correspondence_record.md);
preserve its original receipts and historical39 controls.
Update [Semantics/AGENTS.md](../../leanncd/LeanNCD/Semantics/AGENTS.md) source paragraph with both
RawCorrespondence and RawSemanticConnection, actual-success endpoints and raw test;
update [leanncd/AGENTS.md](../../leanncd/AGENTS.md)'s source-binding entry for discoverability.
Update [DSL/AGENTS.md](../../leanncd/LeanNCD/DSL/AGENTS.md)'s traversal/Structural public surface:
actual name coverage, reusable mapUID lemmas, full `assignUIDs_eq_inline`, no global injectivity.
These small edits ride task4; they are not shipped as already-verified prototype doc edits.

```sh
rg -n 'by construction|raw.*(open|link)|19\.1|RawCorrespondence|RawSemanticConnection' /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/papers/semantics /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/LeanNCD/Semantics/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/LeanNCD/DSL/AGENTS.md
rg -n '\b39\b|six|four|15|fifteen|8765|partial-non-ready' /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4
rg -n 'sorryAx|native_decide|^\s*(sorry|admit|axiom)\b' /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/LeanNCD/Semantics/Source /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/LeanNCD/DSL/Pipeline/Structural.lean /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/LeanNCD/DSL/Traverse.lean
bash /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/close-raw-source-admission-proof-fcf548a4/leanncd
```

Review sweep matches by value; retain historical counts rather than blanket replacements.
Final independent **whole-branch** soundness and fidelity lenses happen after application/docs.
Soundness: actual-success premises, A/B/C, usable raw coordinate witnesses, no tautological raw
denotation, total-store vs complete rational result, result.input boundary and axiom dependencies.
Fidelity: runtime equality, sibling matrix, acceptance neighbors, exact refusal payload/order,
imports/discoverability/docs and honest control classifications.
Keep incremental findings in the execution record; adjudicate, then controller verifies final full
build and both actual manifests itself. Existing source-only reviews do not replace this gate.
Only future authorized execution may commit explicit paths and integrate after those gates.
No automatic merge for this authoring request; no push.

## 7. Record template and budget

Append receipts to the record, not this live recipe: date/base; four patch hashes and ten source
hashes; commands/exit codes for each prefix; exact axiom sets; task-filtered cycle counts/log paths;
all-family target results; full default build; 17 final cycles/restored hashes/green; docs sweep
matches adjudicated; both whole-branch verdicts; final disposition. Use identifiers, never Lean line locators.
Controller readiness section must distinguish cached byte replay from compiled stage replay and
pre-consolidation observations from final-manifest cycles. Pending fields stay pending until observed.

Controller measured named Pitfalls/Checks/Patterns/Context sections **including Global headings**:
leanncd AGENTS2984 chars; DSL AGENTS1790; Semantics AGENTS has no matching named sections,0.
No trimming is required by this metric. It is **not** a measurement of all hook-injected text.
Prototype work used separate bounded dispatches reported around35–60 rounds.
This fresh packaging dispatch is capped at approximately45 turns/250k context; exact SDK telemetry
and cumulative input are unavailable, so no exact turn sum or measured approximately50M authoring
compliance is claimed. Preserve approximately60 turns/250k per future dispatch, approximately50M
authoring target and approximately175M slice-execution budget; surface measured breaches or missing
telemetry. No extra implementation/validation dispatch is spawned by this write-up.
