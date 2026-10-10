# Execution whole-branch runtime/fidelity review

## Scope and evidence boundary

- Independent read-only review of base `9f333b918ca2db2eb343a53269008731e651553e`
  through immutable tip `270b517d0a69bffde95a1633352577425f5858cf`.
  HEAD matched the reviewed tip; the initial worktree status was clean.
- Scope: all branch runtime/proof/test changes, related documentation and
  committed reproduction artifacts. Only this report is modified.
- No builds, mutation cycles, commits or agents are run by this review.
  Controller build/mutation claims are assessed against retained receipts,
  not represented as independently rerun validation.
- Authoring/package base `3d721f9631de8642163446f98b4efc8fe1d078d5`
  is distinct from the execution/review base above.
- Requested budget: approximately 40 turns and 250k context. Exact cumulative
  SDK token accounting is not available to this reviewer; any known breach
  will be surfaced rather than claimed as measured compliance.

## Incremental review

The following checkpoints preserve the review as it progressed. The final
verdict and evidence limits are recorded at the end.

### Runtime and certificate pass

- Inspected the resolver extraction against the original inline diff:
  `assignUIDs_eq_inline` equates the entire `FreshM LabeledProgram` function,
  not only successful values. Thus error results and final counters are
  included; `axisSpecs` only changes visibility.
- Followed actual `resolveSource -> adaptSource -> admitSource` sequencing:
  `checkAxes` precedes `checkTable`, which precedes all input checks.
  `sourceAxis` resolves by UID, intentionally ignoring occurrence name/kind
  after resolution. Zero extents are not newly excluded.
- Declaration certificates use `decls.zipIdx` and original declaration
  lookups; tensor-table `Fin` positions are not substituted for those IDs.
  Supported declarations retain type, name, slots, matching spec, role and
  exact extents. Bias is intentionally ignored, not certified as operative.
- Read the raw and resolved `Forall₂` transports and indexed getters:
  statements, terms, factors and slots retain order, multiplicity, origins
  and empty lists. Memo lookup witnesses use the raw occurrence's name;
  no theorem replaces name binding with equality of raw sentinel UIDs.
- Semantic endpoints consume the existing checked/global projections and
  total-store semiring results. Reached endpoints explicitly require an
  actual complete result, use `result.input`, and expose denotation only at
  output-flagged tensors. No unconditional completion or separately
  specified raw denotation was found in these theorem statements.
- No high-confidence load-bearing defect found in this pass. Concrete
  fixtures, dependency boundaries, docs and artifact fidelity remain under
  review.

### Fixture and semantic-premise pass

- All ten contract families have concrete guards and/or certified donor
  specializations, not just theorem existence checks:
  interleaved declaration IDs, nine tensor/linear type/bias forms, three
  equal-extent declaration-slot neighbors, resolver metadata, exact error
  order, distinct Y/Z destinations, indexed repeated/empty occurrences,
  sentinel-name separation, and the two complete rational donors.
- `DeclarationIdentity` distinguishes B at table position 1/declaration 5,
  ordered A slots `[i,k]`, `[k,i]`, `[i,i]`, and legal reversed reads `[k,i]`.
  `IndexedOccurrences` pins B/A/B, a second term, an empty product, an empty
  sum, copied statements and repeated diagonal read/write slots.
- `ExactErrorOrder` simultaneously violates max/sum, relu/identity and
  target-declaration constraints, then repairs one at a time: nonSum,
  nonIdentity, undeclared Missing, accepted Y. Complete origin equality
  pins absent declaration/term/factor/slot fields too. Existing domain
  fixtures additionally pin first bad domain before an extra-slot rank
  error, with nonzero statement/term/factor locators.
- Followed checked input enumeration, including unused and zero-length
  inputs; existing input fixtures reject missing unused/empty bindings and
  short buffers, and assert exact stored and coordinate-enumerated values.
  This runtime validation is not promoted to a new input-buffer theorem.
- `LeanNCD -> Semantics -> Source` imports both new modules; default
  `Tests` and the admission-test umbrella import the raw fixture module.
- Retained full-build donor windows show parsed complete/4 events,
  X/Y `[3,5]`; asymmetric complete/12 events, Y `[607,6016]`,
  Diagonal `[1,0,0,1]`, Empty `[]`. The Bool guards assert completion;
  values/event counts are observed receipts, not unconditional kernel
  theorems. Named certified execution theorems still take the complete
  outcome equality.
- Inspected docs explicitly preserve `result.input`, output-restricted
  denotation and parser/raw-denotation/completion/buffer/backend nonclaims.
  No stale current claim that the bounded raw-AST link is open was found.
- First deterministic artifact check confirmed all ten installed/tip
  hashes and identical authoring/execution base inputs. Its subsequent
  tracking assertion used too narrow a tree listing (omitted parent-level
  manifests); this is a reviewer-script error, not a repository finding.
  The complete read-only artifact audit remains to be completed.

### Reproduction fidelity pass

- Independently replayed the four final unified patches entirely in memory,
  validating each original hunk and count against execution-base blobs.
  Each stage's exact path set and source SHA256 matched readiness; every
  stage-local old string was unique at its actual stage prefix. Final
  reconstructed bytes equal all ten immutable-tip/installed source hashes.
  No temporary index, patch application or source mutation was performed.
- Verified 23 pinned receipt/authority/projection hashes, all six historical
  seed/candidate hashes and the five exact task projections. Both final
  authorities partition correctly by old text's presence at the recorded
  authoring base, with 11 existing-text and six post-text entries.
- For all 17 execution-final cycles, checked the expected diagnostic in
  that mutation's own block and on the exact file-error line, plus
  mutation exit 1, restoration-hash exit 0, restored-build exit 0 and
  final PASS. This confirms receipt fidelity, not an independent mutation
  rerun or a new cryptographic measurement of the historical restoration.
- All 82 reproduction-directory artifacts committed at the reviewed tip
  match current bytes, including 45 committed `.log` files. Thus ignored
  log inputs are retained rather than silently missing from the package.
- The retained execution full-build receipt ends with successful 8,766
  jobs and contains no error lines; non-fatal warnings remain. Authoring
  controller receipts are kept separate from execution-final receipts.
- Historical `evidence.json`, partial task patches, candidate manifests
  and intermediate pending fixture receipts are explicitly preserved as
  history. They are not counted as current readiness or current controls.
  The package CLI's authoring-base guard is intact; the execution record
  explains its refusal at the different execution base.
- A concurrent untracked soundness-review report appeared after the
  initial clean status. It is outside the immutable tip and was neither
  read nor modified. A reviewer-directory enumeration initially included
  it and correctly refused to call it committed evidence; the subsequent
  tracked-only audit passed. No repository defect is inferred.

## Declaration/slot case-by-class matrix

This is the actual call chain, not a hypothetical independent checker:
raw name resolution and `buildDeclEnv` first, then `checkAxes`, `checkTable`,
`checkInputs`, and ordered statement admission. A cell saying "ignored"
does not mean that an earlier/later seam cannot reject the same input.

| Class / siblings | Required by the applicable seam | Forbidden / existing rejection | Intentionally ignored |
| --- | --- | --- | --- |
| Pinned `.axis`, nat or real, including zero | Emit ordered resolved UID and exact pin; `checkContext` requires UID uniqueness only | Duplicate resolved UID, before checking that axis's optional size | Name/kind are not adapter guards; `tensorDecl` skips axes |
| Unpinned `.axis` | No successful axis emission | `missingDomain`; actual axis pass runs before the table | `tensorDecl` alone skips it, but cannot waive the preceding failure |
| `.iter` | No admitted iteration declaration | Existing iteration refusal in axis/table classification | No successful skip/emission certificate |
| Untyped `.tensor` | Original declaration index/name, adapter f32 metadata, exact ordered slots and matching spec/role/shape | Duplicate name, unbound declaration slot, missing/bad spec | Axis pass skips it; no positive-size restriction |
| `.typedTensor` f32/f64 | Preserve actual selected type as well as the tensor requirements | Same existing table constraints | No new occurrence-kind or read-UID-equals-declared-slot guard |
| `.linear`, false/true bias | Same supported untyped table contract | Same constraints, no new linear-specific rejection | Bias is not operative in admission; axis pass skips it |
| `.typedLinear` f32/f64 x false/true bias | Preserve selected type/name/ordered signature/spec | Same constraints | Bias and post-resolution occurrence kind do not add checks |
| `.typedTensor`/`.typedLinear` complex64/complex128, both bias bits | No supported tensor emission | Raw `buildDeclEnv` rejects complex first; direct resolved snapshots reach existing table complex refusal | Axis pass alone skips these declarations |
| `.predicate` | No supported tensor emission | Existing predicate refusal in table classification | Axis pass alone skips it |
| Explicit specs for every supported tensor/linear | Original declaration IDs, exact extent lists and explicit roles | Duplicate specs first; missing spec/bad shape while scanning declarations; unexpected specs after table construction | Cached env and external-name classification do not determine role |
| Raw same-name occurrences with different UID/kind | Actual memo coverage/name lookup; map only UID and retain metadata | No added initial-UID agreement condition | Initial UID does not choose the binding; generic unnamed/uncovered UData fallback is unchanged |
| Different raw names sharing sentinel UID 0 | Bind by distinct source names; concrete sentinel fixture pins resolved 1/2 and reversed `[2,1]` read | No raw-nonzero precondition | Raw sentinel equality is not used as name identity; no general mint-injectivity theorem is claimed |
| Bare read `.axis`, equal-extent distinct/reversed/repeated slots | Resolve each UID, retain ordered slot list, then check signature extent/rank | Unbound UID or bad domain/rank | Name/kind after resolution; no input-only read restriction or occurrence deduplication |
| Read `.const`, `.scale`, `.shift`, `.affine` | No bare-slot admission | Existing located affine refusal | None at the rejecting read-index seam |
| Bare output `.free`, including repeated slots | Writable named target; ordered resolved slots, local/global projections and exact signature extent/rank | Input writes; unbound UID or bad domain/rank | Name/kind after resolution; support/context dedup is not slot dedup |
| Output `.freeNorm`, `.iterAt`, `.iterNext`, `.affine` | No bare output admission | Existing marked / scanSlot / affine refusal respectively | None at the rejecting output-index seam |
| `.read` versus `.iverson`/`.unaryFn` factors | Exact tensor lookup/name/original declaration origin and every read occurrence | Existing Iverson/unary refusal | Read role is unrestricted; factors are not deduplicated |
| Assignment / scatter / recurMorphism | Sum then identity; exact writable target and ordered terms/factors | nonSum before nonIdentity before target lookup; scatter/recurMorphism refused | Later diagnostics are deliberately not reached after an earlier failure |
| Input / defined / output roles | Every input has checked buffer; defined/output may be written | Input writes; input bindings for noninputs | Noninputs need no input buffer; external names cannot override explicit role |
| Used / unused / empty input buffers | Binding at original declaration ID, ordered shape, canonical count and exact supplied values | Duplicate/unexpected/wrong-role bindings before buffer traversal; missing/shape/length in table order | Unused or zero-size does not waive a binding; zero-size does not require a value |
| Empty products/sums, repeated statements/terms/factors/slots | Preserve exact lists and original ordinals; empty product/sum existing semantics are one/zero | No new nonempty/unique-use/one-write-only restriction | Support deduplication does not remove any source occurrence |

Nat/real zero acceptance is established here by exhaustive inspection of the
unchanged axis/context/table bodies and the generic ordered-pin theorem.
Retained concrete fixtures cover zero nat pins/empty buffers and finite
nat/real neighbors; this review did not run a new real-zero fixture.
All nine tensor/linear type/bias accepted forms are concretely guarded.

## Exact control classification

First failures were checked against the actual declaration containing each
diagnostic, not inferred solely from manifest labels:

| IDs | Load-bearing rejection site | Classification |
| --- | --- | --- |
| M1 | `assignUIDMemo_covers`; also `assignUIDs_eq_inline` | Proof-protected rejection |
| S6 | `AxisSpec.mapUID_sourceUIDRelabel`; also `assignUIDs_eq_inline` | Proof-protected rejection |
| S1, S2, S7 | `checkTable_declarations` | Proof-protected rejection |
| S3, S8 | `tensorDecl_classifies` | Proof-protected rejection |
| M2 | `astRead_fields` | Proof-protected rejection |
| M3 | `admitAstTerm_fields` | Proof-protected rejection |
| S4, S5, E1, E2, E3 | `admitStatement_fields` | Proof-protected rejection |
| E4 | `CertifiedRawTerm.read_projection` | Proof-protected rejection |
| M4 | `AsymmetricOrder` and `IndexedOccurrences` guards after expected-order alteration | Fixture contrast |
| E5 | `ErrorOrder` and `ExactErrorOrder` guards after max-to-sum donor alteration | Fixture contrast |

Thus **15 proof-protected rejections + two fixture contrasts + zero runtime
kills** is accurate. M4/E5 change fixtures, not production execution;
the other controls are rejected by proofs before runtime fixtures can
establish a runtime kill. The runner's actual SHA256 comparison of before
and restored files was inspected, as was validation-before-task-filtering.
Both authorities' retained tables report all cycle, restoration and expected
failure columns as yes/PASS: 11/11 and 6/6.

## Final verdict

**CLEAN within the requested whole-branch runtime/fidelity scope.**

No high-confidence load-bearing runtime regression, correspondence mismatch,
fixture-oracle defect, documentation overclaim or reproduction-fidelity bug
was found at the reviewed immutable tip. Confidence is high for the scoped
static comparisons, exact patch/hash/projection checks and retained-receipt
classification; it is not a claim of independently rerun compilation.

- Reviewed base: `9f333b918ca2db2eb343a53269008731e651553e`.
- Reviewed tip: `270b517d0a69bffde95a1633352577425f5858cf`.
- The only authoring-to-execution-base changed path is the semantics
  specification; all ten patch input blobs compare identically. Authoring
  receipts and execution receipts are explicitly distinguished.
- Runtime bodies outside the resolver extraction are unchanged; the new
  Adapter/Admission definitions describe certificates, not replacement
  checkers/interpreters. The resolver's full-function equality preserves
  errors and final state for every program, not merely tested starts.
- Endpoint axiom receipts use standard `propext`, `Classical.choice` and
  `Quot.sound` or subsets. The scoped source/test proof-token sweep found
  no `sorryAx`, `native_decide`, `sorry`, `admit` or `axiom` declarations.
  Existing unrelated project warnings/sorries are not asserted away.
- Source input buffers are checked at runtime, but the new theorem does not
  certify raw buffer denotation. `ActualValidatedResult` contains legal
  execution from the initial state of its own `input`; completion remains
  an explicit premise. Generic semantics require total stores and the
  existing semiring assumptions.
- No independently specified raw denotation, parser/string correctness,
  global mint freshness/injectivity, unconditional completion, oracle
  equality, float/backend refinement, arbitrary substitution or re-admitted
  permutation result is claimed or independently verified.
- Existing cross-statement additive divergence is outside this change and
  is explicitly retained as a nonclaim; no scope expansion was undertaken.
- No builds, mutations, commits or agents were run. All repository writes
  by this reviewer were to this report only. The concurrent soundness report
  was not consulted.
- No known approximately-40-turn/250k-context cap breach. Exact SDK
  cumulative-token/context telemetry remains unavailable, so measured
  compliance is not claimed.

Review stops here. This is a runtime/fidelity verdict for the named base/tip,
not a merge, integration disposition or substitute for the independent
soundness review.
