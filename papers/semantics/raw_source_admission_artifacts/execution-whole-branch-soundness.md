# Independent whole-branch soundness review

- Reviewed base: `9f333b918ca2db2eb343a53269008731e651553e`.
- Immutable reviewed tip: `270b517d0a69bffde95a1633352577425f5858cf`.
- HEAD matched the reviewed tip; the worktree was clean before this report.
- Method: direct source review, no agents, builds, mutations, or commits.
- Status: COMPLETE -- CLEAN within the stated whole-branch soundness scope.
- Confidence: high for the reviewed contracts and premise chain. No high-confidence
  load-bearing soundness defect was found.

## Incremental evidence

### Resolver, Adapter, Admission

- `assignUIDs_eq_inline` compares the entire original FreshM computation, not just
  a returned program. `assignUIDMemo_covers` derives defined lookup coverage from
  the successful insert-only loop. Neither it nor the same-name UID theorem assumes
  global freshness or injectivity.
- `resolveSource_mapUID_covered` extracts the memo from actual resolution success
  and preserves the supplied specs/inputs. Traversal preserves name/kind and the
  ordered declaration, statement, term, and factor lists.
- `checkAxes_declarations` and `checkTable_declarations` derive ordered selections
  from actual checker success. `TableDeclarations.entry` uses the original
  declaration's zip index and lookup, not its compact table index, and exposes
  supported spelling/type, ordered UID/extent slots, matching spec, role, and shape.
- `admitSource_fields`, `admitStatement_fields`, and `admitTerm_reads` derive
  ordered occurrence relations from successful mapM calls. Unsupported forms are
  excluded by the executable success premise; output writability remains in the
  admitted statement's type. Repeated and empty lists are not deduplicated.
- Recipe tasks 1-4 and the explicit non-claims were read.

### Raw transport and semantic applicability

- `admitRawSource_fields` composes actual resolver and admission success with the
  Adapter certificate. Its memo coverage, raw declaration selections, and raw
  occurrence relations are derived, not assumed as additional endpoint premises.
- `RawCorrespondence.tensor` supplies both original and mapped declaration lookups
  at `entry.declaration`, successful supported classification, matching spec index,
  role, and exact extent shape. `RawCorrespondence.statement`,
  `RawStatementFields.term`, and `RawTermFields.factor` use the same zip-index
  positions as the admitted lists, rather than membership-only or count-only links.
- `RawReadSlots.coordinate`, `RawOutputSlots.coordinate`,
  `CertifiedRawTerm.read_projection`, and `CertifiedRawStatement.output_projection`
  witness the original raw axis at the exact tensor slot, the memo lookup for its
  original name, and equality of both localized and global coordinate components.
  The slot index is not a deduplicated support index.
- The semantic certificate packages structural witnesses with existing semantic
  theorems. It does not define an independent raw interpreter and then prove it
  equal to itself. The absence of independent raw denotation is explicitly stated.
- Reviewed Lowering, Statement, Fiber, Correspondence, Program, relevant
  ProgramCorrespondence, Schedule, and ReferenceExecutor windows. Ordered read
  products preserve factor multiplicity; empty products/sums use one/zero; support
  deduplication affects valuation binders, not factor or statement occurrences.
  Footprints are ordered lists and retain repeated addresses.
- `CertifiedRawSource.collect` derives total-store admissibility through
  `total_admEnv`; generic results require the existing Semiring instance and total
  Store. No claim of partial-read success is hidden in those signatures.
- `admitRawSource_reached` consumes `ActualValidatedResult` and an actual complete
  outcome. `ValidatedResult.result` carries legal Execution from `initial input`;
  `result_success` obtains reachability from it, not from arbitrary Complete alone.
  Model equations and uniqueness are relative to `result.input`.
  `admitRawSource_reached_denotation` retains the output subtype restriction.
- Changed AGENTS, roadmap/spec status, import registration, and the source
  correspondence record state these boundaries honestly.

### Tests, axioms, and final scope checks

- Read all of `SourceRawCorrespondenceTest.lean`, including the ten-family
  distinguishing pins, success proofs, indexed getters, certified donor read/body/
  output connections, and reached execution specializations. Admission successes
  use kernel reduction (`cbv`), not `native_decide`; named execution theorems retain
  their explicit complete-outcome premise.
- Declaration-form fixtures cover tensor/linear, typed/untyped f32/f64, both linear
  bias flags, and metadata differences at use sites. Interleaved and equal-extent
  fixtures distinguish compact table positions, original declaration indices,
  slot identities/order, and matching shape. Repeated factors, copied statement
  occurrences, diagonal slots, empty products/sums, and zero extents are explicit.
- Reviewed the existing `Successful`, `Complete`, `finalStore`, `Models`,
  `InputAgreement`, and output-only `denotation` definitions, and the soundness
  theorems behind the reached endpoints. Reachability plus legal execution is
  retained; arbitrary complete machine states do not establish the endpoint.
- The direct forbidden-proof-token search over Source, Structural, Traverse,
  and the new test module found no `sorry`, `sorryAx`, `admit`, `native_decide`,
  `axiom`, or `unsafe` tokens. Targeted reads of the controller's final build
  receipt confirm that the raw/certified/reached/denotation endpoints, coordinate
  theorems, semantic wrappers, and named donor executions depend only on
  `propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof.
- Scope-honesty check: generic results do not certify the original input buffers;
  conditional reached results use the supplied validated result's input.
  The canonical donors additionally use `sourceInput` and `runSource_eq`.
  Observed completion/value output is not promoted to an unconditional kernel
  completion theorem. No independently specified raw denotation, parser theorem,
  global mint injectivity, oracle equality, or backend/float refinement is claimed.

### Zero-domain coordinate evidence boundary

The asymmetric fixture includes an unused zero-extent source axis. Consequently
its full-source `UIDVal` type is empty: its `DonorReadConnection` and
`DonorOutputConnection` specializations alone are not evidence of non-vacuous
full-source coordinate evaluation. This is not a load-bearing theorem defect or
an assertion that meaningful term/output coordinates are empty.

The usable slot-coordinate API is more general:
`RawReadSlots.coordinate` and `RawOutputSlots.coordinate` accept the context of
the supplied typed Slots. For a certified factor, `RawCheckedFactorFields.slots`,
`CheckedRead.linked`, and `LocalizedRead.linked` transfer the raw slot relation to
the localized term Slots without requiring a full-source valuation. For output
Slots, `RawStatementFields.output_slots` already supplies the corresponding raw
relation. Thus the coordinate theorem can be instantiated on the relevant
localized/output context even when an unused source axis has extent zero.
This availability was checked by reading the definitions and equality premises,
not by adding or compiling a scratch theorem. Statement body/fiber and Program
results do not require such a full-source valuation.

## Evidence limits

- This is a direct independent review of all scoped Lean production/test changes
  and theorem/status documentation between the base and immutable tip above, with
  bounded reads of immediate semantic dependencies. Historical log collections,
  unrelated subsystems, packaging Python, and staging patch copies were not audited.
- Build/mutation execution and byte-restoration success are supplied by the
  controller. No builds, mutations, or typechecks were repeated. Only targeted
  final axiom/donor receipt windows were consulted.
- HEAD still matched `270b517d0a69bffde95a1633352577425f5858cf` at the final
  read-only status check. This review changed only this report. A separate
  untracked `execution-whole-branch-fidelity.md` appeared during the review and
  was not read or changed; no source/docs changes were present.
- No agents, commits, staging, integration, or other source edits were performed.
- No known breach of the approximately 40-turn / 250k-context caps. The review
  used 21 direct tool steps, including incremental report writes. Exact SDK token
  telemetry was unavailable; no measured cumulative-input claim is made.

## Final verdict

**CLEAN within scope**, for base `9f333b91` through immutable tip `270b517d`.
Actual-success premises, original-ID declaration/spec/role/shape transport,
defined name-memo coverage, exact indexed occurrences, coordinate witnesses,
semiring/total-store boundaries, reached rational input/completion premises,
output-restricted denotation, multiplicity, empty identities, and changed-doc
scope claims were reviewed. No high-confidence load-bearing issue was identified.
