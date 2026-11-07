# Final whole-branch review — soundness lens

- Base: `b68f56c4`; reviewed HEAD: `7dd97846`.
- Scope: committed branch code and current semantic/execution claims, with targeted donor traces.
- This review does not run builds or modify implementation, mutation controls, or other documents.
- Incremental checkpoints and final disposition follow.

## Checkpoint 1 — geometry and structural transport

No required finding from the three production modules.

- `Domain` and `Domain.raw_axis` @ `IndexedComponentTransport.lean`: `axes` is a position bijection,
  `extent` preserves each corresponding extent, and `raw_axis` fixes the
  raw map on every integer-valued coordinate (including out-of-bounds ones).
  Surjectivity of `axes` fixes every destination raw component. Together
  with `coherent`, this prevents arbitrary finite-domain reshapes from being
  certified as supported geometry; empty coordinate domains do not remove
  the extent/raw-axis obligations.
- `Domain.policy` and `Domain.read` @ `IndexedComponentTransport.lean`: policy resolution uses the inverse
  raw map, while the admitted raw argument uses the forward map. The
  in-bounds proof derives the inverse commuting equation. Addressed outcomes
  map coordinates; constants and rejection remain unchanged.
- `Embedding` and `Embedding.address_injective` @ `IndexedComponentTransport.lean`: injective tensor identities and
  coordinate equivalences induce address injection. Partial-store pullback
  preserves `none`; composition is forward on addresses and contravariant
  on stores.
- `transport` and `footprint_transport` @ `IndexedComponentTransportExpr.lean`: every expression constructor
  is covered, arbitrary context maps precompose reads/predicates/indices,
  binders lift by `h × id`, and local array shape/layout and registry
  symbols are retained. The footprint statement is exact `List` equality,
  not set/multiset equality.
- `evalWith_transport` and `evalReady_transport` @ `IndexedComponentTransportEval.lean`: evaluation statements quantify
  over arbitrary partial stores and all `Ty Unit` result types, without
  readiness/success/reachability premises. Identity/composition are
  observational laws, with context composition `h ∘ k`, not claims of
  expression syntax equality or whole-component categorical identities.

## Checkpoint 2 — donor semantics and current claims

No required finding from the targeted donor traces or scoped documentation.

- `Coord`, `Coord.raw` and `AdmittedRead` @ `LeanNCD/Semantics/Types.lean`: coordinates are products of
  extent-bounded `Fin`s; `Coord.raw` retains their integer components.
  Thus coherence ties the coordinate equivalence to the specified axis
  permutation, rather than merely to cardinality. `Resolved` has no reject
  constructor; the admission equation rules out admitted rejection.
- `Domain.policy_id` and `Domain.policy_comp` @ `IndexedComponentTransport.lean`: both policy laws quantify over
  arbitrary raw coordinates and split all three outcomes. They are not
  restricted to in-bounds coordinates, where policy equality would be weaker.
- `footprint` and `evalWith` @ `LeanNCD/Semantics/Interpret.lean`: footprints concatenate ordered
  lists and enumerate every reduction/tabulation/primitive argument; `at`
  keeps the entire array footprint. Evaluation sequences the full array
  before selecting its index. Retaining the original constructors/layouts
  therefore preserves the donor's strictness, including unselected
  undefined entries, empty arrays and zero-length reductions.
- `evalReady` @ `LeanNCD/Semantics/Readiness.lean` and
  `evalReady_transport` @ `IndexedComponentTransportEval.lean`: the mapped read check and
  evaluation theorem preserve all three readiness classifications; complete
  interpretation is the same theorem specialized to stores returning
  `some`. No numeric default or reached-state restriction is introduced.
- `RationalReference.Carrier` and `RationalReference.registry` @ `LeanNCD/Semantics/RationalReference.lean` and the production transport
  signatures establish the precise boundary: `Declarations Unit`, rational
  carrier/operations, the unchanged closed registry and unchanged `Ty Unit`.
  This is not a theorem about arbitrary scalar sorts or backend registries.
- All five new Lean modules were read directly, not inferred from the patch
  copies. The primary fixture's explicit unequal-axis embedding, constant
  and rejection cases, nonidentity context, strict-array pair, ordered
  repeated addresses and contextual composition match their documented
  semantic intent. The copied probe adds bounded donor parity, not a second
  universal soundness theorem.
- The full component-interface design, transport plan, execution record and
  authoring record were inspected for semantic claims. The design separates
  local transport from composite match construction, rank/phase execution,
  model gluing and process identities. Its value/process/refinement
  distinction and warning that list priority alone is not a phase barrier
  remain explicit. Later design obligations are not missing implementation
  requirements of this slice.
- Prototype receipts are historical evidence; the documented follow-up and
  authoring/controller records supersede initial counts/locations and
  pending authoring gates. Observer, donor and copied-computation controls
  are expressly not live-production mutation kills or mutation-complete
  coverage.

## Final disposition

**CLEAN — no required findings (no P0/P1/P2 soundness defect identified).**
The reviewed source satisfies the scoped semantic/proof/API obligations;
no load-bearing blocker was found. This does not certify later component
composition theorems.

### Limitations and validation provenance

- Static whole-branch soundness review against the stated base and source
  HEAD; targeted existing semantics only, not a repository-wide audit.
  The controller's subsequently supplied documentation-only scope
  clarification was included; no post-HEAD Lean source change was reported.
- No builds, mutation cycles, probe regeneration or independent kernel/axiom
  runs were performed by this reviewer, as requested. The controller reports
  the full `LeanNCD Tests IndexedExecutionExperiment` build passed (8,869
  jobs) and the 97/82/90 namespace audits used only standard allowed axioms.
  Those are controller evidence, not reruns attributed to this review.
- Integration/observation acceptance belongs to the other final lens.
  Static patch copies and historical receipts do not substitute for the
  actual source proof traces above. No new claim of exhaustive fixture
  mutation sensitivity, automatic adapter synthesis, whole-component
  freshening, model gluing or runner equivalence is made.
- Completed below the 25-turn / 150k-context caps; no breach or nested
  delegation. Aggregate cumulative input-token accounting is not measured
  by this report.
- Only this review artifact was written. No source, other document, build
  artifact, mutation input or Git history was changed by this reviewer.
