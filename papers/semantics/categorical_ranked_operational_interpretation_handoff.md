# New-session brief: ranked operational interpretation and units

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> disclose any breach.

## Copyable launch instruction

```text
Read papers/semantics/categorical_ranked_operational_interpretation_handoff.md
on latest local main. Audit the bounded design questions in the brief, prototype
the smallest sound representation, prepare and verify one implementation plan,
then execute it for a conservative ranked, scope-aware operational interpretation
with event-free administrative identities and certified wires.

Reuse History.done/bind/splice, the existing source identity/wire presentation,
the complete observation laws and actual binary/associative history proofs.
Do not introduce a core identity program, replace the runner, or implement a
generic categorical framework merely to obtain unit equations.

Preserve ordered events, every private snapshot and ordered ledger, strict
failures, full reference relations and whole-interface/empty-input metadata.
Make administrative units preserve the inherited full state, not reset it.
Prove wire identity/composition/inverse and operational unit/congruence laws,
soundness of the chosen rank-restricted source equations, and conservative
agreement with actual existing component executions.

Establish typed arrows and composition-compatible observation agreement before
claiming a process category or operational functor. The unrestricted witness
source quotient is not automatically operationally sound: its leaf/assembly
generators admit unranked components.

Use the repository Full process and release gates, preserve unrelated work,
merge locally when green and reviewed, and do not push. Stop for a load-bearing
design/theorem blocker rather than weaken observations or assume soundness.
```

**Implementation process: Full.** This adds an operational interpretation and
unit/congruence soundness surface. Preparing this brief is documentation only:
it does not authorize implementation in the handoff session.
This is a goal brief, **not a verified plan**. Proposed representations,
new theorem/module names, fixture results and mutation diagnostics must be
prototyped and verified in the next session before becoming plan claims.

## 1. Starting point and the intended result

The finite decidable `Declarations Unit`, exact-rational, sealed matched profile
already has typed whole interfaces and wires, a denotational source category
and witness functor, actual ranked graph/reference phases, lossless histories,
concrete metadata observation laws and structural operational associativity.
The history algebra already has a zero-event successful terminal constructor;
the source syntax already has administrative identities and wires.

The goal is not another identity symbol or a core no-op implementation. It is
a **sound ranked operational interpretation of that administrative structure**,
including unit laws and categorical packaging justified by the interpretation.
Existing nonempty component execution must remain unchanged.

Read first:

1. [Synthesis](categorical_tensor_logic_semantics.md), Sections 6.12, 8, 9.2,
   10.1-10.3 and Appendix A.11.
2. [Operational associativity record](categorical_operational_associativity_record.md),
   especially the proved API, semantic boundaries and integration receipt.
3. [Source record](categorical_source_functor_record.md), for the denotational
   presentation and what its existing functor actually proves.
4. [Lean instructions](../../leanncd/AGENTS.md), then the targeted APIs below.

## 2. Bounded audit before choosing the representation

Do this audit before drafting tasks, not as a second open-ended literature
survey. Record the chosen approach and rejected alternatives with reasons.

### A. Units in histories are not new execution actions

`History.done s a` has no events and one snapshot. `bind` passes a successful
terminal state to the continuation and absorbs failure; `Continuation.shared`
enforces the shared start. Prove the required return/unit lemmas and transport
compatibility rather than assume those additional lemmas already exist.
Use arbitrary relevant incoming states, including nonempty private ledgers.

`GraphHistory.Admissible` constrains event/failure shape; it is not a certificate
that every history is an execution. `CompleteObservation` alone also does not
state that its history starts at its supplied input. The interpretation must
prove the necessary start, boundary and actual-run adequacy properties.

### B. Composition needs explicit wiring and a scope discipline

`compose` takes a supplied `Boundary` and changes declaration/identity spaces.
Existing associativity uses coherent transports, not literal raw-program
equality. Establish typed source/target objects, where wires live, how private
scope is retained, and what makes observation agreement a congruence for
composition. Do not declare a semicategory/category merely because a
three-component transport equation is already proved.

Frame preservation means retaining inherited availability and the ordered ledger
through explicit scope embeddings and compatible prefixes. State the required
freshness/disjointness and boundary consistency conditions. Do not require the
existing checked runner to execute arbitrary prepopulated frames: use semantic
lifting of its actual local histories and the proved phase relations.

### C. Restrict source equations soundly

`IndexedSource.Term.leaf` and the component generators of `Rel` admit unranked
components. Their current soundness proof targets complete-model witnesses,
not sequential histories. The unranked private-cycle donor witnesses the
distinction; static sealing does not prevent downstream work during upstream
blocking.

Choose a rank-certified presentation, or a proved equivalent restriction.
Audit every retained generator: category units/associativity, wire laws,
assembly, inherited boundary squares and actual bracket comparison.
Prove closure and operational soundness before descending to a quotient.
Selecting ranked representatives of the old quotient is not sufficient without
proving the required well-definedness. Do not change the completed witness
presentation or make rank certificates into observable events. Explain how
alternative valid certificates for the same program affect the interpretation.

### D. Retain metadata without making administrative syntax observable work

`CompleteObservation.Agrees` retains whole ports, roles, Option-valued input,
explicit certified domain transports and adapter data, as well as full history.
Actual nested metadata stores the original `(ab, bc)` boundaries. Specify how
identity/wire insertion transports this data and proves neutrality, without
erasing original adapters or recording a spurious new computational footprint.
Preserve both raw-coordinate and admitted-coordinate coherence where applicable.

A nonidentity wire may have zero events but still change the certified interface
view. A vacuous core component may also have zero events but different metadata.
Neither is an identity merely because its event list is empty.

## 3. Design guidance, not a prescribed new framework

Prefer the smallest interpretation using the current histories and
identity/wire syntax. A candidate normal form separates wire-only terms from
terms with computational leaves: wire-only terms need no compiled core program;
nonempty computations reuse existing constructors and actual-run theorems.
This is a proposal to test, not a verified algorithm or mandatory module split.

The abstract history unit preserves its incoming state. A semantic target may
contain administrative arrows not realizable as standalone core programs;
that is not a reason to add a runner primitive or violate `output_defined`.
Success carries the required boundary values; failure must not demand an
unavailable successful output or execute later administrative/computational work.

Useful literature and existing tools:

- [Semicategories and free unital completion](https://ncatlab.org/nlab/show/semicategory):
  adjoining identities preserves already defined composition, once a genuine
  semicategory has been established. Freeness does not prove operational
  adequacy. Distinguish this from a free category on an underlying graph.
- [Mathlib path categories](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/PathCategory/Basic.html):
  zero-edge identities and shared endpoints fit the snapshot intuition.
  Keep terminal absorbing failure explicit; do not introduce a homotopy,
  stuttering or event-permutation quotient.
- [Atkey, Parameterised Notions of Computation](https://bentnib.org/paramnotions-jfp.html):
  parameterised state effects are a useful model for changing store scopes.
  An incoming-state-indexed history family can support return/bind; merely
  naming a monad/Kleisli category proves neither scope coherence nor adequacy.
  A full generic monad implementation is not a prerequisite for this slice.
- [Structured cospans](https://arxiv.org/abs/1911.04630) and
  [decorated cospans](https://arxiv.org/abs/1502.00872):
  possible later interface/private-structure packaging, not automatic closure,
  scheduling or failure theorems. An isomorphism quotient is acceptable only
  with the required observation preservation proved; it is not intrinsically
  forbidden. Do not add a double-category/equipment framework without a
  concrete obligation that the simpler interpretation cannot meet.

## 4. Required semantic obligations

The verified plan must give exact statements for:

1. Generic history left/right units, shared-snapshot normalization, failure
   absorption and compatibility with existing transports/splicing.
2. Event-free administrative identity/wire interpretation over whole interfaces,
   with inherited frame/ledger preservation, wire identity/composition/inverse
   laws, and explicit metadata/input/output transport.
3. A typed rank-restricted sequential presentation and operational soundness of
   every retained generating equation. Preserve nontrivial wires and supplied
   boundaries; no matching by names, equal extents or cardinality.
4. Composition congruence and category unit/associativity laws under the chosen
   full observation relation. If advertised as an operational functor, construct
   the actual functor and its source/target categories, not just fixture parity.
5. Conservative adequacy for existing leaves, binary assembly and actual
   reassociation: use actual default `IndexedOpenComposition.runChecked`,
   `Program.Executor.run` and `referenceSnapshots`, retaining the existing full
   `Relation`, pending occurrences and accumulators. Reuse constructed ranks
   and actual budget results. Administrative insertion must add no core work,
   fresh computational identities, fuel consumption or duplicate snapshots.

Do not assume execution agreement, model existence/uniqueness, successful
completion, identity transparency or source-equation soundness as premises of
the main result. Preserve private failure after visible output and the existing
undefined-event/no-extra-snapshot normalization. Keep malformed raw-input
validation and arbitrary debug-fuel equivalence outside the claim.

If these obligations cannot fit one sound bounded slice, surface the precise
dependency/scope problem before writing an execution plan. Do not silently
complete only abstract unit equations and call that an operational category.

## 5. Discriminating acceptance goals for plan authoring

These are donor/delta requirements, **not measured new fixtures**. The verified
plan supplies exact fixture/cycle counts, observed outputs and intended
diagnostics. Retain nearest legal neighbors and classify runtime observations
versus live-proof controls honestly.

| Goal | Existing donor and required distinction |
|---|---|
| Unit laws retain real work and failures | Clone history `Fixtures.first`, `second`, `privateFailure`; insert the proposed unit before/after. Retain every event/state/terminal payload and one shared snapshot; failure needs no downstream output. |
| Identity preserves a populated frame | Clone `Fixtures.ledgerLeft`, `ledgerRight`, `privateAvailable`; use a nonempty ordered prefix and distinguish reset, reversal and private-value erasure. Restrict frames explicitly if required. |
| Actual private phases remain exact | Use operational `privateComparison`, `privateRows`, `privateReferenceCuts` and total/strict consumer neighbors; insert administrative terms at exterior/interior joins, covering failure in each reached leaf. |
| Certified nonconstant wire transport | Use axis producer/consumer and `axisTailBoundary`; choose a nonidentity coordinate wire whose wrong map changes observations, then test composition and inverse with colliding local identities. |
| Empty metadata is not address enumeration | Use `Fixtures.emptyMetadata`, `MetadataLawFixtures.absentEmptyMetadata`, empty components and `emptyTailBoundary`; preserve explicit presence and coincident cuts with no invented work. |
| No event-free collapse | Compare identity with a nonidentity wire or vacuous component with different interfaces; zero events alone must not establish observation agreement. |
| Ranked restriction is necessary | Use `unrankedRun`/`hidden_no_rank` alongside the legal ranked donor; ensure the proposed presentation cannot silently assert the old unrestricted assembly equation as a sequential execution law. |
| Existing observation remains stronger than values | Retain `reorderedTripleRun`/`strongerThanFinalOutput`; equal final availability must not erase ledger/event/snapshot order. |

Controls should detect unit-as-copy, fresh-state reset, duplicate boundary
snapshot, wrong wire direction/composition, ignored empty presence, lost private
prefix, failure fall-through and unsound rank restriction. Do not count setup
refusal or a type mismatch as an intended runtime observation.

## 6. Targeted source map

All paths here are under
[`leanncd/experiments/indexed_execution/`](../../leanncd/experiments/indexed_execution/).
Use `rg -n`, then approximately 40-60-line windows around the identifiers.

| Identifiers @ file | Role |
|---|---|
| `History`, `History.bind`, `Continuation`, `History.splice`, `map_bind`, `success_cut`, `failure_absorbs` @ `IndexedOperationalHistory.lean` | Existing history algebra and shared-start constraint |
| `GraphMetadata`, `MetadataTransport.Agrees`, `GraphHistory.Admissible`, `toRun_injective`, `ranked_default_exists`, `CompleteObservation.Agrees`, `ReferenceObservation` @ `IndexedOperationalHistory.lean` | Retained data, actual-run bridge and limits of shape-only admission |
| `MetadataTransport.refl/symm/trans`, `CompleteObservation.agrees_refl/agrees_symm/agrees_trans` @ `IndexedOperationalObservationLaws.lean` | Concrete observation laws and empty metadata controls |
| `SharedSplice`, `upstreamState`, `downstreamState`, `liftUpstream`, `liftDownstream`, `BinaryHistory`, `compose_history`, `BinaryHistory.sound` @ `IndexedOperationalHistoryComposition.lean` | Full-state lifts and actual binary composition |
| `state_A/state_B/state_C`, `lift_A/lift_B/lift_C`, `binary_associativity`, `actual_nested_histories` @ `IndexedOperationalHistoryAssociativity.lean` | Structural common-scope reassociation, not assumed run equivalence |
| `graphTransport`, `metadataTransport`, `leftMetadata`, `rightMetadata`, `nested_metadata`, `nested_observations` @ `IndexedOperationalAssociativity.lean` | Native whole-interface and original boundary data |
| `nested_reference_runs`, `ranked_nested_reference_outcomes` @ `IndexedOperationalRuns.lean`; `triple_phases`, `reference_cuts`, `two_reached_empty_B` @ `IndexedOperationalRunsPhases.lean` | Actual reference outcomes, four branches and normalized cuts |
| `WholeInterface`, `inputEnv`, `envInput` @ `IndexedWitnessInterface.lean` | Existing metadata-bearing objects and validated input adapters |
| `Object`, `Wire`, `Wire.identity/comp/inverse/env` @ `IndexedSourceWire.lean` | Existing administrative syntax and certified interface maps |
| `Term`, `Rel`, `assembled`, `pair`, `leftNested`, `rightNested` @ `IndexedSourceSyntax.lean`; `Term.denote`, `sound`, `semantics` @ `IndexedSourceFunctor.lean` | Current unrestricted denotational presentation; audit retained generators |
| `MatchedComponent`, `Boundary` @ `IndexedComponentCompositionScope.lean`; `compose` @ `IndexedComponentComposition.lean`; `compositeRankCertificate` @ `IndexedComponentCompositionRanks.lean` | Existing sealed constructor and supplied rank/boundary evidence |
| `unrankedRun`, `hidden_no_rank` @ `IndexedComponentRankedExecutionFixtures.lean`; operational donors @ `IndexedOperationalAssociativityFixtures.lean` | Negative rank witness and concrete acceptance donors |

## 7. Process and release boundaries

The handoff session performed only a targeted read-only consistency audit before
writing this document: existing history/source constructors, source relation
generators, observation admission, original adapter retention and binary-history
premises were checked on local main. This did not verify a new representation,
unit theorem, source restriction, module split or fixture. Recheck latest local
main and its governing instructions at session start.

Use `slice-plan` and `new-slice`. Prepare an isolated worktree from latest local
main, verify warm Mathlib, and refresh project-owned oleans through the wrapper.
Prototype on the real module split, then use a fresh bounded context to author
one verified plan from the artifacts. Ship mechanically generated per-task
patches and mutation manifests with observed intended diagnostics. Keep the
live plan separate from its evidence record.

Use approximately three work items per dispatch; split before approximately
60 turns or 250k peak context. Authoring targets 50M cumulative input tokens;
execution caps at 175M. Use `token-report.py` and disclose unavailable telemetry
or overruns rather than treating missing transcripts as a budget pass.

Keep the implementation nondefault under `IndexedExecutionExperiment`, with a
discoverable entry point and matching Lean instructions. Controller release
gates: all unfiltered mutation cycles with restored builds/source hashes,
source and namespace axiom audits, full `LeanNCD Tests IndexedExecutionExperiment`
wrapper build, and two final whole-branch review lenses:

- semantic soundness of ranked source equations, scope/frame/metadata transports
  and the actual unit/category/functor claims;
- conservative runner/reference integration, strict failure, empty presence,
  shared snapshots, unchanged observations/budgets and discriminating controls.

Update synthesis status only for results actually proved. Preserve concurrent
edits; merge locally when green and reviewed, clean up only owned task
branches/worktrees, and do not push. Close-out states exactly what the
operational source/target arrows are, which equations are sound, what is
administrative versus core-executable, and what remains open.

**Excluded:** new core operators, runner/scheduler changes, general unranked or
malformed-input operational equivalence, arbitrary debug budgets, reordering or
stuttering quotients, forgotten private work, generic monoidal/PROP/open-network
or double-category frameworks, backend/numerical refinement, a full generic
parameterised-monad library, and re-proving the completed witness semantics.
