# Task 6 — isolated copied witness observation probes

## Delivery

Prototype: `/Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype`.
Started clean at detached `2cbf39e9`; committed as `91721bc0`
(`test(semantics): isolate copied witness observation probes`) with the requested
Copilot coauthor trailer. Prototype status is clean. No push, merge, primary
checkout edits, existing semantics edits, or nested agents.

Only committed files:

- `leanncd/experiments/indexed_execution/IndexedWitnessObservationProbe.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessObservationProbeTest.lean`
- `leanncd/experiments/indexed_execution/IndexedWitnessObservationParity.lean`
- `leanncd/lakefile.toml`: only the existing nondefault
  `IndexedExecutionExperiment` globs.

Controller deliverables, intentionally uncommitted:

- `papers/semantics/categorical_witness_semantics_artifacts/probes.py`
- `papers/semantics/categorical_witness_semantics_mutations_post.json`
- This record.

## Workitem 1 — exact copies and independent parity

`IndexedWitnessObservationProbe` contains these production declarations with
only the declaration name changed:

| Authoritative module | Copied symbols |
|---|---|
| `IndexedWitnessInterface` | `roleInterfaceCopy`, `envInputCopy` |
| `IndexedWitnessSpan` | `componentSpanCopy` |
| `IndexedWitnessComposition` | `boundaryEnvEquivCopy`, `compositeInputEquivCopy`, `compositeOutputEquivCopy`, `toWiredCopy` |

Production references inside bodies remain production references. These are
seven independent body copies, not a second mutually rewritten implementation.
In particular, `toWiredCopy` reuses production `componentSpan`, `wiredSpan`,
`witnessesEquiv`, and `boundaryEnv_projection`. Its embedded compatibility and
complete-model proofs remain intact. Copied boundary/span computations are
observed directly; a mutated boundary is not threaded through `toWiredCopy`.

The source parser selects a named definition through the next top-level
declaration, retaining interior bytes and normalizing only trailing separator
whitespace. Checking compares the complete normalized declaration, not a
hand-reconstructed expression or selected fragments. Three complete production
source SHA-256 values are pinned in the script. The entire generated Probe
scaffold is also checked. `reverseEnvironment` is a separate test-only,
well-typed generic equivalence through `canonicalLayout.enumerate` and
`Fin.rev`, provided for the proposed coordinate controls.

`IndexedWitnessObservationParity` contains seven generic `rfl` theorems:
`roleInterface_parity`, `envInput_parity`, `componentSpan_parity`,
`boundaryEnvEquiv_parity`, `compositeInputEquiv_parity`,
`compositeOutputEquiv_parity`, and `toWired_parity`.
No standalone public laws are copied into Probe. Embedded construction proofs
are not removed or admitted. ProbeTest does not import or reference Parity.
The proposed copied-map cycles build only ProbeTest, never the whole experiment
library or Parity, so generic parity failures cannot stand in for observations.

## Workitem 2 — checked observations and donors

Names below are under `IndexedWitnessObservationProbeTest`.
Numeric propositions were checked with `decide +kernel`; numbers are
kernel-verified assertions, not fabricated evaluation output.

| Fixture symbols | Donor and observation |
|---|---|
| `Hidden.zeroWired`, `oneWired`, `cells`, `distinct`, `equal_output` | Copy decomposition of `IndexedWitnessCompositionTest.Hidden.zero/one`: wired private cells are respectively 0/1, copied downstream output cells are both 1, wired witnesses differ, whole outputs agree. |
| `Hidden.goodSpan`, `good_injective`, `good_option`, `good_option_cell` | A singleton restriction of the actual `oneWired` downstream complete model. Production `Span.partialOption` returns `some` of its output, and mapping the scalar observation returns `some 1`. This proves positive extraction, **not** injectivity of the unrestricted hidden component. |
| `Audit.strict_empty`, `total_cells`, `strict_none` | Strict all-input absence comes from `CompositionTest.Audit.strict_span_empty`; total neighbor retains private audit 1/2 and final output 0. Production partial extraction of the strict consumer is `none` via `IndexedWitnessPartialTest.strict_consumer_undefined`. Absence is donor/consumer theorem evidence, not a copied numeric mutation observation. |
| `Empty.outputCopy`, `metadata`, `present`, `singleton`, `metadata_distinct`, `empty_input_present` | `CompositionTest.Empty` output port remains present, UID 3, axes `[⟨51, 0⟩]`, and singleton environment independently. Whole metadata differs from empty producer metadata. `envInputCopy` of `emptyValidatedInput` preserves the present empty input as `Some`. |
| `Axis.boundary_cells`, `external_copy_cells` | Direct copied boundary gives 5/2, while donor flattened cells give 3/4 and reverse-direction cells give 4/3. Copied external output identification applied to copied composite projection gives 14. |
| `Triple.input_copy_cells`, `copied_boundaries`, `original_final` | `CompositionTest.Triple.aInput/aWitness/bWitness/cWitness`: copied input reconstruction observes 5/2, copied external input identification observes 5, copied boundaries observe 15/12 and 35/32, copied original input leg observes 5/2, copied final projection observes 134. |
| `Triple.leftStore`, `rightStore`, `private_stores`, `leftUid`, `rightUid`, `unequal_raw_ids` | Both donor bracketing private stores retain 15/35/134. Raw A-private IDs differ (164 versus 82); final IDs are 3 versus 7. These are donor/consumer bracketing checks, not independently copied coherence-law computations. |

The Axis producer has no external inputs: an initial attempted nonconstant input
observation there was rejected by Lean and replaced with the actual Triple
input fixture. An initially unavailable `Equiv.ofInvolutive` helper was replaced
with an explicit equivalence using `Fin.rev_rev`. No failed baseline code remains.

## Workitem 3 — controller-owned mutation proposals

The JSON follows the existing `mutation-manifest.sh` schema: ten entries,
unique labels, exact unique `old` strings, task `"6"`, and target
`IndexedWitnessObservationProbeTest`. There are **no `expect` strings**;
the controller must fill those only from actual diagnostic logs.

| Proposal | Evidence intended |
|---|---|
| Boundary coordinate reversal | Copied numeric boundary observations; equivalence remains valid. |
| Zero component output projection | Copied numeric outputs including positive `Some 1`; apex/model witnesses remain intact. |
| Shifted role-interface UID | Copied empty metadata observation; injection proof is retained via cancellation. |
| Zero present input functions | Copied Triple numeric input observations; empty binding remains `Some`. |
| Reverse external input coordinates | Copied Triple external input observation; equivalence remains valid. |
| Negate external output cells | Copied Axis output observation; involutive value equivalence remains valid. |
| Substitute hidden zero witness for one | Donor substitution; private numeric distinction, not a production defect. |
| Read total output instead of private audit | Donor locator substitution; numeric 1/2 audit check, not a production defect. |
| Substitute a zero right-bracket store | Donor store substitution; private numeric checks, not a production defect. |
| Substitute total for strict absence statement | Donor theorem mismatch, explicitly **not numeric** and not a copied-map defect. |

First six are authored as well-typed map changes rather than invalid
equivalence/model constructions. Their mutated elaboration and exact failures
have **not** been executed or verified here. The strict substitution is
intentionally theorem-level donor evidence. No production generic-law mutation
is claimed. `toWiredCopy` has baseline exact parity and donor numeric coverage,
but no independent mutation of its embedded proof-carrying decomposition.

`--emit-manifest` regenerates proposals; do not rerun it after the controller
has populated observed `expect` strings unless intentionally replacing those.
`--check` is a restored-baseline check and deliberately rejects mutated copies.

## Validation and commands

All paths below are absolute; no direct Lake invocation is needed.

Baseline target refresh succeeded:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd IndexedWitnessObservationParity IndexedWitnessObservationProbeTest
```

The copied Probe was built in the preceding targeted refresh and is a dependency
of both targets. Separate single-file ProbeTest checking through the wrapper also
passed. Axiom audits checked 15 Probe constants, seven Parity constants, and
42 ProbeTest constants against the standard whitelist. No `sorry`, `admit`,
`native_decide`, or new axioms were added.

Mechanical restored-baseline check:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_artifacts/probes.py --check
```

Add `--observe` to invoke the single-file `lean-file.sh` wrapper after checking;
it forwards actual Lean output (currently axiom audit counts), not invented
numeric printouts. `--prototype /absolute/checkout` selects another checkout.
`--emit` regenerates the pinned body copies.

Manifest schema/uniqueness validation succeeded:

```text
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-prototype/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-witness-semantics-setup/papers/semantics/categorical_witness_semantics_mutations_post.json
```

Observed result: `manifest OK: 10 entries, 10 selected, every old-string unique`.
No actual mutation-cycle or mutation-manifest builds ran. No full experiment,
default full build, or final whole-branch review ran in this bounded task; those
remain controller release gates. The project-local intermediate build log was
removed after its results were recorded here.

## Budget

The 40-action aim was exceeded: 60 leaf tool actions including this report write.
There were seven parallel batching envelopes; counting those as extra actions
gives 67 and breaches the hard 60-action cap under that interpretation. The
conversation-turn cap was not reached. No nested agents.

The prescribed token reporter was attempted with session
`de983171-486d-493b-8e86-068461660c5c`; it returned
`no transcript for session de983171-486d-493b-8e86-068461660c5c`.
Measured peak/cumulative tokens are therefore unavailable; no invented token
total or unmeasured quantitative compliance claim is supplied.
