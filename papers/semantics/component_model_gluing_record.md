# Complete-model restriction and gluing record

[Handoff](component_model_gluing_handoff.md) |
[Interface design](categorical_tensor_logic_component_interfaces.md)

## Scope and preparation

- Process weight: Full; new rank-independent semantic theorem and soundness surface.
- Task worktree: `pyncd.worktrees/follow-directions-component-model`.
- Task branch: `agents/follow-directions-component-model`.
- Prepared from latest local main `2212263c`; initial task branch had no
  branch-only commits or dirty files and fast-forwarded from `16721af5`.
- `prepare-worktree.sh` verified 8,101 Mathlib oleans / 8,094 sources
  (100%), and 374 project oleans. The nondefault composition modules
  still require building; cache warmth does not establish their availability.
- Protected primary-checkout files, not slice deliverables:
  - `papers/semantics/README.md`, initial SHA-256
    `467f94f6890675822e3972fc72d8d79ebdf3f661d48cdb7f5449606f4f568f25`.
  - `papers/semantics/categorical_tensor_logic_semantics.md`, initial SHA-256
    `81478c0ac0c34fef33e487503a41387f7573c224d11dd25174fb0cee4c7fb994`.
- Other worktrees are outside the task.

## Accounting

`token-report.py 7c2f3b25-15ad-41dd-b8a2-2d3910ed051c` reports no supported
transcript. Cumulative-input-token compliance is therefore unmeasured,
not asserted. Prototype dispatches target 40 turns with a checkpoint
before 60 turns / 250k retained context.

## Current status

Authoring prototype in progress. No generic model theorem, fixture suite,
verified plan, completed execution, or release is claimed.

## Controller occurrence and collection prototype

`IndexedComponentModelTransport` is registered only in the nondefault
experiment. It proves `outcome_upstream`, `outcome_downstream`,
`admEnv_components`, `collect_upstream`, `collect_downstream`, and
`equations_components` for arbitrary complete composite stores.

- Body equality is the existing `interpret_transport` specialized through
  the existing source constructor.
- Defined tensors split into the existing upstream/downstream summands;
  every actual guard-admitted occurrence is retained.
- Each component's occurrence type at its embedded defined tensor is
  definitionally unchanged. `Finset.sum_congr` preserves its entire
  pushforward sum, rather than deduplicating equal contributions.
- Destination equality and `downstream_defined_address` preserve coordinates.
  All coordinate equations are included, including private and zero-writer
  tensors.
- Both `lake-build.sh ... IndexedComponentModelTransport` and the exact
  source-copy `check-snippet.sh` passed.
- `transport_audit.lean` passed: 231 composition constants use only standard
  axioms; both principal equivalences depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- An initial single-file attempt failed because the donor lacked nondefault
  composition oleans. Controller then built `IndexedExecutionExperiment`
  successfully (8,633 jobs), before checking new proofs.
- Equation-proof elaboration initially required canonical embedded subtype
  representatives and an explicit downstream address rewrite. Corrected
  proofs were rebuilt and rechecked; neither failure is mutation evidence.
- Baseline production refresh passed, replaying existing non-semantic
  `sorry` warnings. The new proof surface's namespace audit admits no `sorry`
  or native-decision axioms.

Operational phase/projection, rank stitching, runtime traces, categorical
associativity/identities, wider interfaces, and previous-slice coverage
repairs are excluded.
