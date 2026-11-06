# Component transport: execution record

[Plan](component_transport_plan.md) |
[Design](categorical_tensor_logic_component_interfaces.md)

## Scope and preflight

Execute only the typed transport slice: certified declaration/read adapters,
context-aware expressions, ordered footprints and strict partial evaluation.
Composite matches, ranked phase execution and model gluing remain unimplemented.

- Isolated branch: `worktree-component-transport`.
- Execution base: `b68f56c4`, latest local main at preparation.
- The newer main changes reference/checked scan-read rejection, not this
  slice's source APIs, experiment registration or instruction patch surfaces.
- All three exported patches applied in order to a temporary index against
  this execution base without conflicts.
- The authoring package was copied, leaving its original files untouched.
- `prepare-worktree.sh --base main` passed: 8,101 built Mathlib oleans for
  8,094 sources, plus project build output. No cold Mathlib build.
- Instruction `Patterns`/`Global Pitfalls` measured 2,984 characters;
  no instruction trimming was needed.
- The primary checkout's existing synthesis and contents edits are outside
  this slice and must remain unchanged.
- Project-owned `LeanNCD` refresh passed through the build wrapper
  (8,615 jobs).

## Task checkpoints

### Task 1: certified domains, reads and stores

Static review of the exported patch found no required change. The supplied
axis/raw certificates constrain adapters explicitly; policy conjugation uses
the raw inverse; admitted constants retain their value; address injection
uses tensor injection and dependent coordinate equality. Store restriction
preserves absent cells rather than filling zero.

`IndexedComponentTransport` built successfully (2,960 jobs).
Committed as `d835d55c`; no task-review findings.

### Task 2: expression transport

`IndexedComponentTransportEval` built successfully (2,962 jobs). Review covered all eight
constructors and their matching interpretation/footprint branches: tensor
reads and predicates precompose context; reduction/tabulation extend context
without changing their bound coordinates; selection evaluates its whole
array; primitive symbols, argument order, local shapes and layouts remain
unchanged. The proofs quantify over every partial store and result type,
without a reached-state or successful-output premise.

Ordered footprint transport, evaluation/readiness transport and observational
identity/composition were checked together. No required change or nonstandard
axiom was reported by the task build.

| Case | Required and checked | Forbidden | Intentionally ignored |
| --- | --- | --- | --- |
| Literal | Same rational | New store access | Context, because literal is constant |
| Read | Inject tensor; transport policy/raw/resolved read; precompose context | Name matching or absence-to-zero | None |
| Iverson | Precompose predicate | Drop context map | None |
| Binary | Preserve both operands and ordered repeated reads | Reorder or deduplicate | None |
| Reduction | Preserve bound and extend context by binder identity | Replace bound coordinate | None |
| Tabulation | Preserve shape/layout and full strict array | Change local array domain | None |
| Selection | Precompose index and retain full array evaluation | Select-first bypass | None |
| Primitive | Same registry/type and ordered arguments | Drop undefined arguments | None |
| Addressed outcome | Map coordinate | Wrong tensor domain | None |
| Constant outcome | Same rational and empty footprint | Make missing or zero | Coordinate map, because no coordinate exists |
| Rejection | Preserve rejection; no admitted rejected read | Silently admit | Coordinate map, because no coordinate exists |

Committed as `41305ae5`; no task-review findings.

### Task 3: observations and discovery

Applied the final observation/integration patch without source changes.
`IndexedComponentTransportTest` and `IndexedComponentTransportProbe` built
successfully (8,592 jobs). The source fixture module has 21 checks; the generated probe
repeats those consumers and adds one six-donor parity check under both
present and missing stores.

Review checked nonconstant values and unequal-axis transport, the ordered
repetition observation, context-sensitive binders/indices, constant and
rejected policies, all three readiness outcomes, empty reductions/arrays,
and unused target tensors. The arbitrary-raw policy identity/composition
theorems were included. Namespace-wide audits cover the transport, fixture
and probe namespaces, not merely selected theorem leaves.

Directly related discovery/design documentation now distinguishes implemented
transport from still-proposed component composition.

The generated probe reproduced the patch-applied bytes exactly;
[execution hashes](component_transport_artifacts/execution-probe-hashes.json)
record its input/source bytes. Both unfiltered manifest checks passed with
all 5 and 7 anchors unique.

Namespace audits passed for 97 transport, 82 primary-fixture and 90 probe
constants, using only `propext`, `Classical.choice`, and `Quot.sound`.
The documentation value sweep found only unrelated historical records and
explicitly historical prototype evidence; no stale current transport count
needed repair.

The controller ran both manifests without filters:
[observer/donor results](component_transport_artifacts/execution-observer-results.md)
passed 5/5 and
[copied-computation/donor results](component_transport_artifacts/execution-copied-results.md)
passed 7/7. Every cycle reached its named failure, restored the source
byte-identically, and rebuilt green. These are the declared copied/observer/
donor controls, not live-production mutation kills or per-fixture-complete
coverage.

Task 3 is ready to commit after its direct review; final whole-branch
reviews and integrated build remain pending.

## Release validation and whole-branch review

Pending. Authoring receipts are not substituted for execution checks.

## Accounting and integration

The repository token-report tool returned no SDK session transcript, so
cumulative input tokens cannot be measured and numerical budget compliance
is not asserted. Integration is pending; no remote push is authorized.
