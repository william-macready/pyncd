# Source-category functor: authoring (a) prototype record

This is the audit/compiled-prototype dispatch, **not the live execution plan**.
Authoring (b) must use the preserved artifacts, freeze the live plan and obtain
its reviews before reconstruction/execution. Nothing was committed, reverted,
merged, pushed or removed. Only this isolated worktree was used.

## State and boundaries

Base: `19c9d644` (the full hash is recorded by `package.json`).
Worktree: `/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update`.
Full process: a new typed source presentation and functor soundness surface.
The supplied prepared/warm-cache state was accepted; no primary checkout or
other worktree was touched. The primary's unrelated semantics README is outside
this dispatch.

Tracked edit: `leanncd/lakefile.toml`, adding eight nondefault experiment modules.
New compiled modules: `IndexedSourceWire`, `IndexedSourceSyntax`,
`IndexedSourceFunctor`, `IndexedSourceSemantics`, `IndexedSourceTest`,
`IndexedSourceObservationProbe`, `IndexedSourceObservationProbeTest`,
`IndexedSourceObservationParity`, all under
`leanncd/experiments/indexed_execution/`.
New records/package/manifest use the `papers/semantics/categorical_source_functor`
prefix. Logs are preserved even where gitignored.

No core semantics, runners, registry, production imports or target-category
declarations changed. `IndexedSourceSemantics` is the public nondefault entry.
There is no new rank, phase, backend, runtime identity, free-category library,
automatic match or output-only leaf construction.

## Verified design and audit

| Decision | Checked identifier @ file |
|---|---|
| Distinct source objects retaining entire `WholeInterface`, including empty-port metadata | `Object` @ `IndexedSourceWire.lean` |
| Contravariant explicit port bijection (also the explicit UID renaming), certified coordinate-axis/raw adapters; no carrier-only wire constructor | `Wire` @ `IndexedSourceWire.lean` |
| Domain inversion including extent, raw-axis and coordinate/raw coherence | `Domain.inverse` @ `IndexedSourceWire.lean` |
| Inverse proof eliminates the dependent port equality explicitly, rather than unsafe casts | `Wire.inverseAt`, `Wire.inverseAt_cancel`, `Wire.env_inverse` @ `IndexedSourceWire.lean` |
| Identity and composite environment maps follow coordinate identity and composition | `Wire.env_identity`, `Wire.env_comp` @ `IndexedSourceWire.lean` |
| Exact induced upstream-to-composite input, boundary and composite-to-downstream output maps | `inputWire_env`, `boundaryWire_env`, `outputWire_env` @ `IndexedSourceWire.lean` |
| Typed identities, certified wires, matched leaves with supplied local matches and typed composition | `Term` @ `IndexedSourceSyntax.lean` |
| Inductively generated equivalence/congruence, not denotation equality | `Rel`, `termSetoid` @ `IndexedSourceSyntax.lean` |
| Every generator interpreted soundly | `sound` @ `IndexedSourceFunctor.lean` |
| Quotient `Category.{1}` on the distinct wrapper, actual Mathlib functor | `Hom`, category instance, `semantics` @ `IndexedSourceFunctor.lean` |
| Leaf maps directly to existing all-input complete-store `componentSpan` | `Term.denote` @ `IndexedSourceFunctor.lean` |
| Real composite constructor and exact exterior transports in source assembly | `assembled`, `pair` @ `IndexedSourceSyntax.lean`; `assembly_eq`, `source_assembly` @ `IndexedSourceFunctor.lean` |
| Both real nested bracketings equal one source triple | `left_eq_triple`, `right_eq_triple` @ `IndexedSourceFunctor.lean` |

`Rel` generators are reflexivity, symmetry, transitivity, typed composition
congruence, both units, associativity, wire identity/composition/both inverse
equations, actual binary assembly, both inherited boundary squares, and actual
nested bracket comparison. The last three schemas quantify only actual matched
components/boundaries; there is **no arbitrary environment-equality equation**.
The nested generator is redundant with the derived source triple comparisons;
it deliberately exposes the existing `bracket_hom` comparison as an explicit
source schema and checks its soundness separately.

Assembly soundness calls existing `composition_hom`, preserving its two
exterior legs. Boundary-square soundness calls `left_boundary_square` and
`right_boundary_square`. Nested soundness transports actual graph composites
to the existing rebased spans via `SpanIso.rebaseGraphs`, then calls
`bracket_hom`; it does not assert raw program, declaration or UID equality.
The derived source triple comparisons use source assembly, the generated
boundary squares, wire composition and source associativity.

Port rosters are retained in objects but their arbitrary enumeration order is
not made a wire constraint: the explicit bijection indexes all complete ports.
Sorts are `Unit`, hence all cells have the fixed rational carrier; the wire
changes coordinates/ports only, never rational values. Requiring equal UIDs
would prohibit the deliberately explicit composite tagging transports.

The pinned Mathlib `Functor` requires `obj`, `map`, `map_id`, `map_comp`;
the prototype implements those fields directly. Source objects/homs and target
objects/homs are `Type 1`; environments remain `Type 0`. Constructor-local
declaration/typeclass binders are essential: section-wide binders would turn
`Rel` into a parameterized relation whose unused declarations cannot infer.
No same-universe local smallness, finite rational stores or faithfulness claim.

## Fixture donors, deltas and observed baseline values

All values below are checked kernel observations, not inferred from geometry.
The direct fixtures import the real interpreter; independent map observations
use the three byte-identical computational copies with separate generic parity.
No ProbeTest imports the parity module.

| Family | Exact donor and delta | Observations |
|---|---|---|
| Axis coordinates/inverse | `IndexedWitnessCompositionTest.Axis.sourceEnv`, `wrongReversed`; apply the new certified boundary wire and its inverse | Boundary cells at `p,q`: `5,2`; wrong reversed `q`: `3`; inverse roundtrip selected cells: `5,2` |
| Actual assembly/exterior legs | Axis `witness`, `both_legs`; form source `assembled` and `pair`, prove both source and mapped equality, use exact new exterior wires | Output cell `14`; input inverse equals the actual rebased left leg (a generic equality, not credited as a nonconstant input oracle) |
| Independent nonconstant exterior input | Triple `A`, `aWitness`; new input wire from A to actual AB | Composite tagged input cells: `5,2` |
| Independent exterior output | Triple `leftWitness`; actual left-bracket output wire | Final output cell: `134` |
| Empty metadata/presence | `Empty.metadata_not_equal`, `IndexedWitnessTest.emptyInputEnv`; wrap objects and inspect reconstructed whole input presence | Wrapped interfaces unequal; presence cell `true`, despite empty coordinate carrier |
| Hidden complete stores | `hidden_witnesses_distinct`, `hidden_outputs_equal`, `hiddenOne`; retain original full-witness apex and inspect private store | Distinct witnesses/equal outputs; hidden second private cell `1` |
| Actual nested triple/private identities | `Triple.bracket_applied`, `returned_private_stores`, `bracket_private_identities`; use new source nested terms and common source triple, inspect selected original stores | Selected private cells `15,35,134`; upstream private UID `164` on left vs `82` on right |
| Strict undefinedness/totality | `IndexedWitnessPartialTest.strict_no_domain`, `total_domain`; alias exact scalar profiles `0`/`4` | Negated domain at strict profile and positive domain at total profile, checked as propositions; no finite-model numeric proxy |

Generic category instances test both source units/associativity and functor
identity/composition laws. Wire inverse equations and actual source assembly
are instantiated in Axis. The actual three-component fixture instantiates
both source triple derivations and interpreted bracket soundness, while the
donor's actual witness bracket/private-store theorems remain compiled.

## Mutation evidence and honest limits

`categorical_source_functor_mutations_post.json` has **10 cycles**:

- M1–M3 change only a copied map's rational-value identity into `addRight 1`:
  respectively boundary, nonconstant exterior input and exterior output.
- M4 composes copied inverse transport with existing coordinate reversal.
- M5 substitutes hidden witness zero for witness one.
- M6 substitutes the actual right nested UID observation for the left one.
- M7 substitutes absent input for the reconstructed presence observation.
- M8/M9 swap strict and total theorem donors in both directions.
- M10 substitutes the tagged composite object for the original empty object.

The exact old/new strings, donor selection and target are in the manifest.
`observed_controls.json` records actual failure text and failed fixture names.
Expectations were copied mechanically from the first real cycle log, not
guessed. The initial run's table has no expectations and is only break/restore
evidence. The final populated-manifest run/table is the intended diagnostic
gate; see `mutations_verified.md` and `mutations_verified.log`.

M1–M7 fail kernel `decide` fixture checks (M1 also breaks inverse observations).
M8/M9 produce `Type mismatch`; M10 produces `Application type mismatch`.
Those last three are **theorem-level donor controls**, not numeric values or
production-map defect mutations. Failed theorem elaboration also triggers the
axiom audit on Lean's internal error placeholder; no such placeholder exists
in the green baseline. No mutation of target category or production code was
performed. No independent mutation of proof-carrying model gluing, nested
witness bijections or the generated source recursor is claimed.

The existing manifest wrapper SHA256-checks restoration after every cycle and
reruns the restored target. `TMPDIR` was explicitly set to the package
directory, so wrapper scratch files remain inside this worktree.
The exact-copy audit checks bodies against `Wire.env`; generic parity proves
all three copies equal and the inverse copy equal to actual inverse transport.

## Reviewer-rejectable task/patch boundaries and risk

| Task | At most three work items | Dependency | Fixtures / mutation cycles |
|---|---|---|---|
| 1 | Certified geometry, inversion/coherence, exact assembly transports | none | Generic wire/transport proofs; 0 numeric cycles; compile snippet directly before later wiring |
| 2 | Typed syntax/generated congruence, quotient category/functor, actual binary/nested source assembly | 1 | Every source schema soundness; binary and two nested derivations; 0 numeric cycles |
| 3 | Axis/exterior wire observations, complete/empty/strict witness-boundary observations, actual nested/private observations and isolated parity controls | 1,2 | 5 donor families, 10 cycles, 4 universal parities; high fixture risk, split production fixture commit from controls if dispatch nears 60 turns |

The binary/nested source equations live with the functor soundness proof, not
with fixtures: a reviewer can reject geometry, presentation/soundness or
observational coverage independently. Task 2 adds only public-module build
wiring; task 3 extends wiring to tests/probes. `package.json` records every
source hash, final build-wiring hash, patch hash and base identity.
`task1.patch`, `task2.patch`, `task3.patch` were mechanically generated from
the real files that compiled. `replay.json` records ordered application into a
fresh alternate index based on HEAD and byte equality to all compiled modules
and final lakefile. The real index/worktree was not modified by replay.
An initial missing new-file patch header was repaired and the ordered replay
was rerun successfully; the failed replay is not credited as a pass.

## Exact commands and persistent validation

All commands below use the same absolute worktree and wrappers. The package
script internally expands the eight recorded `check-snippet.sh` commands;
`snippets.json` preserves exact argument arrays and exit codes, and each
`*.snippet.log` preserves the actual compiler output.

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --snippets
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --audit
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --replay-check
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/universe_check.lean
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd LeanNCD Tests IndexedExecutionExperiment
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
/usr/bin/env TMPDIR=/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/mutations_verified.md /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/token-report.py 37386608-c5a8-4c82-a88b-0d50cc6e834c
```

Observed pre-final full build: **8919 jobs, exit 0**.
Final post-cycle full build: **8919 jobs, exit 0**. Final populated unfiltered
manifest: **10/10**, all expected diagnostics seen, every restored file
byte-identical and every restored build green. Unfiltered `--check`: all ten
old strings unique. Eight final module snippets and the separate universe/API
snippet passed. Ordered replay and post-cycle source/copy audit passed.
Logs and `verification_receipt.json` preserve these gates and artifact hashes.
The harness rejected two environment-prefixed `--check` attempts; the plain
wrapper check succeeded (it needs no scratch environment). The universe/API
snippet's noncomputable example was repaired and rechecked before recording
its pass.

Baseline audits observed: `IndexedSource` 130 constants;
`IndexedSourceTest` 14; `IndexedSourceObservationProbe` 4;
`IndexedSourceObservationParity` 4; `IndexedSourceObservationProbeTest` 27.
All use only standard axioms. Printed production results use
`propext`, `Classical.choice`, `Quot.sound` (Domain inverse uses
`propext`, `Quot.sound`). No sorry/admit/new axioms/unsafe proof shortcuts.

## Still required / accounting

No load-bearing design blocker found. Later dispatch (b) must write and review
the live plan from these artifacts, decide the optional fixture/control
subdispatch boundary, and run artifact validation after any edits.
No integration/release claim is made: controller execution, per-task reviews,
both whole-branch lenses, documentation/synthesis updates, final controller
unfiltered mutations/full build and local integration remain outstanding.
The new entry is build-reachable but existing AGENTS/synthesis prose is
deliberately not changed by authoring (a).

The dispatch exceeded the **55-turn aim** during dependent inverse-cast,
constructor-local universe/instance and reassociation compiler iterations.
Token measurement returned `no transcript for session` for the Copilot session
ID. Exact cumulative tokens/context peak are unavailable and not fabricated.
No nested delegation occurred. The implementation author must not inherit
this long context; use fresh authoring (b) and bounded execution contexts.
