# Certified source category and witness-semantics functor

**Process: Full — a new typed presentation, category and functor soundness surface.**
This is the single live implementation plan. The [record](categorical_source_functor_record.md)
holds authoring verification, execution accounting and review findings; the
[prototype record](categorical_source_functor_prototype_record.md) remains historical evidence,
not a second live plan. The [handoff](categorical_source_functor_handoff.md) is the goal brief.

## 1. Frozen scope and acceptance boundary

Implement the exact compiled, real-split prototype preserved in
`papers/semantics/categorical_source_functor_artifacts/`, in three sequential tasks.
Do not redesign or transcribe its Lean. Base:
`19c9d6446552c4f4c507c89be94c3561a94ec5ea`; branch:
`agents/categorical-source-functor-update`; worktree:
`/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update`.
This worktree already has the eight uncommitted new modules and the final
`leanncd/lakefile.toml` experiment-wiring delta. Reconstruction is a controller
step after plan review and artifact verification, not an authoring action.

The result is denotational, for finite decidable `Declarations Unit`, the fixed
exact-rational registry, supplied local `MatchedComponent` matches and explicit
whole-tensor boundaries. Source objects and homs are `Type 1`; environments are
`Type 0`; the source and target use `Category.{1}`. There is no claim of finite
rational model sets, same-universe local smallness, faithfulness, completeness
of source equality, or executable model extraction.

**Excluded:** core Program semantics or constructors; runners, registry and
production imports; target-category/model-gluing rewrites; automatic matching;
output-only leaves; existence/uniqueness/rank/execution-success filters on leaves;
rank stitching; phase/state/trace projection; event-sensitive process identities;
backend or floating-point refinement; broader interfaces; St/Br, PROP, monoidal
or free-category frameworks; unrelated coverage/accounting repairs.
Do not alter `.claude/settings.json`, any unrelated worktree, or the primary's
dirty `papers/semantics/README.md`. The same README in this worktree is not a
required edit. No push.

### Accepted design, not proposed alternatives

| Obligation | Frozen implementation and proof boundary |
|---|---|
| Source objects | `Object` wraps the entire `WholeInterface`; the source category instance is on the wrapper, not a competing instance on the target. |
| Administrative geometry | `Wire` has contravariant explicit port bijection and a certified `Domain` for each port. `Domain.inverse` retains axis/extent/raw/coherence certificates. An arbitrary environment equivalence is not a wire constructor. |
| Wire meaning | `Wire.env` reindexes ports/coordinates and preserves rational values. Identity, composition and inverse environment equations are proved. |
| Exact assembly maps | `inputWire_env`, `boundaryWire_env`, `outputWire_env` identify the actual exterior input, boundary and exterior output equivalences, respectively. No convenient identity substitution. |
| Syntax | `Term` has typed identity, wire, actual matched-component leaf and sequential composition constructors. |
| Arrow equality | Inductive `Rel`, not equality of denotations: equivalence closure, composition congruence, both units, associativity, wire identity/composition/both inverse equations, actual binary assembly, both inherited boundary squares, actual nested bracket comparison. Constructor-local declaration/typeclass binders are retained. |
| Interpretation | `Term.denote` maps identities to target identities, wires to `graphHom`, leaves to the unchanged all-input `componentSpan`, and sequential composition to target composition. `sound` handles every `Rel` constructor. |
| Category/functor | `Hom` is the quotient by `termSetoid`; well-defined `homComp` and category laws descend via source generators. `semantics` is an actual Mathlib functor with object map `Object.interface`, quotient-lifted map, `map_id`, `map_comp`. |
| Actual binary assembly | `assembled` uses the actual `compose` leaf with exterior wires; `pair` uses the original leaves and boundary wire. `source_assembly` equates their arrows. Its interpretation uses `composition_hom`, including both exterior legs. |
| Actual nested assembly | `leftNested` and `rightNested` use actual bracketed constructor leaves and inherited transports. `left_eq_triple` and `right_eq_triple` derive equality to the common `triple` using assembly, boundary squares, wire composition and source associativity, not the bracket generator. |
| Nested schema soundness | Separately, the `Rel.bracket` case of `sound` uses `SpanIso.rebaseGraphs` and `bracket_hom`. The generator is redundant with the derived comparisons; it is an explicit actual-constructor schema, not an arbitrary environment-equality rule. |
| Discovery | Nondefault entry `import IndexedSourceSemantics` imports `IndexedSourceFunctor`; task 2 wires it into `IndexedExecutionExperiment`, task 3 wires tests/probes. No production `import LeanNCD` extension. |

In ordinary right-to-left composition, the source assembly equation is
wire(o) ∘ leaf(compose A B b) ∘ wire(i) = leaf(B) ∘ wire(b) ∘ leaf(A).
Lean's sequential notation orders these as i, composite leaf, o on the left
and A, b, B on the right. Actual nested equality does not identify raw UIDs,
declarations, or programs.

### Case × constraint audit and acceptance deltas

This adds a presentation rather than fixing a recurring rejection predicate.
The audited siblings are the three assembly maps, both inverse equations,
both boundary-square schemas and both actual nested terms; none may be replaced
by a single carrier-only comparison.

| Case/class | Required | Forbidden | Deliberately not constrained / not claimed |
|---|---|---|---|
| Whole-interface objects, including empty ports | Retain UID/sort/domain/roster metadata; distinct wrapped donor interfaces remain distinct | Quotient objects by equal/singleton environment carriers | A port roster's enumeration order is not an additional wire constraint |
| Explicit wires | Supplied bijection of all complete ports and certified coordinate/raw transport | Infer adapters from names, equal extents or arbitrary value-changing environment bijections | Equal UIDs are not required: explicit port pairing is UID renaming; sorts are `Unit` |
| Complete-model leaves | Every validated input and complete private store; strict body-definedness unchanged | Collapse hidden stores by output equality; require a model or unique model to admit a leaf | No executor/cycle solver or model-independent verification |
| Strict/total neighbour | Strict scalar profile `0` has no domain witness; total profile `4` has one at the donor input | Fabricated zero outputs for undefinedness | No new rejection policy or finite numeric count of models |
| Actual assembly/nesting | Exact three maps, both squares and rebased actual bracket comparisons | Literal fresh-UID/program equality; free leaf composition disconnected from `compose` | No event/state/phase or raw syntax associativity |

## 2. Frozen artifacts and reconstruction gate

`package.json` inventories all eight source SHA256s, three patch SHA256s, three
exact computational-copy body hashes and final lakefile hash. The prototype
receipt inventories fourteen artifact identities. Both were checked during
authoring (b); identities and commands are in the separate record.

| Task patch | SHA256 |
|---|---|
| `task1.patch` | `a089ffe7b6753cce0be4b7c812e792650d4b8a01f5e92a62a3e6554c3fba6c03` |
| `task2.patch` | `cd9bdc1196bacab0d21bfd901389b4069e4239be3c77fa1271bc3a43d2377fad` |
| `task3.patch` | `a81bdf2b10ac7fb4a784bd8face150a8b9518e7fe223c64f058e23063861d671` |

Before reconstruction, inspect the preserved scripts and run separately:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update rev-parse HEAD
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff -- leanncd/lakefile.toml
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --audit
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --replay-check
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
```

Require the frozen HEAD, all eight sources matching `package.json`, only the
exact four-line source-module addition in the tracked lakefile diff, unchanged
patches/receipt identities, ordered replay equality and ten unique old strings.
The source addition occupies four added lines, replacing the prior list terminator;
the final diff has five added lines including that retained witness terminator.
The replay uses a separate index, applies all three patches to the recorded
base in order and compares the resulting eight modules and lakefile to compiled
hashes; it neither resets the real index nor reconstructs the actual worktree.

**Only after these gates and plan findings are adjudicated:** the controller
uses `apply_patch` to delete exactly the eight new source files listed in the
three tasks and reverse only the exact source-module lakefile hunk, leaving
the witness-module list and every other byte unchanged. Preserve the package,
manifest, plan, both records, logs and all unrelated files/index changes.
Do not use checkout, restore, reset, clean, reverse-apply over a broad diff,
or delete the whole experiment directory. Do not run `package.py` without an
explicit safe flag: its default exports/rewrites artifacts. Do not use
`--propose`, `--freeze-expectations` or `--receipt` to recreate history.

After surgical deletion, confirm only these source paths disappeared and the
lakefile equals its base version. The existing package/replay evidence still
identifies the preserved bytes, but `--audit` is intentionally not applicable
while sources are absent or only partly reconstructed. Apply the actual task
patches below in order, with each check/review/commit completed before the next.
If any identity, old string, patch applicability or design assertion fails,
STOP and report; do not expand scope or fix prototype code.

## 3. Common execution/review brief

Copy this preamble verbatim into every execution and review brief:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Read approximately 40–60-line windows around the listed identifiers; no whole
large-module reads or target/source rediscovery. The frozen facts above and
donor matrix below are the brief. All tasks run sequentially without asking.
Warm-cache/project refresh discipline comes from `new-slice`; this worktree is
already prepared, so do not create another worktree or overwrite its cache.
The designated Patterns and Global Pitfalls sections of `leanncd/AGENTS.md`
total 2,951 characters before this slice: no instruction-trimming task is needed.

Each task checkpoint: persist exact patch applied, file hashes/footprint,
validation exits, review findings/adjudication, commit ID, remaining work and
usage headroom in the record. Use a bounded per-task diff review; a finding that
invalidates later tasks stops execution. Do not silently amend frozen code.
Reviewers persist incremental findings in their record subsection (the controller
serializes writes if reviewers overlap), not only in a final chat response.

| Task | Reviewer-rejectable work items | Prerequisites | Fixture/cycle risk |
|---|---|---|---|
| 1 | Certified geometry; inverse/coherence; exact three assembly transports | reconstruction gate | Generic wire/transport proofs; 0 numeric cycles; low fixture risk |
| 2 | Typed presentation; quotient category/actual functor; actual binary/nested comparisons and public wiring | 1 checked, reviewed, committed | Every schema soundness, binary and two nested derivations; 0 numeric cycles; proof risk |
| 3 | Axis/exterior observations; empty/hidden/strict complete-witness observations; actual nested/private observations with isolated controls/parities | 1 and 2 checked, reviewed, committed | 5 donor families, 10 cycles, 4 universal parities; high fixture risk |

Task 3 remains one task and one exact patch. If its execution approaches
60 turns or 250k peak context, use
`.claude/skills/slice-plan/split-handoff-template.md`: apply
the entire patch, check and commit fixtures/wiring first, then a fresh bounded
continuation runs probes/parities and all controls, recording its verification
commit. Do not manufacture an unverified fourth patch or rederive mutations.
The continuation's symbols/files are the task 3 list below.
Each dispatch aims below 60 turns/250k peak; authoring target about 50M cumulative
input tokens, execution cap 175M. Attempt token-report at checkpoints/close-out;
disclose unavailable measurements and breaches, never substitute output tokens.

## 4. Task 1 — certified geometry and exact transports

**Files:** `leanncd/experiments/indexed_execution/IndexedSourceWire.lean` only.
Touch no existing transport or witness module. `Domain.inverse` is added in its
existing namespace by the new module, not by editing the original Domain file.

**Identifiers @ files:**

- `Domain.inverse`, `Object`, `Wire`, `Wire.identity`, `Wire.comp`, `Wire.inverseAt`,
  `Wire.inverseAt_cancel`, `Wire.inverse`, `Wire.env`, `Wire.env_apply`,
  `Wire.env_identity`, `Wire.env_comp`, `Wire.env_inverse`, `input`, `output`,
  `inputWire`, `boundaryWire`, `outputWire`, `inputWire_env`, `boundaryWire_env`,
  `outputWire_env` @ `leanncd/experiments/indexed_execution/IndexedSourceWire.lean`.

Apply, then directly compile the new module (task 1 has no Lake-list change):

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task1.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task1.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/experiments/indexed_execution/IndexedSourceWire.lean
```

Review geometry direction, inverse dependent-equality elimination, rational-value
identity and equality to the actual three environment transports. Require the
task 1 file hash from `package.json`. After clean/adjudicated review:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add leanncd/experiments/indexed_execution/IndexedSourceWire.lean papers/semantics/categorical_source_functor_record.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update commit -m "feat(semantics): add certified source wires" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 5. Task 2 — source presentation, category and actual functor

**Files:** `leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean`,
`leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean`,
`leanncd/experiments/indexed_execution/IndexedSourceSemantics.lean`,
and the task 2 hunk of `leanncd/lakefile.toml`.

**Identifiers @ files:**

- `Term`, `Rel`, `termSetoid`, `assembled`, `pair`, `triple`, `leftNested`,
  `rightNested` @ `leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean`.
- `Term.denote`, `sound`, `Hom`, `homId`, `homComp`, category instance,
  `semantics`, `arrow`, `assembly_eq`, `wire_comp_eq`, `arrow_seq`,
  `source_assembly`, `source_assembly_assoc`, `left_eq_triple`, `right_eq_triple`
  @ `leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean`.
- Import `IndexedSourceFunctor` @ `leanncd/experiments/indexed_execution/IndexedSourceSemantics.lean`.
- `IndexedExecutionExperiment` @ `leanncd/lakefile.toml`.

The frozen dependency calls to audit in the patch are `componentSpan`
@ `leanncd/experiments/indexed_execution/IndexedWitnessSpan.lean`,
`graphHom_identity`, `graphHom_comp`, `composition_hom`
@ `leanncd/experiments/indexed_execution/IndexedWitnessComposition.lean`
and `left_boundary_square`, `right_boundary_square`, `bracket_hom`
@ `leanncd/experiments/indexed_execution/IndexedWitnessCoherence.lean`.
Do not reimplement these dependencies.

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task2.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task2.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd IndexedSourceWire IndexedSourceSyntax IndexedSourceFunctor IndexedSourceSemantics
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/universe_check.lean
```

Review every relation generator's interpretation, quotient congruence/category
laws, actual Mathlib functor fields, all-input leaf map, assembly proof's exterior
legs, both derived triple proofs and the separate bracket-schema proof.
Verify task 2 source hashes and exact intermediate lakefile hunk. After review:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add leanncd/experiments/indexed_execution/IndexedSourceSyntax.lean leanncd/experiments/indexed_execution/IndexedSourceFunctor.lean leanncd/experiments/indexed_execution/IndexedSourceSemantics.lean leanncd/lakefile.toml papers/semantics/categorical_source_functor_record.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update commit -m "feat(semantics): present matched sources and their witness functor" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 6. Task 3 — discriminating fixtures, isolated probes and controls

**Files:** `leanncd/experiments/indexed_execution/IndexedSourceTest.lean`,
`leanncd/experiments/indexed_execution/IndexedSourceObservationProbe.lean`,
`leanncd/experiments/indexed_execution/IndexedSourceObservationProbeTest.lean`,
`leanncd/experiments/indexed_execution/IndexedSourceObservationParity.lean`,
task 3 hunk of `leanncd/lakefile.toml`, and the existing
`papers/semantics/categorical_source_functor_mutations_post.json` (run unchanged).

**Identifiers @ files:**

- Category/functor examples, `Axis.coordinate_cells`, `Axis.inverse_cells`,
  `Axis.reversed_control`, `Axis.exterior_cells`, `Empty.metadata`,
  `Empty.input_present`, Triple assembly/bracket instances, `Triple.private_cells`,
  `Hidden.complete_not_output_only`, strict/total leaf instances and
  `#audit_axioms` @ `leanncd/experiments/indexed_execution/IndexedSourceTest.lean`.
- `boundaryCopy`, `inputCopy`, `outputCopy`, `inverseCopy`
  @ `leanncd/experiments/indexed_execution/IndexedSourceObservationProbe.lean`.
- `Axis.boundary_cells`, `Axis.inverse_cells`, `Triple.input_cells`,
  `Triple.output_cells`, `Triple.privateId`, `Triple.private_identity`,
  `Hidden.second`, `Hidden.hidden_cell`, `Empty.presence`, `Empty.presenceCell`,
  `Empty.presence_cell`, `Strict.profile`, `Strict.undefined`, `Strict.totalProfile`,
  `Strict.defined`, `Metadata.original`, `Metadata.distinct`, `#audit_axioms`
  @ `leanncd/experiments/indexed_execution/IndexedSourceObservationProbeTest.lean`.
- `boundary`, `input`, `output`, `inverse`, `#audit_axioms`
  @ `leanncd/experiments/indexed_execution/IndexedSourceObservationParity.lean`.

### Five donor families; exact deltas and measured distinctions

| Family | Donor identifier @ file; clone/change | Baseline observations and purpose |
|---|---|---|
| Axis / binary exterior | `Axis.sourceEnv`, `Axis.wrongReversed`, `Axis.witness`, `Axis.both_legs` @ `leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean`; apply new certified wire/inverse, construct source assembled/pair and interpret them | Boundary p/q `5,2`; wrong reversed q `3`; inverse selected cells `5,2`; binary output `14`. The input-inverse comparison is a generic rebased-left-leg equality, NOT a nonconstant numeric input oracle. Generic source units/assoc, wire inverse and functor laws are also instantiated. |
| Empty / metadata | `Empty.metadata_not_equal` @ `leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean`; wrap both actual interfaces. `emptyInputEnv` @ `leanncd/experiments/indexed_execution/IndexedWitnessTest.lean`; inspect reconstructed whole input presence | Wrapped objects unequal even for empty coordinate carriers; input presence cell `true`. Empty carrier equivalence must not erase metadata or presence. |
| Hidden / full stores | `hidden_witnesses_distinct`, `hidden_outputs_equal`, `hiddenOne` @ `leanncd/experiments/indexed_execution/IndexedWitnessTest.lean`; retain full witness leaf and inspect its second private donor | Distinct witnesses/equal whole outputs; selected second private cell `1`. No output-only collapse. |
| Triple / actual nesting | `Triple.A`, `Triple.aWitness`, `Triple.leftWitness`, `Triple.bracket_applied`, `Triple.returned_private_stores`, `Triple.bracket_private_identities` @ `leanncd/experiments/indexed_execution/IndexedWitnessCompositionTest.lean`; construct both new nested terms/common triple, use actual exterior input/output wires and original stores | Independent nonconstant exterior input tagged cells `5,2`; final exterior output `134`; selected private cells `15,35,134`; upstream nested UID `164` left versus `82` right. Both source triple derivations and mapped actual bracket comparison compile. |
| Strict / total | `strict_no_domain`, `total_domain` @ `leanncd/experiments/indexed_execution/IndexedWitnessPartialTest.lean`; alias exact scalar profiles `0` and `4`, respectively | Negated/positive domain propositions at the supplied donor input. No finite-model numeric proxy; no new core semantics. |

Three computational map bodies are byte-identical to `Wire.env`; `inverseCopy`
uses the copied boundary inverse. Four universal parities connect these copies
to actual maps. ProbeTest does not import parity, so changed copies can fail
observations without parity causing the failure first. These are isolated
map observations, not independent complete-model semantics.

### Observed mutation expectations (run the manifest, never hand-write cycles)

All target `IndexedSourceObservationProbeTest`; M1–M4 alter
`IndexedSourceObservationProbe.lean`, M5–M10 alter
`IndexedSourceObservationProbeTest.lean`. Paths in the manifest are relative
to `leanncd/`. The second expected string is the fully qualified fixture:

| Cycle | Frozen delta | Exact diagnostic expectation | Fixture suffix under `IndexedSourceObservationProbeTest.` |
|---|---|---|---|
| M1 | `boundaryCopy`: rational `Equiv.refl` → `Equiv.addRight 1` | ``Tactic `decide` failed for proposition`` | `Axis.boundary_cells` |
| M2 | `inputCopy`: same value-changing delta | ``Tactic `decide` failed for proposition`` | `Triple.input_cells` |
| M3 | `outputCopy`: same value-changing delta | ``Tactic `decide` failed for proposition`` | `Triple.output_cells` |
| M4 | Copied inverse composed with existing `reverseEnvironment` | ``Tactic `decide` failed for proposition`` | `Axis.inverse_cells` |
| M5 | `hiddenOne` → `hiddenZero` donor | ``Tactic `decide` proved that the proposition`` | `Hidden.hidden_cell` |
| M6 | Actual right-bracket private UID donor replaces left donor | ``Tactic `decide` proved that the proposition`` | `Triple.private_identity` |
| M7 | Reconstructed input presence → absent input donor | ``Tactic `decide` proved that the proposition`` | `Empty.presence_cell` |
| M8 | Strict profile `0` → total profile `4` theorem donor | `Type mismatch` | `Strict.undefined` |
| M9 | Total profile `4` → strict profile `0` theorem donor | `Type mismatch` | `Strict.defined` |
| M10 | Original empty object → tagged composite object donor | `Application type mismatch: The argument` | `Metadata.distinct` |

The literal diagnostics, including backticks, are authoritative in
`observed_controls.json` and manifest `expect` arrays. M1–M7 are kernel `decide`
observation controls on test-only computational copies/donors. M8–M10 are
theorem-level donor substitutions, NOT numeric controls or mutations of generic
proofs, model gluing, target laws, source recursor or nested witness bijections.
Failed theorem elaboration also triggers audits on Lean's error placeholders;
the green baseline contains none. Frozen populated unfiltered evidence is
10/10 expected failures, byte-identical restores and restored builds green.

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task3.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update apply /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/task3.patch
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd IndexedSourceTest IndexedSourceObservationProbe IndexedSourceObservationProbeTest IndexedSourceObservationParity
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --audit
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
/usr/bin/env TMPDIR=/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/mutations_execution.md /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
```

Run controls serially with no concurrent build/source editing. `TMPDIR` is an
explicit literal inside the package, never a system temporary directory. The
new `mutations_execution.md` is an execution result, not a replacement for
historical `mutations_verified.md`. Review discriminating donors, nonconstant
input oracle, metadata/strict acceptance neighbours, copy fidelity/parity
separation, expected failures and complete restoration. After adjudication:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add leanncd/experiments/indexed_execution/IndexedSourceTest.lean leanncd/experiments/indexed_execution/IndexedSourceObservationProbe.lean leanncd/experiments/indexed_execution/IndexedSourceObservationProbeTest.lean leanncd/experiments/indexed_execution/IndexedSourceObservationParity.lean leanncd/lakefile.toml papers/semantics/categorical_source_functor_mutations_post.json papers/semantics/categorical_source_functor_record.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update commit -m "test(semantics): pin source transports and witness boundaries" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## 7. Controller documentation sweep — direct, no extra implementation task

After task 3, edit only directly stale current claims. Required files:
`papers/semantics/categorical_tensor_logic_semantics.md` and `leanncd/AGENTS.md`.
Required synthesis sections: 6.10, 10.2, 10.3, A.9; also the current introductory
witness summary, evidence/perspective rows and 6.6's source-law gap.
The authoring grep found current stale claims there and in the Lean entry.
Historical witness plans/records/reviews and handoffs remain scoped provenance,
not alternative live plans; do not rewrite their completed-slice claims.

```text
rg -n 'source functor|source category|source-category|source identities/functor|Source category, source functor|not a source|source units' /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/AGENTS.md -g '*.md'
rg -n '130|14 constants|27 constants|10/10|ten.*control|four.*parit|source identities/functor laws.*remain|Source category, source functor and process units' /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update -g '*.md' -g '*.json'
```

Document the distinct source wrapper, certified wire direction, generated source
equations and soundness, quotient category, actual functor, binary constructor
equation and both actual nested triple derivations with explicit transports.
Split the mixed ledger row: source category/functor proved for this specified
presentation; core/process units remain open. In A.9 add the source presentation
and functor step without removing the target proof or injective-left boundary.
Add `import IndexedSourceSemantics` to the Lean entry-point text, with test-only
probe/parity separation and no production import claim. Preserve strict
undefinedness, hidden multiplicity and empty metadata acceptance deltas above.
Report 5 families/10 controls/4 parities with the numeric-versus-theorem limits.
Do not relabel historical witness counts as new source counts or silently combine
the two manifests. Identify remaining rank/process/backend obligations only.
No inline Lean blocks; if one is introduced or reformatted, compile its exact
post-edit form with `check-snippet.sh` before shipping.

Stage these two docs and the record explicitly; commit after prose/value/path
checks. Preserve the frozen package and prototype record, including necessary
ignored logs, with explicit paths (never a directory-wide add):

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add papers/semantics/categorical_tensor_logic_semantics.md leanncd/AGENTS.md papers/semantics/categorical_source_functor_plan.md papers/semantics/categorical_source_functor_record.md papers/semantics/categorical_source_functor_prototype_record.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add papers/semantics/categorical_source_functor_artifacts/package.py papers/semantics/categorical_source_functor_artifacts/package.json papers/semantics/categorical_source_functor_artifacts/verification_receipt.json papers/semantics/categorical_source_functor_artifacts/task1.patch papers/semantics/categorical_source_functor_artifacts/task2.patch papers/semantics/categorical_source_functor_artifacts/task3.patch papers/semantics/categorical_source_functor_artifacts/snippets.json papers/semantics/categorical_source_functor_artifacts/replay.json papers/semantics/categorical_source_functor_artifacts/observed_controls.json papers/semantics/categorical_source_functor_artifacts/mutations_verified.md papers/semantics/categorical_source_functor_artifacts/universe_check.lean
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update add -f papers/semantics/categorical_source_functor_full_build.log papers/semantics/categorical_source_functor_artifacts/mutations_initial.log papers/semantics/categorical_source_functor_artifacts/mutations_verified.log papers/semantics/categorical_source_functor_artifacts/universe_check.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceWire.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceSyntax.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceFunctor.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceSemantics.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceTest.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceObservationProbe.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceObservationProbeTest.snippet.log papers/semantics/categorical_source_functor_artifacts/IndexedSourceObservationParity.snippet.log
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff --cached --stat
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update commit -m "docs(semantics): record the certified source functor boundary" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Check the entire staged inventory before every commit; if unrelated paths
were already staged, preserve them without committing them with this slice.
Never stage `.claude/settings.json`. Later stage the two new execution/release
mutation result tables explicitly when they exist; retain necessary fresh
release logs/receipts by individual path, and record their observed identities.

## 8. Controller release gates and task-only integration

The controller, not an agent's report, must run these after all task/docs edits:

```text
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --audit
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --replay-check
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/package.py --snippets
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/universe_check.lean
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
/usr/bin/env TMPDIR=/Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts/mutations_release.md /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_mutations_post.json
rg -n '\b(sorry|admit|axiom|unsafe)\b' /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/experiments/indexed_execution -g 'IndexedSource*.lean'
bash /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/leanncd LeanNCD Tests IndexedExecutionExperiment
rg -n 'axiom audit:|depends on axioms|uses #' /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/papers/semantics/categorical_source_functor_artifacts -g '*.snippet.log'
python3 /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update/.claude/skills/slice-plan/token-report.py 37386608-c5a8-4c82-a88b-0d50cc6e834c
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff --check
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update diff 19c9d6446552c4f4c507c89be94c3561a94ec5ea --stat
```

No matches from the source proof-shortcut grep is expected (rg exit 1 is success
for this negative audit). Require standard-axiom namespace audits:
`IndexedSource` 130, `IndexedSourceTest` 14, `IndexedSourceObservationProbe` 4,
`IndexedSourceObservationProbeTest` 27, `IndexedSourceObservationParity` 4
for unchanged compiled bytes. `Domain.inverse` uses `propext`, `Quot.sound`;
printed source proofs/functor use only `propext`, `Classical.choice`, `Quot.sound`.
Inspect the fresh snippet/full-build audit output, not just copied counts.
Unfiltered manifest execution must again show 10/10 expected failures and
identical restores; `--check` alone is not release evidence.
Preserve fresh release results separately from prototype evidence; the
historical full build was 8,919 jobs/exit 0, not a promised future job count.
Record current controller/subagent session IDs for actual token accounting:
the literal historical session command cannot account for later sessions.

Obtain **two fresh independent whole-branch review lenses** after all changes:

1. Source/functor soundness: exact wire geometry and universes; no
   denotation-defined equality or unsound schema; every generator sound;
   complete-model leaf scope; actual binary/nested constructor connections.
2. Integration/observation: final module/import/wiring reachability; unchanged
   production/target/core scope; discriminating donors and parity isolation;
   honest control limits; docs/acceptance boundaries; artifact fidelity and
   unrelated-dirty-file preservation.

Both review the entire branch against the frozen base, not only their task
diffs. Persist incremental findings in the record's separate lens subsections.
Adjudicate every finding; a load-bearing unfixable or frozen-design contradiction
stops integration. Fix groups get separate bounded contexts, not a broad
redesign. After any change, repeat affected checks and the full controller
release gates. No review or integration pass is claimed by authoring (b).

Only after green full build, actual unfiltered cycles and clean/adjudicated
whole-branch reviews, the controller integrates locally. Main's worktree path
was obtained read-only from this worktree's git metadata; its HEAD had advanced
beyond the frozen base during authoring. Do not assume fast-forward equality.
Inspect/preserve primary dirty state at integration time. If its unrelated
README would be touched by the merge, stop rather than stash/reset/overwrite it.
Resolve only task-related committed integration conflicts, then rebuild/review
the integrated result if resolution changes code or claims. Do not delete this
branch/worktree while gates or integration remain unresolved.

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd status --short
/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff agents/categorical-source-functor-update -m "Merge certified source-category witness functor" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
/usr/bin/git -C /Users/williammacready/code/python/pyncd diff --stat main agents/categorical-source-functor-update
```

With advanced main, the last diff may include legitimate main-only changes;
it is not required to be empty. Require source branch ancestry in main and
verify its task deliverables survived instead:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd merge-base --is-ancestor agents/categorical-source-functor-update main
/usr/bin/git -C /Users/williammacready/code/python/pyncd status --short
```

Commit/persist all requested artifacts and release results before cleanup.
Inventory remaining untracked files; remove only identified slice scratch,
never broad clean/reset or another worktree. The controller leaves this
worktree session before removal. Once clean and integration verified:

```text
/usr/bin/git -C /Users/williammacready/code/python/pyncd worktree remove /Users/williammacready/code/python/pyncd.worktrees/categorical-source-functor-update
/usr/bin/git -C /Users/williammacready/code/python/pyncd branch -d agents/categorical-source-functor-update
```

No force-removal of unknown files, no remote push. Close-out records proved
maps/equations, assumptions and remaining process/backend gaps; every check,
finding, commit, integration result and measured or unavailable budget.
