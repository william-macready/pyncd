# Component transport: execution plan

**Full path:** new typed transport capability with a semantic soundness surface; three dependent, mechanically exported patch units.

Authoring verification passed at the recorded baseline: exact patch replay,
both mutation manifests and the combined default/experiment build. See the
[authoring record](component_transport_authoring_record.md) for receipts and
coverage limitations. This does not execute or land the implementation.

Execution is now complete; the [execution record](component_transport_execution_record.md)
contains actual task commits, controller checks and final review adjudication.
The task instructions and their future-path labels below retain the original
rollout/replay context.

## 1. Authority, inputs and release boundary

Authority: [component-interface design](categorical_tensor_logic_component_interfaces.md), sections 1–2 (local declarations and explicit adapters), 7 (observation levels), and 9 (discriminating examples). This is only the first **transport** slice, not component composition.

Execution inputs, already exported in this directory:
- [01-domain-read.patch](component_transport_patches/01-domain-read.patch)
- [02-expression-laws.patch](component_transport_patches/02-expression-laws.patch)
- [03-observations-integration.patch](component_transport_patches/03-observations-integration.patch)
- [observer/donor manifest](component_transport_mutations_post.json), [copied-computation/donor manifest](component_transport_probe_mutations_post.json)
- [generator](component_transport_artifacts/generate-probe.py), [prototype evidence](component_transport_artifacts/prototype-evidence.json), and the [authoring record](component_transport_authoring_record.md).

The evidence JSON's `followup` supersedes its original snapshot: **21 production fixture checks, one additional probe-parity check, 12 mutation cycles**. Historical four-module/spikes references are not final architecture. Five modules live in the existing nondefault `IndexedExecutionExperiment`; no new library or tracked-spike exception.

### Exact constraints and success criteria

1. Fixed `Declarations Unit`, `RationalReference.Carrier`, `RationalReference.registry` and operations; exact rational scalars. Keep `Ty`, primitive symbols, local `ArrayShape` and `Layout` unchanged.
2. `Domain` carries an explicit axis-position equivalence, extent preservation, `Coord` and `RawCoord` equivalences, `raw_axis`, and the `Coord.raw` commuting certificate. These are **supplied certified adapters**, not automatically synthesized adapters. No arbitrary reshape, slice, or cardinality-based match.
3. `Embedding` supplies an injective tensor map and one `Domain` per tensor. Prove address injection, partial/complete store pulls, identity and composition. Neither names nor coincident numeric UIDs establish a connection.
4. Conjugate policies through the inverse raw adapter and map outcomes: `.at` maps coordinates, `.const` retains its rational, `.reject` stays rejected. Transport raw and resolved read data plus admission. `Domain.policy_id` and `Domain.policy_comp` quantify over **arbitrary raw arguments**, not just in-bounds/admitted reads.
5. `transport f h` precomposes arbitrary context map `h`; extend it by identity on the bound coordinate under `reduce` and `tab`. Include `iverson` predicates and `at` indices. Cover all eight `Expr` constructors.
6. Universally prove exact **ordered, repeated** footprint mapping, `evalWith` and `evalReady` preservation for **all partial stores**, and complete-store `interpret` preservation. Absence is not zero; distinguish `.notReady`, `.evaluated none`, and `.evaluated (some value)`.
7. Identity/composition are observational laws for evaluation and ordered footprints, not equality of typed expression records or a process identity. Readiness identity/composition follow by the transport theorem and footprint/store laws; no separate named ready-id/ready-comp API is promised.
8. Retain strict whole-array evaluation and footprints before selection, zero-length reduction behavior, empty local-array behavior, and unused target tensors.
9. Ship no `sorry`, new axiom, or `native_decide`; audit namespaces, allowing only standard `propext`, `Classical.choice`, `Quot.sound`.
10. Release requires targeted builds, 21 checks plus parity, both complete manifests, controller full default and experiment builds, and two adjudicated whole-branch review lenses.

**Excluded:** `SourceContractMatch` composition; scope checker; role/interface metadata construction; fresh UID allocator/disjoint namespaces; rank stitching; phase theorem; whole-model restriction/gluing; runner equivalence; category library; production API imports. These remain later **unplanned milestones**, not promises of this slice. No event-exact copy identity or whole-model/runner claim follows from local expression transport.

## 2. Execution environment and dependency risk

Each implementer/reviewer brief opens with this shell-harness preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Read identifiers below with `rg -n` and roughly 40–60-line Read windows; never whole large files. No rediscovery/prototyping or transcription of Lean: apply the exact patches. This plan has **zero Lean code blocks**.

| Task | Depends on | Risk / rejectable boundary | Fixtures | Cycles |
|---|---|---|---:|---:|
| 1: domains/reads/stores | none | Dependent coordinate evidence, conjugation and address injection; independently rejectable API | 0 | 0 |
| 2: expressions/laws | 1 | Binder extension, strict arrays, list order and arbitrary partial-store quantification; one structural-proof review cycle | 0 | 0 |
| 3: observations/integration | 2 | 21 consumers, generated proof-free probe, policy laws and nondefault discovery form one release gate | 21 + 1 parity | 12 |

Tasks 1–2 have generic compiled proofs, not computational fixture coverage. Task 3 consolidates the exact verified observational package rather than introducing 21 new design decisions. Pay for **mid-tier per-task reviews**, reserving two distinct final review lenses for the whole branch.

### Preflight: controller, before Task 1

- Invoke `new-slice`; create/enter an isolated **latest local-main** worktree, then run `prepare-worktree.sh`. Never branch from the prototype commit or merge the prototype. Confirm compatible local-main source; stop on substantive patch conflicts.
- Commands below use the **FUTURE** execution checkout `/Users/williammacready/code/python/pyncd.worktrees/component-transport`. If unavailable, choose another isolated path and replace this prefix literally throughout commands before dispatch. It does not exist by assertion in this authoring checkout.
- Have the shell/tool cwd set to that future worktree before preparation; do not construct a compound `cd` command. The preparation script discovers cwd.
- Preserve and copy this plan, design, record, patches, manifests, and generator into matching relative locations there. They are currently untracked authoring inputs: do not assume a worktree operation copied them or discard the originals.
- Run preparation without `--plan`: that option copies from the primary checkout, where this uncommitted authoring package need not exist. The package is already copied by the preceding step. Create the execution ledger separately in the controller's session tracking.
- Check `.lake` preparation success (at least 95% Mathlib cache); stop a cold Mathlib build. Refresh project oleans via `LeanNCD`.
- Check governing instruction hooks before editing. The authoring measurement of `Patterns` plus `Global Pitfalls` was 2,953 characters; remeasure actual injected sections, trim only if above approximately 3k, and record any necessary change.
- Create execution receipts under existing `papers/semantics/component_transport_artifacts/`; never use temporary directories. Do not overwrite the historical authoring receipts.

```bash
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/.claude/skills/new-slice/prepare-worktree.sh --base main
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd LeanNCD
```

Budget: execution total ≤175M cumulative input tokens; each dispatch target ~40 turns, hard ~60 turns and ~250k context. Report breaches. If adaptation threatens that cap, stop at a describable checkpoint and use [split-handoff-template.md](../../.claude/skills/slice-plan/split-handoff-template.md): commit validated production first, then fixtures/cycles. Do not silently expand this slice.

## 3. Task 1 — certified domains, reads and store restriction

**Files**
- **FUTURE, supplied by patch 1:** `leanncd/experiments/indexed_execution/IndexedComponentTransport.lean`.
- Existing modified file: `leanncd/lakefile.toml`.

**Symbols / immediate source context**
- `Domain`, `Domain.id`, `Domain.comp`, `Domain.policy`, `Domain.read`, `mapOutcome`, `mapResolved`, `outcome_map` @ `leanncd/experiments/indexed_execution/IndexedComponentTransport.lean` (**FUTURE**).
- `Embedding`, `Embedding.address`, `Embedding.address_injective`, `Embedding.pull`, `Embedding.pullComplete`, `Embedding.id`, `Embedding.comp`, `Embedding.address_id`, `Embedding.address_comp`, `Embedding.pull_comp` @ the same **FUTURE** file.
- `AdmittedRead`, `ReadPolicy`, `ReadOutcome`, `Resolved`, `Coord.raw` @ `leanncd/LeanNCD/Semantics/Types.lean`.
- `RationalReference.registry`, `RationalReference.ops` @ `leanncd/LeanNCD/Semantics/RationalReference.lean`.
- `IndexedExecutionExperiment` @ `leanncd/lakefile.toml`.

Apply and build:
```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply --check /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/01-domain-read.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/01-domain-read.patch
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd IndexedComponentTransport
```

Mid-tier review: check the certificates constrain the supplied adapters, inverse raw conjugation proves in-bounds behavior, resolved constants remain constant, tensor/address injection uses dependent equality correctly, and pulls preserve missing values. Do not require automatic synthesis. Record findings incrementally in an execution receipt and adjudicate before committing.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport add leanncd/experiments/indexed_execution/IndexedComponentTransport.lean leanncd/lakefile.toml
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport commit -m "feat(semantics): add certified domain and read transport" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Checkpoint: API built/reviewed; 0 fixtures and 0 cycles here. Task 2 remains.

## 4. Task 2 — structural expression transport and observation laws

**Files**
- **FUTURE, supplied by patch 2:** `leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean`; `leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean`.
- Existing modified file: `leanncd/lakefile.toml`.

**Symbols / immediate callers**
- `transport`, `footprint_transport` @ `leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean` (**FUTURE**).
- `evalWith_transport`, `checkReads_map`, `evalReady_transport`, `interpret_transport`, `evalWith_id`, `evalWith_comp`, `footprint_id`, `footprint_comp` @ `leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean` (**FUTURE**).
- `Expr` @ `leanncd/LeanNCD/Semantics/Expr.lean`; `footprint`, `evalWith`, `interpret` @ `leanncd/LeanNCD/Semantics/Interpret.lean`; `checkReads`, `evalReady` @ `leanncd/LeanNCD/Semantics/Readiness.lean`.
- Task 1's `Domain.read`, `Embedding.pull` and address laws are the shared utilities; Task 3's consumers are the next callers.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply --check /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/02-expression-laws.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/02-expression-laws.patch
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd IndexedComponentTransportEval
```

Mid-tier review: check all rows of §5, no restriction to reached stores, ordered `List.map` rather than sets, both binder extensions, unchanged registry/result types/local layouts, and strict `at`. `evalWith_transport`/`footprint_transport` are universal theorems, **not** mutation-sensitive computational assertions. Inspect axiom output; never count a proof-elaboration failure as an observed fixture kill.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport add leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean leanncd/experiments/indexed_execution/IndexedComponentTransportEval.lean leanncd/lakefile.toml
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport commit -m "feat(semantics): prove expression transport observations" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Checkpoint: generic laws built/reviewed; 0 fixtures and 0 cycles here. Task 3 remains.

## 5. Required sibling audit: constructor × outcome classes

This table is a Task 2 review input and Task 3 audit deliverable. Check siblings even when their code is unchanged; preserve it in the execution receipt with any adjudication.

| Case | Required | Forbidden | Silently ignored |
|---|---|---|---|
| `Expr.lit` | Same rational | Tensor/context access | Context map: literal is constant |
| `Expr.read` | Tensor injection; raw/resolved/policy adapters; context precomposition | Name/extent-inferred identity; absence-to-zero | None |
| `Expr.iverson` | Predicate precomposition | Retaining free predicate without `h` | None |
| `Expr.binary` | Both operands, left/right footprint order and repeats | Reordering/deduplication | None |
| `Expr.reduce` | Preserve length/enumeration; extend `h` by identity on `Fin` binder | Replacing bound index; skipping empty identity | None |
| `Expr.tab` | Preserve shape/layout; extend `h` by identity on `Coord`; strict full array | Applying tensor-domain adapter to local shape | None |
| `Expr.at` | Precompose index; evaluate/footprint whole array | Select-first shortcut | None |
| `Expr.prim` | Same primitive, registry, type; all arguments in original order | Ignoring undefined arguments; registry renaming | None |
| `ReadOutcome.at` | Map coordinate | Wrong tensor domain | None |
| `ReadOutcome.const` | Same rational; empty footprint | Ordinary read, missing value, or zero substitution | Coordinate map: no coordinate exists |
| `ReadOutcome.reject` | Preserve rejection; impossible admitted rejected read | Silently admitting rejection | Coordinate map: no coordinate exists |

Only genuinely irrelevant contexts and coordinate maps in constant/reject cases are intentionally ignored. Audit `mapResolved`, `Domain.policy`, `Domain.read`, `transport`, `footprint`, `evalWith`, and `evalReady` together, not just the changed recursive branches.

## 6. Task 3 — observations, proof-free probe and discovery

**Files**
- **FUTURE, supplied by patch 3:** `leanncd/experiments/indexed_execution/IndexedComponentTransportTest.lean`; `leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean`.
- Modified after Tasks 1–2: `leanncd/experiments/indexed_execution/IndexedComponentTransport.lean`, `leanncd/lakefile.toml`, `leanncd/AGENTS.md`.
- Existing authoring inputs to preserve/persist: this plan, authoring record, design, three patches, two manifests, and `component_transport_artifacts/` files listed in §1. Explicitly stage only intended source artifacts, never scratch logs wholesale.
- Documentation amendment: `papers/semantics/categorical_tensor_logic_component_interfaces.md`, sections 2 and 7 only as needed to link the implemented transport surface and distinguish still-proposed composition.

**Symbols**
- `Domain.policy_id`, `Domain.policy_comp` @ `leanncd/experiments/indexed_execution/IndexedComponentTransport.lean`.
- `swapDomain`, `embed`, `pointPolicy`, `constantRead`, `repeated`, `store`, `precompose`, `contextExpr`, `strictArray`, `selected`, `binder`, `zeroReduction`, `indexedArray`, `dynamicIndex`, `emptyTab`, `back`, `rejected_not_admitted` @ `leanncd/experiments/indexed_execution/IndexedComponentTransportTest.lean` (**FUTURE**).
- `probeTransport`, `probeOutcome`, `probeResolve` @ `leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean` (**FUTURE**).
- `audit_axioms` command implementation @ `leanncd/test/Semantics/AxiomAudit.lean`.

```bash
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply --check /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/03-observations-integration.patch
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport apply /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_patches/03-observations-integration.patch
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd IndexedComponentTransportTest IndexedComponentTransportProbe
```

### Fixture donors, exact deltas and OBSERVED values

Donor locators (all existing except the explicitly future local fixture names):
- D1: `LeanNCD.Semantics.Fixtures.direct`, `nested`, `nestedSwapped` @ `leanncd/test/Semantics/ExpressionTest.lean`.
- D2: `LeanNCD.Semantics.Fixtures.strictPolicy`, `constantPolicy`, `constRead` @ that same file.
- D3: `LeanNCD.Semantics.Fixtures.tabulated`, `selected`, `nonselectedUndefined` @ that same file; its reduction/empty donors include `emptyReduction`, `emptyTab`.
- D4: `matrixContext`, `renamedContext`, `zeroContext`, `emptyContext` @ `leanncd/test/Semantics/SourceBindingBoundaryTest.lean`.
- D5: `IndexedCompositionParityTest.strictArray`, `auditBody` @ `leanncd/experiments/indexed_execution/IndexedCompositionParityTest.lean`.
- D6: `evalReady` @ `leanncd/LeanNCD/Semantics/Readiness.lean`; this is an observation API, not a named prior fixture. Combine it with D1's read donor.

Clone/adapt the donors **as already encoded in patch 3**, not by rebuilding them. All fixture labels below have prefix `transport.`. Shared setup uses unequal shapes **2×3 → 3×2**, explicit renamed axis UIDs, source `Fin 2` into target `Fin 3`, a **nonconstant** address-dependent store, and a second cyclic tensor embedding `back`.

| Label | Donor → delta | OBSERVED assertion/value | Sensitivity |
|---|---|---|---|
| `ordered-repetition` | D1 → reads `(0,p),(1,q),(0,p)`, then swap/embed | `[(1,2,0),(2,0,1),(1,2,0)]`; printed evaluation `some 53` | CT1, CT2 |
| `axis-raw` | D4 → explicit unequal-axis swap, raw `(-4,9)` | Raw `(9,-4)`; coordinate `(0,2)` becomes `(2,0)` | No dedicated mutant |
| `boundary-constant` | D2 → conjugated out-of-bounds raw with source first coordinate `-1` | `.const 7` | CP4, CP5 |
| `admitted-constant` | D2 `constRead` → admitted constant, missing store | `.evaluated (some 7)`, footprint `[]` | No dedicated consumer mutant |
| `boundary-reject` | D2 `strictPolicy` → raw `(-2,-2)` | `.reject`; `rejected_not_admitted` proves impossibility | No dedicated consumer mutant |
| `context-precompose` | D1 plus `iverson` → `Unit → Fin 2`, value `1`, predicate/read both context-dependent | `some 18` | CT3, CP1 |
| `strict-selection-failure` | D5 → selected strict reciprocal array, `other=0` | `.evaluated none`, not not-ready | CT5 |
| `strict-selection-success` | Prior failure donor → only `other=4` | `.evaluated (some (1/2))` | No dedicated mutant |
| `strict-full-array` | D5 / prior success → observe full array under missing store | Both entries: `1/2`, `1/4` | CP2 |
| `readiness-missing` | D6 + `repeated` → all addresses absent | `.notReady` | No dedicated mutant |
| `readiness-success` | Prior missing donor → nonconstant available store | `.evaluated (some 53)` | CT4 |
| `reduce-binder` | D3 reduction pattern + D1 read → binder controls first coordinate | `some 33` | CP3 |
| `zero-reduction` | D3 `emptyReduction` → zero-length reduction of literal `99`, missing store | `.evaluated (some 0)` | CP6 |
| `tab-at-context` | D3 `tabulated`/`selected` → tab binder supplies coordinate, outer context supplies index | `some 17` | CT3 |
| `identity` | `ordered-repetition` → identity transport, pulled store | `some 53` | No dedicated mutant |
| `empty-tab` | D3 `emptyTab` + D4 zero extent → transported empty tab with read body, missing store | Evaluated `some` empty array, footprint `[]` | CP7 |
| `empty-scalar-metadata` | D4 `zeroContext`/`emptyContext` → zero-extent axis versus no axes | Layout counts `0` versus `1`, unequal shapes | CP7 |
| `unused-target` | `ordered-repetition` → target tensor `0` absent, image tensors available | `some 53` | No dedicated mutant |
| `composition` | `ordered-repetition` → compose swap/embed with cyclic `back` | Equal **ordered address projections** nested/composed | No dedicated mutant |
| `identity-context-observations` | `context-precompose` → identity embedding with nonidentity context, pulled store | Footprint `[(0,1,2)]`, `.evaluated (some 18)` | CP1 |
| `composition-context-observations` | Prior contextual donor → second cyclic embedding, nested/composed | Equal ordered footprints; both `.evaluated (some 28)` | CP1 |
| `probe-parity` (additional) | Six scalar donors: `repeated`, `selected 0`, `selected 4`, `binder`, `zeroReduction`, `constantRead` → copied translator | Production/probe footprints and ready results equal, **both available and missing stores** | Baseline extraction/parity guard |

`[a,b,a]` is palindromic: **rotation**, not reversal, distinguishes order. CT1 rotates and CT2 removes a repeated entry. Equality of scalar sums alone would not check either requirement. The strict `other=0` versus `other=4` pair distinguishes failure from success; the full-array check also pins both successful entries, not only the selected entry.

### Probe regeneration: preserve expected output before running writer

The generator is **not read-only**: it rewrites the probe. It mechanically extracts transport recursion, `mapOutcome` computation, policy resolve RHS, and consumers; it does not copy accompanying general transport proofs or create another proof compiler. The generated module is test-only.

Save the expected patch-applied probe before regeneration, then compare bytes **before accepting** generated output:
```bash
python3 -c 'from pathlib import Path; r=Path("/Users/williammacready/code/python/pyncd.worktrees/component-transport"); p=r/"leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean"; e=r/"papers/semantics/component_transport_artifacts"; (e/"execution-probe-expected.lean").write_bytes(p.read_bytes())'
python3 /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_artifacts/generate-probe.py /Users/williammacready/code/python/pyncd.worktrees/component-transport /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_artifacts
python3 -c 'from pathlib import Path; r=Path("/Users/williammacready/code/python/pyncd.worktrees/component-transport"); p=r/"leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean"; e=r/"papers/semantics/component_transport_artifacts/execution-probe-expected.lean"; assert p.read_bytes()==e.read_bytes(), "Generated probe differs from expected patch output"; print("Probe regeneration byte parity PASS")'
```

Retain `probe-source-hashes.json` as an execution receipt; do not accept a mismatched extraction by updating expected output blindly. On mismatch, preserve evidence and stop for adjudication. Remove only the saved comparison copy after success; do not stage it.

### Complete manifest checks and cycles — no filters

```bash
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/mutation-manifest.sh --check /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_probe_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_artifacts/execution-observer-results.md /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_mutations_post.json
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/mutation-manifest.sh --out /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_artifacts/execution-copied-results.md /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics/component_transport_probe_mutations_post.json
```

| Controls | Actual modified surface | Expected named failures (manifest is exact authority) |
|---|---|---|
| CT1 / CT2 | **Observer** order projection: rotate / take two | `ordered-repetition` |
| CT3 | **Donor** context map becomes `0` | `context-precompose`, `tab-at-context` |
| CT4 | **Donor** available store becomes missing | `readiness-success` |
| CT5 | **Donor** selected expression becomes literal `1/2` | `strict-selection-failure` |
| CP1 | Mechanically **copied computation**, predicate false | `context-precompose`, both contextual identity/composition checks |
| CP2 | Mechanically **copied computation**, binary operation becomes add | `strict-full-array` |
| CP3 | Mechanically **copied computation**, reduction binder pinned to zero | `reduce-binder` |
| CP4 / CP5 | Mechanically **copied policy computation**, constant zero / raw argument ignored | `boundary-constant` |
| CP6 / CP7 | **Donor** zero reduction becomes nonzero / empty extent becomes one | `zero-reduction` / `empty-tab`, `empty-scalar-metadata` |

These are **not live-production mutation kills**, and not every fixture has an individual mutant. In particular admitted-constant/reject consumers lack dedicated controls. Hashes, regeneration equality and baseline parity protect extraction; they do not prove mutation-completeness or parity for every expression/policy. Universal production proofs and these computational checks are distinct evidence.

### Discovery, review and task commit

- Keep all five modules registered **only** in `IndexedExecutionExperiment`; `import IndexedComponentTransportEval` is the explicit experiment entry point. Production `import LeanNCD` deliberately does not discover this API: this is an explicit exception to production top-level discovery, matching the design's experimental boundary.
- Extend patch 3's `leanncd/AGENTS.md` discovery paragraph to mention the generated test-only probe too; link the design's transport discussion to the exact module identifiers. No production import, new library, or unrelated design edits.
- Mid-tier review checks §5, all fixture donors/deltas/observations, arbitrary-raw policy laws, generation parity, audit output, manifest classification/restoration, and nondefault registration. Record findings as read, not only at the end.
- Record observed fixture/audit counts; historical namespace audits were transport **97**, test **82**, probe **90**, allowing only the standard axioms above. Counts may change after relocation without code source changes; investigate differences, do not falsify receipts to preserve numbers.
- Run the documentation sweep from the execution cwd with the absolute-root search command below; distinguish historical evidence from current claims, and record matches requiring no edit.

```bash
rg -n '16 fixtures|four new modules|all four new modules|spikes/IndexedComponentTransportProbe|remaining_authoring_gates|SourceContractMatch|IndexedComponentTransport' /Users/williammacready/code/python/pyncd.worktrees/component-transport/papers/semantics /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/AGENTS.md /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/lakefile.toml
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport add leanncd/experiments/indexed_execution/IndexedComponentTransport.lean leanncd/experiments/indexed_execution/IndexedComponentTransportTest.lean leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean leanncd/lakefile.toml leanncd/AGENTS.md papers/semantics/categorical_tensor_logic_component_interfaces.md papers/semantics/component_transport_plan.md papers/semantics/component_transport_authoring_record.md papers/semantics/component_transport_patches/01-domain-read.patch papers/semantics/component_transport_patches/02-expression-laws.patch papers/semantics/component_transport_patches/03-observations-integration.patch papers/semantics/component_transport_mutations_post.json papers/semantics/component_transport_probe_mutations_post.json papers/semantics/component_transport_artifacts/generate-probe.py papers/semantics/component_transport_artifacts/prototype-evidence.json papers/semantics/component_transport_artifacts/observer-mutation-results.md papers/semantics/component_transport_artifacts/copied-mutation-results.md
/usr/bin/git -C /Users/williammacready/code/python/pyncd.worktrees/component-transport commit -m "test(semantics): verify transport observations and policy laws" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

Checkpoint: 21 production checks, parity, 12 restored cycles and task review accounted for. If any was skipped, say so; do not mark release complete.

## 7. Controller release gate and integration

The controller itself, not only implementer reports, runs:
```bash
bash /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd/scripts/lake-build.sh /Users/williammacready/code/python/pyncd.worktrees/component-transport/leanncd LeanNCD Tests IndexedExecutionExperiment
```

Also rerun **both unfiltered checks and actual manifests from §6**, using `controller-observer-results.md` and `controller-copied-results.md` as `--out` receipt names in the same artifact directory. Recheck final generated-probe parity and audits after any fixes.

Two final **whole-branch** reviews, each with 40–60-line windows, explicit symbol locators and incremental receipts:
1. **Semantic soundness:** supplied domain evidence, policy conjugation on arbitrary raw coordinates, dependent addresses, all constructors/binders, all partial stores, strictness, ordered multiplicity, observational—not process—identity/composition.
2. **Integration and observations:** exact sequential patch result, all 21 checks and parity, mutation-scope honesty, source hashes and regeneration parity, default/nondefault imports, docs and scope exclusions. No second compiler or unproved whole-model claim.

Adjudicate findings; rerun affected checks plus the controller release gate. Only after **full builds green and reviews clean/adjudicated**, use `new-slice`'s established finish sequence: merge this execution branch to **local main**, verify equivalence, delete that branch and remove its worktree after inspecting status. Preserve unrelated/untracked authoring work. **No push without explicit request.**

Close out in the execution receipt, not by bloating this live plan: exact execution base/commits, commands/results, skipped checks, review dispositions, mutation limitations, measured token total and breaches, and local integration result. No prototype execution, commit or merge is part of this authoring dispatch.
