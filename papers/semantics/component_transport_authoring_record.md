# Component transport: authoring record

## Status and authority

**Phase B, plan only.** This dispatch writes the [execution plan](component_transport_plan.md) and this record from exported verified artifacts. It does not change Lean, replay patches, run builds or mutations, commit, or merge. Prior untracked design/package files are preserved.

Authority: [design](categorical_tensor_logic_component_interfaces.md), sections 1–2, 7 and 9; [slice-plan discipline](../../.claude/skills/slice-plan/SKILL.md); [new-slice preparation/finish discipline](../../.claude/skills/new-slice/SKILL.md). The user selected only typed transport, footprints and `evalReady` preservation.

## Provenance and precedence

Planning/scratch baseline: `c26e68bc6caa24a40f794cf8a9de207a1f7d9604`.
Final candidate supplied by controller: `6d7d0f4e9e9177ed8dbe191e369563ed98fe1d6d`.
These identify authoring provenance, **not required future implementation HEADs**.

| Export | Mechanical provenance supplied by controller | Role |
|---|---|---|
| `component_transport_patches/01-domain-read.patch` | diff baseline → `efa0950c56d05a73fbaf96e6330d9ed16e3447b6` | Domain/read/store API |
| `component_transport_patches/02-expression-laws.patch` | diff `efa0950c` → `5505631605ab0902a229c77098db8234e6053ebc` | Structural expressions and universal laws |
| `component_transport_patches/03-observations-integration.patch` | diff `55056316` → final candidate | Policy laws, 21 fixtures, copied probe and discovery |

The [prototype evidence](component_transport_artifacts/prototype-evidence.json) retains an original snapshot plus **`followup` overrides**. Final counts are **21 production checks + one additional parity check; 5 CT + 7 CP = 12 cycles**. Original 16-fixture, four-module, four-task, optional coverage-follow-up, and spikes-location statements are historical, not current requirements. The final package uses **three tasks** and five experiment modules.

Controller relocated the copied probe to `leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean` and registered it in the existing nondefault `IndexedExecutionExperiment`. Final patches, manifests and generator all use that path. There is no additional library or tracked-spike exception.

`Domain.policy_id`/`Domain.policy_comp` now cover arbitrary raw arguments. Admitted constant reads, complete successful strict-array entries, actual transported empty tabs, and context-aware identity/composition observations are present in final patch 3. Do not carry their earlier absence forward as current gaps.

## Exported prototype observations — not independent Phase B reruns

Sources: [observer results](component_transport_artifacts/observer-mutation-results.md), [copied results](component_transport_artifacts/copied-mutation-results.md), and JSON `verified`/`followup`.

- Generic footprint/evaluation/readiness laws quantify over all contexts/types/partial stores; fixed rational registry/ops, all eight constructors.
- Supplied domain profile includes axis/extent evidence, coordinate/raw equivalences, raw-axis law and commuting law; no automatic adapter derivation.
- Exact ordered footprint printed as `[(1,2,0),(2,0,1),(1,2,0)]`, with evaluation `some 53`. Rotation—not reversal—discriminates order in this palindromic example.
- Final added observations: constant read under missing store → `.evaluated (some 7)` and `[]`; full strict array → entries `1/2`, `1/4`; empty tab succeeds under missing store with `[]`; contextual identity → `[(0,1,2)]` and `18`; contextual nested/composed evaluation → both `28`.
- Historical namespace audits: `IndexedComponentTransport` 97, `IndexedComponentTransportTest` 82, `IndexedComponentTransportProbe` 90, all passing with only `propext`, `Classical.choice`, `Quot.sound`. Counts are recorded observations, not immutable release assertions after relocation.
- Observer receipt: CT1–CT5 each reported expected failure seen, restored build green, file byte-identical; **5/5 PASS**.
- Copied receipt: CP1–CP7 reported the same restoration/failure conditions; **7/7 PASS**.
- No `sorry`, `native_decide`, or newly introduced axioms reported in the verified prototype.

### Evidence classification and limitations

CT1/CT2 modify **observers**. CT3/CT4/CT5 and CP6/CP7 modify **donor fixtures**. CP1–CP5 mutate **mechanically copied production computations without their accompanying general transport proofs**. None is a live-production mutation kill.

The generator extracts translator recursion, outcome mapping and policy-resolver computation, then copies consumers. Parity covers six scalar donors under available and missing stores; hashes plus regeneration equality protect extraction. It is not a second proof compiler, a proof of arbitrary production/probe equivalence, or mutation-complete coverage.

Not every fixture has an individual mutant. In particular admitted-constant and rejected-policy consumers have no dedicated mutation control; copied policy mutations hit the boundary-constant consumer. Universal proofs are not computational assertions. The plan explicitly retains these limitations instead of adding unverified cycles.

No same-old-numeric-UID collision or display-name fixture is claimed. This API has no display names and no namespace allocator; the fixture uses explicit distinct target UIDs. Whole-component freshening, model gluing, rank/phase and runner results remain outside this slice.

## Phase B inspections and observed results

All shell commands were plain separate commands, with absolute paths and `/usr/bin/git -C` where Git was used. Read windows were at most 60 lines. Three requested windows started beyond EOF (patch 2 at 181; patch 3 at 481; assembled plan at 301); the tool returned errors and no data. No Lean compilation was attempted.

| Inspection / command family | Observed result |
|---|---|
| `git status --short` at entry | Only untracked design, transport artifact directory, patches and two manifests; no tracked edits |
| `ls -l` of exported patch/artifact directories | Three patch files; generator, JSON evidence, two mutation-result markdown receipts |
| Read design sections 1–2, 7, 9; all patch windows; both manifests; generator; evidence and receipts | Exact final API and observations used in plan; no Lean transcribed into prose blocks |
| `ls -ld` of source/donor/script paths | Types, Expr, Interpret, Readiness, RationalReference, ExpressionTest, SourceBindingBoundaryTest, AxiomAudit, IndexedCompositionParityTest, build/mutation wrappers and split template exist |
| Python read-only package analysis | Exactly 21 production `#eval check` assertions in patch 3; manifest lengths 5 and 7 |
| Python patch deliverable existence check | All five proposed Lean module paths absent here; `leanncd/lakefile.toml` and `leanncd/AGENTS.md` exist |
| Python scan of added patch lines | No `sorry`, `native_decide`, or `axiom ` declaration found |
| Heading/body character measurement | `Patterns` 427 + `Global Pitfalls` 2526 = 2953; single-file typecheck guidance separately 956; execution must recheck actual injected hooks |
| Final documentation validation | Plan 275 lines, record 104 lines at first validation; zero Lean blocks or unstable Lean line locators; every Markdown link resolved; every one of the 21 production fixture labels present; both manifests parsed as 5/7 entries |

The first broad globbed heading search returned no matches; direct `rg -n` against the known design path located its sections. No code re-exploration or prototype work followed.

### Artifact hashes measured during Phase B

SHA-256 of exact input bytes:

| Artifact (relative to `papers/semantics/`) | SHA-256 |
|---|---|
| `component_transport_patches/01-domain-read.patch` | `3ed6b24de252e82ac3f60106a74bf2d72575bc44a44060dbc40935ca656b06e2` |
| `component_transport_patches/02-expression-laws.patch` | `401791a56b9f8b9f27b672506ab79d04e99b2f9db2b61032a1f36a67f2b7629e` |
| `component_transport_patches/03-observations-integration.patch` | `66d1709c092a3c0602a8a670778f9dc5b52464a799ffdd0c0a6ab50f80639301` |
| `component_transport_mutations_post.json` | `fdb7fffb217866d20a6fdaf3b0799223baa8e28b49690faab358d3b5711f4039` |
| `component_transport_probe_mutations_post.json` | `df4ec410fdd1bcbc5d921f43788e324502ce07af69590377f3465aff923a7f40` |
| `component_transport_artifacts/generate-probe.py` | `5208464afaf590e6f5f84e1cf785897cbfa62d2240d2ab06950917e7bff895a9` |
| `component_transport_artifacts/prototype-evidence.json` | `b4c69ce946951f10c3193e984ea70966dddb414fcf36cf62f75bdadc711c4672` |

## Controller receipt — verified

After Phase B, the controller independently ran the exported package against
the final relocated candidate. These are actual controller observations,
not inferred from prototype reports.

| Required controller authoring check | Status / receipt |
|---|---|
| Apply exact patches 1 → 2 → 3 cleanly in scratch replay | **PASS**; temporary-index replay exactly reproduced the candidate tree; [receipt](component_transport_artifacts/controller-replay.json) |
| Build final default targets | **PASS**, covered by the combined command below |
| Build `LeanNCD Tests IndexedExecutionExperiment` at final relocated state | **PASS**, exit 0; `Build completed successfully (8869 jobs)` |
| Both manifests `--check`, unfiltered | **PASS**; 5 and 7 selected entries, all old strings unique |
| Actual CT1–CT5 cycles, expected strings and byte restoration | **5/5 PASS**; [controller observer/donor receipt](component_transport_artifacts/controller-observer-mutations.md) |
| Actual CP1–CP7 cycles, expected strings and byte restoration | **7/7 PASS**; [controller copied-computation/donor receipt](component_transport_artifacts/controller-copied-mutations.md) |
| Regeneration byte parity, final source hashes, baseline probe parity and audits | **PASS**; regenerated probe had no Git diff; [source hashes](component_transport_artifacts/probe-source-hashes.json); final namespace counts 97 / 82 / 90, only allowed standard axioms |

The controller used the planning checkout's build and mutation wrappers with
the isolated scratch checkout as target. Exact scratch root:
`/Users/williammacready/.copilot/session-state/cd0f9bbb-9e81-4009-befa-fe71e49624ff/files/transport-prototype`.
The combined command was `bash leanncd/scripts/lake-build.sh <scratch>/leanncd LeanNCD Tests IndexedExecutionExperiment`.
Each actual manifest run used the same target and its exported manifest,
without filters; both receipt tables are linked above. No separate redundant
default build was needed.

After successful validation, the controller removed the clean scratch
worktree. The patches, hashes and controller receipts remain in this package.

Controller package review checked semantic scope and execution/integration
instructions directly. It corrected preparation to omit `--plan`, whose
primary-checkout copy source need not exist for uncommitted authoring inputs.
Document validation resolved all links, checked both manifest inventories,
and distinguished 21 primary consumers from their 21 copied consumers plus
one parity check. No Lean blocks require snippet compilation.

These are authoring acceptance receipts, not permission to merge a prototype. Future implementation independently prepares latest local main, applies task patches, builds and commits each task, then repeats controller release checks and two whole-branch review lenses. No independent review dispatch or implementation release is claimed by this record.

## Budgets and remaining gates

- Phase A originally had a 55-turn cap; controller authorized a ≤25-turn follow-up. **Cumulative prototype authoring exceeded the original single-dispatch 55-turn cap**, as explicitly reported in evidence; no measured cumulative turn count is available here.
- Phase B is a fresh artifact-only dispatch capped at **25 turns / 150k context**. Write-up and validation remained below both caps; no breach and no nested agents.
- Overall authoring target is approximately **50M cumulative input tokens**, execution ceiling **175M**, each implementation dispatch approximately 40 turns, at most approximately 60 turns / 250k context. No authoring transcript/token-report measurement is supplied; total authoring tokens are **unmeasured**, not asserted within target. Controller owns aggregate accounting.
- No unresolved design decision or pending controller check blocks this chosen explicit-certified-adapter profile. The stated non-production/per-fixture mutation limitations remain; this is not mutation-complete coverage. Broader design milestones stay unplanned.
- Authoring completion does not execute the implementation plan or commit, merge or push in the planning or primary checkouts. Scratch prototype commits are provenance only.
