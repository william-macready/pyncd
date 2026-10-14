# Part V slice 5: authoring evidence and execution record

## A. Authoring boundary

This record accompanies `plan_layer_slice5_plan.md`. Authoring artifacts are
verified; general certification is unimplemented. This is not a completion
certificate. The fresh authoring dispatch writes only these two Markdown files,
does not implement the plan, launch agents, mutate code, build, stage or commit.
Prototype and final certification are explicitly separate.

Authoring worktree: `/Users/williammacready/code/python/pyncd.worktrees/scan-history-plan`.
Branch: `worktree-scan-history-plan`; base: `581bd163`.
Source inspected: immutable code snapshot `94cc67c9` at the session artifact
`files/scan-plan-snapshot/leanncd/`, not a live mutating prototype checkout.
Read windows were approximately 40–60 lines around named symbols.

Mandatory discipline read: `.claude/skills/slice-plan/SKILL.md`, REFERENCE
verification/sibling-audit/context sections, `new-slice` shell preamble and
`leanncd/AGENTS.md` wrappers. Existing slice-4 plan used only for style.
The live plan contains no Lean fences; future proof contracts are prose/math
with quantified assumptions. No uncompiled invented Lean snippet is shipped.
Any Lean fence introduced later must be checked verbatim after dependencies build.

## B. Verified prototype provenance

Parent-produced inputs, read during authoring:

- `papers/semantics/plan_layer_slice5_patches/manifest.json`.
- `papers/semantics/plan_layer_slice5_artifacts/prototype_api.json`.
- `papers/semantics/plan_layer_slice5_artifacts/prototype_evidence.json`.
- `papers/semantics/plan_layer_slice5_artifacts/authoring_evidence.json`.
- `papers/semantics/plan_layer_slice5_mutations_post.json` and artifact
  `mutation_results.md`.

Manifest base: `581bd1636cb8a9658600fa6bba2b2e648bca18c6`.
Code head: `94cc67c97393fb6d0f5863dd445bd8cfee2ccf99`.
Evidence was copied from prototype evidence checkpoint `a682a2ab`.
Mechanical ordered replay matches the complete prototype leanncd tree.
These are verified package observations, not replay executed by this writer.
Both forms are controller-verified: isolated-index ordered replay/re-replay,
and fresh detached-base working-tree replay with --check before each of three
applications and complete staged leanncd-tree equality against `94cc67c9`.

| Patch | SHA-256 | Synthetic replay checkpoint |
|---|---|---|
| `01-foundations.patch` | `597ca587a77d6ee511cab410d513f6ad44a61fa5786ccc48ff4053797e409ce2` | `94313d8eda90b60cce62f258a235a6927392d5ae` |
| `02-schedule.patch` | `ba03a2b7efb2ec3f05b1f7164eb85272f0d1db57be167fe1eacf57ac35308260` | `4dafdcde1dc0d473c96e713ef3304c9c4cfd307b` |
| `03-fixtures.patch` | `29fd4ad21710c20665cbd79d3138f8c78ac82f91e2cab15b8d2151a53d1e814f` | `476571c2e5a04bb52f450582b2b1c609423fd51f` |

Patches are generated with Git's `--no-signature` option: the standard email
signature whitespace is omitted without altering the replayed code payload.

Immutable window inspection confirms actual namespace, RegisteredF fields,
valuation guards/destinations/constructors, occurrence group tags, full footprint,
independent allocation, command schedule, completed-slice lists and static Live.
New Evaluation/Coverage/Model/Prefix/Validity/Correctness and umbrella paths
are target deliverables, not existing compiled modules.
No source claims beyond that prototype boundary are marked completed.

## C. Historical measurements, not final expectations

| Inventory | Observed prototype/base measurement |
|---|---|
| Base Plan*Test | 367 = 186 evaluated rows + 181 examples/theorems |
| Prototype added assertions | 18 = 14 evaluated rows + four examples |
| Plan*Test after prototype | still 367; two Prototype filenames lie outside glob |
| Combined old glob + two prototype modules | 385; not a final fixture-count promise |
| Prototype full build | 8804 jobs |
| Explicit scan-library audit | 187 constants |
| Explicit plan-fixture audit | 26 constants |
| Allowed axioms | propext, Classical.choice, Quot.sound |
| Existing warnings | four sorry warnings outside Plan, inherited |
| Observed exact mutation cycles before extra parent coverage | four, all restored byte-identically, restored builds passed |

Four cycle outcomes are described in plan §6 and `prototype_evidence.json`.
An earlier omitted-persistent-group exploration preceded the final group-length
proof and is not counted as final-tree fixture evidence.
The final authoring package below extends coverage to all 14 evaluated rows;
future certification controls remain execution work. Audit/build/job counts
above cannot be copied into final implementation status.

## D. Parent final authoring mutation package — confirmed

- Authoring manifest path:
  `papers/semantics/plan_layer_slice5_mutations_post.json`; delivered and read.
- Inventory: eleven entries, all T0; three independent-oracle controls, five fixture
  controls, three actual implementation mutations: persistent occurrence selection,
  successor-time destination and the initial-Z guard.
  Data/display/negative-neighbour controls are not production-semantic mutants.
- Run results:
  `papers/semantics/plan_layer_slice5_artifacts/mutation_results.md`; delivered,
  read; controller confirms anchored 11/11 PASS with actual computed row failures,
  byte-identical restoration and restored builds green.
- Authoring evidence:
  `papers/semantics/plan_layer_slice5_artifacts/authoring_evidence.json`; delivered
  and read; all 14 evaluated-row coverage map and observed anchors included.
- Unfiltered --check: controller confirms eleven unique substitutions pass.
- Exact diagnostic anchors: 38, copied from observed logs and verified in the
  full actual anchored rerun. Exact locations remain in JSON, not unstable prose.
- All 14 prototype evaluated rows have observed discrimination; neither every
  field within each row nor future proof-interface fixtures are thereby pinned.
- Replay/re-replay: controller confirms three synthetic patch commits reproduce
  the complete code tree. No general certification proof is included.

| Observed evaluated row | Killing controls |
|---|---|
| `scan-oracle-scalar-full-history` | S5-C1, S5-C3 |
| `scan-oracle-no-transitions` | S5-C3 |
| `scan-oracle-cross-coordinate-nonlinear` | S5-C2, S5-C3 |
| `scan-oracle-empty-state` | S5-C3 |
| `scan-prototype-scalar-executor` | S5-F1, S5-F2, S5-F3, S5-F7, S5-F8 |
| `scan-prototype-vector-executor-vs-oracle` | S5-F1, S5-F2, S5-F3, S5-F7, S5-F8 |
| `scan-prototype-whole-prior-slice-footprint` | S5-F4 |
| `scan-prototype-no-transitions` | S5-F2, S5-F3 |
| `scan-prototype-empty-history` | S5-F3 |
| `scan-prototype-retained-prefix-memory` | S5-F1, S5-F2, S5-F7 |
| `scan-prototype-inputs-and-published-history` | S5-F1, S5-F2, S5-F7 |
| `scan-prototype-early-publication-rejected` | S5-F2, S5-F5, S5-F7, S5-F8 |
| `scan-prototype-history-alias-rejected` | S5-F2, S5-F6, S5-F7, S5-F8 |
| `scan-prototype-unchecked-alias-corrupts-history` | S5-F2, S5-F6 |

S5-C3's source trace truncation and S5-F3's decoded-list observation truncation
cover N0/d0 output-shape rows, not a proof of late-only Decode. Empty output
Decode may already succeed at pc0. The plan explicitly avoids that false guard.
These eleven cycles supersede the preliminary four-cycle inventory; do not sum
them as fifteen independent cycles. The added source-generator controls show
why successor targeting and the base-only Z guard are independent obligations:
wrong targeting corrupts retained values, while widening the guard can leave
the unchecked numeric trace correct but invalidate the plan's source coverage.
T7b still measures all new execution controls.
Parent owns mechanical package and mutation evidence; writer owns only plan/record.

## E. Authoring self-check

- 15 acceptance tasks, with explicit prerequisites and meaningful proof splits:
  model equations/existence, prefix lists/membership, local conditions/Valid,
  prefix retention/terminal decode, discovery/regression closure.
- T1/T3 and model/prefix work are mathematically independent where indicated, but
  explicit fixture-handoff dependencies serialize shared test edits.
  Equations depend on exact classification; retention joins model correctness
  with valid scheduling.
- Per-task files and symbol locators distinguish CURRENT versus NEW targets.
- Existing source/test/utility/docs paths were inspected or existence-checked;
  new paths are clearly marked. No unstable `File.lean:NNN` citations.
- Generic assumptions include actual validated inputs or actual prefix runs;
  no getD fallback, assumed-success-only final result or scalar-only restriction.
- Prefix proofs use the full original plan's Valid, never truncated-prefix Valid.
- Mixed-registry proof/fixture discrimination remains planned: an unused different
  arity/type entry, beyond the prototype's two unary same-shaped operators.
- Case × class audit includes unchanged footprint/Core/group/SlotView/checker/R/Decode
  siblings and explicit silently-ignored behavior.
- Existing donors and nearest legal neighbours are named. New numeric values are
  unobserved/planned; source oracle remains independent.
- Final filenames/targets follow Plan*Test discovery, as future integration work.
- Public import graph has no child-to-umbrella cycle; docs sweep changes status only.
- Hook-section character measurement at authoring: leanncd AGENTS 0 named injected
  sections, Semantics AGENTS 0, Plan AGENTS 2104; remeasure before edits.
- Final two-lens whole-branch review, controller full build/real mutations/audits and
  local-main unpushed integration are mandatory, not reported completed.
- Controller direct authoring review covers source contracts, task dependencies,
  fixture/patch provenance and discovery. It corrected shared-test handoffs,
  required pointwise-present partial-store reads rather than one-way Agrees,
  added the native_decide scan, and measured two source-generator controls.
  No execution proof, new pin or final implementation build is pre-certified.

Budget measurement attempted with
`python3 .claude/skills/slice-plan/token-report.py f27ccd0f-0115-4a73-a6bb-b6d59a17cf53`:
tool reported no transcript. Cumulative input usage is **unavailable, not zero**.
At initial drafter handoff: live plan 685 lines; separate record 211 lines.
The final assembled sizes are checked by the controller against the 800-line cap.
Authored-file scan found no trailing whitespace, Lean fences or unstable Lean
line citations. The writer reported staying below the 40-turn aim, with no
observed hard-turn or context-cap breach; that report is not independent usage
measurement. Cumulative usage remains unavailable. Hard stop55 / context peak250k.

Controller publication checks: the assembled plan is 695 lines, has 15 tasks
with an acyclic dependency graph, and records shared-test resource handoffs.
All three final signature-free patch hashes match this record and their
ordered replay still equals the immutable prototype leanncd tree.
The complete 11-entry manifest passes unfiltered validation and actual cycles
with all 38 exact failure sites; the prototype checkout is clean afterward.
All 14 evaluated rows have observed controls, with the classification limits
above retained. JSON, documentation links and staged whitespace checks pass.
The unchanged implementation baseline builds in 8796 jobs in the author's
worktree. No Lean fences or new proof implementation are being published:
the new generic proof contracts are requirements, not kernel-checked results.

## F. Execution close-out template — fill only from observed evidence

Status: EXECUTING in `worktree-scan-history-exec`, based on local main `ed884938`.
T0 is accepted; subsequent tasks remain pending until their actual gates pass.

| Task | Accepted SHA / exact scope | Target command/log/result | Fixtures added/retained | Controls/evidence | Review/adjudication |
|---|---|---|---|---|---|
| T0 | `9f9ba4a9`: three checksum-verified patches; exact leanncd tree equals `94cc67c9` | refresh `LeanNCD` 8598 jobs; full build 8804 jobs, PASS | baseline 367; prototype 14 evaluated +4 proof items | unfiltered check 11 unique; 11/11 actual cycles, 38 exact sites; `t0_mutation_results.md` | controller replay/scope review accepted |
| T1 | PENDING | PENDING | PENDING | PENDING | PENDING |
| T3 | PENDING | PENDING | PENDING | PENDING | PENDING |
| T2a | PENDING | PENDING | PENDING | PENDING | PENDING |
| T2b | PENDING | PENDING | PENDING | PENDING | PENDING |
| T4a | PENDING | PENDING | PENDING | PENDING | PENDING |
| T4b | PENDING | PENDING | PENDING | PENDING | PENDING |
| T5a | PENDING | PENDING | PENDING | PENDING | PENDING |
| T5b | PENDING | PENDING | PENDING | PENDING | PENDING |
| T6a | PENDING | PENDING | PENDING | PENDING | PENDING |
| T6b | PENDING | PENDING | PENDING | PENDING | PENDING |
| T7a | PENDING | PENDING | PENDING | PENDING | PENDING |
| T7b | PENDING | PENDING | PENDING | PENDING | PENDING |
| T8 | PENDING | PENDING | PENDING | PENDING | PENDING |
| T9 | PENDING | PENDING | PENDING | PENDING | PENDING |

Close-out must record:

1. Complete whole-slice diff and replay base/code/execution SHA; scope changes.
2. Independent model/evaluation/coverage/Valid/prefix/completion/Decode theorem
   identifiers, actual generic hypotheses and full output-shape claims.
3. Exact fixture inventory, row labels and proof pins; observed new numeric
   expectations with their logs; final Plan*Test glob and lakefile discovery.
4. Actual final manifest schema/count, per-cycle exact failure anchors/log paths,
   proof versus fixture kills, restored file hashes and restored-build results;
   every required row/control mapped, no setup refusal counted as a kill.
5. Controller unfiltered --check and real manifest commands/results, not delegated
   green summaries; post-restoration full build command, jobs, warnings and log.
6. Standard-axiom audit namespaces and actual constants counts; forbidden-token
   sweep results; any inherited warnings with unchanged scope.
7. Both complete-branch review artifacts; findings, severity, adjudications,
   fix commits and focused re-review verdicts. Any parked issue and why the
   agreed goal does not require it, with estimated follow-up cost.
8. Public-import-only pin, documentation sweep result, hook budgets and no new
   general-scan/in-place/source-adapter/partial-F/floating-point claims.
9. Actual per-dispatch turns/context, cumulative authoring/execution input tokens,
   measurement availability, cap breaches and rationale. Unavailable is not zero.
10. Local main integration SHA, final status, safe branch/worktree removal,
    preserved evidence and unpushed status. No authoring/review checkout deletion.

Fixed scope limits: bounded full history only; arbitrary total selected unary
same-sort array operator in an existing registry; AddCommMonoid V; independent
retained slice buffers and separate inputs; no retire/reuse/fusion/relocation,
partial-F/floats/source-adapter or automatic general scan recognition.
Blocked load-bearing work stops; no hidden semantic narrowing or invented pass.
