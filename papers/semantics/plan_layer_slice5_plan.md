# Part V slice 5: certified bounded full-history scans

Status: authoring artifacts verified after a compiled, incomplete prototype;
general certification has **not** been implemented. Base: local `main` at `581bd163`.
Authoring branch: `worktree-scan-history-plan`.
Execution evidence and close-out belong in `plan_layer_slice5_record.md`.

## 1. Process, authority and bounded execution

**Full path:** a new generic scan certificate and numerical retention theorem
introduce a soundness surface spanning source equations, schedules and memory.
This is the mandatory fresh authoring dispatch after prototype verification.
One plan covers slice 5 only; there is no implementation in this document.

Fixed contract: for arbitrary natural `d,N`, including zero, inputs `X,Z` have
shape `(d)` and the **entire** designated output `H` has shape `(d,N+1)`.
For an existing registry and a certified total unary same-sort array operator
`F`, the independent recurrence is `H₀ = X + Z`,
`Hₗ₊₁ = X + F(Hₗ)` for `l<N`. The carrier is any `V` with `AddCommMonoid V`.
Execution uses the existing scalar-operations parameter; scan bodies use
reads, tabulation, primitive application and indexing, not a new scalar DSL.
There are no binary/reduce/iverson scan bodies, so do not invent an `ops.add`
coherence assumption: additive collection uses the existing AddCommMonoid instance.
Executable numeric fixtures use exact rationals.

Storage: `N+1` independent buffers, each of capacity `d`, and separate input
slots. Every completed slice remains readable through every later command.
No retirement, buffer reuse, fusion, relocation, partial operators, floating
point, source-adapter connection or last-state-only output is in scope.
Do not narrow to scalar/affine operators, positive bounds, or `N=2`.
General scan recognition and in-place reuse remain outside this slice.

Every execution brief opens with this shell-harness preamble:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

Controller prepares an isolated implementation worktree using `new-slice`,
checks the actual local base, preserves the Mathlib cache and refreshes project
oleans. The authoring worktree is not the implementation checkout.
Replace `<worktree>` once with its literal absolute path when issuing commands.
Use 40–60-line symbol windows, never whole large modules. CURRENT symbols below
are verified in base or immutable prototype, or an explicitly named prerequisite
whose acceptance must be checked at task entry; NEW symbols are **target names**
until implemented. A target can be renamed with an explicit ledger mapping,
but its quantified contract cannot disappear.

Per-task caps are below; each dispatch has context peak at most 250k and at
most 60 turns. Stop and report before a hard cap, preserving the accepted
checkpoint and precise blocker. Do not conceal a breach. Slice execution
budget is at most approximately 175M cumulative input tokens; authoring target
approximately 50M. Unavailable measurement is not zero or proof of compliance.
Reviewers persist findings incrementally; fix only a bounded finding group.
T2, T4, T5, T6 and T7 are deliberately split into separately rejectable tasks.
If even a split task is forecast beyond 60 turns, use the skill's split-handoff
template: production acceptance first, then its specified fixtures/cycles.

## 2. Verified prototype boundary and replay

Mechanical package: `papers/semantics/plan_layer_slice5_patches/manifest.json`.
It records base `581bd1636cb8a9658600fa6bba2b2e648bca18c6` and prototype code
`94cc67c97393fb6d0f5863dd445bd8cfee2ccf99`.
Ordered isolated-index replay matches the **complete leanncd tree** of that
prototype. Controller also checked all three applications in order in a fresh
detached-base worktree, applied them and verified its complete staged leanncd
tree equals `94cc67c9`. Patch payloads were generated mechanically from compiled source:

| Order | Patch | Contents |
|---|---|---|
| 1 | `01-foundations.patch` | Recurrence, Core, Allocation, Operator |
| 2 | `02-schedule.patch` | Schedule, Plan |
| 3 | `03-fixtures.patch` | Two prototype tests and lakefile registration |

These patches implement only the compiled prototype, **not** the whole plan.
T0 replays them once onto a clean base; do not replay into a checkout already
containing them. New certification proofs and public wiring follow.
Replay proof, checksums and historical observations are in the separate record.

Immutable authoring source is the `leanncd/` subtree under
`/Users/williammacready/.copilot/session-state/f27ccd0f-0115-4a73-a6bb-b6d59a17cf53/files/scan-plan-snapshot/`.
Do not read the live prototype checkout during controller mutation cycles.
`prototype_api.json` and `prototype_evidence.json` under
`papers/semantics/plan_layer_slice5_artifacts/` describe that same code.

Verified facts: independent recurrence and uniqueness; `RegisteredF` certifies
chosen operator, unary arity, both state types and total domain; three source
IDs each enumerate `d*(N+1)` raw valuations with distinct guards; constructors
for persistent, initial and recurrence occurrences; `finProdFinEquiv` transport;
injective placement of `H(i,l)` at buffer `l`, coordinate `i`; exact full
previous-slice recurrence footprint through registry casts; block length `d`,
group length `2*d`, empty groups at `d=0`; `3*(N+1)` singleton commands;
all-boundary layout safety, no Ret, completed-slice Cons/Mat/Pub list equations,
and logical Live membership for `l<k` at `pc=3*k`.
Live membership and rank **do not** establish numerical memory retention.

Missing certification is assigned below, not deferred: interpreter transport
and arbitrary validated input extraction; collected-equation/model correspondence;
coverage and target identities; all-phase bookkeeping; full generic Valid and
checker acceptance; actual-prefix success and retained values; unconditional
completion and complete Decode; hypothesis pins, exposure, docs and final gates.

## 3. Required contracts and sibling audit

Throughout, fix arbitrary `V`, `d,N`, registry `r`, certificate `f : RegisteredF r d`,
scalar operations `ops`, and validated `η : (program f N).Input`.
Use the monoid instance where collection/execution needs it. Extract states
`Xη,Zη` from the present tensor bindings using `Option.get` and presence proofs.
Prove `η = input f N Xη Zη`, including the absent H binding.
Never use `getD 0`, a default-zero array or an assumed canonical input subset.

Let `h = history f.transition Xη Zη`, independently of Program/plan/Decode.
Define a total model store by X/Z bindings and `ρ(H,i,l)=h(l)(i)`.
Prove the Program's collected equation at every H coordinate is exactly
`Xη(i)+Zη(i)` at zero and `Xη(i)+f.transition(previous slice)(i)` at successors.
Then prove existence and an iff correspondence with this independent store,
not only `done_correct` applied to an unchecked source construction.
Finite uniqueness uses bounded induction on `l≤N`; the current infinite
`history_unique` needs a proved extension if reused on a finite history.

For `Bₗ=block f N l`, `Gₗ=group f N l`, write
`B<k` and `G<k` for the flatMaps over the first `k` slices. Exact prefixes:

| Boundary | Cons list | Mat list | Pub list |
|---|---|---|---|
| `3*k` | `G<k` | `B<k` | `B<k` |
| `3*k+1`, `k<N+1` | `G<k` | `B<k ++ Bk` | `B<k` |
| `3*k+2`, `k<N+1` | `G<k ++ Gk` | `B<k ++ Bk` | `B<k` |
| `3*(k+1)` | `G<(k+1)` | `B<(k+1)` | `B<(k+1)` |

At command indices `3*k`, `3*k+1`, `3*k+2`, lookup returns the singleton
init, acc, pub respectively. At the final index it returns none. Handle
`pc=0`, final boundary, `d=0`, `N=0` and combined zero explicitly.
Natural bounds distinguish final `k=N+1` from a slice index `Fin (N+1)`.

Required prefix numerical theorem: for every `pc≤3*(N+1)` there are `Mpc,cpc`
such that running the first `pc` commands from Start is `.done pc Mpc`,
`refState ops η pc = some cpc` and `R ops η pc Mpc cpc`.
For every `i : Fin d`, `l : Fin (N+1)` with `3*(l.val+1)≤pc`,
`readSlot allocation Mpc (historyAddress d N i l)`,
`readPub pc Mpc (historyAddress d N i l)`, and the actual physical slot
`Mpc (.inr ⟨l,i⟩)` each equal `some (h l.val i)`.
Consequently every later boundary preserves that same published value.
This is about actual runs, not arbitrary memories, static Live or ghost history.

Required terminal theorem: for **every** validated η there exists M with
`runPlan ops (Start η)=.done (3*(N+1)) M` and Decode returns `some out`,
where `out` is the full output of shape `(d,N+1)` and
`out(H,historyCoord i l)=h l.val i` for every i,l.
State the output function itself, including empty domains; a vacuous pointwise
claim alone does not show successful Decode when `d=0`.
For `d=0`, Decode may already succeed at pc0 because the output has no coordinates.
Do not require pre-final Decode=none unconditionally; any early-decode-refusal
pin needs `d>0`. Completion, output shape and empty Decode are distinct contracts.
Expose the corresponding independent output denotation, with model-derived
admissibility rather than an unexplained assumed model or assumed successful run.

Audit unchanged siblings and their callers in each owning task:

| Case × class | REQUIRED | FORBIDDEN | SILENTLY IGNORED / disposition |
|---|---|---|---|
| `.tab/.prim/.at` reads | entire previous slice; chosen F through casts | coordinate-only or identity substitution | no dynamic dependency pruning, even if F ignores coordinates |
| Core persistent guard | every `(i,l)` contributes X | missing X after base | raw guards reject no persistent pair |
| Core initial guard | Z only at time zero | Z at later states | other raw times ignored by guard; T3 proves exact classification |
| Core recurrence guard/destination | source `l<N`, target `l+1` | last raw time admitted; wrong destination | filtered valuations are not occurrences; prove no escape |
| occurrence groups | distinct source IDs and full coverage/Nodup | same-size ID replacement; duplicate/omitted terms | group length alone ignores tags; T3/T5 inspect tags |
| publication blocks | every coordinate of every H slice once | final-history omission or final-state-only output | empty coordinate lists do not drop H's output role |
| readiness / command order | prior publication before recurrence acc | reads from partial accumulators, early pub | indices beyond commands have no command; prove boundary convention |
| published-buffer writes | independent placement, retention at every later pc | overwrite, collapse, reinit or retirement of published H | inactive slots outside SlotView are none under R.dead |
| input/output role | X/Z present, H absent from input, H sole full output | missing/extra input binding, H-as-input | empty tensor still requires correct tensor-level presence |
| internal array shape | input/output equal `stateTy d` | scalar F, wrong sort/extent, partial F | other registry operators need not be unary/total; not selected |
| zero bounds | `d=0`, `N=0`, both zero; full Decode succeeds | positive-bound premises or fallback-zero reads | Fin-empty coordinates remove occurrences, not commands/roles |
| alias checker | checkSteps/checkLayouts distinguished | accepting co-live H collisions | unchecked executor may finish corrupt; no runtime detector added |
| SlotView/checkLayouts/R/Decode | all boundaries incl final, physical output | ghost-only retention or boundary-only read proof | generic inactive/retired behavior unchanged; scan has no Ret |
| rank / dependency | earlier-slice readiness, actual numeric preservation | claiming rank alone proves retention | no new rank-synthesis or compiler-recognition claim |

Each task records its rows and any silently-ignored case that escapes required
checks. Existing safe generic behavior is not a cleanup invitation.
Out-of-scope defects are parked with cost; load-bearing blockers stop execution.

## 4. Modules, dependencies and task sizing

Paths below are repo-relative. All ScanHistory library declarations use the
existing namespace `LeanNCD.Semantics.Program.Plan.ScanHistory`.
New paths are not claimed to exist or compile. Import graph, with base imports
omitted: Evaluation → Plan; Coverage → Plan; Model → Evaluation + Coverage;
Prefix → Coverage; Validity → Prefix; Correctness → Model + Validity;
ScanHistory umbrella → Correctness; public Plan umbrella → ScanHistory umbrella.
No child imports either umbrella; no cycle through public Plan.
Existing Recurrence/Core/Allocation/Operator/Schedule/Plan imports stay intact.

| Task | Prerequisites | Max turns | Fixture shapes / mutation obligations |
|---|---|---:|---|
| T0 controller replay/baseline | approved authoring + packages | 20 | 14 evaluated +4 proof replay assertions; eleven measured authoring cycles |
| T1 evaluation/input bridge | T0 | 50 | 2 planned pins: transport, arbitrary validated input; 2 controls |
| T3 coverage/targets | T0,T1 (shared test handoff) | 50 | 2 planned pins: guard classification, tag/target partition; 2 controls |
| T2a collected equations | T1,T3 | 50 | 1 planned equation shape, scalar/vector instantiations; 1 control |
| T2b independent model | T2a | 45 | 2 planned pins: finite correspondence, empty-domain model; 1 control |
| T4a lookup/all-phase lists | T3,T2b (shared test handoff) | 50 | 1 planned full phase table; 1 control |
| T4b membership/readiness bridge | T4a | 40 | 1 planned off-by-one read boundary; 1 control |
| T5a Init/Acc/Pub conditions | T3,T4b | 50 | 2 donor shapes: early pub, wrong same-size tags; 2 controls |
| T5b readiness/Valid/checker | T5a | 45 | 2 donor shapes: full-slice reads, aliases; 2 controls |
| T6a prefix success/retention | T2b,T5b | 55 | 2 donor shapes: scalar all-pc, vector all-pc; 2 controls |
| T6b done/full Decode | T6a | 45 | 2 donor shapes: full-history oracle, empty Decode; 2 controls |
| T7a final names/hypothesis pins | T6b | 35 | 18 inherited assertions preserved; 3 interface pin/control obligations |
| T7b final regression/mutation closure | T7a | 50 | 3 planned shapes/controls: input roles, combined zero/bounds, registry transport |
| T8 public exposure/docs | T7b | 30 | 1 public-import pin/control; no heavyweight docs dispatch |
| T9 reviews/controller gate/integration | T8 | 40 per review | complete measured fixture/cycle inventories, not fixed totals |

There are 15 acceptance tasks including two controller-only gates.
T1 and T3 are logically independent, but both edit the same prototype test module;
T3 therefore waits for T1's accepted fixture checkpoint. Likewise T4a waits for
T2b's fixture handoff although prefix mathematics is independent of model existence.
These resource prerequisites are explicit in the table: do not run implementers
concurrently against shared test files. T2 follows T3 because equation collection
reuses occurrence classification. T6 joins source semantics and valid scheduling.
Do not mutate files while reviewers read their live versions.
Cycle numbers here are coverage requirements, **not** measured new cycle counts:
one final control can cover several rows if its observed failure really proves
each. Map every obligation to the final measured manifest, classify library
proof kills versus numerical fixture kills, and do not add nominal duplicate
cycles just to match this table. Final inventory is measured from that mapping.

### T0 — controller: replay the compiled prototype and baseline

Files: CURRENT mechanical package/manifest and artifact JSON; replayed six
ScanHistory modules, two prototype test modules and `leanncd/lakefile.toml`.
No implementer dispatch. Verify exact patch order, unique application, checksums
and complete-tree replay against code SHA before making a checkpoint commit.
Symbols: CURRENT `program @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Core.lean`,
`plan @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Plan.lean`,
`execute @ leanncd/test/Semantics/ScanHistoryPlanPrototype.lean`.

Measure baseline on immutable base: Plan*Test has 367 assertions, split as
186 evaluated rows and 181 top-level examples/theorems. Prototype adds 18
assertions (14 evaluated, four examples), but its two filenames do not match
Plan*Test; that glob still reports 367, not 385. Reproduce both prototype targets
with the wrapper and full build; compare exact observations in §6.
Verify authoring manifest/evidence availability without inventing missing cycles.
Build: `Semantics.ScanHistoryRecurrencePrototype`,
`Semantics.ScanHistoryPlanPrototype`, then full wrapper build.
Done: accepted replay SHA, base/prototype fixture inventory, full build and audit
observations recorded, no claim that certification already exists.

### T1 — interpreter transport and all validated inputs

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Evaluation.lean`;
CURRENT prototype plan test for two early proof pins.
Symbols: CURRENT `RegisteredF.arguments`, `RegisteredF.transition`,
`RegisteredF.arrayExpr`, `priorSlice`, `recurrenceBody @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Core.lean`;
`input @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Plan.lean`;
`ValidInput @ leanncd/LeanNCD/Semantics/Models.lean`;
`Registry.apply @ leanncd/LeanNCD/Semantics/Types.lean`;
`evalWith @ leanncd/LeanNCD/Semantics/Interpret.lean`;
`sequence_complete`, `tab_complete @ leanncd/LeanNCD/Semantics/Completeness.lean`.
Read 40–60-line windows. Reuse these evaluation utilities and registry apply;
do not write a second interpreter.

NEW target symbols `inputX`, `inputZ`, `input_reconstruct`, `arrayExpr_eval`,
`priorSlice_eval`, `recurrenceBody_eval`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Evaluation.lean`.
Three obligations: Option.get-backed input reconstruction for every η;
evaluation transport for selected primitive with input/output equality casts;
full-array tab/at evaluation giving `some (f.transition slice i)` for a total
store, and for a partial store agreeing on the entire prior-slice footprint.
The partial-store premise is pointwise presence and value equality:
for every prior coordinate j, its read is `some (slice j)`.
The one-way `Agrees` predicate alone permits missing cells and is insufficient.
State all Γ/valuation and scalar-ops parameters; no rfl-shape assumption.
Registry certificates may use nontrivial equality proofs.
Pins: clone `registered`/`scan-prototype-vector-executor-vs-oracle`, vary equality
certificate presentation without changing meaning; clone `scalarInput`, construct
a validated binding directly rather than via `input`, then prove reconstruction.
New outputs remain PLANNED until observed. Controls must target cast/selection
and input extraction independently, with intended failures measured.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Evaluation`,
`Semantics.ScanHistoryRecurrencePrototype`, `Semantics.ScanHistoryPlanPrototype`.
Done: bridge lemmas compile generically, no getD, empty inputs covered.

### T3 — exact occurrence and publication coverage

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Coverage.lean`;
CURRENT prototype plan test for classification/tag pins.
Symbols: CURRENT `statementGuard`, `destination`, `valuationPair_index`,
`persistentOccurrence`, `initialOccurrence`, `recurrenceOccurrence @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Core.lean`;
`block`, `group @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Plan.lean`;
`Coverage1`, `Coverage2 @ leanncd/LeanNCD/Semantics/Plan/Syntax.lean`;
`OccRef.target @ leanncd/LeanNCD/Semantics/Plan/Step.lean`.

NEW targets `occurrence_cases`, `persistent_target`, `initial_target`,
`recurrence_target`, `plan_coverage1`, `plan_coverage2`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Coverage.lean`.
Three obligations: bijective tagged classification into all persistent pairs,
initial i at zero, recurrence i,l with l<N; exact target identities including
the recurrence successor; occurrence/publication flatMap covering and Nodup.
Prove source-ID disjointness, per-slice injectivity and disjoint blocks, not
just cardinality. Raw count is three times `d*(N+1)`; admitted bounds differ.
Explicitly prove N=0 rejects every recurrence valuation and d=0 has no occurrence.
Pins: clone `persistentGroup`/`initialGroup`, compare same-sized lists with
different source IDs; clone zero-transitions and empty-history rows to pin
admitted guards and coverage, including combined zero. Retain the legal groups
as nearest neighbours. Observe any new expected counts before recording them.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Coverage`,
`Semantics.ScanHistoryPlanPrototype`.
Done: completeness/Nodup and exact targets compile for arbitrary d,N.

### T2a — collected equations, not just recurrence-shaped syntax

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`;
CURRENT prototype plan test for collected-equation pin.
Symbols: CURRENT `collect_grouped`, `collect_relabel @ leanncd/LeanNCD/Semantics/Program.lean`;
`models_relabel @ leanncd/LeanNCD/Semantics/Models.lean`;
T1 `recurrenceBody_eval @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Evaluation.lean`;
T3 `occurrence_cases @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Coverage.lean`.
NEW targets `program_admEnv`, `collect_zero`, `collect_succ`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`.

Three obligations: every occurrence evaluates on any total store by F's
totality; exactly two contributions per H coordinate are collected; zero and
successor equations match the independent mathematical recurrence.
Prove each destination fibre excludes all other source times/coordinates.
Use existing grouped/relabelled finite-sum utilities; a helper equivalence
must itself be proved, not postulated. No affine or commutation law for F.
Pin: clone scalar/vector executor row, instead evaluate collected equations on
a directly constructed total store; the witness is independent of execution.
Same-size wrong occurrence control must alter a collected value, not only length.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Model`,
`Semantics.ScanHistoryPlanPrototype`.
Done: exact equations and AdmEnv under only stated assumptions.

### T2b — independent model existence and finite correspondence

Files: CURRENT newly accepted Model module and prototype plan test.
Symbols: CURRENT `history`, `history_unique @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Recurrence.lean`;
`Models`, `InputAgreement`, `denotation_of_model @ leanncd/LeanNCD/Semantics/Models.lean`;
T1 `input_reconstruct @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Evaluation.lean`;
T2a `collect_zero`, `collect_succ @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`.
NEW targets `historyStore`, `historyStore_models`, `models_iff_historyStore`,
`history_output` @ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`.

Two obligations: construct a model for every validated η, using independent
history and the actual X/Z bindings; prove any model equals that whole store by
bounded induction, with the full-history output projection identified.
Do not assume Successful, done, or AdmInput to establish existence.
Pins: clone scalar/vector oracle trace to instantiate the model correspondence;
clone empty-history/no-transitions donors to prove tensor presence, model and
output shape when coordinates or transitions are empty.
Control: wrong recurrence/base equation must break the correspondence pin.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Model`,
`Semantics.ScanHistoryRecurrencePrototype`, `Semantics.ScanHistoryPlanPrototype`.
Done: existence and iff correspondence; no infinite-history uniqueness shortcut.

### T4a — command lookup and exact all-phase prefix lists

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Prefix.lean`;
CURRENT Schedule only if a proved reusable list helper is needed; prototype plan test.
Symbols: CURRENT `scheduleCommands_take`, `consList_at_slice_boundary`,
`matList_at_slice_boundary`, `pubList_at_slice_boundary @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Schedule.lean`;
`prefixAnn_succ`, `cons_succ`, `mat_succ`, `pub_succ @ leanncd/LeanNCD/Semantics/Plan/Simulation.lean`.
NEW targets `command_init`, `command_acc`, `command_pub`, `command_end`,
`prefix_phase_lists @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Prefix.lean`.

Three obligations: indexed lookup for the three phases and end; exact Cons/Mat/Pub
lists for §3; no-retirement at every pc and exhaustive boundary decomposition.
The final boundary is included, not expressed as an invalid Fin slice.
Pin: clone `scalarPrefix` donor and tabulate bookkeeping/lookup at pc=0..9;
the indices before and after acc/pub must differ. Empty blocks retain commands.
Nearest legal neighbour to a shifted lookup is the unmodified full phase table.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Prefix`,
`Semantics.ScanHistoryPlanPrototype`.
Done: exact lists, order and index meanings, not only set cardinalities.

### T4b — prefix membership and publication/read boundary bridge

Files: CURRENT Prefix module and prototype plan test.
Symbols: T4a `prefix_phase_lists @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Prefix.lean`;
T3 `persistent_target`, `initial_target`, `recurrence_target`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Coverage.lean`;
CURRENT `Pub`, `Live`, `Cons`, `Mat @ leanncd/LeanNCD/Semantics/Plan/Syntax.lean`;
`plan_retList @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Plan.lean`.
NEW targets `prefix_membership`, `history_live_iff`, `group_targets_slice`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Prefix.lean`.

Three obligations: exact per-phase membership, group target/fibre characterization,
and H Live iff its publish command has completed at bounded pc.
Inputs are Live from zero; H(i,l) becomes Live at `3*(l+1)`, not after acc.
Pin: clone inputs-and-published-history row, read H immediately before/after pub
and test all previous-slice coordinates on vector donor before recurrence acc.
The legal neighbour is the next completed pub boundary, not a fallback zero.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Prefix`,
`Semantics.ScanHistoryPlanPrototype`.
Done: membership supports all four static side conditions and later retention.

### T5a — InitOK, AccOK and PubOK at their actual command indices

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`;
CURRENT prototype plan test.
Symbols: CURRENT `InitOK`, `AccOK`, `PubOK @ leanncd/LeanNCD/Semantics/Plan/Simulation.lean`;
T3 `plan_coverage1`, `plan_coverage2 @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Coverage.lean`;
T4 `prefix_membership @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Prefix.lean`.
NEW targets `plan_initOK`, `plan_accOK`, `plan_pubOK`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`.

Three obligations: fresh zero-init excludes every earlier consumed destination;
acc groups are Nodup, unconsumed and target materialized addresses;
pub blocks are fresh/materialized and every targeting occurrence is consumed.
Quantify over arbitrary pc and command lookup premises, reducing to phase indices.
Guard/tag proofs must establish all targeting occurrences, not just group members.
Pins: preserve `earlyPublish` rejection and the legal scalarPlan; clone group
donor changing persistent occurrences to initial occurrences without length change.
Record distinct coverage/publication effects, not a duplicated length assertion.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Validity`,
`Semantics.ScanHistoryPlanPrototype`.
Done: three genuine side-condition theorems, including empty groups/blocks.

### T5b — ReadyOK, full Valid and exact checker acceptance

Files: CURRENT scan Validity module and prototype plan test.
Symbols: CURRENT `recurrenceBody_footprint @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Operator.lean`;
`plan_layout`, `plan_singleton @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Plan.lean`;
`ReadyOK`, `Valid`, `checkPlan_iff @ leanncd/LeanNCD/Semantics/Plan/Validity.lean`;
T5a `plan_initOK`, `plan_accOK`, `plan_pubOK`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`.
NEW targets `plan_readyOK`, `plan_valid`, `plan_checkPlan`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`.

Three obligations: exact source-ID footprints are Live before every acc;
assemble all Valid fields including Coverage1/2, no-retire and all-boundary layout;
derive checker acceptance using existing exactness, not a new checker.
Persistent X is available every slice, Z only base, and each recurrence reads
the entire published predecessor. No positivity premise.
Pins: preserve full-prior-slice row and collapsedPlan rejection with independent
checkSteps/checkLayouts legs and legal scalarPlan. Audit unchanged SlotView,
checkLayouts, R and Decode callers as well as changed scan code.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Validity`,
`Semantics.ScanHistoryPlanPrototype`.
Done: generic `plan_valid` and checker true for all bounds, not only decidable fixtures.

### T6a — actual-prefix success and numerical retained values

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`;
CURRENT prototype plan test.
Symbols: CURRENT `R_start`, `readPub_eq @ leanncd/LeanNCD/Semantics/Plan/Memory.lean`;
`step_R @ leanncd/LeanNCD/Semantics/Plan/Simulation.lean`;
`step_not_stuck`, `run_R @ leanncd/LeanNCD/Semantics/Plan/Run.lean`;
`candidate_preserved @ leanncd/LeanNCD/Semantics/Soundness.lean`;
T2b `historyStore_models @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`;
T5b `plan_valid @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`.
NEW targets `prefix_done_R`, `history_retained`, `history_retained_later`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`.

Three obligations: every actual prefix succeeds and carries refState/R;
its published physical H values equal the independent model; later command
boundaries preserve each completed slice. State exact hypotheses as in §3.
Reuse candidate_preserved plus R.pubSlot/readPub_eq to get values, not ghosts.
Existing run_R is a suffix-to-terminal theorem: prove the required finite-prefix
bridge with step_R/refState, without pretending run_R already states it.
Use the original full plan's Valid with `runFrom ... (commands.take pc)` or
step_R/prefix induction; the truncated command list lacks full coverage, so
never assert that the truncated plan is Valid.
Model existence rules out semantic failure; step_not_stuck rules out stuck.
Respect step_R's refState and pre/post-layout hypotheses at every induction step.
Pins: retain scalar physical pc0..9 table; clone vector donor into an all-command
physical read table, keeping two unequal coordinates to detect partial retention.
Observe the new vector prefix table before claiming numeric expected values.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Correctness`,
`Semantics.ScanHistoryPlanPrototype`.
Done: all-command numerical retention, including during later init/acc, not just 3k.

### T6b — unconditional done, full Decode and independent denotation

Files: CURRENT scan Correctness module and both prototype tests.
Symbols: CURRENT `done_of_model`, `done_correct @ leanncd/LeanNCD/Semantics/Plan/Correctness.lean`;
`Decode`, `decode_of_R @ leanncd/LeanNCD/Semantics/Plan/Memory.lean`;
T2b `history_output @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Model.lean`;
T6a `prefix_done_R @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`.
NEW targets `scan_done`, `scan_decode_history`, `scan_denotation_history`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`.

Three obligations: unconditional completion at `3*(N+1)` for every validated η;
full successful Decode at shape `(d,N+1)` equal to independent history;
public semantic/denotation corollary from the actual independent model.
An assumed-done corollary may supplement but never replace unconditional done.
Keep the oracle recurrence independent of Program, plan, executor and decoder.
Pins: scalar and cross/nonlinear whole-history equality; zero-transitions and
empty-history successful Decode as output functions, not just vacuous cells.
Full-history omission must be detectable even if the final state is correct.
Build: `LeanNCD.Semantics.Plan.ScanHistory.Correctness`,
`Semantics.ScanHistoryRecurrencePrototype`, `Semantics.ScanHistoryPlanPrototype`.
Done: all generic contracts in §3, no remaining core certification obligations.

### T7a — test discovery names and final theorem-interface pins

Files: RENAME CURRENT prototype tests to NEW
`leanncd/test/Semantics/PlanScanHistoryOracleTest.lean` and
`leanncd/test/Semantics/PlanScanHistoryTest.lean`; CURRENT `leanncd/lakefile.toml`.
Symbols: CURRENT `trace @ leanncd/test/Semantics/ScanHistoryRecurrencePrototype.lean`;
`registry`, `registered`, `decoded @ leanncd/test/Semantics/ScanHistoryPlanPrototype.lean`;
T6 `scan_done`, `scan_decode_history`, `scan_denotation_history`
@ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`.

Three obligations: rename files/module imports and lakefile targets so Plan*Test
discovers both; preserve existing row labels/expected outputs and oracle separation;
pin final generic theorem hypotheses with arbitrary registry/carrier/bounds/input.
Rename Prototype namespaces consistently or retain with a documented reason;
do not needlessly change row locators used by mutation expectations.
Pins quantify over AddCommMonoid V and arbitrary ops/r/f/η, instantiate at empty
bounds, and identify output shape. No `N=2` or `η=input...` hidden premise.
These proof-interface pins are PLANNED, not already compiled examples.
Build: `Semantics.PlanScanHistoryOracleTest`, `Semantics.PlanScanHistoryTest`.
Done: old prototype registrations removed; new targets compile; measured counts
include all new assertions, not an assumed final total of 385.

### T7b — final regression and measured mutation contract

Files: CURRENT final scan test modules; controller-owned CURRENT-or-PENDING
`papers/semantics/plan_layer_slice5_mutations_post.json` and results/evidence.
Symbols: CURRENT `validateInput @ leanncd/LeanNCD/Semantics/Plan/Step.lean`;
`registry`, `registered`, `scalarPrefix`, `collapsedPlan`
@ `leanncd/test/Semantics/PlanScanHistoryTest.lean`;
`trace @ leanncd/test/Semantics/PlanScanHistoryOracleTest.lean`;
`scan_done @ leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`.

Three additional planned regression shapes: tensor-level input-role rejection with
nearest accepted bindings, including empty X/Z; combined d=0,N=0 and a different
nonempty bound chosen/observed by implementer; equality-transport/selected-operator
variant in a genuinely mixed existing registry with an unused operator of
different arity **and** type. The prototype Bool registry's two operators are
both unary at the same shape and do not yet discriminate this requirement.
Clone `registry`/`registered`, vary the unused branch to a different arity and
scalar/array signature, retain certified selected F and its independent trace.
Clone named donors for the other shapes, change one
field, retain exact neighbours. No unobserved numeric expected values ship.
Only selected F needs the certificate; unrelated registry entries remain unrestricted.

Controller closes the §3/§6 requirement-to-fixture-to-control map. Every claimed
regression/parity guarantee must have a measured mutant; proof kill alone is
not evidence of a numerical fixture kill hidden behind that proof.
Keep exact unique old/new strings and expected failure anchors from actual logs.
Do not invent diagnostic locations, infer restoration, or treat setup refusal as kill.
After renaming, mechanically update existing manifest file/module references,
run unfiltered --check, execute selected cycles, and record byte-identical restores.
If new certification makes an existing semantic mutant fail earlier in a proof,
remeasure its expected anchor and classify that kill honestly; retain separate
observed fixture evidence rather than falsely claiming the old row was reached.
Future proof controls are measured after those proofs exist; prebuilt prototype
cycles cannot establish generic certification. Parent's final manifest is truth.
Build: `Semantics.PlanScanHistoryOracleTest`, `Semantics.PlanScanHistoryTest`;
controller mutation wrapper for final manifest.
Done: every planned requirement has evidence or a reported load-bearing blocker;
no silent fixture/control omission, no guessed mutation totals.

### T8 — public discoverability and bounded documentation sweep

Files: NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory.lean` umbrella;
CURRENT `leanncd/LeanNCD/Semantics/Plan.lean`, final scan test,
`papers/semantics/tensor_logic_semantics.md`,
`papers/semantics/lean_executable_semantics_path.md`,
`leanncd/AGENTS.md`, `leanncd/LeanNCD/Semantics/AGENTS.md`,
`leanncd/LeanNCD/Semantics/Plan/AGENTS.md`;
OPTIONAL NEW `leanncd/LeanNCD/Semantics/Plan/ScanHistory/AGENTS.md`.
Symbols: CURRENT public Plan imports @ `leanncd/LeanNCD/Semantics/Plan.lean`;
`scan_decode_history` TARGET @ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Correctness.lean`;
`plan_checkPlan` TARGET @ `leanncd/LeanNCD/Semantics/Plan/ScanHistory/Validity.lean`.

Three obligations: safe umbrella import reaches certification from
`import LeanNCD.Semantics.Plan` and `import LeanNCD`; compile a public-import-only
theorem pin through registered test targets; sweep formalization-status passages,
proof-table rows and intent-layer discovery links without changing the math.
No fake Lean fences; public-import tests must compile their exact source.
Hook sections Pitfalls/Checks/Patterns/Context must each node total ≤ approximately
3k characters before edits; remeasure and trim only if over. Authoring measured
Plan node 2104 characters; zero named hook sections in the other two nodes.
Any new ScanHistory node obeys the same budget.

Run these commands with the literal implementation worktree prefix:

```bash
rg -n 'scan|Scan|slice-4|slices 1-4|367|186|181|385|8804' <worktree>/papers/semantics/tensor_logic_semantics.md <worktree>/papers/semantics/lean_executable_semantics_path.md <worktree>/leanncd/AGENTS.md <worktree>/leanncd/LeanNCD/Semantics/AGENTS.md <worktree>/leanncd/LeanNCD/Semantics/Plan/AGENTS.md
rg -n '367|186|181|385|8804|187|26' <worktree>/papers <worktree>/docs <worktree>/leanncd --glob '*.md'
rg -n 'ScanHistory|scan_decode_history|plan_checkPlan' <worktree>/leanncd/LeanNCD/Semantics/Plan.lean <worktree>/leanncd/LeanNCD/Semantics/Plan/ScanHistory --glob '*.lean'
```

Sweep the new ScanHistory node too if created. Historical records retain their
dated values; change current inventory/status, not history or recurrence.
Avoid promising general scans, partial F or in-place/reuse certification.
Build: `LeanNCD`, `Semantics.PlanScanHistoryOracleTest`,
`Semantics.PlanScanHistoryTest`.
Done: ordinary public import can name final theorems, status prose is accurate,
actual final inventories—not prototype job/constant counts—are cited.

### T9 — two execution reviews, controller gates and local integration

Files: complete whole-slice diff from base, final record and actual artifact set.
Symbols: all T1–T8 public theorem targets and unchanged siblings in §3.
No implementation dispatch; separate final review lenses, each bounded at 40
turns / 250k context and given exact task sections and 40–60-line windows.
Review findings go incrementally into controller-designated artifact paths.

Soundness lens: source equations, arbitrary selected registry casts, actual η,
coverage, every Valid field, prefix R/refState, physical numerical retention,
unconditional totality and successful empty/full output Decode.
Fidelity lens: full-history versus last-state output; persistent X/Z placement;
internal array shape and bounds; independent rational oracles; all-phase indices;
alias/early-pub neighbours; public exposure, docs, replay and mutation provenance.
Both inspect the whole branch and unchanged sibling contracts, not just the
last task diff. Reject scalar-only, successful-run-only or completion-only substitutes.
Adjudicate every finding; one bounded fix dispatch per related finding group,
then focused re-review plus gate reruns. Real unfixable load-bearing findings stop.

The controller itself runs the full wrapper build and **real**, unfiltered final
manifest, not merely --check or an agent's green report. Record exact commands,
logs, selected cycle count, intended failures, byte restores, restored passes,
fixture recount and standard-axiom audit. Allowed axioms only `propext`,
`Classical.choice`, `Quot.sound`; scan/public pins must have no admissions.
Audit the complete scan namespace plus both final test namespaces; record actual
counts. Scan for forbidden admissions/axioms and unintended scope tokens.
Four existing sorry warnings outside Plan are historical, not permission to add one.

```bash
bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd
bash <worktree>/leanncd/scripts/mutation-manifest.sh --out <worktree>/papers/semantics/plan_layer_slice5_artifacts/final_mutation_results.md <worktree>/leanncd <worktree>/papers/semantics/plan_layer_slice5_mutations_post.json
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|sorryAx|^\s*axiom\b|unsafe|implemented_by' <worktree>/leanncd/LeanNCD/Semantics/Plan/ScanHistory --glob '*.lean'
```

Also scan the umbrella/final tests and inspect the complete diff for unintended
retire/reuse/fusion/relocation/float/source-adapter changes; references in docs
are not by themselves forbidden implementation. A post-mutation final full build
must be green. Record per-task commits, reviewer adjudications and budget data.
Only then merge to local main, delete this execution branch and remove its
worktree safely; identify untracked evidence before cleanup. Do not remove the
separate author's checkout or unrelated worktrees. Do not push; report local
main ahead of origin. Completion is persistent accepted code plus recorded gates.

## 5. Stop and acceptance policy

Each task commits only its explicit paths after its targeted build and local
checks; controller reviews acceptance before dependants proceed. Mutation
commands remain controller-owned. No production edit belongs to the authoring
dispatch. Retain reproducibility artifacts and accepted commits.
If casts or list fibres are difficult, simplify with a proved equivalence,
not a new semantic contract. Real blocked tasks stop with exact evidence.
Documentation, public wiring, final review, full build and local integration
are required tasks, not parked follow-up.

## 6. Fixture donors and observation boundary

Observed at prototype `94cc67c9`, not promises of future measurements:

| Donor / existing row | Observed result | Nearest legal neighbour / use |
|---|---|---|
| `scan-oracle-scalar-full-history`, scalar executor | `[[5],[12],[26]]`, done pc9 | same X=2,Z=3,F=double; preserve independent oracle |
| vector oracle/executor-vs-oracle | `[[4,7],[16,30],[63,482]]`, done pc9 | X=[1,2],Z=[3,5],crossNonlinear; two-coordinate witnesses |
| no-transitions oracle/executor | `[[5]]`, done pc3 | same scalar inputs,F; N=0 |
| empty-state/empty-history | `[[],[],[]]`, done pc9; three capacity-zero buffers | d=0,N=2; tensor-level roles still checked |
| whole-prior-slice footprint | UID12 at coordinates `[0,0]`,`[1,0]` | unmodified complete vector prior slice |
| retained-prefix-memory | exact physical table pc0..9 in prototype source | preserve table; vector table is NEW/unobserved |
| inputs-and-published-history | X=2,Z=3,H=[5,12,26] through readPub at pc9 | input/read roles separated from output projection |
| early-publication-rejected | steps=false, layouts=true, plan=false | scalarPlan checker=true |
| history-alias-rejected | steps=true, layouts=false, plan=false | independent allocation/scalarPlan checker=true |
| unchecked-alias-corrupts-history | done pc9, `[2,2,2]` | same commands with independent buffers |

Exact oracle source is `ScanHistoryRecurrencePrototype.trace` using only independent
history; do not replace it by Program collect, runPlan or Decode.
The selected-op donor registry has another identity operator. Changing selected
operator, or same-size persistent occurrence IDs, must remain distinguishable
even if arity, shapes and group lengths still match.

Four prototype cycles are already observed and restored byte-identically:
scalar oracle double→identity (`[[5],[7],[9]]`); swapped cross-oracle input
(`[[4,7],[19,30],[80,572]]`); selected identity operator (scalar `[5,7,9]`);
same-size persistent-X→initial-Z occurrences (scalar `[12,12,24]`).
Exact substitutions and failure anchors belong to the parent-measured final
manifest/evidence, not hand-written plan instructions. Additional parent controls
are recorded separately when delivered. The delivered manifest currently has
eleven T0 entries: three independent-oracle controls, five fixture controls and
three actual implementation mutations: persistent occurrence selection,
successor-time destination, and the initial-Z guard.
Controller confirmed unfiltered --check on all eleven unique entries and actual
anchored 11/11 PASS with all 38 observed failure-site expectations, byte-identical
restoration and restored builds green. Display/data/negative-neighbour controls are not
semantic implementation mutants; do not advertise eleven production mutants.
The successor-time mutant corrupts already published history; the widened-Z-guard
mutant can leave computed values unchanged while invalidating coverage/order.
Together they pin source fidelity beyond group lengths and value-only comparison.
`authoring_evidence.json` maps all 14 prototype evaluated rows to observed
mutation discrimination. A row kill does not pin every field within that row
or future generic proofs. T7b measures remaining execution coverage.
Future transport, mixed-registry, model, phase, vector-prefix, combined-zero, input-role and
public-import pins above are **PLANNED**; do not claim they already compile or
publish numeric expectations before implementation observes them.
