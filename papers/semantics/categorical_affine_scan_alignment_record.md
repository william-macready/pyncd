# Certified affine-scan alignment: evidence and execution record

## Current state

| Phase | State |
|---|---|
| AUTHORING(a): prototype and observations | Verified in current authoritative evidence |
| AUTHORING(b): fresh-context plan/record | Complete; controller verified the plan and bound the clean replay path |
| Clean ordered task execution | DONE: nine patches replayed, hash-verified and committed on `agents/categorical-affine-scan-alignment-execution` |
| Final controller unfiltered replay/audits/full build | DONE: 34/34 controls, namespace audit (868 constants), full build green (see "Execution record") |
| Two final whole-branch review lenses | DONE: no Critical findings; one Important finding fixed after replay; minors adjudicated |
| Local main integration and owned cleanup | See the last section of this record; no push |

The sections up to "Pending execution ledger" are the authoring record, kept as written; the "Execution record" section at the end is the controller's account of execution. The [plan](categorical_affine_scan_alignment_plan.md)
is the single live slice plan. Root/controller owns execution and release gates.
No implementation source, live documentation/configuration, builds, mutations, commits or agents
were changed/run by AUTHORING(b); only the explicitly requested plan and this record were written.

## Frozen authorities

- [Handoff](categorical_affine_scan_alignment_handoff.md): goal and required theorem strength.
- [Current authoring evidence](categorical_affine_scan_alignment_artifacts/authoring-evidence.json):
  measured prototype/build/audit/control facts; supersedes older BLOCKED/only-shift-closed receipts.
- [Package receipt](categorical_affine_scan_alignment_artifacts/package.json):
  base `13ee25a38366b2069c970754fa371f06d3f15ff9`, nine ordered patch hashes,
  nineteen exact final-file hashes and `ordered_private_index_replay: PASS`.
- [Canonical manifest](categorical_affine_scan_alignment_mutations.json):
  34 final controls, 53 expected strings copied from actual observed failures.
  SHA-256: `8bb0ab94b611e39eb444690ddddce4e516ea28d42e28a215ec47361af99d9f25`.
- `package.py` in the artifact directory mechanically reuses the existing
  `categorical_operational_associativity_artifacts/package.py` generator.
  Its invocation writes artifacts; AUTHORING(b) did not regenerate them.

Ordered patches: `admission.patch`, `component.patch`, `access.patch`, `history.patch`,
`interpretation.patch`, `compiler.patch`, `mixed.patch`, `acceptance.patch`, `documentation.patch`.
Sixteen Lean modules + `lakefile.toml` + two documents = nineteen final-file hashes.
Per-module registration lines preserve the existing globs prefix and make sequential replay valid.
The canonical manifest is carried by the authoring package, not the documentation patch.

## Prototype evidence already observed

The following are root/prototype observations from `authoring-evidence.json`, not builds rerun by the drafter.

| Check | Recorded result |
|---|---|
| `LeanNCD Tests IndexedExecutionExperiment` | Exit 0; 8980 jobs |
| `IndexedAffineScanNamespaceAudit` | Exit 0; 8673 jobs; all 861 new namespace constants audited |
| Allowed axiom closure | Only `propext`, `Classical.choice`, `Quot.sound` |
| Mixed compiler certificate + compiler-history validation | Exit 0; 8671 jobs |
| Closed actual compiler donors | 9 |
| Exact rational whole-history fixture rows | 8 |
| Ordered private-index replay | PASS for all 9 patches and 19 final files |
| All new source audit | No forbidden axiom/constant declarations, sorry/admit/native shortcuts, user paths or diagnostic file writes |
| Canonical unfiltered manifest `--check` | PASS: 34 entries, every old string unique |

Logs are in the root session evidence directory
`/Users/williammacready/.copilot/session-state/e2dbdb15-50e4-4dbf-8586-f7192af11182/files`:
`affine-prototype-full-build.log`, `affine-full-namespace-audit.log`,
`affine-compiler-history-validation.log`.
The 807-second first `IndexedAffineScanCompilerCertificates` compilation was cold project work
with warm Mathlib, not a thirteen-minute cold-Mathlib build. Cached stages were fast;
warm-cache preparation and project-olean refresh remain mandatory for execution.

### What the prototype proves

The bridge consumes actual affine/read/raw/checked scan tables, checker origin, actual basis
positions and capture-slot/signature associations. It constructs admitted padded reads, ordered
factor/term footprints, a finite semantic `program`, graph/closure, `sourceMatch`,
`rankCertificate` and `component`. Matching and rank are not assumed as extra premises.

`History.models_iff_recurrence`, `exists_unique_whole_history`, `wholeStore_base` and
`wholeStore_successor` @ `leanncd/experiments/indexed_execution/IndexedAffineScanHistory.lean`
provide same-table exact rational whole-history/model meaning and unique full stores.
`Interpretation.default_full_history` and `categorical_whole_history`
@ `leanncd/experiments/indexed_execution/IndexedAffineScanInterpretation.lean`
connect actual default semantic runners, their full stores and the existing categorical comparison.
`CompilerHistoryTest.certified_examples_full_meaning`
@ `leanncd/experiments/indexed_execution/IndexedAffineScanHistoryCompilerTest.lean`
retains these consequences for the nine closed actual compiler donors, rather than only numeric parity.

The profile is one spatial axis/one advancing clock, `H[i,t]`, history `[d,n+1]`,
identity-assignment external base, canonical complete successor writes, f64 real sum/product
metadata, arbitrary integer-affine spatial/external rows and own-clock `t-k`, `k≥0`.
Actual zero-spatial/zero-recurrence compiler certificates are inhabited and retain empty-port metadata.
No source UID reconstruction, checker/general-admission change, or new administrative wires is claimed.
No Float `runDenseScan` correctness, universal parser/compiler theorem, general St/Br functor,
arbitrary temporal reindexing/prefix law or finite padded-gather fusion is proved.
Masks/casts/reductions/nonlinear/partial primitives and scratch chains remain excluded.

### Mutation evidence and classification

| Task ID | Runtime observations | Implementation live proofs | Live-proof oracles | Total | Expected anchors |
|---|---:|---:|---:|---:|---:|
| admission | 2 | 0 | 0 | 2 | 2 |
| component | 0 | 3 | 0 | 3 | 9 |
| access | 5 | 0 | 1 | 6 | 7 |
| history | 0 | 3 | 1 | 4 | 11 |
| interpretation | 0 | 2 | 1 | 3 | 8 |
| compiler | 8 | 0 | 0 | 8 | 8 |
| mixed | 0 | 0 | 0 | 0 | 0 |
| acceptance | 8 | 0 | 0 | 8 | 8 |
| documentation | 0 | 0 | 0 | 0 | 0 |
| **Total** | **23** | **8** | **3** | **34** | **53** |

Every final candidate was actually observed to fail its mutated build, restore byte-identically
and pass the restored build in authoring. Some controls fail live proofs/types and are classified
accordingly; setup refusal does not count. This is not a claim of 34 runtime-core defect kills.
The final controller's **unfiltered intended-diagnostic replay is still PENDING**.

There were 35 exploratory cycles. One retired source-factor-order mutation altered capture
numbering and failed earlier capture metadata; it was replaced, not added to the final count.
The replacement reverses semantic `orderedProduct` traversal without changing compiler tables,
capture metadata or commutative rational values. The non-palindromic second mixed term makes
the exact ordered footprint discriminate the semantic defect.
Authoring logs: `affine-authoring-access-mutations.log`, `affine-authoring-remaining-mutations.log`,
`affine-authoring-order-mutation.log` in the session evidence directory above.

Eight independent history rows cover shift, stride, reversal, mixed, deep, zero recurrence,
empty spatial and both zero. The ninth certified donor is the ordinary `(2,2)` boundary donor,
not an extra rational-history row. Empty-case mutations protect metadata despite no coordinates.
Wrong-map/basis/multiplicity controls distinguish full histories; equal-valued factor reordering
is caught by footprints. Padded zero followed by a missing in-bounds demand stays strict failure;
all-padded actual factors succeed with zero.

## Fresh-context AUTHORING(b) checks

Performed deterministic read-only checks against the package and current files without opening live
Lean proof sources for exploration:

- Base and nine-patch order agree across authoritative inputs.
- All nine patch byte hashes match `package.json`.
- All nineteen prototype final-file byte hashes match `package.json`.
- Canonical manifest SHA-256 matches `authoring-evidence.json`.
- Manifest has 34 unique labels, 53 nonempty expected-anchor strings and valid task IDs;
  every old replacement string occurs exactly once in its target, and old/new differ.
- Class totals and per-task cycle/anchor counts agree with the current evidence.
- Inspected frozen patch imports, public symbols, fixture assertions and documentation deltas
  in bounded windows to establish file lists, code prerequisites and replay-only prerequisites.

These checks do not rerun Lean, mutation failures, private-index replay, or final release review.
No unresolved package/hash/schema defect was found in these checks.
Controller review verified the plan prose, patch/task prerequisites, classifications and
controller commands against the artifacts. The execution path
`/Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution`
and branch `agents/categorical-affine-scan-alignment-execution` were both unused when checked.
All nine patch hashes, nineteen source hashes and the canonical manifest hash still matched.
The plan contains no transcribed Lean blocks. The authoring-only commit is the next operation;
clean execution and all final gates remain pending.

## Budget and delay disclosure

As of **2026-11-12T21:10:54.247Z**, deduplicated recorded Copilot SDK `session.usage_record`
telemetry reports:

| Measurement | Recorded value / interpretation |
|---|---|
| CLI input tokens | **174,907,950**; cache tokens already included, do not add them again |
| Peak prompt context | **425,440** |
| Authoring target | 50M cumulative input — **exceeded** |
| Approximate context guideline | 250k — **exceeded** |
| Dispatch/turn stop limits | Explicitly waived by user; waiver does not erase the overruns |
| External Claude Code usage | Unavailable and **excluded** from these SDK totals |
| Prescribed `token-report.py` | No transcript available; SDK totals are partial alternative telemetry |

Delay included a long compiler-proof attempt, a failed worker and an unbounded diagnostic.
Recovery used the mixed proof completed by the separately user-assigned Claude Code actor;
root independently validated that contribution. Preserve its source and credit; do not attribute
its unavailable usage to measured CLI totals or invent a quantitative delay/token breakdown.
The later snapshot for this writing dispatch is not measured here.

Execution-only accounting starts separately against the 175M execution budget.
The existing cumulative authoring figure does not show that execution passed its cap.
Controller must append actual execution telemetry and disclose missing data/overruns.

## Pending execution ledger

| Milestone | Required receipt | Current state |
|---|---|---|
| Freeze authoring | Controller plan/record review; authoring-only package commit; absolute replay-path binding | Verified and bound; commit next |
| Preserve prototype | Owned persistent preservation, including external mixed proof; nineteen hashes | PENDING controller receipt |
| Prepare clean execution | Frozen base + authoring package; warm Mathlib; refreshed `LeanNCD`; unrelated main/JAX changes preserved | PENDING |
| Tasks 1–3 | Patch checks, targeted builds, source hashes, task controls/spec reviews/commits | PENDING |
| Tasks 4–5 | Generic recurrence/full-store/category checks and task controls/reviews/commits | PENDING |
| Tasks 6–8 | Actual compiler certificates, all history rows, namespace target and task controls/reviews/commits | PENDING |
| Task 9 | Documentation sweep, all nineteen final hashes, explicit-path commit | PENDING |
| Controller canonical replay | Unfiltered `--check` and all 34 cycles / 53 anchors; byte restoration and restored-green results | PENDING |
| Source/namespace audits | All sixteen sources, complete new namespace, standard-only axiom closure | PENDING |
| Final review lens 1 | Admission/footprint/rank/match/whole-model/full-store/category soundness | PENDING |
| Final review lens 2 | Actual checked/compiler tables, policies/order/zero cases and exact-arithmetic boundary | PENDING |
| Controller full build | `LeanNCD Tests IndexedExecutionExperiment` through prescribed wrapper | PENDING |
| Local integration | Preserve concurrent main, validate combined tree, merge locally, clean only owned work; no push | PENDING |

Append execution commits, hashes, generated mutation results, review findings/adjudications, controller
build receipt, execution-only usage and local merge/cleanup status here as they actually occur.
Never replace this record with a generated `--out` table or mark prototype evidence as controller execution.

## Execution record (controller)

Executed by Claude Code as controller after the authoring Copilot session stopped itself
(2026-11-12). Execution worktree: `/Users/williammacready/code/python/pyncd.worktrees/categorical-affine-scan-alignment-execution`,
branch `agents/categorical-affine-scan-alignment-execution`, created from the pinned authoring commit
`92822f3a` (local tag `affine-scan-alignment-authoring-package`, base `13ee25a3`, unchanged `main`).
No push.

### Replay (tasks 1 to 9)

Each patch's SHA-256 matched `package.json`, `git apply --check` and `git apply` succeeded in order, and every
newly introduced module matched its package hash. The implementation tree was byte-identical to the preserved
prototype. After task 9 the plan's check passed: 9 patch hashes, 19 final source hashes, canonical manifest hash.

| Task | Commit | Target built | Build time |
|---|---|---|---|
| 1 admission | `2506d59d` | `IndexedAffineScanPrototypeTest` (four boundary rows accepted) | 61 s |
| 2 component | `37daef1e` | `IndexedAffineScanRank` | 59 s |
| 3 access | `87a00d34` | `IndexedAffineScanAccessAgreement` | 32 s |
| 4 history | `4306d6d9` | `IndexedAffineScanHistory` | 32 s |
| 5 interpretation | `d8fba011` | `IndexedAffineScanSemantics`, `IndexedAffineScanHistoryTest` | 47 s |
| 6 compiler | `7fdcb719` | `IndexedAffineScanCompilerCertificates` | 814 s (genuine compile; no prototype artifacts were synced in) |
| 7 mixed | `877c01a2` | `IndexedAffineScanMixedCompilerCertificate` | 207 s |
| 8 acceptance | `9b560e33` | `IndexedAffineScanNamespaceAudit` (861 constants, standard axioms only) | 46 s |
| 9 documentation | `0b3bce82` | none (documentation sweeps run and adjudicated) | n/a |

Documentation sweeps: matches were the new documentation plus unrelated historical job counts and hex constants;
no stale "only shift closed" claim. The source sweep found no `axiom`, `constant`, `sorry`, `admit`, `native_decide`,
`ofReduceBool`, absolute user path or diagnostic file write in the sixteen `IndexedAffineScan*.lean` modules.

### Deviations from the plan, and why

- **Per-task filtered mutation checkpoints were not run.** Their coverage is a strict subset of the final unfiltered
  replay, which was run in full, and each module was built at its own task. This saved roughly three hours of builds.
- **Per-task spec reviews were replaced by the two final whole-branch reviews**, run before the mutation gate so a
  fix could not invalidate its evidence.
- **Concurrent controller.** On entry, a Copilot session was still live in the prototype worktree and running
  mutation cycles that edit sources in place. My reviewers read a clean snapshot while it ran; after it reported
  itself stopped, nothing else touched the tree. The earlier stuck `lake build` (PID 22665, over two hours) was
  stopped at the user's request, and the mixed certificate was unblocked by a general lemma
  (`inferAxisSizesCore_of_sized`), because `cbv` cannot evaluate diagnostic text (`Std.Format.be` is partial).
- **Post-replay adaptation.** Commit `fa961ae3` changes six frozen files after review (below). Their hashes therefore no
  longer equal `package.json`, which remains the original receipt and was not regenerated.
- The prototype's debug `IO.FS.writeFile` probes in `IndexedAffineScanCompilerCertificates.lean` had already been
  removed before the package was frozen, so the replayed files contain none.

### Final reviews (Fable)

Both reviewers read the committed tree read-only and ran nothing.

| Lens | Result |
|---|---|
| 1. Soundness: admission, bounds, padding, footprints, rank, match, whole model, full stores, category | No Critical or Important. Minors: profile admits a step capture of the history's own slot (see fix); Float boundary only in module docstrings; wording "empty-port"; one redundant conjunct (`Profile.lean`, `stateReadCausal #[1]` implied by `stateRowsOk`) |
| 2. Applicability: checked/compiler tables, policies, order, zero cases, Float boundary, mixed lemma | No Critical. One Important (same history-slot aliasing finding). Minors: `(2,2)` boundary donor has no pinned history; Float boundary not on the main theorems; 25 bare `#eval` lines and duplicate `#print axioms`; `contextPos = #[1]` arm unwitnessed by compiler donors |

Both reviewers confirmed the mixed-certificate lemma matches `inferAxisSizesCore`, that `mixed_inference_fst` is the
unweakened statement for both signature orderings, and that `mixed_inferred` keeps the real warning component.

**Fixed (`fa961ae3`).** The unchanged scan checker admits a step block whose state capture is retargeted to the
history's own outer slot as an external capture; the profile would then model the scan's own output as a free external
input. Demonstrated on the real shift donor: checker accepts, fixed profile returns `unsupported`. `capturesBounded`
now requires every external capture to avoid the history's own slot, `Profile.external_not_history` states it, a runtime
control in `IndexedAffineScanHistoryCompilerTest` checks the real-donor case, and the Float/`runDenseScan` boundary
is stated on `exists_unique_whole_history`, `default_full_history`, `categorical_whole_history` and
`certified_examples_full_meaning`. Documentation now says zero-extent history-port metadata and that all nine compiler
donors use the context-first term ordering (verified by printing every donor's term positions).
Changed files: `Profile`, `Rank`, `History`, `Interpretation`, `HistoryCompilerTest`, `AGENTS.md`, the synthesis document.

**Parked (not required by the goal).** Redundant `stateReadCausal` conjunct (harmless, ~0.5 dispatch); bare `#eval`
noise in `CompilerExamples` (editing it forces a 14-minute `CompilerCertificates` rebuild); `(2,2)` boundary history
row (the plan deliberately keeps it as the ninth certified donor, not a rational-history row); two `simpa` lint warnings at
`IndexedAffineScanCompilerCertificates.lean:194`.

### Controller gates

| Gate | Result |
|---|---|
| Full `LeanNCD Tests IndexedExecutionExperiment` build (after the fixes) | Exit 0, 8980 jobs, 1016 s. New control prints "history-slot alias controls passed" |
| Namespace audit `IndexedAffineScanNamespaceAudit` | 868 constants under `IndexedExecutionExperiment.AffineScan`, standard axioms only (861 at freeze, plus the 7 declarations added by `fa961ae3`) |
| Source hygiene sweep | No matches |
| Unfiltered manifest `--check` | 34 entries, 34 unique labels, 53 anchors, every old string unique, before and after the fixes |
| Unfiltered mutation replay (`mutation-manifest.sh`, no filters) | 34/34 PASS, 10,662 s; every expected anchor seen, byte-identical restores, restored builds green |
| Alias-guard cycle (added after the manifest was frozen, not in it) | Guard neutralised: build fails at `external_capture_checks` (`Rank.lean:18`) with `sorryAx` audit failure; restored byte-identically; restored build green. A live-proof control; the runtime control was demonstrated on the unmutated tree but not separately mutation-tested |

Classification is as authored: of the 34, 23 protect runtime observations, 8 protect live implementations through
proofs and 3 reverse logical oracles. They are not 34 runtime-core defect kills. Some live-proof diagnostics include
type/proof failures plus the namespace `sorryAx` rejection.

#### Mutation results table (generated by the wrapper)

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| AA-M1 rank-length omission live-proof control | yes | yes | yes | PASS |
| AA-M2 finite shift bias sign fixture delta | yes | yes | yes | PASS |
| AA-M3 nonzero padded read fixture delta | yes | yes | yes | PASS |
| AA-M4 ordered repeated read fixture delta | yes | yes | yes | PASS |
| AA-M5 flattened alias upper-bound neighbor fixture delta | yes | yes | yes | PASS |
| AA-M6 invalid finite padded inverse fusion fixture rewrite | yes | yes | yes | PASS |
| construction-writer-all-ordered-dependencies | yes | yes | yes | PASS |
| construction-actual-spatial-basis-not-zero | yes | yes | yes | PASS |
| construction-state-own-clock-not-spatial-column | yes | yes | yes | PASS |
| construction-canonical-base-time-zero | yes | yes | yes | PASS |
| construction-history-extent-includes-base-and-zero-boundaries | yes | yes | yes | PASS |
| construction-input-ports-include-actual-step-externals | yes | yes | yes | PASS |
| AH-M1 actual base spatial-coordinate shift | yes | yes | yes | PASS |
| AH-M2 actual successor clock off by one | yes | yes | yes | PASS |
| AH-M3 checked observation drops all nonfinal history slices | yes | yes | yes | PASS |
| AH-M4 strict zero-times-missing live-proof oracle reversal | yes | yes | yes | PASS |
| AH-M5 categorical witness image replaced by empty domain | yes | yes | yes | PASS |
| AH-M6 empty-spatial port erasure live-proof oracle reversal | yes | yes | yes | PASS |
| compiler-spatial-stride-coordinate | yes | yes | yes | PASS |
| compiler-mixed-context-basis-column | yes | yes | yes | PASS |
| compiler-deep-temporal-causality | yes | yes | yes | PASS |
| compiler-canonical-external-base-boundary | yes | yes | yes | PASS |
| compiler-ordered-product-footprint | yes | yes | yes | PASS |
| compiler-repeated-factor-multiplicity | yes | yes | yes | PASS |
| RH-M1 shift rational-history oracle | yes | yes | yes | PASS |
| RH-M2 stride rational-history oracle | yes | yes | yes | PASS |
| RH-M3 reversal rational-history oracle | yes | yes | yes | PASS |
| RH-M4 mixed rational-history oracle | yes | yes | yes | PASS |
| RH-M5 deep rational-history oracle | yes | yes | yes | PASS |
| RH-M6 zero-recurrence rational-history oracle | yes | yes | yes | PASS |
| RH-M7 empty-spatial metadata oracle | yes | yes | yes | PASS |
| RH-M8 empty-base metadata presence oracle | yes | yes | yes | PASS |
| CB-M7 semantic captured-clock look-ahead | yes | yes | yes | PASS |
| CB-M8 semantic nonzero padding | yes | yes | yes | PASS |

34/34 cycles passed.

### Execution accounting

`token-report.py` for the controller session (partial: it covers this Claude Code session, not the Copilot authoring
session, and counts cache-inclusive input) reported 36.0M cumulative input at the time of the gates: controller 31.9M,
review 1 1.8M, review 2 2.2M. Against the 175M execution budget this is within budget. Both review dispatches stayed
within 250k peak context (190k and 168k) and 60 turns (16 and 24). The controller session's peak was 419k, which
exceeds the roughly 250k guideline; it spanned the earlier proof work and the whole replay. The authoring overruns
disclosed above are unchanged.

### Addendum: output-first term-ordering control (post-merge)

Review lens 2 noted that no compiler donor exercises the output-first term ordering (`contextPos = #[1]`).
The compiler cannot produce it (`Compile.lean:800-801` fixes context positions first), so a probe built
output-first variants of the real compiled shift, mixed and deep donors (iteration shape `[d,n]`, coefficient
columns swapped, meaning unchanged). The unchanged checker accepts them, the profile accepts them, and the
exact-rational whole history is identical to the original on every coordinate. No defect was found.

This is now a build-time control, `IndexedAffineScanOutputFirstTest` (new module, registered in `lakefile.toml`
and imported by `IndexedAffineScanNamespaceAudit`). It checks that the flipped terms really are output-first
(non-vacuity), checker and profile acceptance, history equality with full coordinate count, and that a flip that
reorders positions but not coefficient columns is distinguished from the original. Evidence: audit target 882
constants under `IndexedExecutionExperiment.AffineScan` (868 plus the module's 14), standard axioms only;
`IndexedExecutionExperiment` library build green (8729 jobs).

Three manual `mutation-cycle.sh` cycles (not in the frozen manifest), each broke the build, restored
byte-identically and rebuilt green:

| Cycle | Mutation | Killed by |
|---|---|---|
| OF-M1 | `termSupported` drops the output-first allowance | Existing proof: `supported_basis` (`Construction.lean:158`) and the `sorryAx` audit |
| OF-M2 | `stateRowsOk` demands the context-first time row for output-first terms | Existing proof: `captured_state_earlier` (`Construction.lean:199`) and the `sorryAx` audit |
| OF-M3 | The control's flip leaves the coefficient columns alone (test-side) | The control itself: "the unchanged checker refused the output-first plan" |

The implementation mutations are caught by proofs before the runtime control runs, so the control adds an
end-to-end witness over real compiled plans rather than a new kill of those mutants. The sample is three donors,
not a proof for the arm in general (the proofs cover that). The control sits in its own module so these
cycles stayed in the minutes range rather than rebuilding `CompilerCertificates`.

