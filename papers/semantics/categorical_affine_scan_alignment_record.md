# Certified affine-scan alignment: evidence and execution record

## Current state

| Phase | State |
|---|---|
| AUTHORING(a): prototype and observations | Verified in current authoritative evidence |
| AUTHORING(b): fresh-context plan/record | Complete; controller verified the plan and bound the clean replay path |
| Clean ordered task execution | PENDING |
| Final controller unfiltered replay/audits/full build | PENDING |
| Two final whole-branch review lenses | PENDING |
| Local main integration and owned cleanup | PENDING; no push authorized |

This record is not a completion claim. The [plan](categorical_affine_scan_alignment_plan.md)
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
