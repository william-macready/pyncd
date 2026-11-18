# Independent scope/caller/package review

## P2 — SCOPE-01: grouped Python cycles do not establish twelve precision-specific kills

- **Location:** live plan §§6 and 9 (T2/final Python-manifest commands and acceptance);
  `02.patch` verifier diagnostics and `jax_maxplus_mutations_python.json`.
- **Concrete failure:** the immutable baseline `mutation_python_manifest.verify` ORs the exit
  statuses of all declared precision runs and concatenates their output. Its `main` accepts a
  control when that aggregate status is nonzero and the expected strings occur anywhere in the
  aggregate output. The new zero-init, freeze-time, signed-zero-max and custom-JVP controls have
  no precision-distinguishing expected diagnostics. Either precision can therefore survive while
  the displayed command still reports `PASS ... | killed | restored`. Successful execution of
  those commands cannot certify the plan's required twelve precision-specific kills, and the
  runner does not print the individual mutant outputs for the executor to inspect.
- **Minimal correction:** make the packaged execution protocol obtain and check a killed result
  with the intended diagnostic separately for each declared precision (and retain per-leg evidence),
  without ad-hoc execution-time manifest edits. Alternatively, explicitly narrow the acceptance and
  evidence claims to aggregate controls; do not infer twelve independent kills from six grouped
  `PASS` lines. This is a future execution-protocol finding, not a claim that the author's actual
  precision-specific observations failed or that the pending/readiness status was concealed.

Checkpoint: typed admission, signature revalidation, standalone/named/positional/scan routing,
strict candidate/evidence/scatter defaults, original logic-source reuse, manifest task ordering and
the finalized supplemental scan-Python anchor have been inspected through immutable patches and
baseline Git blobs. Numerical/gradient correctness is the sibling review's responsibility.

## Final verdict: changes required

One meaningful finding: **SCOPE-01**, limited to the precision-specific mutation acceptance
protocol/claims. No additional high-confidence scope, caller, packaging or dependency defect found.

Read-only package inspection confirmed all four patch hashes and snapshot hashes, both unchanged
provided-manifest hashes, exact patch-header/touched-file agreement, approved Git-blob SHA256
agreement, consistent baseline hashes and task-by-task changed-path agreement. Final T4 has eight
touched files and fifteen cumulative snapshot entries. The live plan is 516 lines. The supplied
controller result now reports both overall and supplemental scan-Python status `passed`, with six
inherited scan-Python controls and the preserved single-anchor `JS-P-05` repair.

The live draft's pending header, seven-file T4 table/prose and historical last-read readiness
paragraphs still need the parent-coordinated refresh already announced. These are disclosed
close-out items, **not additional readiness findings**. Readiness also awaits the sibling review
and adjudication of content findings. Stage A's known turn-cap breach and unavailable telemetry
are explicitly disclosed; the unrelated parked scatter anchor is not counted as a pass.

Limits: immutable patches, task snapshots/package artifacts and baseline Git blobs only; no
working feature-source review, builds, tests, mutations, commits or agents. The only written file
is this review. This review stayed within the requested turn budget; exact token/context telemetry
is unavailable, with no known context-budget breach.

## Final bounded follow-up — SCOPE-01 resolved; verdict clean

The revised provided Python manifest has twelve entries, each declaring exactly one precision:
the same six intents are independently gated for float64 and float32. Intended diagnostic strings
remain attached to each leg. This removes the aggregate-OR masking route identified in SCOPE-01
without changing the shared runner or production source.

Inspected `controller_results.json.precision_gate_review_fix`: observation and subsequent strict
execution each report all twelve labeled legs killed/restored with exit 0. The deliberate
float64-only broken cast reports `PASS CHECK-P-PRECISION-64`, then
`FAIL CHECK-P-PRECISION-32 | SURVIVED | restored`, with actual/expected exit 1. This is the required
closed-failure proof; clean-restoration evidence is retained.

Read-only hashing confirms both provided assets match refreshed package hashes and all four patch
and snapshot hashes still match the previously reviewed values. T4 remains eight touched paths /
fifteen cumulative snapshot entries. Refreshed plan/record distinguish twelve independent new
cycles, six underlying new intents, and the complete pool's 33 unique intents / 39 entries per
full-pool pass; inherited grouped checks are no longer misrepresented as independently gated
precision kills. The live plan is 543 lines; the record is 177.

**No unresolved scope/caller/package blocker remains.** This supersedes the earlier
changes-required verdict. Parent may finalize the disclosed proof/readiness header and stale
last-read proof-pending wording after both reviewers acknowledge; that announced close-out refresh
is not an additional finding. Numerical implementation bytes are unchanged, and this follow-up
does not reopen the sibling numerical review.

Follow-up limits honored: bounded read-only artifact inspection and this report-only append;
no builds, mutation execution, feature-source reads/edits or agents. No known budget breach.
