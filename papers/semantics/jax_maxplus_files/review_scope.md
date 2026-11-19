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

## Coverage amendment — independent final package/execution/scope review

Review in progress. This amendment review preserves the original review above; its historical
clean verdict is not renewed signoff. Numerical/oracle discrimination belongs to the independent
numerical reviewer. Pending review readiness is intentional, not a finding.

Initial checkpoint: inspected package metadata, T2/T3/T4 cumulative maps, verifier implementation
and opening live-plan contract. They declare three provided manifests, sequential T1–T4,
4/7/7/15 cumulative entries and 3/4/3/8 touched paths; T3 alone introduces the gradient manifest
execution. Validation below will distinguish these declarations from mechanically checked facts.
Only this report is edited; no production replay, builds, pools, installation or nested agents.

Mechanical checkpoint: task-0 verifier exited 0: “Package OK: 4 ordered patches, 3 provided
manifests, task 0 boundary; index unchanged.” Scratch was explicitly kept inside this worktree.
An independent stdlib-only asset check also passed strict ordered private-index replay with
`git apply --cached --check --whitespace=error-all` followed by cached application. All three
provided manifests were seeded before T1 and absent from every patch's changed paths. Header,
actual changed-path and task-list sets agree exactly; snapshots are 4/7/7/15, touched paths
3/4/3/8. All approved SHA256/blob pairs and baseline provenance agree, including unchanged
affected source on planning-descendant HEAD/main. Main remains
`d7ac2640cdb37fbb64403337c9ee87bfa51b6726`; T1/core/renderer/runtime/runner bytes match the
original reviewed package.

Kernel 18 and gradient 8 entries have valid singleton precision pairs, nonempty diagnostics and
unique anchors at their intended boundaries; replacement Python parses without executing it.
Kernel anchors also remain valid after T3. The complete six-manifest pool has 53 entries / 40
intents, not 53 total physical executions. Both documents have clean whitespace, balanced
fences, no Lean snippets/source-line citations and resolving relative links (23/20); live plan
630 lines, record 291. Unified-diff context-space markers were preserved, not stripped.

### Amendment verdict: CLEAN — no load-bearing package/execution/scope finding

- T2 explicitly generates checked-only standard bundles and runs only kernel 18. T3 first
  regenerates full bundles, repeats kernel 18, then runs the separate gradient 8. The shared
  mutation runner has no task selector and still aggregates grouped statuses with OR; singleton
  `runs` entries isolate every new precision gate without claiming inherited grouped precision
  certification. Original SCOPE-01 negative-survival evidence is retained, not newly executed.
- Controller summaries match every current singleton label: T2 kernel 18, T3 kernel 18,
  gradient observe 8 and strict 8. Runner summaries support 52 checked / 44 refusals /
  56 source views and five AD points with 40 gradient / 40 point-forward views; point counts
  are not deployment counts, and baseline/permutation overlap is explicit. Numerical correctness
  and witness discrimination remain the numerical reviewer's responsibility.
- Comparing all final approved hashes with the original package leaves exactly three changed
  outputs: the max-plus Lean fixture, its Python verifier and bridge README. Original logic
  integration, runtime/core/renderer, runner and every legacy repin remain byte-identical.
  `controller_results.json` is unchanged. Its operator/legacy proof is explicitly retained;
  no amendment rerun of the inherited 25 controls is claimed. Original clean reviews are
  historical, not renewed signoff.
- Entire tracked `leanncd` content agrees with the source baseline at HEAD and in the working
  tree; no untracked nonignored implementation files are present there. Task-0 independently
  confirms the three future production files absent and affected sources/docs/legacy manifests
  restored. Main's planning-descendant identity is unchanged. No Boolean support or current
  implementation authorization was added.
- Portable manifests, patches, snapshots and compact reports suffice for execution. Archived
  host-specific commands/log paths are historical provenance, not required inputs; none were
  opened or run here. Live instructions provide worktree-relative assets and interpreter setup,
  prohibit patch/manifests improvisation and block execution until renewed signoff.

Non-blocking wording nit: `authoring_evidence.json` → `tasks[T2].scope` still says “ten checked
witnesses”; its adjacent `fixtures`, authoritative counts and live plan correctly specify 13
(11 assignments + 2 scans). This stale summary does not alter task acceptance or readiness.

### Commands, limitations and budget

Observed exit 0 for:

1. `env TMPDIR=<absolute-review-worktree> python3 <absolute-review-worktree>/papers/semantics/jax_maxplus_files/verify_package.py --task 0`.
2. Independent inline stdlib asset validation: baseline/approved Git blobs, ancestry/main identity,
   strict whitespace private-index replay, seeded assets, exact changed paths, singleton schemas
   and anchors, replacement syntax, JSON, counts, document links/fences/whitespace.
3. Independent metadata/proof-reuse check: original controller byte identity, all amendment
   singleton summary labels, approved-output differences and complete restored `leanncd` boundary.
4. Explicit-path `git diff --check` over the changed tracked non-patch package/doc/report assets.

No source execution, builds, pools, dependency installation, fixture/manifest mutation, staging,
commits or agents were performed. Private-index replay never touched the real index or applied
implementation to the working tree; review scratch was removed automatically. Recorded controller
runtime/build results were inspected as supplied evidence, not freshly reproduced.

Original Stage A's known 45-turn-cap breach and the corrective prose writer's >12-turn breach
remain disclosed. Exact telemetry remains unavailable; skeptical point 4 is not claimed solved.
This review stayed below 18 turns, with no known 100k peak-context breach; exact token/context
telemetry is unavailable. Only this report was edited. Pending controller readiness close-out
after both renewed reviews is expected, not a defect or authorization to implement.
