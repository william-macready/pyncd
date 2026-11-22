# JAX max-plus plan: authoring record

**Status: execution-ready plan; corrective controller verification and both renewed reviews complete. Implementation not started.**
This is the planning/authoring record, not the future implementation record
`papers/semantics/jax_maxplus_record.md`. No production changes have landed as part of this
write-up, and no implementation, commit, merge or push was performed by the prose author.
During original authoring the controller independently tested the prototype and restored every
temporary source, documentation and legacy-manifest edit. The separate corrective controller
pass is now recorded passed below. Only the plan package is delivered.

The original chronology below, including its clean reviews, counts, hashes and completed-readiness
wording, is retained as historical evidence. The corrective amendment appended at the end supersedes
those live-status claims; old clean reviews are not renewed coverage signoff.

## Scope and process

Full path: a new max-plus backend capability with a soundness-sensitive render-only policy.
One [live plan](jax_maxplus_plan.md), max-plus only. Boolean destinations/reachability execution,
min-plus, Iverson lowering, non-real scatter, traceback and executable evidence remain excluded.
The named/positional/standalone affine renderer and single-axis scans are the intended boundary.
The plan preserves explicit checked cast false as well as true, native ordered folds and the
custom zero-pair addition JVP; it does not claim general semiring laws or NaN-payload parity.

The source baseline is `c5000dd462d72ed0ffcd5806937aa37fa477e9b0`.
The planning branch is `agents/jax-maxplus-plan`; execution will require a new local-main worktree.
Layout only was borrowed from the opening of `jax_nonlin_plan.md` and the headings of
`jax_nonlin_plan_record.md`; their numbers, old scope and readiness were not inherited.

## Evidence read by the fresh prose author

- [package.json](jax_maxplus_files/package.json), authoritative four-patch/two-input package.
- [authoring_evidence.json](jax_maxplus_files/authoring_evidence.json), compact observed facts,
  scope matrix, donors, symbol map, counts, tooling and budget disclosures.
- [prerequisite_contract.json](jax_maxplus_files/prerequisite_contract.json), selected max-plus
  observations concerning folds, casts, OOB/unary reads, empties and scan state initialization.
- [task1.json](jax_maxplus_files/task1.json), [task2.json](jax_maxplus_files/task2.json),
  [task3.json](jax_maxplus_files/task3.json), [task4.json](jax_maxplus_files/task4.json):
  cumulative hashes; task file lists were taken from patch headers/package `touched_files`.
- Relevant bounded hunks of [01.patch](jax_maxplus_patches/01.patch),
  [02.patch](jax_maxplus_patches/02.patch), [03.patch](jax_maxplus_patches/03.patch) and
  [04.patch](jax_maxplus_patches/04.patch). No implementation was transcribed into the plan.
- [New Lean manifest](jax_maxplus_mutations_post.json),
  [new Python manifest](jax_maxplus_mutations_python.json), and bounded verifier/tooling inspection.
- [controller_results.json](jax_maxplus_files/controller_results.json), sampled while `running`.

No current source contents, transient source diffs/status, tests, builds or mutation executions
were used by the prose author. Directory/path checks are existence checks, not implementation
validation. Exact future new source paths come from `new file mode` headers in 02.patch.
Existing prototype file presence during controller work is not treated as baseline existence.

## Observations supplied by the prototype stages

These are artifact-reported observations, not fresh execution results from this write-up:

| Boundary | Observed |
|---|---|
| T1 | 2/2 strict Lean controls killed, expected tagged diagnostics, restored green |
| T2/T3 checked fixtures | 9 assignments + 1 scan, 40 precision/eager/JIT views |
| Metadata rejection | 44 precision/eager/JIT refusals |
| Original grouped Python controls | 6/6 aggregate controls killed/restored; not proof of twelve independent kills |
| Revised Python acceptance | 12/12 singleton-precision cycles for six intents; observe/strict passes and one-leg-survival rejection verified |
| Original Viterbi | 7 reused source variants, 56 precision/named/positional/eager/JIT views |
| Gradients | 8 precision/named/positional/eager/JIT views |
| Coupled legacy controls | Nonlinear 8/8 and scan 11/11 killed/restored green in Stage B |
| Normal verifier | Zero nested self-mutations |

The independently enumerated winning path is `(0,1,2,1,0,1)`, score `-5.25`, margin `0.25`.
Winning Init derivative is 1; Init/Trans/Emit gradients are exact path counts with Allow frozen
and the spare Emit row zero. The opposing-infinity false-source case is NaN, and the checked hole
history is `[[3,7,13,19],[-inf,11,17,23]]`.
The scalar/JVP pin kills removal of the custom JVP even when forward primal bits still pass.

No arbitrary NaN-payload preservation, max-tie/nonfinite derivative guarantee, full-corpus speed
claim or general checked/reference equivalence theorem follows from this evidence.

## Package collision found and corrected before drafting

Stage B mistakenly included new planning-manifest add-file diffs in implementation patches.
Replay against the bare source baseline passed but would collide after committing planning assets.
The controller removed only those add-file diffs and their source-snapshot entries; implementation
bytes did not change. Both manifests are now immutable **provided inputs**.

`verify_package.py` seeds a private index from the source baseline plus those provided inputs,
replays all four patches, verifies SHA256/blob snapshots and checks the requested working-tree
boundary without changing the real index. Source-baseline descendants with planning assets are
allowed only while affected source hashes match. No history rewrite or execution-time patch
regeneration is part of the solution.

The original Stage A/B raw evidence and intermediate snapshots are archived in the author session,
outside the repository package. They are provenance, not execution dependencies; no host-specific
archive paths are needed by the executor.

## Controller verification and readiness

The coordinated refresh read [controller_results.json](jax_maxplus_files/controller_results.json)
with both core `status` and `scan_python_followup_status` **passed**. Recorded controller passes:

- Complete max-plus runner; 40 checked views, 44 metadata refusals, 56 Viterbi views, 8 gradients.
- New Lean 2/2, historical grouped new Python 6/6, coupled nonlinear 8/8 and scan Lean 11/11
  aggregate controls killed/restored with byte-identical tracked-source restoration.
- Full LeanNCD/Tests/JaxExperiment build: 8847 jobs.
- Nonlinear 55 f64 / 47 f32 eager/JIT model/property/gradient fixtures.
- Curated affine: 20 fixtures (controller-confirmed count); scatter 10 f64 / 5 f32 bit-identical
  eager/JIT fixtures. No timing is invented.
- Supplemental inherited scan-Python 6/6 aggregate controls killed/restored; package task-0 passed,
  source/docs/legacy edits restored, and local main unchanged at the source baseline.

The directly coupled `JS-P-05` anchor now selects the unique step-count assignment rather than
assuming adjacent `steps`/`states` lines. Its original decrement, expected failure and one-step-too-few
intent are preserved. Other existing Python-manifest anchors retained baseline count one.
Final T4 has **8 touched files / 15 cumulative snapshots**, with 04.patch SHA256
`a788fbe33b2a518982f7551846fb66220c45d9a05ef5e32a856e6fdd757b8242`.
There remain exactly two provided manifest inputs; this inherited manifest is a patch output.

## Independent reviews and SCOPE-01 adjudication

- [Numerical / gradient / oracle review](jax_maxplus_files/review_numerics.md): **CLEAN**.
- [Scope / caller / package review](jax_maxplus_files/review_scope.md): initial P2
  **SCOPE-01** resolved; final verdict **CLEAN**, with no unresolved blocker.

SCOPE-01 identified an evidence gap, not an implementation numerical failure: the unchanged Python
mutation runner ORs grouped precision exit statuses and concatenates diagnostics. A kill in one
precision can mask survival in the other, so six grouped PASS lines cannot certify twelve
independently killed legs. Earlier prototype reports are not sufficient acceptance evidence.

The parent correction splits six new max-plus mutation intents into twelve immutable singleton-
precision manifest entries. Each listed cycle independently checks kill/diagnostic/restored green;
no source/harness change, patch regeneration or execution-time manifest edit is needed.
Only the provided Python-manifest SHA is refreshed through package.json/verifier authority, not
copied inline. All four implementation patches and source/task blobs remain unchanged.

The negative-control criterion is explicit: when only float64 fails, float64 PASS plus float32
SURVIVED/FAIL must give overall **exit 1**. Successful strict twelve-cycle evidence, that negative
control and clean restoration are recorded in `precision_gate_review_fix`.
The controller observed all twelve singleton entries pass in both observe and strict runs.
Its deliberately float64-only broken cast produced float64 PASS, float32 SURVIVED/FAIL and
overall exit 1. The final scope review confirmed the fix and package hashes; the numerical
review reaffirmed CLEAN because all implementation patch/source bytes remained unchanged.
Earlier fresh-author reads preceded this proof; this paragraph records the completed close-out.

The pool has **33 unique mutation intents / 39 manifest entries or listed cycles per complete pool
pass** (2 + 12 + 8 + 11 + 6). Repeated T2, T3 and final invocations add physical executions; 39 is
not a total of all commands/executions across phases. Inherited grouped manifests retain historical
aggregate semantics; no per-precision kill count is inferred from them. Only new singleton entries
certify precision legs independently. Parent/controller owns final readiness/signoff.

## Authoring budgets and limitations

- **Stage A explicitly reported exceeding its 45-turn cap.** This is a known breach, not merely
  unmeasured usage. Exact final turn/token/context totals are unavailable.
- Stage B self-reports within 35 turns/120k context. Exact token telemetry is unavailable.
- The authoring target is 50M cumulative input tokens; exact aggregate tokens/context are unavailable:
  the token-report path had no transcript to measure. No estimated total is substituted.
- The fresh prose dispatch has a 25-turn/100k-context bound; its own outcome is recorded below after
  document-only validation. No agents were launched by this dispatch.
- Future execution remains capped at 175M total, about 60 turns/250k peak per dispatch. Its record
  must disclose actual measurements or unavailable telemetry, and any breach explicitly.

## Parked issue and nonclaims

`JS-T1-04` in the preexisting scatter manifest has zero matching baseline anchors. It is unrelated
to required max-plus behavior, is not repaired or counted as a pass, and would take roughly one
separate bounded Direct dispatch (done 2026-11-22: main `a4552839`, `40b7af4a`; scatter manifest 6/6). T4 changes only
directly coupled nonlinear/scan Lean/Python repins.
No unrelated AGENTS trim was scheduled: recorded hook sections were under about 3k characters,
including the leanncd pre-edit measurement of 2951.

## Document-only validation

The coordinated document-only refresh found all 37 relative links resolving, no trailing whitespace,
balanced fences and no numerical Lean line citations. `/bin/ls -d` verified referenced existing
artifacts, source locations, runners, wrappers and skill paths without reading transient source.
The three absent implementation paths exactly match 02.patch add-file headers; they are labeled
new files in the plan. The future execution record is explicitly labeled future, not existing.
Task dependencies are baseline → T1 → T2 → T3 → T4; post-manifest validity starts only at its
recorded boundary and required bundle generation. There are no Lean blocks requiring compilation.

The live draft remained below the hard 800-line limit in document-only checks; its exact handoff
line count is reported with the deliverables. Final T4 metadata is incorporated as disclosed above.
The initial fresh author stayed within the 25-turn cap; exact token/context telemetry is unavailable,
with no known context breach.
An initial document-check command was blocked by the shell quoting guard before execution;
the rewritten check passed. No source mutation, package execution, runtime validation, commit,
merge, push or additional agent was performed by this prose dispatch.
Both final reviews are linked above, precision-gate proof is complete and no review-closeout gate
remains open. The prose author's coordinated refresh stayed within its ten-turn budget; the
controller subsequently finalized readiness wording from the completed proof and acknowledgements.
Exact token/context telemetry remains unavailable.

Final package validation also replayed every patch with `git apply --whitespace=error-all`.
All applied source additions and non-patch assets are whitespace-clean. Generic staged whitespace
checking reports the required blank-context markers (and terminal context) inside unified-diff
containers; those format markers were preserved, not stripped or hand-edited. No implementation
patch hash changed during this classification.

## Corrective coverage amendment — skeptical points 1–3 only

**Status: prose amended; controller proof/restoration passed; both renewed reviews clean.**
The fresh prose author read immutable package/snapshot maps, selected amendment JSON evidence and
bounded fixture/oracle patch hunks only. No transient feature source, builds/tests, source/JSON/patch
edits, commits, merge, agents or backend implementation were undertaken by this dispatch.
This pass does not address performance/process point 4 or solve missing budget telemetry.

### Why the original acceptance and reviews were insufficient

The max-only reversed-factor mutant actually survived the old packaged positive acceptance in
both precisions; its ten checked fixtures also survived. This was a real test blind spot, not a
demonstrated defect in the current runtime. Prior clean numerical/scope reviews did not establish
that invariant. The unchanged runtime already passes the new witnesses; no new capability is claimed.

- **Point 1:** `max_factor_order_cancellation`, accepted by both assignment checkers, reads
  `[L,-L,1]`, `L=2^54`, exact/finite in both carriers. Correct left-fold yields 1, reversal 0.
- **Point 2:** `scan_mixed_init_holes`, accepted by both scan checkers, retains two persistent
  tensors with distinct zero/neg_inf inits and scalar base overlays. Both full histories are checked:
  `[[3,7,13,19],[h,11,17,23]]`, respectively `h=+0` and `h=-inf`. Reusing the first init fails.
  Separately, nonempty-source reciprocal `[2]` over three positions yields `[.5,-inf,-inf]` and
  kills removal of the final max-unary OOB mask. The preserved empty-source log case exercises a
  different early-return path and cannot stand in for it.
- The [numeric evidence](jax_maxplus_files/revision_numeric_evidence.json) records 13 checked
  fixtures (11 assignments, 2 scans), 52 dtype/eager/JIT views, unchanged 44 metadata refusals,
  18 kernel singleton observe/strict passes, and 12 targeted numerical-return kills across the
  three new intents × both precisions × eager/JIT. No syntax/import failure is counted as a kill.
- **Point 3:** [gradient evidence](jax_maxplus_files/revision_gradient_evidence.json) checks five
  mathematical points on the same actual compiled source plan and reused named/positional functions.
  Baseline winner `(0,1,2,1,0,1)` scores -5.25, gap .25; `Init[2]+=4` changes it to
  `(2,1,2,1,0,1)`, score -4.75, gap .25. Existing permuted inputs give `(1,3,0,3,1,3)`,
  score -5.25, gap .25. Full Init/Trans/Emit transport covers Init's axis, both Trans axes and
  Emit's state axis; frozen Allow is transformed too.
- `Init[2]=1±delta`, native `delta=2^-47` for f64 / `2^-18` for f32, produces opposite unique
  finite winners with positive margins `7.105427357601002e-15` / `3.814697265625e-6`,
  exactly eight output ULPs on both sides. These are not genuine ties.
- Expectations independently enumerate prefixes/full paths in native NumPy carriers with source
  seed/factor order, not runtime operations/results or a narrowed f64 oracle. Full forward histories,
  Score and all parameter gradients are checked; never-read NaN Emit row gradient is zero and
  Allow is excluded from differentiation. Forty gradient and forty point-forward executions cover
  five mathematical points; baseline/permutation overlap the preserved 56 original source views.
  All seven original source/metamorphic and six Lean-only reachability cases remain.

### Revised package, controls and evidence boundaries

Package.json is authoritative for three provided manifests, task file lists and current hashes.
The source baseline remains `c5000dd462d72ed0ffcd5806937aa37fa477e9b0`; execution may use a
descendant only with unchanged affected source. 01/core/renderer/runtime bytes are unchanged.
02/03 are mechanically regenerated compiled fixture/verifier patches; 04 retains its docs/legacy
repins with README coverage prose updated. Touched-file counts remain 3/4/3/8, snapshots 4/7/7/15.
The current 04 SHA was read from package.json, not inherited from the historical hash above.
All three provided manifests are private-index seeds, never implementation patch add-files.

The added `jax_maxplus_grad_mutations_python.json` is **T3-only**; the unchanged runner has no task
selector. T1 uses Lean 2; T2 kernel 18; T3 regenerates full bundles then kernel 18 and gradient 8;
final controller runs all three provided manifests. Never put gradient-only anchors into T2.
Revised full pool: **40 unique intents / 53 entries per complete pool pass**:
2 + 18 + 8 + 8 nonlinear Lean + 11 scan Lean + 6 scan Python. Repeated phases add physical runs.
Inherited grouped semantics are not retrospectively precision-certified; SCOPE-01's independent
precision gating and deliberate one-leg-survival rejection remain required.

Gradient controls distinguish stale-baseline parameters (verifier orchestration), wrong gradient
transport (oracle control), right-biased approximate max (`near_tie_below`) and complementary
tie-preserving left-biased approximate max (`near_tie_above`). Each has one entry per precision.
The bounded gradient author observed/strict-verified six entries and separately both-sided targeted
numeric probes. The parent added the persistent tie-preserving left-biased pair; the completed
controller observe and strict runs now kill all eight entries, with the left pair specifically
failing `near_tie_above` in both precisions. A near-below-only kill is not both-sided evidence.

`controller_results.json` remains original operator/legacy proof for unchanged runtime/core/renderer
and old verifiers/inputs. The final prose-author read of `coverage_amendment_controller.json`
observed `status="passed"`, all amendment checks complete, source restored and main unchanged:
T2 checked runner/kernel 18; T3 full runner, gradient observe/strict 8 and kernel 18; unchanged
Lean 2; full prototype build (8847 jobs); task-4 and restored task-0 package proofs, index unchanged.
The controller reports baseline restore/rebuild complete and all temporary production/docs/legacy
edits restored, with runtime/core/renderer bytes preserved. Package.json's three provided hashes
are final, including the observed eight-entry gradient manifest. The portable report, not its
archived raw-log/session paths, is execution evidence.
Hash-based reuse of legacy proof does not mean all 25 inherited controls reran.
Renewed numerical/scope reviews are complete; the parent/controller closeout below records final readiness.

### Corrective authoring budgets and document checks

Both amendment fixture authors self-report within their 30-turn limits; the numeric author reports
an upper bound of 27 and unavailable transcript-based token metrics, and the gradient author reports
within 30 turns/100k context. Exact cumulative token telemetry is unavailable, not zero or solved.
The known original Stage A 45-turn breach above remains disclosed. This fresh prose dispatch is
bounded at 12 turns/70k context, with final file/line/check results in its handoff; no nested agents.
No Lean blocks were introduced, so no snippet compilation is needed. Amendment readiness is not
inferred from prose validation.
Document-only checks found all relative links resolving, balanced fences, no trailing whitespace
or Lean file:line citations, and a live plan below 650 lines. All three provided-asset hashes and
four patch/snapshot hash pairs matched package.json; task counts matched 3/4/3/8 and 4/7/7/15.
The explicit two-document `git diff --check` passed. The initial prose write-up stayed within the
12-turn bound; incorporating the late controller-completion proof exceeded that dispatch cap.
No known context-cap breach; exact token telemetry remains unavailable. No runtime tests/builds
were run or claimed by this author.

### Controller readiness closeout

Both appended amendment reviews are clean:
[numerical/coverage](jax_maxplus_files/review_numerics.md) and
[package/execution](jax_maxplus_files/review_scope.md). The numerical reviewer independently
checked all five input points in both native carriers against rational prefix/path enumeration,
including path-count gradients, permutation transport, cancellation and both tolerance controls.
The package reviewer verified task-0 hashes, strict ordered private-index replay, provenance,
provided manifests, task boundaries, counts and documentation. Neither reviewer reran backend
pools/builds or changed production source. Both report within their 18-turn bounds, no known
context-cap breach, and unavailable exact context telemetry.

The package review's sole nonblocking nit was the stale phrase "ten checked witnesses" in the
canonical T2 evidence summary. The controller corrected it to thirteen; this changes no patch,
provided manifest, oracle or expected output. Readiness wording and evidence statuses now reflect
the renewed signoff. No load-bearing finding remains.

The controller's final token-report invocation again returned "no transcript"; no telemetry
workaround or estimated totals were used. The original Stage A and corrective prose-author
turn-cap breaches remain disclosed above. Process/performance point 4 remains outside scope.
Only planning assets are to be integrated to local main, with no push. Implementation stays
unapplied; its future execution still requires the separate worktree and all execution gates.
