# T9 independent whole-slice soundness review

## Scope and checkpoint 1

- Read-only review checkout: `/Users/williammacready/code/python/pyncd.worktrees/scan-history-final-review`.
- Verified HEAD: `8978f8bd99f4503850cf7026fb9080637bb6916a`; whole-slice diff base: `ed884938`.
- Only this report is written. No builds, mutations, production edits, commits, or nested agents.
- Reviewed the plan §3 contract and T9 review requirements, whole-slice changed-file inventory, and `ScanHistory/Core.lean` in full.
- Core inspection confirms generic registered unary same-state-array operator, certified total domain, separate X/Z/H roles, persistent X at every time, initial Z only at zero, recurrence from time `< N` to its successor, and whole prior-slice expression construction. Proof/caller and numerical retention checks are in progress.
- No finding yet; this is not a clean verdict.

## Measurement

## Checkpoint 2 — complete ScanHistory library inspection

Read all twelve ScanHistory implementation modules, not just their public statements.

- `Recurrence` is independent of Program, execution, and Decode. `Model` derives exact two-term zero/successor collection equations by destination-fibre classification, constructs a total X/Z/H store, and proves finite uniqueness by `Fin.induction`. No unjustified infinite-history extension is used.
- `Evaluation` extracts X/Z through validated presence proofs and reconstructs every input, including absent H. Registry input/output transports are eliminated by equality reasoning; `.tab/.prim/.at` evaluation uses the complete previous slice. Partial-store evaluation requires explicit `some` values at every previous coordinate.
- `Coverage` classifies every guarded tagged occurrence and proves injection, group/block Nodup, inter-slice disjointness, and exhaustive occurrence/address coverage. `Prefix` handles all three phases and the final boundary with exact list equations and publication/materialization/consumption inequalities.
- `Allocation` places H(i,l) in physical buffer l, coordinate i, with global placement injection. `Validity` supplies all nine generic Valid fields and derives acceptance by the existing exact checker equivalence.
- `Correctness` uses a prefix bridge over the original valid plan, retaining its actual command indices, reference state, pre/post layouts, and R. It does not assert validity of a coverage-incomplete truncated plan.
- Retention is tied to actual deterministic prefix runs, model-preserved reachable published values, logical slot reads, publication reads, and the actual physical `M (.inr ⟨l,i⟩)`. The terminal theorem supplies unconditional completion and `some` of the full typed history output; its quantification includes d=0, N=0 and both zero. Admissibility/denotation are model-derived.
- Scan source search found no admissions, new axioms, unsafe mechanisms, opaque implementations, or extra narrowing instances. Standard-axiom build audits are controller-provided evidence, not independently rerun here.

No high-confidence finding identified so far. Unchanged generic R/run/step/soundness and checker definitions/callers are currently being audited before a verdict.

Tool-response rounds at this checkpoint: 12 (including this report write).

## Checkpoint 3 — unchanged semantic spine and exact checker

- Inspected unchanged `Plan/Syntax`, `Memory`, `Step`, `Validity`, `Simulation`, `Run`, `Correctness`, root `Models`, `Soundness`, and the immediate interpreter/completeness/invariant dependencies relevant to the scan proofs.
- R includes reachability, pending/published bookkeeping, numerical pub/acc slot equations, accumulator retention, unmapped-slot `none`, and retired-publication consistency. Its published-slot equation is restricted by actual Live/SlotView, not by an independently assumed ghost buffer.
- Actual init and acc writes preserve other live resources using post-init and pre-acc layout separation respectively. `step_R` consumes both boundary layouts; the new original-plan prefix bridge supplies them through generic `Valid.layout_boundary`.
- Unconditional terminal success is not inferred merely from a conditional `done_correct`: model existence rules out semantic failure; Valid progress rules out stuck; terminal adequacy establishes complete reference state and actual successful Decode.
- Checked tensor-level input presence, full-coordinate decoder construction (including empty function domains), monoid collection versus scalar operations, and the guarded use of existing executor fallback accessors. The scan adds no default-zero input extraction.
- Checked both directions of the existing checker equivalence, including all-boundary layouts, guarded occurrence/address enumerations, readiness, freshness, materialization and publication order.
- Reviewed docs' formalized separate-buffer full-history claim against these statements. No source recognition, partial F, reuse, in-place, floating-point, or production-backend theorem is smuggled into the claim.

Controller subsequently reports final gates complete: unfiltered mutation manifest 32/32 PASS, 55 exact anchors, byte-identical restores, full wrapper build green (8811 jobs), all 16 inherited PlanTest modules byte-identical, 18 prototype assertions preserved, and 516 fixtures = 239 eval + 277 proof. The reviewed production/test snapshot remains exactly 8978f8bd; the controller's later integration changes are doc-only with unchanged leanncd subtree. These are reported controller evidence, not rerun by this reviewer. No pending-gate gap is asserted.

No high-confidence finding so far. Remaining work: finish new test/interface/negative-neighbour inspection and close out residual limits.

Tool-response rounds at this checkpoint: 20 (including this report write).

## Final verdict — CLEAN

No high-confidence meaningful soundness finding. No requested fix or severity-ranked defect is raised. This is the whole-slice soundness lens against `ed884938..8978f8bd`, not a last-diff review or an inference from green gates.

All code references below are relative to frozen `leanncd/LeanNCD/Semantics/`:

| Required contract | Inspected evidence and conclusion |
|---|---|
| Exact independent recurrence and arbitrary inputs | `Plan/ScanHistory/Recurrence.lean:10-29`; `Core.lean:46-74,112-161`; `Evaluation.lean:8-34`. Input reconstruction includes X/Z tensor presence and absent H, rather than assuming constructor-generated inputs. No positivity premise or fallback extraction. |
| Chosen existing-registry array F and whole previous slice | `Evaluation.lean:36-116`; `Operator.lean:5-35`; `Validity.lean:121-168`. Cast transport preserves selected registry meaning, exact input/output array type, and full tabulated footprint. Unselected operators need not be unary or total. |
| All and only guarded occurrences, exactly once | `Coverage.lean:11-29,60-130,132-281`. Raw valuations are classified using guards, source tags remain distinct, target equations are exact, and occurrence/address coverage is paired with Nodup and inter-slice disjointness. Not a mere cardinality proof. |
| Collected equations and finite unique model | `Model.lean:116-271`. Zero fibre is X+Z; successor fibre is X+F(previous slice). Collection is proved over arbitrary total stores before constructing the independent model; finite induction proves the iff. No circular appeal to execution or assumed successful Decode. |
| All phases, all Valid fields, exact checker | `Prefix.lean:13-337`; `Validity.lean:8-208`; unchanged `Plan/Validity.lean:29-63,130-165,267-280,436-461`. Includes endpoint lookup, init/acc/pub boundary equations, empty commands, retire exclusion, readiness, all-boundary layouts, and both directions of checker exactness. |
| Original-plan numerical prefix bridge | `Correctness.lean:15-78`; unchanged `Plan/Memory.lean:276-279,332-376`, `Plan/Simulation.lean:826-880`, `Plan/Run.lean:87-116`. Segment membership is related to original commands at pc+j, with original refState/R and actual pre/post layout obligations. No truncated-plan Valid assumption. |
| Physical published retention at every boundary | `Correctness.lean:83-135`; unchanged `Soundness.lean:58-87`, `Plan/Memory.lean:332-350,381-387`. Actual prefix success establishes R; reachable publication agrees numerically with the independent model; actual readSlot, readPub and physical buffer-slot equations follow. Later-boundary equality is derived from those values, not static Live/rank alone. |
| Unconditional full/empty typed Decode and denotation | `Model.lean:273-280`; `Correctness.lean:139-166`; unchanged `Plan/Correctness.lean:91-126,140-157`, `Plan/Memory.lean:209-219,390-407`, `Models.lean:80-96`. Existence of an actual completed run and `some (history_output ...)` is proved for every validated input. The output is the full independently defined H function, including empty domains. AdmInput is proved from model existence/uniqueness. |
| No hidden narrowing or unsafe proof escape | All twelve scan modules and both final test modules inspected; admission/axiom/unsafe/implemented_by/native_decide source searches return no forbidden mechanisms. Generic pins retain arbitrary V, d, N, registry, certified f, ops and validated input. Controller-supplied compiled standard-only audits: 6395 root declarations, 405 scan/public-test declarations; not independently rerun. |

### Final test and interface checkpoint

Read both new test modules in full, including the independent recurrence oracle, arbitrary-store collection tests, generic hypothesis pins, every-phase physical memory observations, mixed-registry tests, and successful typed full/empty output-function assertions. The relevant test root is frozen `leanncd/test/Semantics/`.

- `PlanScanHistoryOracleTest.lean:1-71` imports recurrence rather than scan execution/model, and fixes scalar and cross-coordinate nonlinear whole histories to explicit rational values, including the extended fourth slice.
- `PlanScanHistoryTest.lean:240-263` distinguishes checker rejection of early publication and co-live buffer collision; the unchecked collapsed allocation still finishes with corrupted full history, so completion alone is not treated as a soundness oracle.
- `PlanScanHistoryTest.lean:826-905` distinguishes equal group lengths from correct source tags, coverage, freshness and publication-order acceptance.
- `PlanScanHistoryTest.lean:970-1205` pins all-boundary R and physical values, existential successful runs, full typed Decode, and explicit empty-domain output functions without a successful-run premise.
- `PlanScanHistoryTest.lean:1218-1371` checks missing X/Z and H-as-input rejection even with empty coordinates, extended nonlinear output, and a genuinely mixed registry whose unused binary scalar entry is partial. Audit commands cover the complete scan namespace and both final test namespaces.
- Public import chain checked: `LeanNCD.lean:155` → `Semantics.lean:8` → `Plan.lean:12` → `Plan/ScanHistory.lean:1` → `Correctness`; both new test modules are registered in `lakefile.toml:92-93`.
- Current formalized-status docs and intent-layer contracts inspected agree with the actual theorem scope: constructed separate-buffer full history, not general source recognition or two-buffer/in-place certification.

### Residual limits and completion accounting

- No builds, mutations, nested delegation, production edits, commits, or live execution-source reads were performed. The only written file is this report.
- The controller's final build, unfiltered mutation execution, restore hashes, fixture preservation/counts and compiled axiom inventories are accepted as reported evidence, not independently executed or remeasured here. Every evidence/provenance row was not separately re-audited by this structural soundness lens.
- Unchanged generic dependencies were inspected along the actual scan proof/runner/R/model/Decode call path; this is not a fresh audit of every unrelated pre-existing semantics theorem.
- Later doc-only integration beyond frozen HEAD was not independently reviewed. The controller reports unchanged production/test sources, so the frozen semantic verdict applies to that unchanged subtree.
- Partial selected F, floating-point refinement, source recognition, retirement/reuse/copy, production backend correspondence, and compiler recognition remain explicitly outside this slice, not missing premises smuggled into its theorem.
- Final reviewer tool-response round count: **26**, including the concluding report verification read. This counts batched parallel tool calls as one assistant/tool-response round. No cumulative input-token measurement is available under this review's read-only/no-execution constraints; no measured token total or claim of a measured context budget is invented.
- Required soundness areas are covered; no load-bearing blocked or silently omitted contract remains.
Cumulative input-token measurement is unavailable in this read-only, no-execution review; no token total is claimed.
