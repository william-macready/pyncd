# JAX max-plus plan: authoring record

**Status: execution-ready package; controller verification and both final reviews are clean.**
This is the planning/authoring record, not the future implementation record
`papers/semantics/jax_maxplus_record.md`. No production changes have landed as part of this
write-up, and no implementation, commit, merge or push was performed by the prose author.
The controller independently tested the prototype and restored every temporary source,
documentation and legacy-manifest edit. Only the plan package is delivered.

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
separate bounded Direct dispatch. T4 changes only directly coupled nonlinear/scan Lean/Python repins.
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
