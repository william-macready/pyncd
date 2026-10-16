# T9 independent whole-slice FIDELITY review

Review range: `ed884938..8978f8bd`. Read-only evidence checkout:
`/Users/williammacready/code/python/pyncd.worktrees/scan-history-final-review`.
Only this review artifact is written. No builds, mutations, nested agents,
production edits, commits or live execution-tree reads are performed.

## Scope and review checkpoints

Review in progress. Frozen plan §3, §6 and T9 have been read. The review covers
the whole slice and the plan's inherited sibling contracts, including full
history, input roles/shape/zero bounds, independent oracles, command phases,
physical retention, negative/accepted neighbours, public discovery, documentation
and committed provenance/mutation evidence.

The record explicitly leaves the controller's final unfiltered 32-cycle gate,
post-restoration full build and integration pending. Those close-out fields are
not treated as implementation defects. Prototype measurements are not treated
as evidence that new generic proofs were present in the prototype.

## Checkpoint 1: production contracts

No substantive finding established in the complete new production source read.
`Core` fixes H's axes to `[spaceAxis d, timeAxis N]`, makes X persistent and
Z base-only, and targets recurrence source `l<N` at `l+1`.
`RegisteredF` constrains only the selected unary, total, same-array-type entry.
`Evaluation.input_reconstruct` uses presence-justified `Option.get` and excludes
H, including empty domains. `Model.collect_zero/collect_succ` prove exact
two-source fibres; finite model uniqueness uses bounded `Fin.induction`.

`Prefix` supplies all three command phases, exact lists/membership, terminal
lookup, final-boundary decomposition and no retirement. `Validity` proves all
components from actual command lookup. `Correctness.prefix_done_R` is actual
run/refState/R success, and `history_retained` identifies readSlot, readPub and
physical `.inr ⟨l,i⟩` values at every completed-prefix boundary.
`scan_decode_history` quantifies over arbitrary validated inputs without
successful-run or positive-bound assumptions and returns the entire typed
`history_output`, not only its final slice. Fixture/provenance/doc review remains.

The controller's notification of concurrent unrelated local-main advancement
does not change this frozen range and is not a slice defect.

## Checkpoint 2: fixtures, public surface and committed evidence

Both complete final scan fixture modules have been read. The independent exact
rational oracle imports the recurrence foundation and never derives its trace
from collection, execution or Decode. Scalar `[5,12,26]`, nonlinear
`[[4,7],[16,30],[63,482]]`, extended `[609,30368]`, no-transition and empty
histories agree with the independent equations. Typed Option/function equalities
prevent empty-coordinate vacuity and final-only observations from masquerading
as complete Decode. Scalar/vector physical tables cover pc0..9, with distinct
coordinates and all three phases.

Negative early-publication and collapsed-history fixtures separately distinguish
steps/layout rejection, retain accepted neighbours, and exhibit unchecked alias
corruption. Raw input-role neighbours reject missing X/Z and extra H for both
nonempty and empty tensors. The mixed registry's unused operator is genuinely
binary, scalar and partial; the selected entry alone is certified, and nonlinear
full-history parity survives its transport through the same registry.

Read-only checks establish:

- all three committed patch SHA-256 values match the manifest; synthetic final
  checkpoint and T0's complete `leanncd` tree each equal prototype `94cc67c9`;
  all eight replayed source/test blobs also match individually;
- all 18 inherited prototype assertions (14 evaluated + 4 proof items) retain
  exact bodies/expectations modulo comments/whitespace;
- final `Plan*Test.lean`: 18 modules, 239 evaluated + 277 proof = 516 assertions;
- 32 distinct final manifest edits, each old string unique in frozen source;
  55 location-qualified anchors, classified as 3 oracle, 16 fixture-observation,
  8 production-library-proof and 5 proof-interface controls;
- the 31 committed T7b observation records map exactly to the final manifest
  after 33 test anchors shift by seven lines; the other 20 anchors do not move.
  Their recorded mutation/restore-hash/restored-build exits are 1/0/0.

These are provenance/source checks, not a fresh mutation run. The initial
15/31 stale-anchor failure table is retained honestly; repaired anchors and
six-control/public-control reruns are distinguished from the pending complete
final gate. S5-F2/F7/F8 are correctly reclassified as generic-proof barriers:
historical prototype numerical kills are not advertised as reachable final
fixture kills. Public `Plan`/`LeanNCD` exposure and both default test registrations
are present; the public-import omission control pins two consumer failure sites.

## Final verdict: CLEAN

No high-confidence substantive implementation bug, fidelity defect, coverage
hole or inaccurate mathematical/scope claim was found in `ed884938..8978f8bd`.
No implementation change is requested.

### Completed coverage

- **Whole branch and inherited siblings:** read every new production module and
  both complete final scan tests, the required plan windows, committed evidence,
  and all changed live-documentation/discovery windows. Checked inherited
  `ValidInput`/validation, SlotView/LayoutOK, Start/readPub/Decode, R.dead/pubSlot,
  and model-to-completion contracts against their scan callers. No generic
  storage/retirement/kernel contract was rewritten. All 16 inherited Plan test
  modules are byte-content identical to the review base.
- **Full history/source fidelity:** all slices, X at every slice, Z only at
  zero, exact successor destinations and source bounds; exact tagged coverage
  rather than length-only reasoning; complete prior-array footprint/evaluation;
  no fallback-zero input extraction, hidden positivity or canonical-input-only
  restriction. H alone is output with shape `(d,N+1)`. Bounds d=0, N=0 and both
  zero preserve command counts and tensor-level input roles.
- **Execution rather than ghost-only evidence:** all-phase command indices,
  Cons/Mat/Pub thresholds and final lookup are explicit; actual prefix success
  establishes refState/R; physical slots, readSlot and readPub retain independent
  numerical values at every later command boundary. Independent typed
  full-output equality includes successful empty Decode. Empty Decode at pc0
  is explicitly accepted, not falsely rejected.
- **Discrimination:** independent exact-rational scalar/nonlinear/extended
  histories, sentinel direct-store collected fibres, scalar/vector all-command
  memory tables, early-publication and alias rejection with legal neighbours,
  unchecked alias corruption, terminal-only negative observation, raw binding
  rejection including empty tensors, arbitrary generic theorem signatures, and
  mixed-registry different-arity/different-type/partial unused entry are covered.
- **Discovery/docs:** both final tests are default registered targets;
  `LeanNCD -> Semantics -> Plan -> ScanHistory -> Correctness` exposes the API.
  The test consumer has no direct production child import beyond public
  `LeanNCD`; the oracle's recurrence-only import does not expose certification.
  Changed live spec/roadmap/discovery prose matches the implemented full-history
  instance without changing existing recurrence/scheduling mathematics or
  claiming automatic scan recognition, two-buffer liveness, in-place reuse,
  selected partial F, floating-point or source-adapter certification.
- **Provenance/mutation fidelity:** original 11 controls/38 anchors are accounted
  for: every inherited fixture row locator survives either as a reachable
  current pin or explicitly historical metadata behind a new proof barrier.
  Four duplicate phase edits are retained as historical labels/tasks on
  S5-F1/F5/F7/F8: 35 phase-labelled edits become 31 unique pre-public controls,
  then 32 with the public import control. Multi-site expectations remain
  conjunctive in the runner; controls pin located row diagnostics or specific
  generic-proof/interface failures, not merely a nonzero build exit.

### Gate update and limits

After the frozen-source review, the controller reported the actual final
**unfiltered 32/32 cycles PASS**, all **55 exact anchors**, byte-identical
restoration, and a post-mutation full wrapper build green in **8811 jobs**.
The controller also reported source/test snapshot equality with `8978f8bd`
and conflict-free integration of upstream-only documentation with the exact
`leanncd` subtree unchanged. These are controller-reported gate results, not
commands rerun by this reviewer; neither earlier pending fields nor shared-main
concurrency is classified as a slice defect.

The committed phase-result tables and repaired-anchor observation JSON were
inspected; their external raw session logs were not opened. Patch hashes,
committed replay/prototype tree equality, exact source-match uniqueness,
assertion preservation, inventory and anchor relocation were checked read-only.
No fresh replay application, Lean build, mutation cycle or kernel/axiom execution
was performed. The source has no new admission/unsafe mechanism; the existing
audit helper explicitly allows only propext, Classical.choice and Quot.sound,
and the scan test audits all three final namespaces. Its pre-existing demo bad
axiom is outside those namespaces and is an expected-error self-test, not a scan
axiom. A row/control kill is not claimed to pin every field of that row.

No broad unrelated audit, new assumption or parked substantive issue was added.
Only this artifact was written, incrementally.

### Review budget

Actual reviewer tool use: **22 assistant tool-call turns**, including **17
parallel batches**; **111 individual leaf tool operations**, or 128 calls when
parallel wrappers are counted too. This distinguishes turns from operations.
The 40-turn target / 50-turn hard limit was not exceeded. Exact peak context and
cumulative input-token measurements are unavailable in this frozen-read-only
review; unavailable is not zero and no numerical context-budget compliance is
asserted.
