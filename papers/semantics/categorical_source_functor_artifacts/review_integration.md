# Whole-branch integration / observation review

- Candidate: `94f7bc8f`; frozen base: `19c9d6446552c4f4c507c89be94c3561a94ec5ea`.
- Lens 2: integration boundaries, discriminating fixtures and observation controls,
  artifact reliability/provenance, documentation scope. Read-only implementation;
  this report is the only permitted write. No nested agents.
- COMPLETE: one P2 documentation-boundary finding (DOC-1), no additional
  high-confidence implementation/integration finding. Not CLEAN until DOC-1 is
  fixed or adjudicated. Scope: entire candidate branch against the frozen base,
  including added sources/tests, immediate donors, wiring, artifacts and the
  requested current synthesis/entry-point sections.
- Budget: aim ≤35 turns, <250k peak. Actual Copilot token measurements have not
  been obtained; no claim of measured token compliance.

## Confirmed findings

### P2 / DOC-1 — stale headline proof boundary

`Summary / strongest defensible conclusion @ papers/semantics/categorical_tensor_logic_semantics.md`
(around lines 104–106) still says “Source-category laws, ranked phase execution
and event-sensitive process laws remain separate obligations.” This unqualified
source-category claim contradicts the preceding new paragraph and Section 6.10:
`IndexedSourceFunctor` now supplies a proved category and genuine functor for
the specified matched-component/coordinate-wire presentation. The highest-level
quoted conclusion therefore still reports this slice's completed obligation as
open. Root cause: inherited summary quotation was not included in the boundary
update. Surgical fix: state the specified source category/functor among proved
results, and qualify only **broader source interpretations/laws**, ranked phases,
and event-sensitive process laws as open. Check the summary against 6.10,
10.2/10.3, conclusion and A.9 after editing. The record's “Direct documentation
sweep” PASS/no-current-denial assertion also needs adjudication against this
missed quotation. No implementation repair performed.

## Verified boundary checks

- All eight added Lean modules inspected. `IndexedSourceSemantics` imports the
  actual functor; the only lakefile delta adds these modules to nondefault
  `IndexedExecutionExperiment`. No production/core/default-test/runner/script/
  JAX or historical witness-handoff/record/semantics-README delta.
- Actual assembly interpretation uses `composition_hom` with exact input,
  boundary and output wire equivalences and both exterior legs. Both actual
  nested source terms derive equality to the common triple without `Rel.bracket`;
  its separate soundness case uses the existing `bracket_hom`.
- Fixtures retain Axis `5,2` versus wrong-reversed `3`, inverse cells and binary
  output `14`; Triple nonconstant tagged exterior input `5,2` and output `134`;
  actual bracket witnesses/private stores `15,35,134`, and nested UID `164`
  versus `82`. The binary input-inverse assertion is a rebased-left-leg equality,
  not a separate nonconstant numeric input oracle; the plan states this honestly.
- Empty singleton environment carriers do not erase whole-interface metadata
  or validated-input presence. Hidden distinct complete stores have equal outputs;
  the functor leaf retains unchanged all-input `componentSpan`. Strict negated
  domain is profile `0`; the positive-domain neighbour is profile `4`.
- ProbeTest imports no source parity module (directly or through its dependencies).
  Three computational copy bodies match `Wire.env`; four generic parity theorems
  remain separate. M1–M7 are isolated copy/donor observations; M8–M10 are
  theorem-donor substitutions, not independent expression/model verification
  or mutations of proof-carrying gluing/source recursors.
- Read-only `package.py --audit` passed eight source hashes, three patch hashes,
  final wiring and exact-copy hashes. All fourteen historical receipt identities
  also matched. Read-only unfiltered manifest `--check` passed ten unique old
  strings. Prototype receipt explicitly remains authoring-only; release receipt
  explicitly leaves final reviews/integration/push pending.
- Independently checked bounded mutation-log sections: each of the ten entries
  has its exact diagnostic and fixture, mutated exit `1`, restored-build exit
  `0`, and manifest byte-restore PASS. Initial historical run is expectation-free
  (`n/a`), not an expected-string gate; verified/execution/release tables each
  have ten expected-string PASS rows. An initial reviewer assertion incorrectly
  required `yes` in the initial table; corrected to its documented `n/a` scope.
- Both historical and fresh full-build logs end in 8,919-job success and contain
  no error lines. Eight recorded snippet exits are zero; universe/API compile
  marker is present. Namespace audits and printed new proofs use only standard
  axioms; the new-source shortcut scan has no matches.
- Synthesis evidence/6.6/6.10/10.2/10.3/conclusion/A.9 and Lean AGENTS entry
  otherwise distinguish the proved specified source category/functor from
  broader source/interface, rank/phase/trace, event-sensitive process and backend
  obligations. No event-free core identity or cyclic-model solver is claimed.
- Independently replayed task1/task2/task3 unified patches **in memory** over
  frozen-base bytes obtained with read-only `git show`. Exactly the eight added
  modules and staged experiment-wiring changes are present; all nine final
  SHA256s match the compiled package. No alternate index or receipt was written.
  Checked the transitive ProbeTest import graph: neither source nor witness
  observation parity is reachable. Both changed documentation files' local
  Markdown link paths exist.

## Close-out / limits

No new build, mutation, snippet regeneration or evidence-export operation was
run: controller release logs and receipts were inspected and independently
checked without overwriting them. Fresh reviewer commands were read-only
artifact/copy audit, unfiltered manifest schema/old-string check, token-report,
negative source/import/diff audits and in-memory evidence/replay checks.
The only write was this incremental report via `apply_patch`; no code, docs,
plan, scripts, index, primary or other-worktree mutation, nested agent, commit,
merge or push occurred.

The review stayed below the 35-turn aim by direct interaction count.
`token-report.py 37386608-c5a8-4c82-a88b-0d50cc6e834c` returned “no transcript”;
actual Copilot peak/cumulative tokens are unavailable, not measured compliant.
No known reviewer budget breach. Historical prototype 55-turn overrun remains
disclosed in its untouched receipt; it is not this review's accounting.
