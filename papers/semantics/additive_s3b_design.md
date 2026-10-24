# S3b design: production tropical sorts become max-plus and min-plus

Status: brainstormed and audited 2026-10-22; the user chose the cut and the six open decisions in §2 (all by accepting the
recommendations). The §6 table lists the calls the author made. Parent: `additive_production_decision_note.md` (§A, §F, §E).
Audit: `additive_s3b_audit.md` (read-only, main `740bd4f8`). Plan: `additive_s3b_plan.md` (S3b-i only; S3b-ii gets its plan after S3b-i lands, CLAUDE.md Rule 13).

## 1. Purpose and intent

The spec's tropical sorts are semirings: max-plus (⊕ = max, ⊗ = +, 0_K = -inf, 1_K = 0) and min-plus (⊕ = min, ⊗ = +, 0_K = +inf,
1_K = 0). Production is not: `Combine.max`/`Combine.min` (reference), `admittedAlgebraMax`/`Min` and the f32 twins (checked plan)
are (max or min, ×, ∓inf, 1.0). That is a valid collection monoid but not a semiring (-inf·0 is NaN, × does not distribute over max
for negatives), so §17 of the spec does not apply to it, and a user writing `maxreduce(A[i,k]*B[k,j])` gets max-times where the
spec (and the S2b oracle) say max-plus. The goal: tropical semirings work in general in production, bit-agreeing with the S2b
oracle wherever the oracle can express the program.

This is a MEANING CHANGE to existing programs (decision note §A10). Success means: every program the oracle can express agrees on all
four legs (`fourLegParity`); every changed expected value in the test tree is recorded old -> new with its reason; no test is weakened.

Anti-goals (would make it a failure even if green): a silently changed expected value; a max-plus-only fix whose min-plus twin
is untested; a padded-0.0 behaviour surviving in any tropical statement unnoticed; the known-difference apparatus of the sorted
differential left in place describing divergences that no longer exist.

## 2. Decisions

Already fixed (decision note §A1-A2, §F; user): the sort table below; false Iverson, OOB read pad and bool->tropical cast produce
0_K / 1_K of the sort; real<->tropical casts are the identity; ⊕ and `max`/`min` are NaN-propagating; (-inf)+(+inf) is IEEE NaN;
a tensor's sort is DERIVED from its writer's `maxreduce`/`minreduce` annotation (`predicate` declaration = bool, otherwise real;
no declaration syntax; user confirmed 2026-10-22); the two tropical algebras share code.

Decided 2026-10-22 (user accepted the recommendations):

1. `real -> bool` reads keep their current behaviour (accepted, identity). Rejecting them is parked.
2. `ScalarBinOp.max`/`min` become NaN-propagating in both backends and for every algebra, including bool (differs only on non-binary NaN input).
3. A sort-neutral writer of a tropical tensor pads OOB bare reads with the TENSOR's 0_K. In S3b-i the only such writer is a scan base
   (`M[j,0] := X0[j]` of a max-plus state); its sort is the state's sort, taken from the scan's annotated statements.
4. `OutOfBoundsPolicy.zeroPad` keeps its name; its doc comments are rewritten ("the pad is 0_K of the statement sort for a bare read").
5. Mixed-sort programs get production-only coverage (hand expectations, `planAgrees`, duality twins). Extending the oracle to
   per-tensor sorts, and to casts, Iverson values and padding, is a later follow-up.
6. Scan-local scatter keeps overwriting on collision (parked F3).

## 3. Semantics (the contract the slice implements)

Statement sort `S(stmt)`: `bool` if the destination is declared `predicate`; else max-plus if `agg = max`; min-plus if `agg = min`; else real.
Tensor sort `algebraOf T`: bool for a `predicate` declaration; else the annotation of its writers (a scan state: its base and recurrence
statements; a sort-neutral writer, i.e. one term, one `read`/`unaryFn` factor, no contracted axis, adopts the annotation of the others);
else real. A never-written input is real (or bool if declared `predicate`).

| Quantity (statement of sort K) | Value |
| --- | --- |
| ⊗ of the factors of a term | real `×`; bool `min`; tropical `+` |
| empty product (no factors) | 1_K (tropical: 0.0) |
| ⊕ over contracted coordinates and over terms | real `+`; bool `max`; max-plus NaN-propagating `max`; min-plus NaN-propagating `min` |
| empty sum, zero-extent reduction, unwritten scatter cell, unwritten scan-state cell | 0_K (tropical: -inf / +inf) |
| Iverson factor `[p]` | 1_K if p else 0_K (tropical: 0.0 / ∓inf) |
| OOB bare read | 0_K of K |
| OOB read under a `unaryFn` | 0.0; the primitive is applied to real input; the result is read back into K by the identity |
| scatter collision | ⊕ of K (S3a already does this for real and predicate) |

Reads, by source sort (the tensor's `algebraOf`, bool if declared `predicate`) and statement sort K:

| source \ K | real | bool | max-plus | min-plus |
| --- | --- | --- | --- | --- |
| real | id | id (unchanged, parked) | id | id |
| bool | false 0, true 1 | id | false 0_K = -inf, true 1_K = 0.0 | false +inf, true 0.0 |
| max-plus | id | REJECT `sortCastUnsupported` | id | REJECT |
| min-plus | id | REJECT | REJECT | id |

Rejections (new): tropical -> bool, max-plus <-> min-plus (cast table); a tropical destination with `nonlin ≠ identity` (decision note A8; programmatic
statements only, since `relu(maxreduce(..))` has no surface form); two annotated writers of one scan state that disagree.

Where the rejections live (builder-check answers, verified against the code 2026-10-22):
- They sit beside `checkPredicateOutput` (`Structural.lean`) and are enforced wherever that rule is: source `checkDtypes`, `checkScheduledDtypes`
  (so `validateScheduled`, hence `evalScheduled` and the checked compile entry). They run on the source schedule BEFORE collection.
- `route` of a DIRECT `ScheduledProgram` is semantics-free and stays so (`physicalizeForRoute` does not call `validateScheduled`, so it never enforces the
  predicate-output rule either). No sort, cast or A8 rejection is added on that path; `RouteFragments` and its `physicalizeOne_length_eq_fragmentWidth`
  obligations are untouched. CORRECTION found while prototyping (P4): the SURFACE `compile` pipeline runs `checkDtypes`, which does enforce the predicate rule, so
  the per-statement tropical-nonlin rule is also called from `checkDtypes` (surface programs are rejected at `compile` too). The cast and scan-state rules need the
  schedule-level map and live only in `validateScheduled` (scan nodes are not grouped inside `checkDtypes`).
- The sort type is named `SortAlgebra` (`real | bool | maxPlus | minPlus`): `LeanNCD.Algebra` is already a class and `Algebra` clashes in the aggregate build.
  Consequently `LoweringTest` AGG1/AGG2 (they call the regression-only `splitNonlins` directly) and `RouteFragmentCorpusTest`'s `aggregate` fixture
  (route, payload `.represented`) are UNCHANGED. The audit's "become rejections" list is wrong for those two; only execution-entry tests can flip.
- `algebraOf` is computed on the SOURCE schedule inside `validateScheduled` and stored in `CheckedScheduledProgram.algebras`. It is a partial map; a lookup
  of an absent name falls back to the declaration (`predicate` = bool, else real). A top-level name with two or more writers is NOT given an entry in S3b
  (collection's `multiWriterAlgebra` remains the only refusal for tropical multi-writer sets, so `CollectTest` C6/C6b/C6c and `CollectEvalTest` J4 keep their
  constructors), and the private `T#k` tensors need no entries because collection admits only real-sum and predicate multi-writer sets today.
  Writer agreement is checked for scan states only (base plus recurrence statements).

Accepted (new): top-level `maxreduce`/`minreduce` scatter, with 0_K fill and ⊕ collisions (the S3a guard exists only to wait for this slice).

f32: identical semantics; constants are bit patterns (⊗ identity `0x00000000`; ⊕ identities `0xff800000`, `0x7f800000`).

## 4. Shape of the change (what the plan decomposes)

- One shared definition for the two tropical algebras per layer, parameterized by direction: reference `Combine`, checked
  `ContractionAlgebra` (f64 and f32), the oracle already has `MaxPlus`/`MinPlus`. They differ only in ⊕, 0_K and the f32 bit pattern of 0_K.
- Reference: `gather` receives the statement's (0_K, 1_K) for bare-read pad and Iverson; `evalScatter` initialises from `Combine.unit0` and folds with `Combine.combine`
  (the `boolDest` special case disappears); scan state initialises at the state's 0_K; the two scatter guards go.
- Checked plan: `gatherFactorWith` pads a bare read with the decoded `reduceId` (today `ops.zero`); the Iverson arm decodes `factorId`/`reduceId`;
  `ReadPlan` gains a cast field filled by `residualizeAssignment` (the plan has no per-source sort; `ScalarDType` stays `f64|f32|bool`);
  scan state init takes the state's 0_K; the scatter guard goes. The cast-legality rejections live in `validateScheduled`, which both backends share.
- `validateScheduled` computes `algebraOf` once and stores it in `CheckedScheduledProgram` (a new field). Reference per-statement entry points keep `decls`;
  the map is threaded only to scan state init, the neutral scan base and the casts (audit §2 gave 5-24 call sites per entry point).
- Oracle/differential: the divergence apparatus (`tropicalMultiFactor`, `tropicalScatterFill`, `unexplainedAgree`, the `scatterPolicy` refusal,
  `scatterFillNotIdentity` matching) is deleted; tropical programs are expected `fourLegParity`.
- Test helper: `DenseTensor.approxEq` must treat equal infinities as equal (today `|x-y| < ε` is false for -inf vs -inf).

## 5. Test shape

- Negation-duality twins: for each max-plus fixture a min-plus twin from negated data and negated expectation (min-plus(x) = -max-plus(-x)). The shared
  definition means a symmetric bug would pass a one-sorted suite; the twin is what catches it.
- Observed values only (slice-plan §1); each migrated expectation is logged old -> new -> reason in the record.
- Each cast cell, each new rejection and each new constant site (pad, Iverson, empty product, empty sum, zero-extent reduction, scatter fill, scan-state init)
  has a pinning fixture and an accept-neighbour, on both backends and in f32.
- Oracle parity covers what the oracle admits (multi-factor, scatter fill, zero-factor). Production-only: casts, Iverson, padding, mixed sorts.

## 6. Calls the author made (not user decisions; mark and correct)

| Call | Why |
| --- | --- |
| Slice name "S3b" = the semiring flip for single-writer programs; tropical multi-writer collection (A4 agreement) is S3b-ii, planned after | multiWriterAlgebra is refused today and the oracle's multi-writer rows are unencoded; the flip does not need agreement except within a scan state |
| Plan covers S3b only | Rule 13: one plan per slice |
| `approxEq` is fixed in production source (equal values compare equal, so equal infinities do; NaN stays unequal) | one-line test helper, needed for RC10's -inf cell |
| The tropical-nonlin rejection (execution entries only, beside `checkPredicateOutput`) and the scan-state annotation-agreement rejection are in scope | both are needed for a well-defined sort per statement/state; route is untouched (§3) |
| A test pins ("become rejections") from the audit are not trusted until observed | audit §8c was unread for 3 of the 5 and wrong for 2 |
| `EvalError.scatterFillNotIdentity` and `CapabilityError.scatterOptsNotAdmitted` are deleted with their only consumers (the sorted differential's condition) | audit §11.9; they are kept alive only by `confirmsSorted` |
| Prototype-first authoring in five dispatches, patches per task | slice-plan §6; T3/T4/T5 carry the design risk |
| The cast mechanism (reference cast copy vs gather map; plan `ReadPlan.cast`) and where the per-state sort lives in the scan plan are left to the prototype | UNVERIFIED in the audit (`ScanStatePlan` not read) |

## 7. Non-goals (owner)

Tropical multi-writer collection and the writer-agreement rule (S3b-ii); multi-writer scatter B5; scan-local overwrite F3; JAX/Python tropical execution
(`Executable` gate stays); `real -> bool` rejection; `zeroPad` rename; oracle per-tensor sorts and oracle coverage of casts/Iverson/padding; Python-side tropical.

## 8. Cost and risk

Execution budget about 175M (Rule 6). Expected breaches: casts (T4), sort derivation and rejection constructors (T3), oracle cleanup (T7), test migration (T8, three dispatches).
Authoring target about 50M; S1, S2a and S2b each ran roughly 2x. Surface any breach in the record.

## 9. The shape the prototype landed (supersedes §4 where they differ)

Verified by an in-order replay of the 16 patches onto the slice tip: the tree is identical to the prototype tip. Eight prototype dispatches (P1-P8) built the whole slice as
16 per-task patches (`additive_s3b_files/patches/`); the full `Tests` build is green at the tip (8825 jobs). Differences from §4:

- **No `algebras` map in either backend.** Casts need only local facts: a bool source is `isPredicateDest decls src` (reference) or a `bool` slot signature (plan), and a statement is
  tropical iff `agg ≠ .sum`. `CheckedScheduledProgram.algebras`/`algebraOf` exist for validation only. The cast is `ReadPlan.boolToTropical : Bool := false` (plan) and a trailing
  cast argument of `gatherRead`/`gatherCast` (reference); truth is "stored value is not 0".
- **Scan state sort and neutral writers: one mechanism.** `scanStateStmts` rewrites each sort-neutral statement's `agg` to the state's sort before evaluation or compilation, so the OOB
  pad and the cast key move together; `scanStateSorts` (DSL/Ast.lean) is shared by validation and both scan entries. The checked plan carries the state's init as `StateInit`
  (`zero`, `negInf`, `posInf`; `StateSlot.initValue`, default `.zero`), with `ScanPlanError.stateInitNotAdmitted` for a tropical init on a bool state.
- **Neutral writers are decided by shape only.** A neutral statement's own annotation is ignored. Consequence (PARKED, pinned by `parkedAllNeutralScanState`): an all-neutral scan state
  with a tropical annotation evaluates REAL; the alternative (a neutral annotation votes for the sort) is a design decision for a later slice.
- **New errors:** `tropicalNonlin`, `scanStateAlgebraMismatch`, `sortCastUnsupported` (`CompileError`), `PlanError.castNotAdmitted`, `ScanPlanError.stateInitNotAdmitted`. No exhaustive `match` broke.
  Deleted with their only consumers: `EvalError.scatterFillNotIdentity`, `CapabilityError.scatterOptsNotAdmitted`, the oracle's `scatterPolicy` refusal, `SortedClassification.knownContractDifference`,
  and the conditions `tropicalMultiFactor`, `tropicalScatterFill`, `unexplainedAgree`. The oracle now admits top-level tropical scatter, and the sorted snapshots declare the strided axis as 8
  (production's derived extent).
- **Test shape actually built:** a duality property over the existing generators (`DualityTest`: 3832 + 13 + 2 + 2 programs on the reference, the f64 plan and the f32 plan; `enumPrograms` has no
  max aggregation, so the property tropicalises it), hand twins for every fixture the property does not cover, a bool-cast module (`BoolCastTest`), and a test-side fix to the independent
  scan oracle (`ScanUnroll` filled an unwritten tropical cell with the real 0).
- **Authoring cost:** see the ledger. Every prototype exceeded the 60-call cap by the harness count (96 to 149 calls); the cost drivers were hand mutations (P1, P2), harness refusals and builds.
