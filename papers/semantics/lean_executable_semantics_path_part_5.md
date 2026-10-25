# Lean executable reference - 5. Remaining work, in dependency order

[Previous: 4. What is implemented and proved](lean_executable_semantics_path_part_4.md) | [Contents](README.md) | [Next: 6. The landed admitted-core milestone](lean_executable_semantics_path_part_6.md)

## In this part

- [5. Remaining work, in dependency order](#5-remaining-work-in-dependency-order)
  - [5.1 Beyond the bounded source fragment](#51-beyond-the-bounded-source-fragment)
  - [5.2 Later: compiled and numerical refinement](#52-later-compiled-and-numerical-refinement)

## 5. Remaining work, in dependency order

### 5.1 Beyond the bounded source fragment

The first source slice is described in
[Section 4.7](lean_executable_semantics_path_part_4.md#47-bounded-source-correspondence-and-differential-debugging). The
remaining source work is broader than that finite bare-slot fragment: scans,
marked arrays and slices, affine reads (affine writes are covered by the S2a oracle (landed, merge 7a551faa), without a raw-parse theorem), guards and Iverson factors, nonlinear
primitives and their before-versus-after-collection boundary, unpinned dimension
inference, general expression substitution with renaming applied by admission,
and rank synthesis, plus schedule construction for programs outside the fragment.
The bounded raw-AST link is now certified from actual admission success;
parser/string correctness and an independently specified raw denotation remain open.

Differential debugging beyond the bounded profile needs a stated criterion for
non-integral and f32 numerics, native hooks for causal localization, comparison
of native nonoutputs.

The decision to remove overwrite and realize additive collection in production
(collection by private per-statement tensors and a collector, destination-owned
algebra, max-plus and min-plus sorts, out-of-range writes as errors) is recorded in
[the decision note](additive_production_decision_note.md). Slice 1 implemented collection
for sum-algebra bare-slot writers (`collectDefinitions`, `desugarMultiWriters`,
`ScanStmt.publications`, `PlanBindings.privateSlots`); the note's other slices (scatter,
scan multi-writer sets, scatter multi-writer B5, scan-local scatter overwrite F3) remain planned; top-level all-max/all-min multi-writer collection (S3b-ii) has landed (merged to local main as 349b6127) (plan `additive_s3bii_plan.md`, design `additive_s3bii_design.md`; mixed, scatter, scan-node and in-scan groups stay refused);
scatter collision ⊕ (S3a), out-of-range write errors (B6) and, in S3b, production tropical sorts, the bool -> tropical cast and the
`0_K` constants (`additive_s3b_record.md`) have been implemented for top-level scatters; the oracle for affine write slots (S2a, landed, merge 7a551faa)
and the oracle and sorted differential for single-sort max-plus and min-plus programs (S2b, merge cf7d6eee)
are executed evidence, not theorems. Two slice-1 caveats on the routed
path: `route` runs `desugarMultiWriters` before physicalization, and a routed collector step
records the same step as a product (`.contract` is (×, Σ, 0)), so routed steps do not keep
term structure (pre-existing for a user-written `A + B`; the real fix is parked with S3). A
plain writer plus a scan-scratch name that has a reader fails `cyclicDataflow` through
`validateScheduled` (the topology assertion runs before collection) and `multiWriterScan`
through a direct `desugarMultiWriters` call.

The [semantic gap audit](tensor_logic_semantic_gap_audit.md) (G04, F01) records the pre-slice
production divergence for multiple statements defining one left-hand side. Production now sums
the definitions and the differential compares them by value; the audit keeps the findings as
audited before slice 1.

### 5.2 Later: compiled and numerical refinement

[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) supplies
the next contract beyond a debug-capable reference executor:
logical-to-physical representations, kernel contracts, simulation/progress,
batching, and buffer liveness for scans. Rank alone never justifies overwriting
a still-needed value. A checked production plan is not automatically a
certificate for these new semantics.

Slices 1-4 of the plan layer and their review/probe follow-ups are merged and pushed
([Section 4.9](lean_executable_semantics_path_part_4.md#49-part-v-slice-1-the-singleton-command-plan-layer)): singleton and fused commands,
retirement of defined published addresses, typed static same-sort reuse with
boundary-local layout safety, with Lemma 31.2, Theorem 31.3 and
Lemma 32.1 proved for that profile.

**Certified bounded full-history scan (slice 5).** The
[Section 33.1 separate-buffer plan](tensor_logic_semantics_part_v.md#331-a-separate-buffer-history-plan)
has the entire history $H$ designated as output. Each slice is constructed
directly in distinct retained storage; all published slices stay live through
decoding. `Plan.ScanHistory` proves exact `Valid`/checker acceptance,
actual-prefix success and physical numerical preservation at every command
boundary, unconditional completion, and complete typed history decoding.
The independent recurrence is connected to collected equations, finite model
existence/uniqueness and output denotation. Theorems cover arbitrary natural
$d,N$, including zero, any `AddCommMonoid V`, a registered total unary same-sort
array operator $F$ and every validated input. This uses the existing static
allocation and correctness machinery without state retirement,
two-buffer reuse, or copy/relocation. Under the dense profile its retained output
uses $d(N+1)$ scalar slots. Terminal-only two-buffer scans and reusable working
buffers with retained-history copy/relocation are later milestones with distinct
output contracts; neither is a prerequisite for the full-history baseline.

Implementation plan: [Part V slice 5](plan_layer_slice5_plan.md), with measured
prototype and authoring evidence in its [record](plan_layer_slice5_record.md).
Generic certification is implemented, publicly reachable from `import LeanNCD`
or `import LeanNCD.Semantics.Plan`. The registered `PlanScanHistoryTest` and
independent `PlanScanHistoryOracleTest` retain all old assertions and cover
scalar/nonlinear full-history equality, all-command physical reads, successful
typed empty Decode, input-role rejection and a genuinely mixed registry.
The record distinguishes oracle/fixture/interface controls from generic-proof
kills, retains historical prototype evidence and records the final actual gates.

The remaining buffer work is capability work, not the old fixture-probe backlog:
copy/relocation would free working storage while retaining a value elsewhere;
input retirement needs caller-memory ownership; in-place execution needs
read-before-write or snapshot guarantees. The Section 33.2 two-buffer scan
still needs an actual schedule and last-reader/liveness proof, with full-history
and terminal-only outputs kept distinct. The completed static-reuse layer alone
does not provide any of these extensions or certify the production backend.
Not yet done: automatic general scan recognition, two-buffer last-reader liveness,
retiring inputs, relocation/copy,
dynamic allocation, cross-sort reuse and in-place kernels/snapshots;
concrete implementation-error sources (an abstract fault oracle with the error-free profile restated is done, `Plan/Faults.lean`); cross-sort primitives and non-exact numeric
kernel fixtures.

Floating-point correspondence needs its own ordered-reduction or numerical
correctness criterion. Exact commutative pushforward laws do not imply bitwise
schedule independence. Full $D$-graded categorical interpretation, general
cyclic solving, and configurable boundary-policy integration are also separate
extensions, not prerequisites silently added to the core executor.

---

[Previous: 4. What is implemented and proved](lean_executable_semantics_path_part_4.md) | [Contents](README.md) | [Next: 6. The landed admitted-core milestone](lean_executable_semantics_path_part_6.md)
