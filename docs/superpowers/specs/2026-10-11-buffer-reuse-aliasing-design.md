# Part V buffer reuse and aliasing (slice 4): design

Status: approved by the owner in the 2026-10-11 implementation conversation;
production and regression prototype compiled through `deb4fecd`; both controller
full builds and the axiom audit are green. Exact ordered patch replay from
`4ffdc342` to `deb4fecd` is controller-verified (isolated-index final git diff
exit 0). All 64 mutation verdicts pass; both fresh whole-branch reviews are
clean or adjudicated. Landed on local `main` via merge `c44f8a21`; not pushed.
Decisions D1-D6 were confirmed individually before approval.
Base: local `main` at `4ffdc342`.
Path: Full (physical storage, placement, validity and refinement interfaces change).
Source brief: [buffer reuse and aliasing brief](2026-10-11-buffer-reuse-aliasing-brief.md).
Template: [slice-3 retirement design](2026-10-11-buffer-retirement-design.md), retained
unchanged as the record of the preceding slice.

## 1. Goal

Allow different logical defined addresses to occupy the same physical slot at
different times. A retired address remains in the reference published store as
ghost history, but its former slot may subsequently hold another accumulator or
published value. No kernel or output decoder may use ghost history as storage.

Success requires actual reuse, not merely clearing a retired slot or introducing
buffer metadata while kernels continue using canonical tensor slots.

## 2. Decisions confirmed by the owner

| ID | Decision |
|---|---|
| D1 | Explicit finite physical buffers, each with identity, sort and capacity; static per-plan placement of defined addresses. The old one-buffer-per-tensor layout remains the canonical default. Inputs have separate storage. |
| D2 | The layout view is injective over all simultaneously represented resources at every annotation boundary, including intermediate boundaries within fused commands. The checker decides this exactly. |
| D3 | Replace `R.dead` by: every physical slot outside the image of the current layout view contains `none`. Retirement still immediately clears its members' slots. |
| D4 | Dependent types enforce capacity bounds and address/buffer sort compatibility. The checker handles temporal alias safety, not malformed raw placement metadata. |
| D5 | Kernels remain non-in-place. Accumulation reads the pre-command published view before committing writes. Snapshots and justified live-source/destination overlap are deferred. |
| D6 | Scope is same-sort static reuse, checker/proofs, canonical compatibility, and singleton/fused/fault-wrapper regressions. Inputs remain separate and non-retirable; outputs cannot be retired or overwritten after publication. |

An output accumulator may take a slot formerly occupied by a retired internal
address. Once that output is represented, its storage cannot be taken by another
resource. Thus output retention does not forbid reuse *into* output storage.

## 3. Physical storage and placement

### 3.1 Storage metadata

- Separate buffer identity from logical tensor identity. A physical buffer has
  one declared sort and a finite capacity; distinct buffer identities remain
  distinct even when their sorts and capacities coincide.
- Slot indices are bounded by their buffer capacity. Placement carries the
  proof that a defined address's sort matches its buffer's sort.
- Represent supplied-input storage separately from reusable defined storage.
  A defined placement cannot target an input slot.
- The storage description and placement are static plan metadata. No new
  allocation, relocation or copy annotation is introduced.
- Canonical metadata supplies the existing dense tensor layout and injective
  placement. Existing fixtures keep their logical meaning and observed results.
  Necessary API migrations must not weaken their assertions.

The compiled prototype chose `Allocation` (explicit complete finite buffers,
computable equality, per-buffer sort/capacity, bounded sort-certified `locate`)
and `Slot = InputSlot P ⊕ BufferSlot A`. `Memory`, reads, writes, decoding and
outcomes carry allocation; expansion preserves it. The fresh implementation plan
is `papers/semantics/plan_layer_slice4_plan.md`, with mechanical patches and
observations in the separate record. Equality transport uses proved sort
equalities; there is no conversion between incompatible scalar carriers.
Computable enumeration and slot equality must not require a new global
`DecidableEq S` or a noncomputable instance in the executable checker.

### 3.2 Layout view and reads

- Published resources are represented exactly on `Live pc`.
- Accumulator resources are represented on `Mat pc` and not `Pub pc`.
- Both use the chosen placement, not the old global canonical `place`.
- `readPub` returns memory values only for live addresses. A retired logical
  address returns `none` even if its former slot is occupied again.
- `Decode` follows the same physical placement and remains partial. It cannot
  fill missing outputs with zeros or recover overwritten values from history.
- Empty coordinate domains require no slots; scalar domains require one.

## 4. Validity and the exact checker

Add a named layout-safety clause requiring injectivity on the layout view's
domain. It distinguishes published and accumulator resources, not only logical
addresses or tensors. In particular, it rejects:

- two distinct live published resources sharing a slot;
- a live published resource sharing a slot with a materialized accumulator;
- two distinct materialized unpublished accumulators sharing a slot.

Inactive, untouched or retired resources do not reserve a slot. Reinitializing
the same still-untouched logical accumulator remains governed by existing
`InitOK`; it is not mistaken for overlap between distinct resources.

The computable check enumerates resources from certified tensor/coordinate
lists and checks every boundary, including the initial and final boundary.
Fused validity/checking remains validity/checking of the expansion. Expansion
preserves storage metadata and placement, and its check sees every intermediate
annotation boundary, not only the outer command boundaries.

Preserve the existing coverage, freshness, materialization, readiness and
retirement clauses. Preserve exact `checkPlan_iff` and fused checker parity.
Layout safety is a static safety condition, not a runtime alias detector:
unchecked invalid plans may still run to `done` with corrupted values.

## 5. Refinement and kernels

### 5.1 Relation

Retain reachability, pending/published bookkeeping, mapped-resource memory
agreement, accumulator retention, and `retPub`.

Replace address-indexed `dead` with the unmapped-slot invariant from D3. Its
conclusion applies to unused buffer capacity as well as a slot just freed by
retirement. After reuse it no longer requires that physical slot to be empty.

Layout injectivity is an explicit premise available wherever simulation needs
to distinguish physical slots. The unconditional canonical injectivity theorem
remains a canonical-layout fact, not a theorem about arbitrary placements.

### 5.2 Preservation obligations

| Operation | Required argument |
|---|---|
| `Start` | Install supplied inputs in separate storage; all reusable slots start `none`. At boundary zero the mapped resources are exactly inputs. |
| `execInit` | Newly materialized targets are distinct from surviving represented resources by post-boundary injectivity. Writes install logical zeros under `InitOK`; other unmapped slots remain `none`. |
| `execAcc` | Read the old published view, then update already represented accumulator slots. Injectivity separates destination slots from live sources and other accumulators. Transactional semantic failure is preserved. |
| `execPub` | Change accumulator resources into published resources without writing memory; preserve the physical image and values under the existing publication conditions. |
| `execRet` | Pre-boundary injectivity separates retired members from surviving resources. Clear exactly the freed slots; preserve surviving memory and leave the reference state unchanged. |

Carry these premises through `step_R`, run preservation, progress, terminal
adequacy and the correctness/model theorems. Preserve the existing restriction
that step simulation uses the deterministic reachable `refState`.

Fused prefix transport requires agreement of storage/placement as well as
logical prefixes. Fault-oracle states and outcome types carry the same physical
memory; preserve error-state `R`, no-fault parity and transactional failure
snapshots. Do not introduce a new concrete implementation-error source.

## 6. Acceptance and regression evidence

The requirements below were measured by the landed implementation. The record
contains observed values: actual retired-slot overwrite, rejected live alias
despite unchecked `done`, three pair classes/final boundary, cross-tensor output
decode 2, ℤ/ℚ decode `(11,7/8)`, fused internal-only conflict and post-write
fault-state R. All 281 baseline assertions remain; after fixture-probe closure the total is
367 = 186 `#eval check` rows + 181 proof items (354 at the original checkpoint,
360 after the review fixes).
The follow-up also pins a live output's slot claimed by a later internal tensor,
re-retirement after reuse, and custom zero-capacity storage.
All 64 actual mutation verdicts pass with byte-identical
restoration; this evidence was measured separately from compilation. Supplemental
source-copied probes cover all ten retirement mutations, six reuse computational
mutations and the independent unused-slot consumer, without admitting proofs or
modifying production.

1. Clone `rtInitAfter`, place point 2 in point 0's slot, and retain point 1 in
   its own slot. Prove the checker accepts, the run is `done`, and `R` holds at
   every boundary, including after the reused-slot initialization and write.
   Observe slot transitions, old-address reads, ghost history and decode.
2. Clone that fixture and instead place point 2 in still-live point 1's slot.
   Prove checker rejection and record the actual unchecked run and values.
   Do not assume rejection implies a stuck runtime.
3. Add overlap discriminators for the three resource-pair classes in section 4,
   with nearest legal neighbors. Include final-boundary and fused-intermediate
   conflicts so checking fewer boundaries cannot pass unnoticed.
4. Exercise reuse between different tensors of the same sort, ensuring the
   new buffers are not tensor slots with only renamed metadata.
5. Exercise heterogeneous carriers using `PlanMultiSortTest` as the donor;
   preserve sort-indexed initialization, accumulation, reads and decoding.
6. Include a retained nonempty output using the scalar-role donors, plus
   empty/scalar canonical regressions. The routed chain's empty output alone
   does not establish meaningful output-decoder coverage.
7. Test a fused reuse plan and its expansion, no-fault wrapper parity, and a
   fault after reuse with the error-boundary representation relation.
8. Pin the unmapped-slot invariant before and after retirement and after later
   writes, including unused physical capacity.

Preserve all existing Plan regression assertions modulo required API migration.
Re-measure fixture counts; do not propagate historical counts without checking.
Mutation-test the new checker and invariant regressions, distinguishing a
fixture's discrimination from a library proof that rejects the mutant first.
Use repository mutation wrappers and byte-identical restoration, never
destructive checkout/reset commands.

## 7. Execution and definition of done

After approval:

1. Prototype on the real module split, compile, observe fixture results, and
   verify mutations. Emit per-task patches mechanically from compiled code.
2. Author one bounded implementation plan from those verified artifacts, with
   explicit file/symbol windows, fixture donors and mutation counts.
3. Execute all tasks, migrating every physical-memory consumer, expansion and
   fault wrapper. Update only directly related documentation.
4. Run all four inherited mutation manifests unfiltered and the new manifest.
   If API changes invalidate a mutation target, preserve its semantic intent;
   repair observed diagnostic locations without weakening expected failures.
5. Run the full build and axiom audit. No new `sorry`, `admit`, `axiom` or
   `native_decide` in the Plan files. New theorem axiom reports must contain
   only the permitted standard axioms.
6. Perform fresh whole-branch soundness and spec-to-Lean fidelity reviews.
   Update the Part V "As formalized" paragraphs, proof-status rows, path
   documentation and `Plan/AGENTS.md`, with measured counts and no stale
   claims that reuse is still absent.
7. Record verified results, deviations, skipped work and measured token usage.
   Merge locally only after the full build and reviews pass. Do not push.

## 8. Out of scope

The Section 33.2 two-buffer scan program and its liveness proof; full-history
copy/relocation; dynamic allocation; in-place kernels and snapshots; retiring
inputs; cross-sort reuse; concrete implementation-error sources; and any
connection to the separate checked `Eval/Plan` backend.
