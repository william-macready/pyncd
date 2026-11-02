# F3-a record: the reference scan write sums and errors, like the top level

Branch `worktree-scatter-f3a`, base `0ce996c3` (main after the scatter-geometry B post-landing fixes).
Process weight: Direct path (slice-plan §0), probe first, no plan document. Not pushed.

## Labels

- **F3**: the scan-local scatter gap. Before this work the reference scan write overwrote on a collision
  and skipped an out-of-range write, while the top level (S3a, B6) summed and errored.
- **F3-a**: align the reference scan write (`writeScanStmtSlice`, `Eval/Scan.lean`) with the top level.
  Landed here.
- **F3-b**: the checked scan path admits constant and multi-axis scan slots. Not started, see "Parked".

## What landed

| Commit | Content |
|---|---|
| `8742d84f` | `writeScanStmtSlice`: a collision folds with the state's `Combine` (`stateCombine nm`, the same expression the allocation already used); an out-of-range write is `scatterWriteOutOfRange` (it used to be skipped). Both call sites (base, recurrence) go through it. |
| `6c6198b2` | Fixtures (a) to (d) in `test/Eval/ScanTest.lean`: real sum, product sum, max and min folds, negative bias and negative scale errors. |
| `043e3beb` | Docs for the new behaviour. |
| `02301bc5` | The two review lens findings files. |
| `e590eb21` | Review F1 fix (signed zero), fixtures (f) and (g), review D3, D4, D6 (comment fix, recurrence-site fixture, `end LeanNCD.Eval` restored). |
| `9a3d5988` | Docstring rewrite: copy rule and the full collision list (review F2). |
| `8e01bae1` | Docs truth (review D1, D2, D7, F3 doc, wording slip). Lean edits are comment-only. |

Full build `LeanNCD Tests JaxExperiment`: 8844 jobs green at `e590eb21` and at `8e01bae1` (executor), and
again on the final tip `8e01bae1` (controller run, 8844 jobs, exit 0).

## Semantics, in one place

- A cell starts at `0_K` (real 0, predicate false, max-plus `-inf`, min-plus `+inf`).
- The first write to a cell **copies** (a cell whose bits still equal `0_K` counts as untouched). Later
  writes fold with `⊕` of the state's sort. Copy-on-untouched is value-equal to `0_K ⊕ w`, except for the
  sign of a zero (real sort: `0.0 + -0.0 = +0.0`), and it keeps the reference bit-identical to the checked
  path, which copies a single write. No written-mask is kept, so a cell whose written value is bitwise
  `0_K` still looks untouched and the next write copies over it; value-equal (`0_K ⊕ w = w`).
- An output coordinate outside the state extent, or a slot count that differs from the state rank, raises
  `scatterWriteOutOfRange`. The rank case reuses the constructor and its message is misleading there.
- Across-step collisions cannot occur in admitted programs: bases pin an advancing index to 0 and steps
  write `index+1`. The collisions the reference can now see are within one call (multi-axis row, repeated
  axis UID) or cross-call in hand-built programs (a recurrence writing the current cell; a state that omits a
  scan axis, whose sum depends on iteration order).
- A raw **constant** scan slot never reaches the write: `checkStatePlacements` refuses it
  (`scanWriteRowNotAdmitted`, `affineWithoutSource`). The checked path refuses it too
  (`overlappingScatter`). Both backends refuse it, so F3-b would have to admit it on both sides.

## Review adjudication

Two lenses, run read-only on `8742d84f..043e3beb`. Lens 1: observers of the reference scan and wrongly
changed programs (`additive_f3a_review_siblings.md`). Lens 2: fixtures pin the intent, docs are true
(`additive_f3a_review_docs.md`).

| ID | Sev | Finding | Disposition |
|---|---|---|---|
| L1-F1 (= L2-U1) | P2 | A real-sort state lost a written `-0.0` (`0.0 + -0.0 = +0.0`); reproduced through `compileToScheduled`: reference bits `[0,0]`, checked `[0x8000000000000000, 0]`. Reachable via `leakyrelu` of a tiny negative. | **Fixed** `e590eb21`. Deviation from the lens's option (b): no written-mask, copy when the cell's bits equal `0_K`. Fixture (g) pins the bits; mutant "unconditional fold" killed by (g). |
| L1-F2 | P3 | Collision list incomplete (recurrence writes the current cell; state omits a scan axis). | **Fixed** (docstring, `Eval/AGENTS.md`). A reference guard for "state omits a scan axis" was **not** added (outside F3-a). |
| L1-F3 | P3 | `scatterWriteOutOfRange` misleading for rank mismatch and scan site. | **Doc fixed**. Dedicated constructor **parked**. |
| L2-D1 | P2 | Docs said a constant scan slot is summed by the reference; the reference refuses it earlier. | **Fixed** in six places. |
| L2-D2 | P2 | Two status banners still listed "scan-local overwrite (F3)" as open. | **Fixed** (`backend_missing_functionality.md`, `max_min_aggregation.md`). |
| L2-D3 | P3 | Fixture comment listed "skip" for programs with no out-of-range write. | **Fixed**. |
| L2-D4 | P3 | Recurrence call site covered only by a dense copy. | **Fixed**: fixture (f). Mutant "revert only the recurrence write to overwrite" killed by (f). |
| L2-D5 | P3 | No boolean-state fixture. | **Parked** (about 0.1 dispatch). |
| L2-D6 | P3 | `end LeanNCD.Eval` deleted from `ScanTest.lean`. | **Fixed**. |
| L2-D7 | P3 | F3-a and F3-b undefined. | **Fixed**: defined above and in `additive_scatter_geometry_design.md`. |
| L2-U2 | - | Two dated narratives still say "still overwrites". | **Left alone** (history). |

Mutants (executor-run): original m1 (fold to overwrite), m2 (`stateAgg` ignored), m3 (throw to skip),
plus after the fix M1 (unconditional fold, killed by (g)) and M2 (recurrence write only, killed by (f)).
I did not re-run them. I checked the kill claims against the fixtures by hand.

## Limits

- The checked scan path is unchanged. F3-a makes the reference stricter and summing, but no program the
  checked path newly accepts.
- "Admitted programs have no scan collisions" is audited (lens 1), not proved.
- Fixtures cover real, max and min states. A predicate state is untested (D5).
- Token cost was not measured with `token-report.py`; no Rule 6 total is claimed.

## Parked

- **F3-b** (checked scan path admits constant and multi-axis slots): new write-row kinds, reworked checks
  at nine tripwire sites, a summing compiled step for f64 and f32, reference admission of constants, and
  lifting the compile-time `overlappingScatter` refusal. Decide after a cost probe.
- **Top-level signed zero**: top-level `evalScatter` still folds from `0_K` with no copy rule. Whether the
  checked top-level plan copies a single write (so the same `-0.0` divergence exists at top level since
  S3a) was **not probed**. Cheap to check.
- D5 boolean-state fixture; dedicated rank-mismatch error constructor; reference guard for a state that
  omits a scan axis (iteration-order-dependent sum, hand-built only).
- Slice B parked items are unchanged (see `additive_scatter_geometry_b_record.md`).
