# F3-a review, lens 2: fixtures pin the intent, docs are true

Branch `worktree-scatter-f3a`, commits `8742d84f` (code), `6c6198b2` (fixtures), `043e3beb` (docs), base `0ce996c3`.
Method: read the three diffs, re-derived fixture values by hand, ran `test/Eval/ScanTest.lean` through `lean-file.sh`
(clean, no output), ran one scratch probe (deleted), value-grepped the repo.

## Findings

### D1 [P2] Constant scan slot is said to reach a reference collision and be summed; the reference refuses it before any write
- Where: `leanncd/LeanNCD/Eval/Scan.lean` `writeScanStmtSlice` docstring ("a slot naming two source axes such as `S[j+q]`, a constant
  slot, or a repeated axis UID in an `.assign` reach a collision here, and they now sum"); `Eval/Plan/Compile.lean` comment above
  `checkScanScatterLHSSlot` ("Constant affine slots and normalized multi-axis rows are BOTH still refused here: the checked scan path does
  not support colliding scan-local writes yet ... the reference already sums them"); `DSL/Pipeline/Structural.lean` header comment
  (raw constant scan slot refused because "the reference already sums it, F3-a"); `Semantics/AGENTS.md` ("Scan-local multi-axis/constant
  slots stay refused ... the reference already sums them, F3-a"); `Eval/Plan/AGENTS.md` ("scan-local constant/multi-axis slots stay
  refused (F3-b, the checked scan path cannot place colliding writes yet ...)"); `additive_scatter_geometry_design.md` state table, row
  "Scan-local scatter", constant column "same" (reference sums).
- OBSERVED: `Eval/Scan.lean` `checkStatePlacements` (shape 9, `affineWithoutSource`) throws `scanWriteRowNotAdmitted` for any `.affine`
  slot whose normalized coefficients are empty (a constant) before state allocation. Probe, hand-built `.scatter "S" [.affine (.const 3),
  .iterAt l 0]` and the `.assign` twin through `evalScanF64`: both gave
  `error evalScan S: base statement 0 for S has an affine slot at dimension 0 that names no source axis`. So the reference never reaches
  `writeScanStmtSlice` with a constant slot; it neither sums nor overwrites it. The implementer's fixture comment (ScanTest, "a CONSTANT
  slot cannot collide here ... source axis is contracted") is right about "no collision" but gives a different reason from the real
  gate, and the docstring sentence two commits earlier in the same series contradicts it.
- Also: a constant slot has no source axis, so it can never collide inside one statement; "checked path refuses constants because it
  cannot place colliding writes" is a wrong rationale. The slots that really collide are multi-axis rows (`j+q`).
- Fix: drop "a constant slot" from the `Scan.lean` docstring list; in the Compile/Structural/Semantics/Eval-Plan/design-table wording
  scope the "reference already sums / colliding writes" clause to the multi-axis row only, and say a raw constant scan slot is refused by
  both backends (`scanWriteRowNotAdmitted` in the reference, `overlappingScatter`/capability in the checked path). Cost: comment-only,
  about 6 sentences, Direct path, no rebuild risk beyond Lean comment edits.

### D2 [P2] Two status banners still list "scan-local scatter overwrite (F3)" as an open gap; the reference no longer overwrites
- Where: `papers/backend_missing_functionality.md:17` ("STILL OPEN: ... scan-local scatter overwrite (F3) and JAX/Python tropical
  execution"); `papers/max_min_aggregation.md:18` (same list). Confirmed unedited by this branch (`git diff 0ce996c3 HEAD --stat` does not
  list them).
- OBSERVED: the sibling banner in `lean_executable_semantics_path_part_5.md` WAS rewritten in the docs commit to "scan-local scatter
  collisions in the checked path F3-b; the reference side F3-a has landed", so the repo now disagrees with itself about whether F3 is open.
  The commit body says "Historical records, plans and the S3b/slice-A design rationale are left as written"; these two are live status
  banners, not records. Not false in spirit (the checked-path gap remains), but the word "overwrite" is now wrong and a planner reading it
  would re-plan F3-a work.
- Fix: replace with "scan-local scatter collisions in the checked path (F3-b; the reference sums since F3-a)". Cost: two one-line edits.

### D3 [P3] Fixture comment (a) lists "skip would leave 0" as a candidate reading for a program with no out-of-range write
- Where: `test/Eval/ScanTest.lean`, comment above fixture (a), and the header "(sum vs overwrite vs skip)".
- OBSERVED: skip only differs from throw on an out-of-range write; (a), (b), (c) have none (extents are the exact reach). The only fixtures
  where skip is a distinct reading are (d). Harmless, but the claim "each construction makes the candidate readings differ" is
  imprecise for skip in (a)-(c).
- Fix: delete "skip would leave 0" from (a). Cost: one comment line.

### D4 [P3] The recurrence call site of `writeScanStmtSlice` is covered only by a dense copy
- Where: `ScanTest.lean` fixtures (a)-(d): every collision / range case is a BASE statement; the recur statement is always `f3Copy`
  (`S[o,l+1] := S[o,l]`, injective, in range).
- OBSERVED: probe (recur and base both `.scatter` with slot `j+q`, sizes l=3) gave `[4,3]` with columns `[1,11,110,100]` repeated in all
  three steps, i.e. the recur site sums too, so the behaviour is right, but no committed fixture pins it. A mutant that reverted only the
  recurrence call (`evalScan`, the `stateNames.contains nm` arm) to overwrite or skip would survive for the real sort (copy onto a zero
  cell: sum == overwrite) and the out-of-range error is never raised at the recur site by any fixture. Under the tropical sort the copy
  would still kill a wrong-combine mutant (`-inf + x = -inf`). The implementer's m1/m2/m3 mutated the shared function, so their kill claims
  hold; they say nothing about call-site mutants.
- Fix: add one recur-site collision fixture (the probe program, expected columns `[1,11,110,100]` x3) and optionally a recur-site
  out-of-range one. Cost: about 15 lines, one dispatch-fraction.

### D5 [P3] No fixture for a boolean (predicate) scan state, though the docs list `∃`
- Where: `Scan.lean` docstring, `Eval/AGENTS.md` ("real `+`, predicate `∃`, tropical `max`/`min`").
- OBSERVED: `combineFor` returns `Combine.bool` (min factors / max terms, unit0 0.0) for a predicate state, so the claim is true by
  construction; but the new fixtures exercise real, max, min only. A mutant making `stateCombine` ignore the predicate arm would survive.
  Also the docs elsewhere note a scan-local scatter into a predicate state is "still accepted by the reference and refused by the checked
  path", so a bool collision fixture is feasible.
- Fix: optional bool twin of (a) with `predicate S`. Cost: about 15 lines.

### D6 [P3] `end LeanNCD.Eval` deleted from the end of `ScanTest.lean`
- Where: `git diff 8742d84f 6c6198b2 -- leanncd/test/Eval/ScanTest.lean`, last hunk (`-end LeanNCD.Eval`, nothing re-added); file now ends
  with the (e) comment.
- OBSERVED: Lean accepts an unclosed namespace at EOF (file compiles clean), so no failure, but it is an unexplained removal unrelated to
  the goal (CLAUDE.md Rule 3) and diverges from sibling test files that close their namespace. The commit body does not mention it.
- Fix: restore the `end`. Cost: one line.

### D7 [P3] `F3-a` / `F3-b` labels are used in shipped comments with no definition anywhere in the repo yet
- OBSERVED: `rg "F3-a|F3-b"` outside the review/probe files finds only this change's own edits; neither label is defined in any record or
  plan. Pre-existing bare `F3` meant "scan-local scatter overwrite" (`additive_s3a_record.md`, `additive_s3b_record.md`); `Wave F F3` is an
  unrelated older label in `Plan/Scan.lean`, `Executable.lean`, `EvalPlan.lean`. The close-out record should define F3-a/F3-b.
- Fix: the F3-a record (planned) states the split. Cost: none beyond the close-out.

## Unconfirmed

- U1. `Scan.lean` docstring: "a cell is written at most once and holds the written value". Folding from 0_K means `+0.0 + (-0.0) = +0.0`
  (sign of zero lost) and NaN handling follows `Combine`; numerically equal under `==`, not bitwise. I did not probe; impact is nil for
  the `==`/`approxEq` comparisons used by the gates.
- U2. Historical landing narratives still say "(scan-local reference write still overwrites; parked)": `papers/semantics/tensor_logic_semantic_gap_audit.md:343`,
  `additive_production_decision_note.md:360`. They describe S3a at its landing and read as dated history; left alone is defensible, a
  one-clause "(since F3-a it sums)" would be cheap.
- U3. I did not rerun the implementer's three mutants (no edits to tracked files allowed); I only checked their claimed counter-values
  against the fixtures by hand (see below) and the full `ScanTest.lean` run (green, no output).

## Fixture audit (task item 1), by hand

- (a) base `S[j+q,0] := X[j]`, X=[1,10,100], j<3, q<2. Slice shape (j,q) (first-seen source-axis order), cell c = j+q. Sum: c0=1; c1=X0+X1=11;
  c2=X1+X2=110; c3=100, matches `[1,11,110,100]`, state shape `[4,2]` (extent 3+2-1). Overwrite, last write in (j-major, q-minor) order:
  c1 from (1,0)=10, c2 from (2,0)=100 -> `[1,10,100,100]`, matches the comment, and differs from sum at c1 and c2. (Differs; good.)
- (b) product: c0=1*3; c1=1*7+10*3=37; c2=10*7+100*3=370; c3=100*7=700. Overwrite `[3,30,300,700]` (last (j,q) per cell) matches. Differs at c1, c2.
- (c) slot `2j+2q`, extent 2*2+2*1+1=7, cells 0,2,4,6 written (2 and 4 twice). Max with X=[-1,-10,-100]: c0=-1, c2=max(-1,-10)=-1, c4=max(-10,-100)=-10,
  c6=-100; odd cells -inf; matches the data. Negative X makes max != last-write (overwrite c2=-10, c4=-100) and max != min (min c2=-10). Sum
  reading `[-1,0,-11,0,-110,0,-100]` (cell 6 = -100) matches. Min twin X=[1,10,100]: min c2=1 vs overwrite 10, c4=10 vs 100, untouched +inf. All
  readings differ. (Good; the sign choice is exactly what makes the pair discriminating.)
- (d) negative bias `S[j-1,0]`, extent 2: first write j=0 lands on [-1,0] with source coord [0]; the asserted error payload
  `scatterWriteOutOfRange "S" [-1,0] [0]` is exact. A skip mutant returns `#[10,10,100,100]`, which is what the commit body reports for m3, consistent.
  Negative scale `S[-2j,0]`, extent 0, first write on [0,0], payload exact. In-range neighbour `S[j,0]`, sizes o=3, gives `X` in both columns.
  The negative-scale case has no one-change positive-scale neighbour in this block (covered by the unchanged S-B fixtures, per comment (e)); the
  neighbour also changes the `o` extent 2->3, which is needed for consistency, not a masking risk.
- Constant slot claim: confirmed by code that it cannot collide (empty normalized coefficients, no source axis, `scanScatterSourceAxes`
  drops it and the RHS contracts any read axis), but see D1: the reference refuses it earlier, so the stated reason is incomplete.
- `throwError` abort: each `run_cmd` aborts at its first failing assertion. Conditionally covered only when an earlier arm fails:
  (c) min arm (after max arm), (d) negative scale and in-range neighbour arms (after negative bias). With the file green all arms ran, so
  there is no coverage loss; it only means a regression reports the first broken arm, not all. Does not matter.
- Mutants: m1 (fold->overwrite) killed by (a), (b), (c-max) per my derivations; m2 (stateAgg ignored -> real sum) killed by (c) only, as
  stated (real fixtures cannot see it); m3 (throw->skip) killed by (d). Claims consistent with the fixtures. Residual: D4 (call-site), D5 (bool).

## Docs audit (task item 2), sentence by sentence

- `Scan.lean` docstring: fold with state's `Combine` (true), error `scatterWriteOutOfRange` (true), cell starts at 0_K (true, `stateCombine nm .unit0`
  allocation), "checked path admits only injective in-range placements ... audited, not proved" (carried over), constant-slot clause FALSE (D1).
- `Compile.lean` / `Error.lean` / `Structural.lean` x2 / `StructuralTest.lean` comments: the multi-axis halves are true; constant halves carry D1.
  `Error.lean` `multiAxisScatterLhs` doc is multi-axis only, TRUE. `Structural.lean` line 1161 comment ("cannot place a raw constant there yet
  (F3-b)") is true and makes no collision claim.
- `Eval/AGENTS.md` (three statements): predicate `∃` is `Combine.bool` (true); "raises the same error since F3-a (it used to skip)" true;
  "a scan-local scatter folds the same way since F3-a" true; "only hand-built programs reach a scan collision (the checked scan path refuses those
  slots, F3-b)" true for `j+q` rows. Sentence lives in Contracts (not an injected Patterns/Pitfalls section).
- `Eval/Plan/AGENTS.md`, `Semantics/AGENTS.md`: D1 only.
- `additive_scatter_geometry_design.md`: state-table row D1 (constant column), non-goal line true.
- `tensor_logic_boundary_policies.md`: "fold the same way in the state's sort and raise the same error since F3-a": TRUE.
- `lean_executable_semantics_path_part_5.md`: true; but see D2 for the sibling banners that were not swept.
- Value-grep: `overwrit|SKIPPED|skipped|last write wins|F3` under `LeanNCD/`, `docs/`, `leanncd/AGENTS.md`, test `overwr|skip`: no remaining false
  scan-write statement in source or tests. In `papers/` (excluding records, reviews, plans, `additive_s3b_*`): D2 (two banners), U2 (two historical
  narratives), plus dated design/plan notes left as history.

## Hygiene (task item 3)

- `git diff 0ce996c3 HEAD -G "[A-Za-z]+\.lean:[0-9]+|Test:[0-9]+"`: empty. No `File.lean:NNN` citations or `Test:` line ranges introduced.
- Edited AGENTS.md nodes: the edits are in `Contracts` bullets (Eval line 64 and 72, Eval/Plan table row, Semantics paragraph). Eval/AGENTS.md
  `## Pitfalls` is 1027 chars and `## Patterns` is 3 lines; neither was touched, none of the three nodes' injected sections exceeds 3k.
  The one long Contracts bullet (Eval line 64) grew by about 500 chars; it is not an injected section.
- Commit bodies: the test commit reports m1/m2/m3 with observed counter-values that match my derivations; "no older fixture failed" and "8844 jobs
  green" are unverified by me (the controller's `lake build` governs). They do not claim mutation coverage of the recur call site or the bool arm.

## Checked and clean

- Fixtures (a)-(c) counter-values and sums re-derived by hand; all candidate readings (sum / overwrite / other sort) differ, including `max` vs `min`.
- (d) error payloads exact, in-range neighbour accepted.
- `ScanTest.lean` compiles clean with the new block.
- No file:line citations; AGENTS injected sections within budget.
- `tensor_logic_boundary_policies.md`, `part_5.md` edits, `Error.lean` `multiAxisScatterLhs` doc, `Eval/AGENTS.md` predicate/tropical/error claims: true.
- No stale "skips silently" / "still overwrites" in `LeanNCD/` source or `test/`.
