# Scatter geometry slice B: review lens 2 (surface grammar, degenerate forms, truth of the package)

Reviewed: plan package on main 5944c140; code at proto tip 2ad72b7c (worktree proto-scatter-geometry-b).
Probes were run with `lean-file.sh` on untracked `spikes/ReviewL2_*.lean` files (deleted at the end).

## Section 1: grammar probes (observed)

Each slot spelling was put in `S[<slot>] := A[a]` through `tlprog!` and the elaborated slot list printed.
Parse result per spelling (constructor in the elaborated `LHSSlot`):

| slot | result |
|---|---|
| `a+b`, `a + b`, `a +b`, `a+ b` | `.affine (.affine 0 [(1,a),(1,b)])` (all four identical) |
| `a + b + 1`, `a + b +  1` | `.affine (.affine 1 [(1,a),(1,b)])` |
| `a + b +1` | PARSE error `unexpected token '+1'; expected ']'` (not a mis-parse) |
| `a +1`, `a+1` | `.affine (.shift a 1)` (scan step reading, reclassified later) |
| `2*a + b`, `2*a+b`, `2 * a + b` | `.affine (.affine 0 [(2,a),(1,b)])` |
| `a + 2*b`, `a + 2*b + 3*c` | multi-term, coefficients kept |
| `2*a + 3*b + 4` | `.affine (.affine 4 [(2,a),(3,b)])` |
| `2*a + 3`, `2*a+3` | `.affine (.affine 3 [(2,a)])` (unchanged single-axis) |
| `a + 3` | `.affine (.shift a 3)` (unchanged) |
| `a + a` | `.affine (.affine 0 [(1,a),(1,a)])` (unmerged) |
| `0*a + b` | `.affine (.affine 0 [(0,a),(1,b)])` |
| `1*a + 1*b`, `a + 1*b + 2` | multi-term (bias 0 / 2) |
| `a + b + c`, `a+b+c` | three terms |
| `x .`, `x.` | `.freeNorm x` (unchanged) |
| `=3`, `= 3`, ` = 3 `, `=0` | `.affine (.const n)` |
| `=3, a+b` | `[.affine (.const 3), .affine (.affine 0 [(1,a),(1,b)])]` |
| `3` | `.iterAt .. 3` (unchanged) |
| `=3+1`, `=3 + 1`, `=a`, `=-1` | parse errors (`unexpected token '+1'` / `'+'` / `unexpected identifier; expected numeral` / `'-'`) |
| `a + b + 1 + 2`, `3 + a + b`, `a*2 + b` | parse errors |
| `x+y+1`, `a + 2*b +1` | parse error `'+1'` |

See findings below.

## Section 2: degenerate forms (observed, programs run through reference, checked f64 and checked f32)

Inputs `A[a]=[1,2,3,4]`, `B[b]=[1,10,100]`, `S` over unsized `k` unless stated.

| program | observed |
|---|---|
| `S[a + a] := A[a] · B[b]` | shape [8], cells `[111,0,222,0,333,0,444,0]` in all three legs; compile accepts |
| `S[0*a + b] := A[a] · B[b]` | shape [3], cells `[10,100,1000]` in all three legs (a is a collision axis); compile accepts |
| `S[0*a] := ...` (single axis) | compile accepts, all legs fail at RUN: `evalScatter S: write to output coord [0] (from source coord [0, 0]) is outside the destination extent` |
| `S[0*a + 0*b] := ...` | same run-time error as above (no placing term) |
| `S[0*a + 0*b + 2] := ...` | run-time error, `write to output coord [2] ... outside the destination extent` |
| `S[=0] := A[a]·B[b]` | shape [1], cell `[1110]`, all legs |
| `S[=3] := A[a]` with `k` unsized | shape [4], cells `[0,0,0,10]`, all legs |
| `S[a + b]` with `k = 2` pinned | all legs fail: `multi-writer S: writer 1, dimension 0: extent 6 exceeds declared box extent 2` |
| `S[=2]` with `k = 2` pinned | all legs fail: `multi-writer S: writer 1, dimension 0: extent 3 exceeds declared box extent 2` |
| `S[3*a + 3*b]` | shape [16], stride-3 cells, all legs |

## Findings

### L2-1 (P3) unspaced bias `a+b+1` is also a parse error; docs only name `a + b +1`
- Location: plan section 2 (line 103), `DSL/AGENTS.md` Pitfall "`S[a + b +1]` is a parse error", `Syntax.lean` comment @ tl_axis_term block.
- OBSERVED: probe `S[x+y+1]` gives `error: unexpected token '+1'; expected ']'`; `S[a + 2*b +1]` same. `S[a+b+c]` and `S[a + b +  1]` parse fine. It is a clean parse error, never a mis-parse (no silent bias drop).
- The natural unspaced spelling `a+b+1` is the more likely user slip than `a + b +1`, and is not named. Single-axis `a+1` stays `.shift` (probe: `a+1` -> `.affine (.shift a 1)`), so the user reads `x+1` as fine and `x+y+1` as broken.
- Fix: widen the Pitfall and the Syntax comment to "any `+1` written with no space before the 1 (`a+b+1`, `a + b +1`)". Cost: 0.1 dispatch (inside T5 patch regen, which changes the T5 blob hashes for `Syntax.lean`, `DSL/AGENTS.md`, patch blob and the section 7 rows).

### L2-2 (P3) plan section 4 task table mis-states the T2 guard count
- Location: plan section 4 table row T2: "F1-F8 ... (8 families, 20 added guard lines) plus `conditionCount fI2 == 0`".
- OBSERVED: `rg -c "^\+#guard" T2-engine-fixtures.patch` = 20 total; 19 are in `ScatterGeometryTest` and 1 is `conditionCount fI2 == 0` (SourceDifferentialScatterTest). So "20 plus conditionCount" would be 21.
- Fix: say "19 added guard lines plus the `conditionCount` guard (20 in the patch)". Cost: 0 dispatch (prose edit; no hash in the table covers the plan file).
- Same check for the other counts: T3 14 added guards (`rg -c` = 14, matches), T4 21 (matches, and `rg -c "^#guard"` on the file = 21).

### L2-3 (P3) all-zero-coefficient rows are accepted at compile and fail only at run time, unpinned
- Location: plan section 2/3 (degenerate forms), `DSL/AGENTS.md` grammar bullet.
- OBSERVED (table above): `0*a + b` is accepted and sums into cell b; `0*a + 0*b` and `0*a + 0*b + 2` (and single `0*a`) compile (`compErr = none`) and every leg fails at run with `write to output coord [..] is outside the destination extent`. The rule is consistent ("accepted iff some term places the write") but the failure is a run-time evaluation error, not a compile error, and the plan says the `Out[0*i]`/zero-coefficient cells are "not pinned".
- A user is mildly surprised that `S[0*a + 0*b + 2]` compiles. No code defect; the docs bullet "`0*a + b` ... behaving as `b`" omits that `a` becomes a summed collision axis (cells are `10*B[b]`, not `B[b]`).
- Fix: either leave parked (plan already lists it) or reword the AGENTS bullet to "`0*a + b` places by `b` and sums over `a`". Cost: 0.1 dispatch for the wording, 0.3 to pin the all-zero run error.

### L2-4 (P3) diagnostic wording for a single boxed writer says "multi-writer ... writer 1"
- OBSERVED: `S[a + b]` (one writer) into pinned `k = 2` fails with `multi-writer S: writer 1, dimension 0: extent 6 exceeds declared box extent 2`; same text for `S[=2]` into `k = 2`.
- This is the B5c boxed-single-writer path reusing the group error text; not introduced by slice B but now reachable from two new surface spellings. Information only; no plan claim is false.
- Fix: park. Cost 0.2 dispatch.

### L2-5 (P3) master design doc status table is stale until the section 8 completion note is added
- Location: `papers/semantics/additive_scatter_geometry_design.md:17` ("Surface syntax ... not parseable"). Historical snapshot (slice A authoring); plan section 8 already requires a completion note for the design note. Information only.

## Section 3: truth of the package

### 3a blob table (clean)
Script (`scratchpad/hashes.py`) recomputed all 32 rows with `git rev-parse <stage>:<path>`: T1 rows at `68a0e93c^` (also equal at tip), T3 rows at `68a0e93c`, T4 rows at `08ff6ba5`, T5 rows at `2ad72b7c`. Output: `32 rows 26 paths`, `mismatches 0`. Patch blobs at main `5944c140` match the five plan values (`0264270c...`, `9f1a2da8...`, `260faaa6...`, `60747c3f...`, `5a5c3b41...`).

### 3b patch file lists (clean)
`rg -n "^diff --git"`: T1 14 files (matches plan's list and "14 files"), T2 2 (ScatterGeometryTest, SourceDifferentialScatterTest), T3 3 (Elab, Syntax, ParseProgramTest), T4 2 (lakefile.toml, ScatterSurfaceTest), T5 13 (DSL/AGENTS.md, Elab, Collect, Syntax, Plan/AGENTS.md, Error, Uid, Semantics/AGENTS.md, test_portfolio.md, ScatterGeometryTest, EdgeCaseTest, KnownGapTest, SourceDifferentialScatterTest). All match the plan per-task lists.

### 3c counts
- Manifest: python load of `_mutations_post.json` gives 17 entries, task labels 9 x `T1`, 8 x `T3`. Entry-to-kill-module mapping matches section 7 caveat (a): entries 1,2 -> B5BoundaryTest; 3,6 -> B5cSingleBoxTest; 4,5 -> SourceDifferentialScatterTest; 7 -> ScatterGeometryTest; 8 -> B5bBoxTest; 9 -> B5NativeTest.
- Line-pinned `expect` strings at tip: B5BoundaryTest 80 `#guard sourceError twoAxes == none`, 81 `explicitConstant == none`; B5cSingleBoxTest 113 `shapesOf idiom ...`, 139 `[groupsOf one, ...`; SourceDifferentialScatterTest 181 `conditionCount fFbig == 0`, 185 `conditionCount fI2 == 0`; B5bBoxTest 61 `refShape concatExceeds`; B5NativeTest 182 `refShape bareExact badIn64`; ScatterGeometryTest 474 `rawInGroup == some (.multiWriterScatter "S")`. Every pinned line holds a guard of the claimed kind.
- "No Lean code fences, no `File.lean:NNN`": `rg -n '```|[A-Za-z]\.lean:[0-9]'` on the plan returns nothing (exit 1).
- Tool-call usage of `mutation-manifest.sh`: usage text `[--cd <dir>] [--check] [--task <id>] [--out <file.md>] <leanncd-dir> <manifest.json> [label-prefix...]` matches plan section 1 (`--check <leanncd> <json>`, `--task T1`, `--task T3`, `--out`).

### 3d T5 doc truth (clean, sampled against code at tip)
- `elabTLLHSSlot` docstring: `x +1` -> `.affine (.shift x 1)`, multi-axis unmerged and source order, `0*a + b` keeps zero coefficient, `=n` -> `.affine (.const n)`: all confirmed by the grammar probes.
- `DSL/AGENTS.md` bullets: scan constant slot `overlappingScatter` (compile) and multi-axis `multiAxisScatterLhs` (preflight): both pinned at `ScatterSurfaceTest.lean` (`scanConstStep`, `scanMultiStep`, line 172).
- `Semantics/AGENTS.md`: "`fI1`/`fI2`/`fMask`/`fFbig` are parity": `SourceDifferentialScatterTest.lean:160,161,163,357` all `== "parity"`. C1 `281/186/38` at `OracleSortRulesTest.lean:115` and `99` at `:508`.
- `test_portfolio.md` KG-reshape rows: do not claim reshape/Kronecker/im2col coverage; claim only that multi-axis parses and runs (confirmed).

### 3e stale-claim greps at tip
- `boundedScatter|isConstUnit|constUnitPrefix|checkReservedAxisNames|reservedAxisName` over `leanncd` (`*.lean`, `*.md`, excluding `docs/superpowers`, `.lake`): exactly 3 hits, all in `ScatterGeometryTest.lean` (lines 385, 388, 408), all saying the names are deleted. Matches plan.
- `slice B|Slice B` over `LeanNCD`: 10 hits in 8 files, all past tense. Matches plan.
- `until slice B|slice B will|remain refused|does not parse|multiAxisScatterLhs|multiWriterScatter|scatterOrAffineLhs` over `leanncd` and `papers/semantics/*.md` (non-historical): no hit is now false. Checked in context: `Collect.lean:29` ("hand-built schedule ... remain refused"), `Uid.lean:109` (`outside bounded B5: predicate destination, raw constant scatter, or unlowered scatter-shaped assign`), `Semantics/AGENTS.md:155,178`, `Eval/Plan/AGENTS.md:37,56`, `Error.lean:277-282`, `Compile.lean:96-131` ("scan-local only"), `OracleSortRulesTest.lean:617,638`. Historical hits only in landed-slice plans and artifacts.

## Section 4: executability for a non-Claude executor
- `prepare-worktree.sh` (referenced as `.claude/skills/new-slice/prepare-worktree.sh`) is a repo bash script; the `git worktree add <repo>/.claude/worktrees/scatter-geometry-b-exec -b scatter-geometry-b-exec main` line branches from LOCAL main as stated (new-slice SKILL's EnterWorktree-from-origin trap is explicitly corrected in plan section 1). No tool names, hooks or skills are required by the plan; the only Claude-adjacent references are the `.claude/` paths of a repo script and the "new-slice finish sequence" (a markdown skill file a human can read). P3, not a defect: a GPT executor needs that SKILL.md readable; confirm it is in the executor's checkout (it is tracked).
- Section 1 preamble forbids `cd x && y`; the plan's own commands (`git worktree add`, `bash .../prepare-worktree.sh "from inside it"`) say "from inside it" which for a non-`cd` shell means an absolute path invocation; fine but not spelled. P3.
- Job counts: plan section 3 line 187-188 states each count with its observation basis (T1 only 8843, T1+T2 8843, T1-T4 and T1-T5 8844; "T3 alone was not built separately" disclosed). The T3 check in section 4 only asks for a targeted build, consistent.

## Unconfirmed (not run)
- "15 re-pinned guards in 7 modules": the T1 patch removes 25 `#guard` lines (`rg -c "^-#guard|^-  *#guard"`); mapping removals to 15 re-pins (some multi-line or deleted) was not done. The 7 test modules re-pinned are confirmed by the file list (StructuralTest, B5BoundaryTest, B5cSingleBoxTest, ScatterGeometryTest, OracleMixedRefusalTest, OracleSortRulesTest, SourceDifferentialScatterTest).
- Risk-table F-label counts beyond the T2/T3/T4 patch guard counts.
- `git apply --check`, a full `lake build` and the real manifest run (explicitly not allowed here); job counts 8843/8844 not re-observed.
- Size-0 axes in a multi-axis slot with BOTH axes empty: my probe passed a size-4 `A` against `a = 0` and got an unrelated `axis size conflict`, so it is not evidence. The one-empty-axis case (`b = 0`) is pinned by `ScatterSurfaceTest.emptySurf` (shape [4], zeros) and was not re-run.

## Checked and clean
- New grammar changes no previously valid parse: every new alternative needs >= 2 axis terms or a leading `=`, both parse errors at base 759bbf56; probes of all existing forms (`x`, `x .`, `x.`, `3`, `x +1`, `x+1`, `a + 3`, `2*a + 3`, `2*a+3`) give the same constructors as the U2 pin. No ambiguity: nothing returned a choice-node or elaboration error.
- `=` handling: no new combined token (`"=" num` is two tokens); `tl_rel_op`, predicate `=` (`tl_bool_expr`), `axis i : ℕ = n` and `iter l = n` rules are untouched. `ParsePredicatesTest` and `IterDeclTest` re-ran clean with `lean-file.sh`; the full tip build (8844 jobs per the plan) covers ~60 test modules using `tlprog!`.
- Spacing variants `a+b`, `a +b`, `a+ b`, `a + b`, `2*a+b`, `2 * a + b` all give the same constructor; `[=3]`, `[= 3]`, `[ = 3 ]` identical; `[=0]` accepted as `.const 0`; `[=3+1]`, `[=a]`, `[=-1]` are parse errors, `[3]` stays `.iterAt`.
- Degenerate behaviours stated by the plan (`a + a` -> shape [8], `0*a + b` -> shape [3]) reproduce in all three legs.
- Hash table, patch blobs, patch file lists, manifest counts and pinned lines, section 7 diff-size claim (26 leanncd paths = `git diff --stat 759bbf56 2ad72b7c` minus the two paper files), fence/line-number grep, sweep greps: all true.
