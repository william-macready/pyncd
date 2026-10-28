# B5b plan: authoring record

Evidence for [the plan](additive_b5b_plan.md). Kept out of the live plan so the plan stays short.

## Prototype

Worktree `worktree-b5b-proto`, prepared with `prepare-worktree.sh` from local `main` `2ce6365c`
(Mathlib 8101/8094, 100%). Three commits, one per task: T1 (production + native fixtures), T2
(predictor + oracle rows), T3 (docs). The patches in `additive_b5b_patches/` are `git diff --binary`
of those commits, so they are the text that compiled.

## Observed values (real runs, none hand-derived)

Probes before any change (`342106e4`, `B5NativeTest` helpers `ref64`/`run64`/`run32`):

| Program | Result |
| --- | --- |
| assign scratch `S1[i]` (extent 2) read by `S[k] := S1[k]`, `k = 4` | `[5, 7, 0, 0]` on all three legs |
| scatter scratch `S1[2*j]` (`j = 1`, extent 2) read bare, `k = 4` | `sizeConflict` uid k, `4 vs 2` (reference and plan) |
| same scatter scratch read as `S1[k + w]`, `w = 1` | `[5, 0, 0, 0]` on all three legs |
| `S[i] := A[i]; S[1*i + 2] := B[i]`, `S(4)` | collection accepts; `writerExtentMismatch "S" 1 0 4 2` |
| writer 2 `S[3 - i]` with `i = 2` in an exact group | `sizeConflict`, derived extent 1 (legacy linear boundary) |

After the change (patches applied):

| Program | Result |
| --- | --- |
| `concat` (pinned `k = 4`), both writer orders | `[-5, -2, -7, -3]` on reference, checked f64, checked f32 |
| `concatExact` (`k` unpinned) | `writerExtentMismatch "S" 1 0 4 2` on all three |
| `concatExceeds` (`k = 3`) | `writerExtentExceedsBox "S" 2 0 3 4` on all three |
| `bareMismatch` (pinned `k = 4`) | `[5, 20, 28, 0]`; exact twin keeps `writerExtentMismatch "S" 2 0 4 3` |
| `bareExceeds` (`j = 5`) | `writerExtentExceedsBox "S" 2 0 4 5` |
| `declaredMismatch` (`k = 5`) | `[-5, -7, -2, -3, 0]` |
| `tropBox` / `tropMinBox` (`k = 5`) | `[-5,-inf,-2,-inf,-inf]` / `[-7,inf,-3,inf,inf]`, f32 bits equal |
| `lateMismatch` | 12 values `[3,6,6,3,4,0,13,16,12,7,8,0]`; `lateExact` mismatch `"S" 3 1 3 2`; `lateExceeds` `"S" 3 1 3 4` |
| `negativeWriter` | fits the box by derived extent, then reference `scatterWriteOutOfRange "S#2" [3] [0]` and plan `nodeError 1 (scatterWriteOutOfRange 0 2 3 1)` |
| oracle C1 histogram | `[("writerExtentExceedsBox", 81)]` (no row becomes accepted) |
| oracle hand rows | 11 rows, 7 predicted accepts |
| box-extent-10 overlap rows | `fourLegParity`, values in the plan |

## Verification

- Targeted builds green after each step; no other existing test flipped beyond the pins the plan
  lists (the one full build before the final edits showed no other failures).
- **Final tree: `lake-build.sh … Tests JaxExperiment` = `Build completed successfully (8840 jobs)`**
  on the three committed prototype commits (working tree otherwise clean of Lean edits).
- Mutation manifest: 13/13 PASS across two runs. The first run killed all 13 builds but 7 entries
  named the wrong module in `expect` (`B5bBoxTest` is shadowed by `B5NativeTest`); corrected, and
  those 7 re-ran 7/7 PASS. Mutated files restored byte-identically each time.
- `mutation-manifest.sh --check` on the final manifest: 13 entries, 13 selected, every old-string unique.

## Not verified at authoring (executor must)

The patches were not replayed onto a second clean checkout with a build; `git apply --check` and
hash equality are the executor's fidelity gate (plan section 7). Authoring token cost was not
measured. No review lens has read the diff; the executor schedules both (plan section 7).

## Decisions made by the author

New constructor name `writerExtentExceedsBox`; `sizingView` as the exemption mechanism; the
obligation carries `boxed`, computed from a pinned map passed by `validateScheduled`; oracle value
rows use a local `mkBox` snapshot with extent 10 rather than changing the shared `mk` fixture.
