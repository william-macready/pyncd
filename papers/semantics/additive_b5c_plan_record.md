# B5c plan: authoring record

Evidence for [the plan](additive_b5c_plan.md). Kept out of the live plan so the plan stays short.

## Spikes and prototype

Two throwaway spike builds on `b45deb9b` sized the blast radius (design note section 5): the rule as
first written failed 8 test modules (the idiom `Out[2*i]` into a declaration over the source axis `i`,
refused with `writerExtentExceedsBox`); with the D5 exclusion, 2 modules and 4 guards (the oracle's
known-difference pins `fH9` and `fR`, and `DefaultF32Test`'s declared-versus-undeclared variant). The
prototype worktree on `329a1e4a` then implemented the rule properly: three commits (T1 production and
native fixtures, T2 oracle, T3 docs); the patches in `additive_b5c_patches/` are `git diff --binary` of
those commits, so they are the text that compiled.

## Observed values (real runs, none hand-derived)

Before any change (`b45deb9b`, reference / checked f64 / checked f32 agree):

| Program (`axis i = 2`, `A = [-5, -2]`) | Result |
| --- | --- |
| single `S[2*i]`, `S` declared `k = 4`, `8`, `3`, or unpinned | shape `[4]`, values `[-5, 0, -2, 0]`, no error |
| single bare `S[i]`, `S` declared `k = 4` pinned | shape `[2]` |
| two writers `S[2*i]`, `S[2*i + 1]`, `k = 8` | shape `[8]` |
| reader `R[k] := S[k]`, `k = 8`, one writer | refused, `sizeConflict 8 vs 4` |
| `te[2*i]` with a synthesized `tensor f64 te(i)` (DF4) | derived `[4]`; the f64 harness (`explicitF64Decls`) synthesizes the declaration from the first use site |

After the patches (`B5cSingleBoxTest`):

| Program | Result |
| --- | --- |
| `one` (`k = 8`) | `[-5, 0, -2, 0, 0, 0, 0, 0]`, shape `[8]` on all three legs |
| `oneEqual` (`k = 4`) | `[-5, 0, -2, 0]` |
| `oneExceeds` (`k = 3`) | `writerExtentExceedsBox "S" 1 0 3 4` on all three legs |
| `oneInferred` | shape `[4]` |
| `bareOne` (`k = 4`) | `[-5, -2, 0, 0]`; `bareOneTight` (`k = 2`) `[-5, -2]`; `bareOneExceeds` (`k = 1`) `writerExtentExceedsBox "S" 1 0 1 2` |
| `idiom`, `identityOne` | shapes `[4]`, `[2]`, unchanged |
| `tropOne` (`k = 8`) | `[-5, -inf, -2, -inf, -inf, -inf, -inf, -inf]`, f32 bits equal |
| `oneReader` | `S` and `R` shape `[8]`, `R = [-5, 0, -2, 0, 0, 0, 0, 0]` |
| `groupsOf` table | `[S] [S] [] [S] [] [] [S] [] [] [] []` over `one oneEqual oneInferred bareOne idiom identityOne tropOne predOne multiAxisOne constOne concat` |
| `routeError one`, `routeError bareOne` | none (still routes) |
| oracle `fH9` | `parity`, `conditionCount 0`, published `[9]` on oracle and both legs (was `known:extent`) |
| oracle `fR` | `nativeFailure`, `conditionCount 0`, names `Y#1` (was `Y`, one condition) |
| SHAPED staged rows | 17 rows, 11 predicted accepts, predicted = observed on all |

## Corrections made along the way

- The first prototype of the oracle predictor treated an `.assign` with an affine slot as a plain
  assign and missed the single-writer refusal; fixed by one rule over bounded slots for both statement
  forms (an affine `.assign` is a scatter after lowering).
- A planned oracle fixture for the D5 idiom was abandoned: the oracle itself refuses the idiom first
  (`writeOutOfRange`), so it never reaches the native legs. The D5 clause in `declaredShapeWins` has no
  isolating fixture; the plan records it as a silently-ignored cell.
- `conditionCount` is defined after `fH9` in `SourceDifferentialScatterTest`; its guard sits with `fR`'s.

## Verification

- Targeted builds green after each step.
- **Final committed prototype tree: `lake-build.sh … Tests JaxExperiment` = `Build completed
  successfully (8841 jobs)`** (the full build after the first fixup, which dropped the identity clauses, failed
  `DefaultF32Test` on the scalar rows `rounding-chain` and `pred-scan`; the rank-0 fixup fixed it and this
  count is from the build after it).
- Mutation manifest: 11/11 PASS on the final committed tree (`mutation-manifest.sh --out`), files restored byte-identically,
  restored builds green. History: the first 12-entry run killed 9 and left 3 alive (two equivalent
  identity-clause mutants, one fixture gap); fixing that and the scalar regression it exposed produced
  the 11-entry manifest.

## Not verified at authoring (executor must)

The patches were not replayed onto a second clean checkout with a build; `git apply --check` and hash
equality are the executor's fidelity gate (plan section 7). Authoring token cost was not measured. No
review lens has read the diff.
