# S2a T4 stage A (78cecd9d) + stage B (7cf28ba2) review, lens: NO MASKING

Read via `git show` / `git grep` at 7cf28ba2 only (working tree is being mutated by the controller). Nothing built.
Stage C (e54795e9) and the known-accepted items (confirms cause-only at stage B; plan §2 "Deliberately NOT done") excluded.

## Answers to the five questions

1. Conditions: all three are DETECTED from the source (`detectConditions` reads `source.statements` / `snapshot.resolved.stmts`
   only) and CONFIRMED by `confirms` against native legs. `confirms` requires BOTH legs in the code (`legacyCollision && checkedCollision`;
   `legacyCompile .. && .sourceCompilation (.scanAxisNotIter _)`; `.observed l, .observed c _ => shapeOnly l && shapeOnly c`).
   `fMask` is sound for what it targets: Z's constant slot makes the legacy leg fail with `.compile` (overlappingScatter), which
   `legacyCollision` rejects, so the run falls to `nativeFailure`. Stage order `multi ++ collisions ++ extents` matches the pipeline
   (compile, evaluation, output binding); head-only is sound because a later-stage condition is unobservable once an earlier stage fails.
   Findings F1, F2 below are the residual masking surfaces.
2. Count check: restored. `checkFiber` non-bare `expectedCount` enumerates the support box (`forms` uids ++ term read uids, context
   order, same axes/order as `Oracle.termFiber`) and counts assignments whose `formsAt` lands on the cell; every occurrence must
   also land on the cell and be non-duplicate, so the fiber is pinned exactly. `dropOccurrence true` gives `occurrences 3 2` (fE cell 0:
   a=0, b in 0..2) with sums adjusted so only the count is wrong; `dropOccurrence false` (neutral tamper machinery) is `accepted`.
   Bare path unchanged (`bare` test identical to the old condition).
3. `compareSource` -> `sourceDebugAffine` -> `admitSourceAffine`. For every statement shape `admitSource` accepted (`.assign` with all-free
   slots, and all non-assign/scatter statements) `admitAffineStatement` delegates to the same `admitStatement`, so no previously
   accepted program can newly refuse. Changes are on previously-REFUSED shapes only: scatter with free slots + fill 0 + sum/reject
   is newly admitted as a plain assign; a scatter with other policy refuses with `.scatterPolicy` instead of `.unsupported .scatter`;
   non-free assigns refuse (or are admitted) via `admitAffineWrite`. `admitIdentifiedSourceAffine`'s Nodup guard cannot fail on
   zipIdx-derived originals. No test under `test/Semantics/SourceDifferential*` pins a scatter/affine refusal (grepped).
4. T4-06 is redundant: `legacyWithInputs` computes `phase := match error.error with | .compile _ => .compilation | _ => .scheduledEvaluation`
   from the very `EvalError` that `legacyCollision` then matches. `.scatterCollision` is a direct `EvalError` constructor
   (`Eval/Error.lean:284`), never wrapped in `.compile`, so `.scatterCollision` implies phase `scheduledEvaluation`. Only
   raiser is `Eval/Scatter.lean:85` (evaluation). The removed conjunct could never be false when the match held.
5. Neighbours: see table in F4. (6) No `sorry`/`axiom`/`native_decide`/`unsafe`/`set_option`/`implemented_by` in any touched file (rg at 7cf28ba2).

## Findings

- **Major** `confirms` / `.scatterExtentOverridesDeclared` (Differential.lean) masks value divergence on every output, including
  unrelated tensors. Both legs are `.observed` here, but their `outputs` are `.error issues` (shape/length of the one declaration), and
  `compareNative` returns `.disagreement (.bindingIssues ..)` before `compareValues`. `classification` returns
  `knownContractDifference` before `nativeAgrees`, so NO cell of any output (Y or an independent bare tensor Z in the same program) is
  ever compared to the profile's expected bits. Evidence: `shapeOnly` constrains only issues touching `declaration`; nothing
  checks other outputs' values; `observeBindings` drops all output bits when any issue exists (raw bits remain only in
  `report.env`). Concrete shape: fH9 plus an independent bare statement `Z[k] = ...` whose native values are wrong still classifies
  `known:extent`. Why it matters: this is precisely the "known condition explains away an unrelated native divergence" the lens
  forbids, and unlike collision/multi-writer (where nothing runs, so nothing is lost relative to `nativeFailure`) here full values were
  available. Suggested: after the extent condition confirms, compare the remaining outputs (from `report.env`) and fall through on
  disagreement, or record explicitly as accepted/parked.
- **Minor** both-legs requirement is untested for 5 of the 6 halves. Only the legacy half of `scatterCollisionRejected` is
  discriminated (fMask: legacy compile failure, checked capability failure that `checkedCollision` accepts). Surviving mutants by
  fixture inspection (SourceDifferentialScatterTest at 7cf28ba2): `checkedCollision := fun _ => true` (every guard still holds:
  fE/fF have a real checked collision/capability, fMask killed only via legacy); the `.sourceCompilation (.scanAxisNotIter _)` clause of
  `multiWriterScatter` replaced by `true` (fG only has the true case); either `shapeOnly` conjunct of the extent condition (fH9 only
  has both true). No fixture has legacy matching and checked failing differently (e.g. fE-style collision plus an independent
  `convSlot` `.sum` scatter on Z: legacy collides on Y, checked fails by capability on Z, `checkedCollision` absorbs it: cause-only,
  known, but the guard that would document it is absent).
- **Minor** `confirms` `.multiWriterScatter` keys on an incidental error. Legacy half is `toString` substring `"scanAxisNotIter"`;
  both halves accept ANY `scanAxisNotIter` (e.g. from an unrelated scan). The designed slice-1 rejection for this shape is
  `CompileError.multiWriterScatter` from `desugarMultiWriters` (`DSL/Pipeline/Collect.lean:95-96`, called only from `Lowering.lean:592` and
  `ScheduledValidation.lean:133`, not from `compileToScheduled`). If the source->scheduled path ever desugars, fG flips to `nativeFailure`
  (loud, so not masking) and the condition needs rewriting. Worth a comment at `confirms`.
- **Minor** fF' comment is inaccurate and F/F' do not exercise detection. Comment says "no condition", but `detectConditions` still emits
  `scatterExtentOverridesDeclared` for fF' (single writer, `derivedShape = 1*4 + 4*3 = 16` vs declared 12); it simply is not confirmed
  because the checked leg refuses by capability. Also, with `writeCollides` forced to `true` fF' (and fA) would classify identically
  (legacy does not collide, so `legacyCollision` fails): E vs A and F vs F' discriminate only through native confirmation, not through
  `writeCollides`, which has no direct guard. And `derivedShape` is validated only for coefficients 1 and 2 (comment); the 16 for fF'
  is never compared to a native shape.
- **Minor** head-only ordering: a head condition whose predicted production error does not occur (e.g. `writeCollides` true but
  production accepts) blocks later conditions from being tried, so a program that also has a real extent override reports
  `nativeFailure`/`nativeDiscrepancy` instead. Loud, not masking.
- **Question** `fMask` covers differing error KIND only (compile vs evaluation); a same-kind unrelated failure (a second, independent
  `scatterCollision` on Z) is absorbed. Accepted at stage B per plan (T4-08); noted only so the stage-C reviewer checks that
  fixture exists.

### (5) Fixture rows and accept-neighbours (7cf28ba2)

| row | fixture | neighbour | readings differ? |
|---|---|---|---|
| a,b,c | fA, fB, fC parity | each is the accept-side | n/a |
| d,d' | fD (`.sum` conv slot), fD' (`.sum` const slot) both `nativeFailure` | F (same slot, `assign`) | yes: D has no collision condition (policy `.sum`), legacy sums; guard pins only the class, not which leg/cause failed |
| e | fE `known:collision` | fA (drop factor `b`) | yes (fE collides over `b`, fA injective) |
| f | fF `known:collision` | fF' (coef 4) | yes, but see fF' finding |
| g | fG `known:multiWriter` | single-writer `snap 8 ..` = fA | yes |
| h9 | fH9 `known:extent` | fA (k=8) | yes (declared 9 vs derived 8) |
| h6 | fH6 refuses `writeOutOfRange` | fA / fH9 | yes |
| i | fI1, fI2 `nativeFailure` | none needed (neither collision-confirms); I2 does detect a collision that production refuses earlier at compile (not `scatterCollision`) so it stays `nativeFailure`: intended |
| mask | fMask | fE | yes |

Verdict: ACCEPT WITH FINDINGS (0 Critical, 1 Major: F1 extent confirmation skips all output value comparison; 4 Minor; 1 Question). Items 2, 3, 4, 6 clean.
