# P4 / A2 findings: legacy-vs-oracle value guards for the collision-sum scatters (review F4, plan T4-A2)

Branch `proto-s2a-p4` (from `proto-s2a-p3`). Test file only: `leanncd/test/Semantics/SourceDifferentialScatterTest.lean`
(append-only, before `end SourceDifferentialScatterTest`; no production file and no `Differential.lean` change).
Patch: `p4_patches/0001-proto-s2a-p4-legacy-vs-oracle-value-guards-for-the-c.patch`.

## What the guards use
`ComparisonRun.legacyComparison` exists but is a tolerance-profile comparison (`compareNative profile obs`); it is used as
one conjunct (`legacyCompared`). Exactness comes from direct extraction: `legacyCells` (legacy leg's declaration-5 output
bits) and `oracleCells` (the oracle's declaration-5 values as `Float.ofInt num` bits, `none` if any value is not an
integer), compared bit for bit, plus hand-value guards on both. Names/comments say LEGACY-ONLY agreement.

## Guards (line numbers in the committed file)
| line | guard | hand cells |
|---|---|---|
| 235 | `legacyCells fD == handBits [...]` | 1,12,123,234,340,400,0 |
| 236 | `oracleCells fD == handBits [...]` | same |
| 237 | `legacyMatchesOracle fD` (nonempty, bit-equal, `legacyComparison = .compared (.ok .agreement)`) | - |
| 239 | `legacyCells fD' == handBits [0,0,0,10]` | 0,0,0,10 |
| 240 | `oracleCells fD' == handBits [0,0,0,10]` | same |
| 241 | `legacyMatchesOracle fD'` | - |
| 250 | accept-neighbour `legacyCells fN == ...` (`fN` = collision-free `.scatter Y[a+4b] += X[a]*W[b]`, k = 16) | 1,2,3,4,10,20,30,40,100,200,300,400,0,0,0,0 |
| 251 | `legacyMatchesOracle fN` | - |
| 252 | accept-neighbour `legacyCells fN' == ...` (`fN'` = collision-free `.scatter Y[2a] += X[a]`, k = 8) | 1,0,2,0,3,0,4,0 |
| 253 | `legacyMatchesOracle fN'` | - |

Hand values (computed from X=[1,2,3,4], W=[1,10,100] before the first build, in the comment above the guards):
fD cells: c0=1; c1=2+10=12; c2=3+20+100=123; c3=4+30+200=234; c4=40+300=340; c5=400; c6=0. fD': Y[3]=1+2+3+4=10.
All guards passed on the first build that compiled them, EXCEPT `fN` with declared k = 12: that build failed at lines 249/250
(production derives shape 16 for the `a+4b` form, p3_observed (f'): a declared 12 is a shape-binding issue, not a value). The
neighbour was changed to k = 16 (cells 12..15 = 0) and then passed. No hand value was adjusted to match output.

## Mutation controls (target `Semantics.SourceDifferentialScatterTest`; all restored, restore hash ok, restored build green)
| id | file / change | observed failing guard lines (new guards in bold) |
|---|---|---|
| A2-M1 | `Oracle.lean` `total := total + product` -> `total := product` (last occurrence wins) | 134,135,137,138,148,151,182,**236,237,240** (script prints 10 lines via `head`: TRUNCATED at exactly 10, so 241/251/253 may also fail; not observed). The new guards are among the failures. |
| A2-M2 | same site -> `total := if occurrences.length == 1 then total else total + product` (first occurrence of every fiber dropped) | FULL log (`MUTATION_LOG`): 130,131,132,134,135,137,138,140,142,143,144,147,148,151,182,**236,237,240,241,251,253** (21 lines). Legacy-value guards 235/239/250/252 correctly keep passing (the legacy leg is untouched). |
| A2-M3 (legacy, EXPENSIVE, not in the draft manifest) | `Eval/Scatter.lean` `.sum` branch `out.set! oc (if boolDest then Max.max prev val else prev + val)` -> `out.set! oc val` | FULL log: exactly **235,237,239,241** (legacy hand values and legacyMatchesOracle for fD and fD'). The collision-free neighbours (250..253) do NOT fail, as intended: the guards bite only where collisions occur. |

No survivor. No existing guard was edited. M1's expectation list is therefore only the three new guards observed; the draft
manifest `p4a2_mutations_draft.json` (task "T4", two oracle cycles) lists those observed positions (M1: 236,237,240; M2: 236,237,240,241,251,253).

## Notes
* `mutate-and-build.sh` prints only `head` (10) lines of `error:`; set `MUTATION_LOG=<file>` (prefix assignment) to keep the full log.
* A truncated cycle at 10 lines was met once (M1) and is flagged above rather than re-run.

## Builds
1. `Semantics.SourceDifferentialScatterTest` (rebuilt the Differential chain): failed at the `fN` k = 12 guards (above).
2. Same target after the k = 16 fix: green.
3. Cycles M1, M2 (twice: second with the full log), M3: each mutated build failed, restore hash ok, restored build green.
A full `lake build Tests` was NOT run (only the one target and its chain).

## Harness tool calls
About 35 (counted by hand, including the cancelled waits), within the 40 budget.
