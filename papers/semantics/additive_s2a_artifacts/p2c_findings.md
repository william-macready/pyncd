# P2c findings: mutation controls for T1 / T2 fixtures

Branch `proto-s2a-p3`, tip 92a94309 at start. Cycles run via `leanncd/scripts/mutation-cycle.sh`
(driven by a scratch loop script, one log per cycle). Every cycle: restore hash OK, restored build
passes. `git status --short` is clean after the last cycle. No cycle printed 10 failure lines
(max 5), so none is truncated. Killed cycles are in `p2c_mutations_draft.json` (11 entries,
`mutation-manifest.sh --check` OK); the two survivors are listed only here (a survivor cannot pass the manifest runner).

Targets: T1 = `Semantics.SourceAffineDestinationTest`, T2 = `Semantics.SourceAdmissionAffineTest`.
Files are relative to `leanncd/`. Positions are copied from the observed `error:` lines.

## Table

| Label | Task | File | old -> new | Observed failing positions | Outcome |
|---|---|---|---|---|---|
| T2-M1 range-error slot forced to 0 | T2 | LeanNCD/Semantics/Source/Admission.lean | `slot := some bad } .writeOutOfRange` -> `slot := some 0 } .writeOutOfRange` | none, mutated build passed | **SURVIVED** |
| T2-M2 range check off by one | T2 | Admission.lean | `decide (writeValue f v < a.extent)` -> `decide (writeValue f v ≤ a.extent)` | Admission.lean:343:68 (omega in `fitIndex`) | KILLED by proof, no fixture reached |
| T2-M3 scatter accepts reduce max | T2 | Admission.lean | `!(opts.reduce == .sum \|\| opts.reduce == .rejectCollisions)` -> same `\|\| opts.reduce == .max` inside | SourceAdmissionAffineTest.lean:116:0 | KILLED by guard |
| T2-M4 scatter fill check removed | T2 | Admission.lean | `opts.fill != 0 \|\| ` -> `` | SourceAdmissionAffineTest.lean:119:0 | KILLED by guard |
| T2-M5 support order reversed | T2 | Admission.lean | `firstUIDs (forms.flatMap WriteForm.uids)` -> `(firstUIDs (...)).reverse` | SourceAdmissionAffineTest.lean:93:0 (only the two-axis `Y[a+b]` view) | KILLED by guard |
| T2-M6 scale slot drops coefficient | T2 | Admission.lean | `pure (idxAffineForm e)` -> `pure (match e with \| .scale _ a => (0, [(1, a.uid)]) \| _ => idxAffineForm e)` | SourceAdmissionAffineTest.lean:80:0, 82:0, 112:0, 114:0 | KILLED by guard |
| T2-M7 affine shift READ admitted | T2 | Admission.lean | `\| .const _ \| .scale .. \| .shift .. \| .affine .. =>` -> new arm `\| .shift a _ => let _ ← sourceAxis c .read here a; pure a.uid` before `\| .const _ \| .scale .. \| .affine .. =>` | Admission.lean:520:28 (unsolved goals, a theorem in the mutated file) | KILLED by proof, no fixture reached |
| T2-M8 const slot offset ignored | T2 | Admission.lean | `pure (idxAffineForm e)` -> `pure (match e with \| .const _ => (0, []) \| _ => idxAffineForm e)` | SourceAdmissionAffineTest.lean:86:0, 89:0 | KILLED by guard |
| T2-M9 range error blames first fitting axis | T2 | Admission.lean | `!coordAll shape (fun w => formFits ax f (coordLookup w))` -> `coordAll shape (...)` in `bad` | SourceAdmissionAffineTest.lean:89:0 | KILLED by guard |
| T2-M10 rank check removed | T2 | Admission.lean | `if forms.length ≠ sig.length then` -> `if False then` | none, mutated build passed | **SURVIVED** |
| T1-M1 globalFiber ignores destination | T1 | LeanNCD/Semantics/Source/Fiber.lean | `if Term.globalDestination output term v = p then ...` -> `if True then ...` | Fiber.lean:293:2 (type mismatch in `globalFiber_reenumerate`) | KILLED by proof, no fixture reached |
| T1-M2 collectedBody empty fibers read 1 | T1 | LeanNCD/Semantics/Source/Correspondence.lean | `... x else some 0)` -> `... x else some 1)` | Correspondence.lean:107:6 (rewrite failed in a proof) | KILLED by proof, no fixture reached |
| T1-M3 statement fiber keeps only first term | T1 | LeanNCD/Semantics/Source/ProgramCorrespondence.lean | `(statement.terms.map (...globalFiber...)).sum` -> `... .headD 0` | ProgramCorrespondence.lean:46:2 (type mismatch in `fiber_partition`) | KILLED by proof, no fixture reached |

Totals: 13 cycles (T1: 3, T2: 10); 2 survivors; 4 proof-only kills; 7 guard kills.

## Not run, and why (fail loud)

- **T2 "static range check removed" (planned M1).** Not type-correct: `admitAffineOutput`'s
  `AdmittedOutput` field `dest` is built from the `hfit` proof, so the only way to admit an
  out-of-range write is to change `formFits`/`formsFit`. The off-by-one (M2) is the nearest
  mutation; it failed at a proof, not at a fixture. The `slot` blame mutations (M1, M9) are the
  guard-level substitutes.
- **T1 "`AdmittedStatement.destination` ignores `dest`" (planned M1).** Not type-correct: a
  replacement needs a `Coord (σ.signature t).axes` without using `dest`, and none exists in
  scope. Replaced by T1-M1 (`globalFiber` ignores its destination test).
- **T1 "collapsing write loses its sum" at the `Correspondence.lean`/`Fiber.lean` level.** `foldValues`
  and the `∑` in `globalFiber` are not editable without touching shared code. T1-M3 (statement
  fiber keeps only the first term) is the nearest.

## Findings

1. **T2-M1 SURVIVES: the blamed slot of a range error is only tested at slot 0.** Every
   `isOutOfRange` fixture fails at output slot 0 (`Y[a+1]`, `Y[2*a]`, `Y[2, a]` with const 3,
   `Y[a+b]`), so `slot := some 0` is indistinguishable from `some bad`. T2-M9 (first fitting axis) is
   killed only at line 89 (the `Y[3, a]` fixture, whose slot 0 fails and slot 1 fits).
   Proposed fixture (not added): `Y` over `[a, k]`, `|k| = 2`, write
   `[.free a, .affine (.shift a 1)]`: slot 0 fits, slot 1 images 1, 2, out of range at slot 1.
   ```lean
   #guard refused (admitSourceAffine (snap 2 [a, k]
       (.assign "Y" [.free a, .affine (.shift a 1)] readX))) (outSlot 1) isOutOfRange
   ```
   Accept-neighbour: `snap 3 [a, k]` with the same statement admits.

2. **T2-M10 SURVIVES: the rank check of `admitAffineOutput` has no fixture.** No T2 fixture writes a
   different number of slots than the destination's rank. With the check gone, `formsFit` returns
   false on length mismatch and the error becomes `.writeOutOfRange` at slot 0 instead of
   `.rank`, and nothing notices. Proposed fixture (not added): a rank-1 `Y` written with two
   slots; the rank error's slot is `min forms.length sig.length`, so slot 1, with `.rank 1 2`.
   ```lean
   private def isRank : SourceCause → Bool | .rank 1 2 => true | _ => false
   #guard refused (admitSourceAffine (snap 3 [k]
       (.assign "Y" [.affine (.shift a 1), .free a] readX))) (outSlot 1) isRank
   ```
   Confirm the `.rank` constructor's argument order and that `.rank` carries `(expected, got)` as
   `.rank sig.length forms.length` does in the source before adding.

3. **Proof-only kills mean the fixtures were not exercised (T2-M2, T2-M7, all of T1).** These
   mutations broke the build at a theorem, so they say the proofs are sensitive, not that the
   guards are. The guards behind them (T2 lines 71-76 range accept/refuse neighbours; line 133-137
   read refusals; T1 lines 78-87 fiber rows) were not run against these mutants. T1 is
   structurally so: `Term.globalFiber`, `collectedBody` and `AdmittedStatement.globalFiber` are
   each unfolded by a correspondence theorem, so any value-changing edit fails the proof first, and
   the T1 `#guard`s only matter if a def and its theorem change together. No fixture is proposed;
   guard-level evidence would need a test-side mutation (`indexMap`/`coordOfList` in the test file),
   which this task excluded. T1's guards are therefore **unmeasured**, not shown weak.

4. **T2-M5 is caught by a single guard (line 93).** Support order is observed only through the
   two-axis `Y[a+b]` view (`[7, 8]`); a reordering that keeps a single-axis list is invisible, as expected.

## Budget

Harness tool calls: about 33 by my own count (all tool types counted, including this file's
write and the commit; the first batch of 11 cycles and the 2 added cycles each ran as one
script, so the cycles themselves cost few calls). Within the 40-call budget. Context
peak well under 150k. No breach.
