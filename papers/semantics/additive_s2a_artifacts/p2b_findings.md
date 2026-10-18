# S2a P2b findings: the exact oracle on affine write slots

Branch `proto-s2a-p2b` (from `proto-s2a-p2a` @ dc23ea69). Code commits eccc3676 (oracle +
Observation), 923542dd (fixtures + lakefile), d1dfd0e4 (fixture 9). Patches in `p2b_patches/0001..0003`.
Mutation draft: `p2b_mutations_draft.json` (9 cycles, task "T3", all run, all killed).

## 1. Oracle design (Oracle.lean, +23/-2)

- `Cause.writeOutOfRange (slot : Nat) (value : Int) (extent : Nat)` (new constructor, last).
- New `private def destination origin shape assignment forms`: for each destination slot j the form
  `c0 + Σ coef * assignment[uid]` is evaluated as an `Int`; `0 <= v < shape[j]` gives `v.toNat`,
  else `Unavailable ⟨origin with slot := some j, .writeOutOfRange j v extent⟩`. A uid missing from the
  assignment is `.missingUID` at that slot; a form/shape length mismatch is `.coordinateRank`.
- `termFiber` now computes `output` with `destination … statement.output.forms` over the shape of the
  destination TABLE ENTRY (`entry.axes.map extent`), never `dest`, `sourceSlots` or `shape` from the
  admitted output. The support enumerated is `forms.flatMap WriteForm.uids ++ reads`.
- Unchanged: `run`, `contribution`, the per-term sum, `coordinates shape` iteration (every
  destination cell gets a row per writer, so empty fibers are rows with no occurrences and value 0;
  fixture 1 reads zeros at odd cells), same-LHS summing in `run`, `slots` (still used for reads).
- Bare statements: forms are `indices.map single`, so the enumerated axes (a context-order filter by
  UID set) and every produced `Occurrence` are the same as before. Evidence: no existing test was
  edited and the full `Tests` build is green (section 6).
- Independence: a `dest`-based oracle would be semantically equal by `FormsSpec`, so no fixture can
  tell it apart; independence is by construction (the oracle's code never mentions `dest`), not by
  test. Mutation (i) is therefore "forms ignored, old `output.indices` path", the observable variant.

## 2. Observation findings (Observation.lean, +41/-0)

- The old `normalizeOracleContribution` assumed row.coordinate is an assignment of the output INDEX
  axes (`statement.output.indices`, inverted by `assign`). For an affine statement that is wrong in
  three ways, and two are SILENT: (a) rank mismatch (`Y[2, a]`: 1 index, 2 coordinates) throws `.rank`;
  (b) `Y[2*a]` (1 index, 1 coordinate) inverts to `a := coordinate`, which is wrong and yields a bogus
  occurrence; (c) structurally an oracle row is a destination CELL, which has 0..n executor
  occurrences (n > 1 on collisions, 0 on empty fibers), but `OracleRow.occurrence` holds at most one.
- Fix, minimal and without touching `OracleRow` or any P3-owned consumer: the existing function
  throws the new `NormalizationCause.nonBareWrite` for a statement whose forms are not
  `indices.map WriteForm.single` (fail loud; bare path byte-identical), and a new
  `oracleOccurrences source row : Except NormalizationError (List ContributionObservation)` gives the
  executor-comparable occurrences: bare = old `occurrence.toList`; non-bare = each distinct restriction
  of the ORACLE's own occurrence assignments (all terms) to `statement.output.context.axes` uids (the
  executor key order, `outputAssignments`), valued by the sum of `Occurrence.value` over the terms/
  contracted fibers sharing it. New cause `missingAssignment uid` if an oracle assignment lacks an
  output axis.
- Known limitation (not fixed): an executor occurrence whose contracted fiber is EMPTY (an extent-0
  contracted axis) leaves no oracle occurrence, so it is not recovered for non-bare rows. Bare rows
  recover it by inversion as before. No fixture covers it.
- P3 consequence: `Differential`/`NumericalProfile`/`Diagnostics` still consume `OracleRow.occurrence`
  (an `Option`) and will now see `nonBareWrite` for affine statements via `normalizeOracle`. P3 must
  switch them to `oracleOccurrences` (list valued). Not touched here per the brief; no current test
  runs the differential on an affine statement (full `Tests` is green).

## 3. Fixtures (test/Semantics/SourceOracleAffineTest.lean, new, 171 lines)

Inputs `X[a] = [1,2,3,4]` (decl 3), `W[b] = [1,10,100]` (decl 4), `|a| = 4`, `|b| = 3`, `Y` decl 5.
Donors: `SourceOracleTest` (oracle value + contribution-row assertions, `Oracle.run` + order),
`SourceProgramCollectionTest` (executor-vs-oracle tensor comparison; the tensors comparison uses
`SourceProgramFixtures.tensorObservations`/`outcomeKind`), `SourceAdmissionAffineTest` (snapshot shape,
`.affine`/`.scale`/`.shift`/`.const`), `SourceDifferentialGeometryTest` (`canonicalContributions`
== normalized oracle rows). `parity s y occ` asserts: oracle `Y` == hand `y`; executor completed and its
tensors equal the oracle tensors; executor `canonicalContributions` of the events == the
oracle-derived canonical occurrences (non-empty); executor contribution values == hand `occ`. The
executor is run on the `admitSourceAffine` source (`runSourceDebug`), since `sourceDebug` goes through
the default entry.

| # | line | Statement | Hand-computed Y (and executor occurrence values) |
|---|---|---|---|
| (c) | 75 | bare neighbour `Y[a] := X[a]`, Y over a | [1,2,3,4]; occ [1,2,3,4] |
| 1 | 79 | `Y[2*a] := X[a]`, \|k\|=7 | [1,0,2,0,3,0,4]; occ [1,2,3,4] |
| 2a | 84 | `Y[2,a] := X[a]`, Y over [k,a], \|k\|=3 | [0,0,0,0, 0,0,0,0, 1,2,3,4] |
| 2b | 89 | `Y[1+0*a] := X[a]`, \|k\|=3 (all collide) | [0,10,0]; occ [1,2,3,4] |
| 3 | 100 | `Y[a+b] := X[a]*W[b]`, \|k\|=6 | [1,12,123,234,340,400]; occ [1,10,100,2,20,200,3,30,300,4,40,400] |
| 3' | 104 | cell [2] of 3: fiber assignments `[(7,0),(8,2)],[(7,1),(8,1)],[(7,2),(8,0)]`, outputs `[2]`x3, values [100,20,3], cell 123 | |
| 4 | 120 | `Y[a+2] := X[a]`, \|k\|=6 | [0,0,1,2,3,4] |
| 5 | 125 | diagonal `Y[a,a] := X[a]`, Y over [a,a] (bare path) | 16 cells, Y[i][i] = X[i] |
| 6 | 131 | `Y[2*a] := X[a]*W[b]` (b contracted), \|k\|=7 | [111,0,222,0,333,0,444]; occ [111,222,333,444] |
| 7 | 140, 141 | `Y[a] := X[a]` + `Y[b+1] := W[b]`, Y over a, both orders | [1,3,13,104]; occ [1,2,3,4,1,10,100] / [1,10,100,1,2,3,4] |
| 8 | 145 | `Y[2] := W[b]` (all-const forms), \|k\|=4 | [0,0,111,0]; occ [111] |
| out-of-range | 158, 159, 161 | admitted bare statement with tampered forms: `[2a]` -> `.writeOutOfRange 0 4 4`; `[a-1]` -> `.writeOutOfRange 0 (-1) 4`; neighbour `[a]` runs | |
| 9 | 168 | `Y[a+b] := X[a]` (b only in the form), \|k\|=6 | [1,3,6,9,7,4]; occ [1,1,1,2,2,2,3,3,3,4,4,4] |

Accept-neighbour (c): the bare `Y[a] := X[a]` goes through the same `parity` helper and gives the old
answer; fixture 5 is itself a bare-path fixture (diagonal). I used ONE shared bare neighbour for all
fixtures, not one bare variant per fixture (the brief's "e.g." wording); say so if a per-fixture
neighbour is wanted. Fixtures that must tell readings apart are non-symmetric (X = [1,2,3,4], W =
[1,10,100]); the convolution values are all distinct.

## 4. Mutation cycles (all run via `mutation-cycle.sh`, target `Semantics.SourceOracleAffineTest`)

Every cycle: `mutation_exit=1 restore_hash_exit=0 restored_build_exit=0` (PASS: mutation broke the
build, restored build green). Positions are copied from the observed output, as `SourceOracleAffineTest.lean:L:0`.
Cycles (i), (iii) and (vi) printed exactly 10 error positions: the script may truncate its listing
at 10, so further failures in those cycles are neither confirmed nor excluded.

| # | file | old -> new | observed failing lines |
|---|---|---|---|
| i | Oracle.lean | `destination … forms` -> `slots … output.indices` | 79 84 89 100 104 120 131 140 141 145 (not 125: bare diagonal; not 75) |
| ii | Oracle.lean | `total := total + product` -> `total := product` | 89 100 104 131 145 168 |
| iii | Oracle.lean | `value + coef * …` -> `value - coef * …` | 75 79 84 100 104 120 125 131 140 141 |
| iv | Oracle.lean | `let mut value : Int := form.1` -> `:= 0` | 84 89 120 140 141 145 159 |
| v | Oracle.lean | `pure ⟨term.origin, occurrences, total⟩` -> empty fiber 1 | 79 84 89 120 125 131 140 141 145 |
| vi | Observation.lean | non-bare guard -> `unless true do` (old inversion path) | 79 84 89 100 120 131 140 141 145 168 |
| vii | Oracle.lean | `else throw (…writeOutOfRange…)` -> `else pure (value % extent).toNat` (wrap) | 158 159 |
| viii | Observation.lean | `(g.1, g.2 + o.value)` -> `(g.1, o.value)` | 131 145 |
| ix | Oracle.lean | `support := forms… ++ reads` -> `[] ++ reads` | 168 |

No survivor. Cycle (ix) first looked like a survivor risk: fixtures 1-8 all read every form axis, so
omitting the forms from the support changed nothing; fixture 9 (axis only in the form) was added to
kill it and is its only killer. Cycle (viii) is killed only by the two fixtures with a contracted
axis (6, 8). Fixture 9 and `#guard 168` are the last fixture in the file; the file ends at line 171
(`end` at 171). If fixtures are appended later, `expect` line numbers above stay valid only for edits
after line 171.

## 5. Per-file counts (vs dc23ea69)

| File | + | - |
|---|---|---|
| LeanNCD/Semantics/Source/Oracle.lean | 23 | 2 |
| LeanNCD/Semantics/Source/Observation.lean | 41 | 0 |
| lakefile.toml | 2 | 1 |
| test/Semantics/SourceOracleAffineTest.lean (new) | 171 | 0 |

No existing test edited. Not touched: NumericalProfile, Differential, Diagnostics, NativeLegs,
`DSL/`, `Eval/`, Admission.

## 6. Builds and budget

- `LeanNCD.Semantics.Source.Observation` (built Oracle too): green, 8517 jobs.
- `lean-file.sh test/Semantics/SourceOracleAffineTest.lean`: clean (twice, before/after fixture 9).
- Each mutation cycle built `Semantics.SourceOracleAffineTest` (8520 jobs) mutated and restored.
- `LeanNCD Tests` (one run, tip d1dfd0e4): `Build completed successfully (8818 jobs)` (baseline 8817, +1 new test module). Includes
  `Semantics.AxiomAudit`: "6564 constants under LeanNCD.Semantics use only standard axioms" (P2a: 6511).
  No sorry, native_decide or new axiom.
- Not run separately: `LeanNCD` alone (covered by the `LeanNCD Tests` run, which builds it) and
  `Semantics.AxiomAudit` (part of `Tests`; see the result line above).
- Harness tool calls: about 57 (budget 60); context peak well under 250k. One avoidable overspend:
  the first lake-build printed ~25k tokens of replayed warnings because its output was not redirected.

## 7. Gaps and open items (fail loud)

1. No statement/source-level theorem that the oracle's `destination` equals `dest ∘ project`
   (the oracle is tested, not proved, per the brief).
2. `oracleOccurrences` cannot recover executor occurrences for empty contracted fibers of non-bare
   rows (section 2); no fixture.
3. The scatter statements (`.scatter` with `reduce := sum`/`rejectCollisions`) are admitted by P2a but
   have NO P2b oracle/parity fixture; they run the same affine path as `.assign` in admission, but
   `rejectCollisions` semantics (collision must be an error) is not exercised by the oracle at all
   (the oracle sums collisions). P3/S3 must decide.
4. The P3 differential (`Differential`/`NumericalProfile`/`Diagnostics`) is not yet affine-aware
   (section 2).
5. No AGENTS.md update (prototype).
