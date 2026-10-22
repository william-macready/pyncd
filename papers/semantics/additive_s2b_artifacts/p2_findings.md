# S2b prototype P2: carrier through the whole stack (findings)

Branch `proto-s2b-p2` (scratch, off `proto-s2b-p1` 131bc192). Four layer commits plus this file. New
module `leanncd/LeanNCD/Semantics/Source/SortedDifferential.lean`, new test
`leanncd/test/Semantics/SourceSortedDifferentialTest.lean` (in the `Tests` globs). All outputs below
are `#guard_msgs` captures in that test.

End to end works: a `max`/`min` program goes through admission + selection, oracle (`runWith`), Core leg
(`runSourceAt` at the tropical `K`), `ExtVal` observation, tropical profile, and production bit
comparison. The real path (`compareSource`, `SourceRun`, `NumericalProfile.checkProfile`, every proof
file) is unchanged, and no existing fixture's expected value was edited. Full `Tests` build on the
proto tip: green, 8822 jobs.

## Q4. Shared value type

`Oracle.ExtVal := fin ℚ | negInf | posInf` (`Carrier.lean`, `DecidableEq`). Its `Repr` prints `fin q`
exactly as `ℚ` prints, so a real rendering through it is byte-identical. The carrier record gained
`observe : K → ExtVal`: real `.fin`; max-plus `⊥ ↦ negInf`; min-plus `⊤ ↦ posInf`; toy `OrAnd` `fin 0/1`.

The observation types did NOT switch to `ExtVal`. They take a value parameter with the default `ℚ` (P1's
pattern): `TensorObservation (V := ℚ)`, `TensorDifference V`, `ComparisonCause V`, `ComparisonError V`.
`compareTensors` is generic in `[DecidableEq V]`. Every existing mention still means `ℚ`, so real
comparisons are unchanged by construction. Tropical runs instantiate `V := ExtVal`. Events, contributions,
accumulators, readiness and `SnapshotObservation` stay `ℚ`. These are real-only debug layers (see Q5).

## Q5. Core leg

| Mention group | Became generic? | How |
|---|---|---|
| `elaborateSource` | made `abbrev` | real `At` abbreviations must unify with it |
| `sourceDefined/Valuations/Occurrences/Coordinates/OccurrenceKeys/PublicationKeys/Schedule` + `_nodup/_complete` | yes | `…At source r` over `{K} [Semiring K]`; real names are `abbrev … RationalReference.registry`, and the 4 real theorems used outside the file are restated as one-liners |
| `sourceInputBinding`, `sourceInput`, `runSource`, `runSource_eq`, `runSourceDebug`, `sourceResult_*` | no, real-only | proof-carrying, stated at `RationalReference.ops`; the new `sourceInputBindingAt C` (through `C.ofRat`) and `runSourceAt C source r` (at `semiringOps`) sit next to them |
| `Registry.none K` (new, `Program.lean`) | n/a | empty primitive registry for non-real carriers |
| Observation: `observeTensors` | generic sibling `observeTensorsAt r obs` | only the published cells are needed for parity |
| Observation: events/snapshot/readiness/`SourceRun`/`normalizeOracle*` | no, real-only | a tropical `SourceRun` would have to carry `Sorted : Type 1` |
| ProgramCorrespondence, RawSemanticConnection, Permutation, NumericalProfile, Differential | 0 lines | no tropical theorems; tropical profile is a sibling |

Measured: Schedule + Observation = 158 + 16 changed lines (the stop line was 300), so I did not cut.
Real-only layers are refused loudly, not skipped. The real harness `compareSource` admits through
`admitSourceAffine` (unsorted), so a `max` program is an admission error
(`unsupported nonSum`, fixture). `admitSource`/raw chain still refuse `nonSum`.

Parity (Core vs oracle, `published` comparison in `ExtVal`): agreement on every tropical fixture.
Observed Core `Y` cells (inputs `Z[a,b] = 10a+b-5`, `X = [1,2,3,4]`, `W = [1,10,100]`):

| Program | Carrier | Core = oracle `Y` |
|---|---|---|
| `Y[a] := max Z[a,b]` | maxPlus | `-3, 7, 17, 27` |
| `Y[a] := min Z[a,b]` | minPlus | `-5, 5, 15, 25` |
| `Y[a] := max X[a] W[b]` | maxPlus | `101, 102, 103, 104` |
| `Y[2a] := max X[a]` (affine `.assign`) | maxPlus | `1, -inf, 2, -inf, 3, -inf, 4` (empty fibers) |
| `Y[2a] := min X[a]` | minPlus | `1, +inf, 2, +inf, 3, +inf, 4` |
| `Y[a] := sum Z[a,b]` (through the sorted entry) | real | `-12, 18, 48, 78` |

## Q6. Admission and selection

- Selection key is `admits : AggOp → TensorElementType → Bool` (record field replacing P1's `agg`).
  The ordered table `standardCarriers : List Sorted` uses first match. `Sorted` packages `K` with its
  `Semiring/DecidableEq/Repr`, the carrier and a name. `selectCarrier keys table` returns:
  no statements gives real; one agg and one element type gives the first admitting entry; several aggs
  give `mixedSorts aggs`; one agg with several destination element types gives `mixedElementTypes`; and
  no admitting entry gives `noCarrier`.
- `admitAffineStatement … (sorted : Bool := false)`. With `sorted`, the `rhs.agg` is rewritten to `.sum`
  before the existing code runs. The admitted statement is sort-free, and the aggregation is a
  program-level key read back from the snapshot (`sortKeys`). Because of this, `admitStatement`,
  `StatementFields` and `admitStatement_fields` are untouched.
  `admitSourceAffine snapshot (sorted := false)`, and `admitSourceSorted snapshot table :
  Except SourceDiagnostic (AdmittedSource × Sorted)`.
- Diagnostics: one new arm `SourceCause.sortSelection (error : Oracle.SelectionError)`, plus the
  `SelectionError` type. No exhaustive matcher broke.
- Scatter: today's rule is `fill = 0 ∧ reduce ∈ {sum, rejectCollisions}`, with `fill : Int`. For a
  tropical statement `0_K = ∓inf` is not an `Int`, so §2.3 can never hold. Sorted admission refuses
  every `max`/`min` `.scatter` with the existing `scatterPolicy` (fixture). Hand-built affine `.assign`
  has no fill and is admitted, giving the ±inf fixtures above.
- Fixtures: selection real/max/min, mixed giving `sortSelection (mixedSorts [sum, max])`, unsorted
  entry refusing max, tropical scatter giving `scatterPolicy`. Toy table extension (in
  `SourceOracleCarrierTest`): `(max, f32)` picks `orAnd`, and `(max, f64)` with the toy table picks
  `maxPlus`.
- Gotcha: `Sorted : Type 1`. `do` blocks in `Except _ Sorted` fail universe unification on Type-0 binds,
  so write those functions as a `match`.

## Q7. Tropical numerical profile (`checkSortedProfile`)

Rules:
1. Every finite read is an integer in `[-2^20, 2^20]`.
2. Per occurrence, the partial sums of `|finite reads|` stay at most `limit`. This reuses the
   `subsetProductBound` kind, because `⊗` is `+`.
3. `⊕` (max/min) only selects, so fiber, statement and collection add no magnitude.
4. A finite output cell must pass `checkValue .tensorCell`.
5. `±inf` is its own class (`ExtClass.negInf/posInf`) with bits `0xFFF0000000000000` and
   `0x7FF0000000000000`, never an envelope failure.
6. Non-finite reads are absorbing and are skipped in the bound.

Observed: single max/min and product max/min are in the envelope. With `X[0] = 2^20`, product max trips:
`outsideEnvelope` at the read origin (statement 0, term 0), assignment `[(7,0),(8,0)]`, kind
`subsetProductBound`, value `1048577 > 1048576`.

Not built: a tropical sibling of `checkOracle`'s receipt re-check (it re-derives oracle arithmetic in
`ℚ`). No `±inf` cell has been compared against production bits, because production refuses every program
that produces one (Q8).

## Q8. Differential against production

| Fixture | Classification (sorted harness) |
|---|---|
| `max Z[a,b]`, `min Z[a,b]` (single factor) | `fourLegParity` |
| `sum Z[a,b]` via sorted entry | `fourLegParity` |
| `max X[a] W[b]` | `nativeDiscrepancy`, both legs at `[0]`: expected 101.0 (`4636807660098813952`), observed 100.0 (`4636737291354636288`), production max-TIMES |
| `min X[a] W[b]` | `nativeDiscrepancy`: expected 2.0, observed 1.0 (min-times `1*1`) |
| `Y[2a] := max X[a]` | `nativeFailure`: legacy `evalPlain: scatter Y aggregates with max but fills unwritten cells with a finite value, not the -inf identity`; checked fails at preparation |
| existing `compareSource` on a max program | admission error `unsupported nonSum` (not run) |

The plan must list these as structural known differences with confirmers (S2a pattern):
`tropicalMultiFactor` (ORIGIN-BOUND on the cell's tensor; both legs bit-mismatch) and
`tropicalScatterFill` (legacy message names the tensor; the checked leg's preparation cause must be
inspected and bound). Without them the harness reports `nativeDiscrepancy`/`nativeFailure`, which is
correct but unexplained. Guards to keep: the single-factor parity rows, which are the S3b target
semantics, and the unsorted-entry refusal.

## Per-file change table (P2 diff vs P1)

| File | Must change? | What (lines +/-) |
|---|---|---|
| Carrier.lean | yes | `ExtVal`, `admits`/`observe`, `Sorted`, `standardCarriers`, `SelectionError`, `selectCarrier` (+78) |
| Program.lean | yes | `elaborateSource` abbrev, `Registry.none` (+13) |
| Schedule.lean | yes | `At` forms, real abbrevs, `sourceInputBindingAt`, `runSourceAt` (+158 churn) |
| Observation.lean | small | `TensorObservation (V := ℚ)`, `observeTensorsAt` (+16) |
| Diagnostics.lean | small | V-parameter on cause/error/difference, generic `compareTensors` (53 churn) |
| Admission.lean | yes | `sorted` flag, `sortKeys`, `admitSourceSorted` (+40) |
| Adapter.lean | yes | `SourceCause.sortSelection` (+3) |
| NativeLegs.lean | small | `NativeSource.sorted`, `runNative (sorted)` (11) |
| SortedDifferential.lean | new | oracle/Core in `ExtVal`, tropical profile, native bits, classification (202) |
| NumericalProfile, Differential, ProgramCorrespondence, RawSemanticConnection, Permutation | no | untouched |

## Extensibility re-check (fourth carrier after P2)

A fourth carrier needs its type and `CommSemiring`, a record (`admits`, `ofRat`, `observe`) and one
`Sorted` table entry. Callers pass an extended `table`, as the toy does: 4 lines of record and 1 line of
entry, plus P1's 17-line semiring. There are zero edits to Oracle, Schedule, Admission or
SortedDifferential, and the toy stays in the test file. The limit is the DSL: `AggOp` is closed and
there is no Boolean element type, so a real fourth carrier still needs a DSL key. The toy is keyed on
`(max, f32)` only to demonstrate the mechanism.

## Parked / out of scope (one-line cost)

- Merging the sorted harness into `ComparisonRun`/`Classification` (one harness, one render): about 1 task.
  Needs `SourceRun` to carry a carrier, which makes it `Type 1`, or a sum type.
- Tropical oracle-receipt re-check (generic `checkOracle` over semiring ops): about 1 task.
- Tropical Program/Global-model theorems (`ProgramCorrespondence` at `K`): about 1 task. Not needed for
  executable parity. The `AdmittedSource.program_*` lemmas are already generic.
- `observeTensors` duplicates `observeTensorsAt … id`: unify with an `Option.map id` rewrite, under
  10 lines.
- `mixedElementTypes` may be too strict (it refuses a sum program mixing f32/f64 destinations through
  the sorted entry). Decide in the plan; 0 dispatches.
- An empty-reduction `±inf` reaching production through an extent-0 axis was not probed.

## Proposed task split

| Task | Files | Fixtures | Mutation cycles |
|---|---|---|---|
| T1 value type + carrier record + selection | Carrier, Diagnostics, Observation | 6 (selection real/max/min/mixed, toy table x2) | 2 (first-match order, mixed refusal) |
| T2 generic Core leg | Program, Schedule | 6 Core-value rows (Q5 table) + real regression = full build | 2 (`ofRat` binding, registry) |
| T3 sorted admission | Admission, Adapter, NativeLegs, Source AGENTS | 5 (unsorted refuses max, sorted admits bare/affine, tropical scatter, mixed) | 3 (agg rewrite, scatter guard, sortKeys) |
| T4 tropical profile + sorted differential + known-difference conditions | SortedDifferential (+ NumericalProfile `StructuralCondition` arms) | 8 (Q8 table + envelope trip) | 3 (bound rule, ±inf bits, confirmer origin) |
| T5 (optional) harness integration | Differential, Observation | re-run Q8 rows | 1 |

Split point: T4 with confirmers is the largest, at an estimated 50-60 implementer turns. If confirmers
grow like S2a's, split conditions into T4b. T1 to T3 are each at most about 35 turns.
