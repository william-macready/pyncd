# S2b: tropical (max-plus, min-plus) carriers in the Source oracle and differential: implementation plan

Status: prototyped (P1, P2), prototype replayed as per-task patches and verified; this plan executes them.
Base: slice branch `worktree-additive-s2b-tropical-carriers` at `e937e895` (local `main` `5e9bfdf0`, S2a landed,
plus the design-note §6.1 commit). Worktree: `/Users/williammacready/code/python/pyncd/.claude/worktrees/additive-s2b-tropical-carriers`
(Lean project `<wt>/leanncd`). This branch IS the execution branch: plan, record, patches and manifest are committed on it.
Rationale: `papers/semantics/oracle_extension_s2_design.md` §6 and §6.1 (decisions, user-approved 2026-10-19).
Prototype evidence: `papers/semantics/additive_s2b_artifacts/p1_findings.md`, `p2_findings.md` (also on the scratch branches
`proto-s2b-p1` `131bc192`, `proto-s2b-p2` `3fcb6c54`; do not merge them). Authoring-verification record:
`papers/semantics/additive_s2b_record.md` (not here).
Shipped patches: `papers/semantics/additive_s2b_files/patches/` (`leanncd/` paths only, names `T<k>-NN-slug.patch`).
Manifest: `papers/additive_s2b_mutations_post.json`: 9 cycles (T1 2, T2 3, T3 2, T4A 2), all observed to fail with their
`expect` strings and to restore (9/9, authoring dispatch B). T4B has NO cycles yet (not prototyped; `T4-M3..M5` are written by
the T4B dispatch once the observed causes exist). No cycle may be hand-written during execution.

## 0. Goal, process weight, fixed decisions

**Goal.** The Source differential's exact oracle evaluates single-sort programs over the real, max-plus and min-plus
semirings, so S3b (tropical sorts in production) has an independent reference. Concretely: (1) the oracle is generic in a
carrier `K`; (2) a sorted admission entry selects the carrier from the program's aggregations and refuses a mix; (3) the
executed Core leg runs at the same `K`; (4) a sibling sorted differential compares Core, oracle and production bits in an
extended-value type, with a tropical numerical profile and two structural known-difference conditions
(`tropicalMultiFactor`, `tropicalScatterFill`). The real path (`compareSource`, `SourceRun`, `checkProfile`, every proof
file) is unchanged by construction; no existing fixture's expected value is edited.

**Process weight: Full.** New capability over a soundness surface (differential reference for a new algebra), 4 code tasks
plus a docs sweep, 14 patches (10 regrouped from the prototype commits, 4 new audit/discoverability patches), about 12
mutation cycles (`slice-plan` §0). The patches carry about 1300 lines, so execution is mostly patch application; the one
non-prototyped part is T4B (known-difference conditions).

**Fixed decisions (do not reopen; user, 2026-10-19, design note §6.1).**
- Single-sort programs: all `sum` is real, all `max` is max-plus, all `min` is min-plus. A mix is refused with
  `SourceCause.sortSelection (SelectionError.mixedSorts aggs)`. Casts across sorts are out of scope (later item).
- Carriers: min-plus `MinPlus := Tropical (WithTop ℚ)` (Mathlib laws); max-plus `MaxPlus := Tropical (WithBot ℚ)ᵒᵈ` plus a
  6-line `LinearOrderedAddCommMonoidWithTop (WithBot ℚ)ᵒᵈ` instance. Negation transport rejected (a missed sign flip at any
  boundary is a silent wrong answer). `0_K` is `-inf`/`+inf`, `1_K` is `0`, `⊕` is `max`/`min`, `⊗` is `+`.
- Carrier record `Oracle.Carrier K = {admits : AggOp → TensorElementType → Bool, ofRat : ℚ → K, observe : K → ExtVal}`.
  `0/1/⊕/⊗` come from `[Semiring K]`, the same instance the Core leg lowers through (`semiringOps`). Selection is a
  first-match table `Oracle.standardCarriers : List Oracle.Sorted` keyed on `(agg, destination element type)`.
- **Extensibility requirement (user).** A further semiring is one carrier record plus one table entry, with NO edit to
  oracle evaluation, `Schedule` or `Admission`. Proof obligation: a toy fourth carrier (`OrAnd`, Boolean or/and) defined in a
  TEST file only, selected through an extended table (T1 fixtures). The limit is the DSL, not the oracle: `AggOp` is closed
  and there is no Boolean element type, so a real fourth carrier still needs a DSL key; the toy is keyed on `(max, f32)`
  only to show the mechanism.
- `ExtVal := fin ℚ | negInf | posInf` is the one shared observation value. Observation and comparison types take a value
  parameter DEFAULTING to `ℚ` (`TensorObservation (V := ℚ)`, `TensorDifference V`, `ComparisonCause V`,
  `ComparisonError V`; `compareTensors` generic in `[DecidableEq V]`), so every existing mention still means `ℚ`.
  Events, contributions, accumulators, readiness and `SnapshotObservation` stay `ℚ` (real-only debug layers).
- The unsorted entries (`admitSource`, `admitSourceAffine` default) still refuse `max`/`min` with `.unsupported .nonSum`.
  The sorted entry `admitSourceSorted` rewrites the admitted statement's `rhs.agg` to `.sum` BEFORE the existing admission
  code runs: the admitted statement is sort-free and `admitStatement`, `StatementFields`, `admitStatement_fields` are untouched;
  the aggregation is a program-level key read back from the snapshot (`sortKeys`).
- Every tropical `.scatter` is refused with the existing `.unsupported .scatterPolicy` (`fill : Int` cannot equal `∓inf`, so
  §2.3's `fill = 0_K` never holds). A hand-built affine `.assign` (no fill) is admitted: empty fibers give `∓inf`.
- `SelectionError.mixedElementTypes` (one agg, destinations of several element types) stays a refusal on the sorted
  entry ONLY. The unsorted real path is unaffected.
- The Core leg is generic through `…At` forms (`runSourceAt`, `Registry.none`); the real names are abbreviations at
  `RationalReference.registry`. Proofs (ProgramCorrespondence, RawSemanticConnection, Permutation) stay real-only.
- Independence caveat (state it in the review): the oracle and the Core leg take their algebra from the SAME `[Semiring K]`
  instance, so tropical Core-vs-oracle parity checks scheduling, input binding and observation, NOT the algebra. The algebra is
  pinned by the hand-valued oracle fixtures (T1) and by production agreement on single-factor rows (T4).
- f32 is the default dtype; the oracle and reference evaluator are f64-only. Every fixture here declares f64 through its
  `snap` helper. An f32 destination reaches `selectCarrier` (the key includes the element type) but its production leg is not
  compared in f32 here (same scope as S2a).
- Models: Sonnet 5.5 high for implementers and per-task reviewers; Opus 5.5 high for the two final reviews.

## 1. Execution protocol

Patch application is in TASK order (T1..T4), not prototype commit order. If a `git apply --check` fails, STOP and report
(base mismatch; do not hand-merge). Per task:
1. `/usr/bin/git -C <wt> apply --check --index <patch>` for each listed patch in order; then without `--check`.
2. Build the task's targets, ONCE, in the background (`bash <wt>/leanncd/scripts/lake-build.sh <wt>/leanncd <targets>`);
   wait for the notification (no monitors, no polling; never end a turn while a build you started is running).
3. Read the task's production hunks and fixtures in 40-60 line windows; tick the task checklist and its §3 rows.
4. Commit once per task (patches are staged by `--index`; also stage explicitly named added files), message below, ending
   `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Never commit `.claude/settings.json`. No pushing.
5. Report commit hash, targets built, jobs, turns and context peak (Rule 6: <= ~60 turns, <= ~250k) and say if breached.

**Order and dependencies.** T1 first; T2 needs T1; T3 needs T2 (its fixtures run an admitted tropical program); T4 needs T2
and T3. Label note: the prototype's findings number the Core leg T2 and admission T3. This plan runs ADMISSION as T2 and the
Core leg as T3, because the Core-leg fixtures need a program admitted by the sorted entry; each task then owns fixtures it
can fail on. The two groups touch disjoint files; the admission patches were `git apply --check`ed against the T1 state
without the Core-leg patch, and the shipped order (T2 before T3) is the one built and replayed.

**Test-file hand-offs.** `SourceSortedDifferentialTest.lean` is created by T2-03 (admission rows only, imports `Admission`),
extended by T3-02 (Core rows, a local `yCore` helper) and finished by T4-02, whose final text equals the prototype file
byte for byte. `SourceOracleCarrierTest.lean` is created and finished in T1-03.

**Controller steps per task (not the implementer):**
`bash <wt>/leanncd/scripts/mutation-manifest.sh --task <Tn> <wt>/leanncd <wt>/papers/additive_s2b_mutations_post.json`
and read the table. A mutation that does not fail with its `expect` strings is a finding, never a pass.

**Reviews.** Per task one mid-tier review of the commit diff plus the §3 rows the task owns (reviewer appends findings to
`papers/semantics/additive_s2b_review_<Tn>.md` as it goes; 40-60 line windows). Final: TWO Opus lenses (§5). One fix
dispatch per finding group, given only its plan sections.

## 2. Global constraints (exact values)

- **Baseline (measured).** Full `Tests` build on main `5e9bfdf0` (S2a): 8818 jobs, green. The P2 prototype tip measured
  **8822 jobs** (+4: `Carrier`, `SortedDifferential`, two test modules). The author's replay of the ten prototype patches
  (branch `proto-s2b-p4`, tree identical to `proto-s2b-p2`) measured **8822 jobs** for `lake-build.sh <wt>/leanncd Tests`
  (8823 when invoked as `LeanNCD Tests`; the extra job is the extra top-level target), with `Semantics.AxiomAudit` "6826
  constants under LeanNCD.Semantics use only standard axioms". The full 14-patch tree (branch `proto-s2b-p5`, equal to
  `proto-s2b-p5b`, the patches applied in nominal order) measured **8823 jobs** for `Tests` (+1: `SourceSortedAuditTest`), and the
  audit then counts **6997 constants** (T4-03 puts `Carrier` and `SortedDifferential` under `import LeanNCD.Semantics`, so the
  audit covers them). The total is the check: the executor also greps the final `Tests` log for the three new test modules
  (`SourceOracleCarrierTest`, `SourceSortedDifferentialTest`, `SourceSortedAuditTest`). The final T4B code adds jobs only if it
  adds modules (it should add none).
- **Intermediate builds measured by the author** (target set, jobs, all green; these builds were run once each on the replay
  branch `proto-s2b-p4`, builds listed once each; the audit patches T1-04/T2-04/T4-03/T4-04 were built once together on
`proto-s2b-p5`: 8619 jobs for `LeanNCD` plus the three touched test modules): T1 `LeanNCD Semantics.SourceOracleCarrierTest` 8616 jobs; T2 `Source.Admission`, `Source.Adapter`,
  `Source.NativeLegs`, `Semantics.SourceSortedDifferentialTest`, `Semantics.SourceAdmissionAffineTest`,
  `Semantics.SourceAdmissionAcceptanceTest` 8557 jobs; T3 `Source.Program`, `Source.Schedule`, `Source.Observation`,
  `Semantics.SourceSortedDifferentialTest`, `LeanNCD` 8614 jobs; T4 is covered by the full `LeanNCD Tests` build (8823 jobs)
  because `SortedDifferential` is imported only by its test until T4-03. (Job counts include the closure the targets import.)
- **New modules.** `LeanNCD.Semantics.Source.Carrier` (T1; reachable from `import LeanNCD` through `Adapter`),
  `LeanNCD.Semantics.Source.SortedDifferential` (T4; reachable only after T4-03 adds it to `LeanNCD/Semantics/Source.lean`).
  New test modules `Semantics.SourceOracleCarrierTest` (T1), `Semantics.SourceSortedDifferentialTest` (T2 creates, T3/T4 extend),
  `Semantics.SourceSortedAuditTest` (T2-04). Registered in `leanncd/lakefile.toml`.
- **No existing test is edited** (only new test files; `lakefile.toml` gains globs). `git diff --stat main -- leanncd/test` must
  list only new files.
- **Fixture and cycle counts** (`rg -c "^#guard" <file>` counts `#guard_msgs` too; counts below are on the author's final tree):

  | Task | Test file | `#guard` | `#guard_msgs` | Intended cycles |
  |---|---|---|---|---|
  | T1 | `SourceOracleCarrierTest.lean` | 12 + 3 audit | 3 | 2 |
  | T2 | `SourceSortedDifferentialTest.lean` (Q6) + `SourceSortedAuditTest.lean` | 6 audit | 6 | 3 |
  | T3 | `SourceSortedDifferentialTest.lean` (Q5 rows) | 0 | 6 | 2 |
  | T4A | `SourceSortedDifferentialTest.lean` (Q7/Q8 rows) | 2 bits pin | 8 | 2 |
  | T4B | `SourceSortedDifferentialTest.lean` additions (conditions) | to be authored | about 6 | 3 |

- **Observed Core and oracle values** (inputs `X = [1,2,3,4]`, `W = [1,10,100]`, `Z[a,b] = 10a + b - 5`
  = `[-5,-4,-3,5,6,7,15,16,17,25,26,27]`; `|a| = 4`, `|b| = 3`, `|k| = 7`; `Y` is declaration 6; Core cells equal the oracle's
  in `ExtVal`, comparison `published`):

  | Program | Carrier | `Y` cells |
  |---|---|---|
  | `Y[a] := max Z[a,b]` | maxPlus | `-3, 7, 17, 27` |
  | `Y[a] := min Z[a,b]` | minPlus | `-5, 5, 15, 25` |
  | `Y[a] := max X[a] W[b]` | maxPlus | `101, 102, 103, 104` |
  | `Y[2*a] := max X[a]` (affine `.assign`) | maxPlus | `1, -inf, 2, -inf, 3, -inf, 4` |
  | `Y[2*a] := min X[a]` | minPlus | `1, +inf, 2, +inf, 3, +inf, 4` |
  | `Y[a] := sum Z[a,b]` (sorted entry) | real | `-12, 18, 48, 78` |

  Oracle-level carrier rows (T1, `SourceOracleCarrierTest`; `Y[a] := X[a]*W[b]`, `Y[2*a] := X[a]`): real `[111,222,333,444]`,
  `[1,0,2,0,3,0,4]`; max-plus `[101..104]`, `[1,-inf,2,-inf,3,-inf,4]`; min-plus `[2,3,4,5]`, `[1,+inf,2,+inf,3,+inf,4]`.
- **Observed production classification** (sorted harness, `compareSortedSource`, order `some [6]`):

  | Fixture | Classification |
  |---|---|
  | `max Z[a,b]`, `min Z[a,b]`, `sum Z[a,b]` | `fourLegParity` |
  | `max X[a] W[b]` | `nativeDiscrepancy`, both legs `mismatch` at declaration 6 coordinate `[0]`: expected `4636807660098813952` (101.0), observed `4636737291354636288` (100.0): production is max-TIMES |
  | `min X[a] W[b]` | `nativeDiscrepancy`, both legs at `[0]`: expected `4611686018427387904` (2.0), observed `4607182418800017408` (1.0): min-times `1*1` |
  | `Y[2*a] := max X[a]` | `nativeFailure`: legacy `evalPlain: scatter Y aggregates with max but fills unwritten cells with a finite value, not the -inf identity`; checked leg `failure "checked preparation"` (cause NOT yet captured, see T4B) |
  | `max X[a] W[b]` with `X = [1048576,2,3,4]` | `unsupportedNumericalProfile (outsideEnvelope ...)` at the read origin (statement 0, term 0), assignment `[(7,0),(8,0)]`, kind `subsetProductBound`, value `1048577` over maximum `1048576` |
  | existing `compareSource` on a `max` program | `.error (.admission d)`, `d.cause = .unsupported .nonSum` (not run) |

- **Tropical numerical profile (`checkSortedProfile`).** Every finite read is an integer in `[-2^20, 2^20]`; per occurrence the
  running sum of `|finite reads|` stays `<= 2^20` (kind `subsetProductBound`, because `⊗` is `+`); `⊕` selects, so fiber,
  statement and collection add no magnitude; a finite output cell passes `checkValue .tensorCell`; `±inf` is its own class
  `ExtClass.negInf/posInf` with bits `0xFFF0000000000000` / `0x7FF0000000000000`, never an envelope failure; non-finite
  reads are absorbing and skipped in the bound.
- **The `±inf` bit patterns are not exercised by any prototype fixture** (production refuses every program that yields one), so
  they are pinned by a T4A audit fixture against Lean's own `Float.toBits`.

### Deliberately NOT done, with owner (Rule 14)

| Item | Owner / disposition |
|---|---|
| Merging the sorted harness into `ComparisonRun`/`Classification` (one harness, one render) | parked; ~1 task; needs `SourceRun` to carry a carrier (`Type 1`) or a sum type |
| Tropical oracle-receipt re-check (`checkOracle` re-derives arithmetic in `ℚ`) | parked; ~1 task (generic `checkOracle` over semiring ops) |
| Tropical Program/Global-model theorems (`ProgramCorrespondence` at `K`) | parked; ~1 task; not needed for executable parity; the `AdmittedSource.program_*` lemmas are already generic |
| Extent-0 axis producing `±inf` that reaches production (not probed) | parked; ~0.5 task (one probe + fixture) |
| `observeTensors` duplicates `observeTensorsAt … id` (unify, under 10 lines) | parked; cleanup candidate, 0 dispatches of its own |
| Cross-sort programs (`mixedSorts`) and casts, tropical constants, tropical sorts in production | S3b (production) / later sort-family item |
| Scatter ⊕ semantics, `fill`/`CollisionReduce` deletion, range errors | S3a |
| A real fourth carrier (needs a DSL key: closed `AggOp`, no Boolean element type) | unowned; DSL change |
| `sortSelection` diagnostics carry an EMPTY statement origin (`sourceError .statement {}`); a fixture cannot bind a locator | parked; ~0.3 task |
| Core leg exercised with the toy carrier (the toy runs through oracle and selection only) | parked; the Core code is generic over the same `[Semiring K]` that the tropical rows exercise |
| f32-destination production comparison for tropical programs | unowned (same scope as S2a) |

## 3. Sibling audit (case x class): deliverable of T1, T2, T4A

The new refusal arms and the sorted flag sit beside existing refusals; unchanged siblings are invisible to a diff. Classes:
R required refused, A required admitted, **S silently ignored (no fixture, no code path forces it)**. Every S cell below is
closed by a fixture in the stated task (the audit fixtures are Lean blocks compiled against the final tree, listed in the task).

| # | Arm / entry | Case | Class | Pinned by |
|---|---|---|---|---|
| 1 | `sortSelection` | agg mix `[sum, max]` through `admitSourceSorted` | R | T2 `SourceSortedDifferentialTest` Q6 row 4 |
| 2 | `sortSelection` | agg mix `[sum, min]` at `selectCarrier` | R | T1 `pickName` row 4 |
| 3 | `sortSelection` | one agg, destinations f64 and f32 (`mixedElementTypes`) | R | **S**, closed T1 audit `A1` |
| 4 | `sortSelection` | key with no admitting entry (`noCarrier`), reachable only with a custom table | R | **S**, closed T1 audit `A2` |
| 5 | `sortSelection` | empty program selects `real` | A | **S**, closed T1 audit `A3` |
| 6 | `sortSelection` | first-match order: toy `(max,f32)` wins over `maxPlus`, `(max,f64)` still `maxPlus` | A | T1 `pickName` rows 1-3 |
| 7 | `sortSelection` | order of refusals: a mixed program that ALSO has a refused statement reports the statement's cause (admission before selection) | R | **S**, closed T2 audit `A4` (violates both conditions at once) |
| 8 | `scatterPolicy` (tropical) | affine `.scatter` max with `reduce := .rejectCollisions` | R | T2 Q6 row 6 |
| 9 | `scatterPolicy` (tropical) | bare-slot `.scatter` max / min (the guard fires before the slot split) | R | **S**, closed T2 audit `A5` |
| 10 | `scatterPolicy` (tropical) | `.scatter` SUM through the sorted entry is still admitted (the flag must not over-refuse) | A | **S**, closed T2 audit `A6` |
| 11 | `scatterPolicy` (tropical) | hand-built affine `.assign` max/min admitted, odd cells `∓inf` | A | T3 Q5 rows 4-5 |
| 12 | `nonSum` (unsorted) | `admitSourceAffine` bare `.assign` max (`admitStatement` site) | R | T2 Q6 row 5 asserts `isSome = false` only; cause pinned by `compareSource` row (T4A) |
| 13 | `nonSum` (unsorted) | `admitSourceAffine` affine `.assign` max/min (`admitAffineWrite` site, the SECOND `nonSum` check) | R | **S**, closed T2 audit `A7` (both aggs, asserts the cause) |
| 14 | `nonSum` (raw default) | `admitSource` max | R | existing `SourceAdmissionAcceptanceTest` (`rawRefuses parsedNonSum .nonSum`), unchanged |
| 15 | sorted flag | readers of `rhs.agg` elsewhere in `Source` | n/a | audited: only the two `nonSum` sites and the `StatementFields` pin; production readers (`Collect`, `Lowering`, `Structural`, `Eval`; found by `rg -n "\bagg\b" leanncd/LeanNCD`) are not on the sorted path |
| 16 | `StructuralCondition` | exhaustive matchers over the type | n/a | only `confirms` in `Differential.lean`; T4B adds explicit arms there (see T4B) |

## 4. Tasks

All Lake targets are `LeanNCD.Semantics.Source.<Module>` for modules and `Semantics.<TestName>` for test modules, as in
`lakefile.toml`. Symbols are `identifier @ file`; read windows of 40-60 lines, never a whole file over ~20k characters.

Risk/cost table (author-estimated; the prototypes ran P1 and P2 as single dispatches):

| Task | Patches | Fixtures | Cycles | Estimate | Cap, split |
|---|---|---|---|---|---|
| T1 | 4 | 12 + 3 / 3 msgs | 2 | <= 35 turns | no split |
| T2 | 4 | 6 msgs + 6 | 3 | <= 35 turns | no split; `Admission.lean` rebuild is the long step (background) |
| T3 | 2 | 6 msgs | 2 | <= 35 turns | no split |
| T4 | 4 + T4B (no patch) | 8 msgs + bits pin + about 6 | 2 + 3 | A <= 25, B 40-60 turns | TWO dispatches: A = T4-01..T4-04 (patches, build, label cleanup), B = T4B (new production code, then fixtures) |

Execution should cost far less than prototyping (it applies patches); the budget statement is in §5.

### T1. Value type, carrier record, selection, carrier-generic oracle

Patches, in order: `T1-01-oracle-carrier-generic.patch`, `T1-02-extval-observe-selection.patch`,
`T1-03-carrier-oracle-fixtures.patch`, `T1-04-selection-audit-fixtures.patch`.
Prototype commits: `131bc192` (P1; findings file excluded), `4dfa0fc5`; T1-03 is the P2 form of the carrier test plus the
lakefile glob; T1-04 is new (audit rows A1-A3, compiled in the authoring record).
Files: `leanncd/LeanNCD/Semantics/Source/{Carrier (new),Oracle,Diagnostics,Observation}.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/SourceOracleCarrierTest.lean` (new).
Symbols: `Carrier`, `Carrier.real/minPlus/maxPlus`, `MinPlus`, `MaxPlus`, `ExtVal`, `Sorted`, `standardCarriers`,
`SelectionError`, `selectCarrier` @ `Source/Carrier.lean`; `runWith`, `run` and the `(K : Type := ℚ)` structures
@ `Source/Oracle.lean`; `compareTensors`, `ComparisonCause`, `ComparisonError`, `TensorDifference` @ `Source/Diagnostics.lean`;
`TensorObservation`, `observeTensorsAt` @ `Source/Observation.lean`.
Lake targets: `LeanNCD`, `Semantics.SourceOracleCarrierTest` (builds every existing consumer of the generalised types, so the
real-regression claim is checked by compilation; measured 8616 jobs).
Commit message: `feat(semantics): carrier-generic Source oracle, ExtVal observation and carrier selection (S2b T1)`.
Fixtures (donor: the P1 `snap`/`yWith` helpers in `SourceOracleCarrierTest` itself; inputs `X = [1,2,3,4]`, `W = [1,10,100]`):
real, max-plus and min-plus on `contraction` and `strided` (6 `#guard`, values in §2), three `#guard_msgs` renderings of
`±inf` (`some [101, 102, 103, 104]`, `some [1, -inf, 2, -inf, 3, -inf, 4]`, `some [1, +inf, 2, +inf, 3, +inf, 4]`), the toy
`OrAnd` rows (all `true`; strided `[t, f, t, f, t, f, t]`), and four `pickName` rows: `(max,f32)` with the toy table is
`orAnd`; `(max,f64)` with the toy table is `maxPlus`; `(max,f32)` with `standardCarriers` is `maxPlus`;
`[(.sum,.f64),(.min,.f64)]` with the toy table gives `mixedSorts [sum, min]`.
Audit fixtures (T1-04, new): `A1` `selectCarrier [(.sum,.f64),(.sum,.f32)]` is `mixedElementTypes [f64, f32]`; `A2`
`selectCarrier [(.sum,.f64)] []` is `noCarrier sum f64`; `A3` `selectCarrier [] standardCarriers` selects `real`.
Cycles (2, for dispatch B to write): `T1-M1` first-match order in `selectCarrier` (`find?` made to take the LAST admitting
entry; breaks the toy rows); `T1-M2` the mixed refusal (`mixedSorts` branch returns the first agg's carrier; breaks
`pickName` row 4 and audit rows). Note: the `MaxPlus` instance and `observe` fields are pinned by the max/min `#guard` and
`#guard_msgs` rows, not by a cycle.
Expected: all targets green; no existing test edited; no `sorry`; `Semantics.AxiomAudit` unchanged.
Checklist: (a) `Oracle.run` is `runWith Carrier.real` and every pre-existing oracle test builds unchanged; (b) the default
`ℚ` parameter appears on every structure and no existing mention was edited; (c) `Carrier.real.observe = .fin`, max-plus
`⊥ ↦ negInf`, min-plus `⊤ ↦ posInf`; (d) `ExtVal`'s `Repr` prints `fin q` exactly as `ℚ` does (the real rendering is
byte-identical); (e) the toy lives only in the test file.
Reviewer lens: algebra and observation. Is `MaxPlus`'s `+` really `max` with `0 = ⊥`? Is any `ℚ` still hard-wired in a
now-generic function?

### T2. Sorted admission, native-leg flag, admission fixtures

Patches, in order: `T2-01-sorted-admission-selection.patch`, `T2-02-sorted-native-legs.patch`,
`T2-03-sorted-admission-fixtures.patch`, `T2-04-sorted-admission-audit-fixtures.patch`.
Prototype commit: `3a9f3044` (T2-01, T2-02); T2-03 is the Q6 rows of `300d8e19`'s test file split off at the admission
boundary (header `import LeanNCD.Semantics.Source.Admission`, `open Oracle` only); T2-04 is new (audit rows A4-A7).
Files: `Source/{Admission,Adapter,NativeLegs}.lean`, `leanncd/lakefile.toml`,
`leanncd/test/Semantics/SourceSortedDifferentialTest.lean` (new), `leanncd/test/Semantics/SourceSortedAuditTest.lean` (new).
Symbols: `admitAffineStatement (sorted : Bool := false)`, `admitSourceAffine (sorted := false)`, `sortKeys`,
`admitSourceSorted` @ `Source/Admission.lean`; `SourceCause.sortSelection` @ `Source/Adapter.lean`;
`NativeSource.sorted`, `runNative (sorted := false)` @ `Source/NativeLegs.lean`.
Lake targets: `LeanNCD.Semantics.Source.Admission`, `LeanNCD.Semantics.Source.NativeLegs`,
`Semantics.SourceSortedDifferentialTest`, `Semantics.SourceSortedAuditTest`, and the pre-existing guards
`Semantics.SourceAdmissionAffineTest`, `Semantics.SourceAdmissionAcceptanceTest` (must still pass unchanged). Measured for the
patch-only part (without T2-04): 8557 jobs.
Commit message: `feat(semantics): admitSourceSorted selects one carrier per program; unsorted entries still refuse max/min (S2b T2)`.
Fixtures (donor for audit rows: the `snap`/`single`/`strided`/`carrierOf` helpers of T2-03; clone a row, change one field):
Q6 six `#guard_msgs`: `carrierOf (single .sum)` is `"real"`; `.max` is `"maxPlus"`; `.min` is `"minPlus"`; mixed
`[assign sum, assign max]` is a `sortSelection (mixedSorts [sum, max])` refusal; `(admitSourceAffine (single .max)).toOption.isSome`
is `false`; affine `.scatter` max with `reduce := .rejectCollisions` is `unsupported scatterPolicy`.
Audit rows (T2-04, new): `A4` a two-statement program `[assign sum ..., scatter max (affine) ...]` refuses with `scatterPolicy`,
NOT `sortSelection`; `A5` a bare-slot `.scatter` with `agg := .max` and one with `.min` are both `scatterPolicy`; `A6` a
`.scatter` with `.sum` and `reduce := .rejectCollisions` and bare slots, through `admitSourceSorted`, selects `real`; `A7`
`admitSourceAffine (strided .max)` and `(strided .min)` are refused with `.unsupported .nonSum`.
Cycles (3): `T2-M1` the sorted rewrite `{ rhs with agg := .sum }` removed (max falls back to the `nonSum` refusal; breaks Q6
rows 2-3); `T2-M2` the scatter guard `(sorted && rhs.agg != .sum)` removed (tropical scatter admitted; breaks Q6 row 6 and
`A5`); `T2-M3` `sortKeys` always reports `.sum` (selection picks `real`; breaks Q6 rows 2-3).
Expected: green; `admitStatement`, `StatementFields`, `admitStatement_fields`, raw entry unchanged (the diff of
`Admission.lean` touches only `admitAffineStatement`, `admitSourceAffine`, `sortKeys`, `admitSourceSorted`).
Checklist: (a) §3 rows 1, 7-13 ticked with fixture names; (b) every caller of `admitSourceAffine` outside the sorted path still
gets `sorted = false` (`rg -n "admitSourceAffine" leanncd/LeanNCD`: `NativeLegs.NativeSource.admission` and `runNative`, `Provenance.admitIdentifiedSourceAffine`, and the differential's reference
entry in `Observation.lean`; the author's `rg` found exactly these); (c) `SourceCause.sortSelection` addition broke no exhaustive match (build proves it).
Reviewer lens: can the flag wrongly refuse a valid program? (audit `A6`, the existing S2a fixtures).

### T3. Carrier-generic Core leg

Patches, in order: `T3-01-generic-core-leg.patch`, `T3-02-core-leg-fixtures.patch`.
Prototype commit: `4233ba57` (T3-01); T3-02 is the Q5 rows of `300d8e19`'s test with a local `yCore` helper (T4-02 replaces
its body, the rows stay byte-identical).
Files: `Source/{Program,Schedule}.lean`, `leanncd/test/Semantics/SourceSortedDifferentialTest.lean`.
Symbols: `elaborateSource` (now `abbrev`), `Registry.none` @ `Source/Program.lean`; `sourceDefinedAt`, `sourceValuationsAt`,
`sourceOccurrencesAt`, `sourceCoordinatesAt`, `sourceOccurrenceKeysAt`, `sourcePublicationKeysAt`, `sourceScheduleAt` (+ `_nodup`,
`_complete` forms), the real abbreviations `sourceDefined...sourceSchedule`, `sourceInputBindingAt`, `runSourceAt` @
`Source/Schedule.lean`; `observeTensorsAt` @ `Source/Observation.lean` (T1). Proof-carrying real-only names
(`runSource`, `runSource_eq`, `runSourceDebug`, `sourceResult_*`, `sourceInputBinding`) are NOT generalised.
Lake targets: `LeanNCD.Semantics.Source.Schedule`, `LeanNCD.Semantics.Source.Program`, `Semantics.SourceSortedDifferentialTest`,
then the full `LeanNCD` closure (the S2a Source tests are the real-regression check; they are built by the final `Tests`). Measured: 8614 jobs.
Pitfall observed: the test needs `open Debug Oracle` (`observeTensorsAt` lives in namespace `Debug`); without `Debug` the six
rows fail with `Unknown identifier` and a cascade of `sorry`-abort messages.
Commit message: `feat(semantics): carrier-generic Core leg: runSourceAt, schedule At forms, Registry.none (S2b T3)`.
Fixtures (6 `#guard_msgs`, donor: T2-03 helpers): the six Core rows of the §2 table (`yCore` of `single .max`, `single .min`,
`product .max`, `strided .max`, `strided .min`, `single .sum`), rendered `some [some -3, some 7, some 17, some 27]` etc.
(copy each from the patch).
Cycles (2): `T3-M1` `sourceInputBindingAt` binds `C.ofRat (q + 1)` instead of `C.ofRat q` (breaks all six rows);
`T3-M2` `observeTensorsAt` replaces the published cell by `obs` of a constant (breaks the `-inf`/`+inf` rows). The prototype's
proposed "registry" cycle is NOT killable by a fixture (`Registry.none` is never consulted: admission refuses unary factors)
and is dropped; the registry is checked by the build only.
Expected: every S2a/S1 Source test builds unchanged; real abbreviations unify with `elaborateSource` (the reason it is an
`abbrev`). Checklist: (a) the four real theorems used outside `Schedule.lean` are restated as one-liners; (b) no real-only
name changed type; (c) `runSourceAt` reads `semiringOps`, not `RationalReference.ops`.
Reviewer lens: churn in `Schedule.lean` (158 lines): is every real consumer still stated at the real registry?

### T4. Tropical profile, sorted differential, structural known-difference conditions

**Dispatch A (mechanical).** Patches, in order: `T4-01-sorted-differential.patch`, `T4-02-sorted-differential-fixtures.patch`,
`T4-03-source-aggregator-import.patch`, `T4-04-tropical-bits-pin.patch`.
Prototype commit: `300d8e19` (T4-01 = `SortedDifferential.lean`; T4-02 = the final prototype test file relative to T3's state);
T4-03 (one line, `import LeanNCD.Semantics.Source.SortedDifferential` in `LeanNCD/Semantics/Source.lean`, discoverability) and
T4-04 (audit row) are new.
Files: `Source/SortedDifferential.lean` (new), `Source.lean` (aggregator), `leanncd/test/Semantics/SourceSortedDifferentialTest.lean`.
Symbols @ `Source/SortedDifferential.lean`: `ExtClass`, `checkExt`, `SortedCell`, `checkSortedProfile`, `CellMismatch`,
`compareBindings`, `LegResult`, `SortedClassification`, `SortedRun`, `compareSortedSource`, `oracleTensorsAt`, `coreTensorsAt`.
Lake targets: `LeanNCD.Semantics.Source.SortedDifferential`, `Semantics.SourceSortedDifferentialTest`, `LeanNCD`.
Measured: the full `LeanNCD Tests` build, 8823 jobs. Commit message: `feat(semantics): sorted differential over ExtVal with tropical numerical profile (S2b T4A)`.
Fixtures (8 `#guard_msgs`: the §2 classification table, plus the `compareSource` refusal row): copy from the patch.
Audit (T4-04, 2 `#guard`): `ExtClass.negInf.bits == (-(1.0 / 0.0) : Float).toBits` and
`ExtClass.posInf.bits == (1.0 / 0.0 : Float).toBits` (independent of the constants in the source).
Cycles (2): `T4-M1` the profile bound `bound + |q|` replaced by `bound * |q|` (the running bound starts at 0, so it never trips;
breaks the `1048576` envelope-trip row); `T4-M2` swap the two `±inf` bit constants in `ExtClass.bits` (breaks the bits pin only: the
prototype has NO classification row that compares a `±inf` cell with production bits).
Cleanup step at the end of dispatch A (one commit): the patched text carries prototype labels. Run
`rg -n "S2b P[12]|\(prototype\)" leanncd/LeanNCD leanncd/test` and reword each docstring/comment to `S2b` (docstring text only; no
code token changes), then rebuild `LeanNCD` and `Semantics.SourceSortedDifferentialTest` once.

**Dispatch B (T4B: NOT PROTOTYPED; the one task part without a verified patch).** Add the two structural known-difference
conditions with confirmers, following the S2a origin-bound pattern (`StructuralCondition`, `detectConditions`, `confirms`,
`ownedBy`, `legacyCollision`, `checkedCollision` @ `Source/Differential.lean` and `Source/NumericalProfile.lean`).
Files: `Source/NumericalProfile.lean` (two constructors), `Source/Differential.lean` (explicit `false` arms in `confirms` so the
real harness never confirms them; this is the only exhaustive matcher, §3 row 16), `Source/SortedDifferential.lean`
(`detectSortedConditions`, `confirmsSorted`, a `SortedClassification.knownContractDifference (condition)` arm consulted AFTER
the published-agreement check and BEFORE the native-failure arms), the test file.
- `tropicalMultiFactor (origin)`: detect = a `max`/`min` statement with a term of two or more factors (production multiplies, the
  oracle adds). ORIGIN-BOUND confirmer: BOTH legs are `mismatch` AND each mismatch's `declaration` equals the origin's tensor
  declaration. Fixtures: `product .max`, `product .min` become `knownContractDifference (tropicalMultiFactor _)` (today
  `nativeDiscrepancy`, §2); accept-neighbour: `single .max` stays `fourLegParity`; differing-origin fixture (two outputs, only
  the second multi-factor) shows the condition is bound to the right tensor.
- `tropicalScatterFill (origin)`: detect = a `max`/`min` statement with a non-bare (affine) write. Legacy leg ORIGIN-BOUND: the
  message `scatter <name> aggregates with max but fills ...` must name the condition's tensor (`ownedBy`). Checked leg: today
  recorded as `failure "checked preparation"` WITHOUT its cause; the implementer FIRST runs a probe to observe the preparation
  cause, extends `LegResult.failure` (or the leg's message) to carry it, and binds it by origin as `checkedCollision`'s
  preparation arm does (context `"{tensor}: ..."` must name the tensor). The observed cause is copied into the plan record,
  not guessed. Fixtures: `strided .max` and `strided .min` become `knownContractDifference (tropicalScatterFill _)`; a
  same-cause/other-tensor fixture stays `nativeFailure`.
- Order of conditions (pipeline order): scatter-fill failure at preparation precedes the multi-factor value comparison, so a
  program with both confirms the head only, as S2a's `classification` does; record that in the docstring.
Cycles (3, to be written after the observed causes exist): `T4-M3` multi-factor confirmer drops the declaration binding;
`T4-M4` scatter-fill confirmer accepts any tensor name; `T4-M5` `confirmsSorted` accepts a cause-only checked leg.
If dispatch B passes ~60 turns, commit the production half first and hand off the fixtures + cycles with
`.claude/skills/slice-plan/split-handoff-template.md`.
Reviewer lens (Opus review of this diff): does any condition mask a real native divergence? (the `usedDType`-style masking of
S2a: check that a fixture with the condition's shape AND an unrelated mismatch is still reported).

### T5. Documentation sweep (no code)

Commands (each hit is updated or recorded unchanged with the reason; historical records keep their dated counts):
1. Job counts: `rg -n "8818|8822" leanncd/LeanNCD/Semantics/AGENTS.md leanncd/AGENTS.md papers/semantics/lean_executable_semantics_path.md papers/semantics/additive_production_decision_note.md`
   (the author found 0 hits in these four files; a hit is a stale count to update, a dated record keeps its count).
2. Semantics node (`leanncd/LeanNCD/Semantics/AGENTS.md`, the Source section): `rg -n "S2a|Test.lean|fixtures|nonSum|bare" leanncd/LeanNCD/Semantics/AGENTS.md`. Add: the carrier record and
   `standardCarriers` table (one new semiring = one record + one entry), the sorted admission entry and the unsorted refusal,
   `sortSelection`, the sibling sorted harness and why it is separate, the two known-difference conditions, the tropical profile
   rules, the independence caveat, and the parked items. Keep injected sections under ~3k characters (trim first if over).
3. Path doc: `rg -n "S2a|S2b|tropical|max-plus|oracle" papers/semantics/lean_executable_semantics_path.md` (additive sections; there are S2a paragraphs near the
   `admitSourceAffine` description and the "planned" list near the end that names max-plus as remaining).
4. Gap audit: `rg -n "G04|F01|S2a" papers/semantics/tensor_logic_semantic_gap_audit.md`; state what S2b closes (tropical oracle) and what remains (S3a/S3b).
5. Decision note §E rows and design note: `rg -n "S2b|S2a|S3a" papers/semantics/additive_production_decision_note.md papers/semantics/oracle_extension_s2_design.md`;
   mark S2b landed with the merge hash AFTER the merge: the design note §7 status line (`rg -n "Status 2026-10-18" papers/semantics/oracle_extension_s2_design.md`)
   and the decision note's **S2** row in the §E table (`rg -n "^\| \*\*S2\*\*" papers/semantics/additive_production_decision_note.md`).
6. Source docstrings: `rg -n "agg = sum|sum only|refuses.*max|nonSum|bare-slot" leanncd/LeanNCD/Semantics/Source/{Oracle,Admission,Observation,Differential,NumericalProfile,Adapter,Carrier,Schedule}.lean`;
   any docstring that says the oracle is sum-only is rewritten. Run `lake-build.sh <wt>/leanncd LeanNCD.Semantics.Source.Oracle` if a docstring edit is made.
7. Value-grep for stale numbers after the final build: `rg -n "8818 jobs|accepted == |agg = .sum" papers leanncd --glob '*.md'`.
Discoverability (the deliverable): `import LeanNCD` reaches `Carrier` (via `Adapter`) and, after T4-03, `SortedDifferential`;
the Semantics AGENTS node names both. No source line numbers in any shipped text; cite identifiers.

## 5. Final reviews and merge (Rule 13)

**Budget (Rule 6).** Slice execution target <= ~175M cumulative input tokens (measured with
`python3 .claude/skills/slice-plan/token-report.py <session-id>`); this slice should come in far lower because 14 of its 15 work
packages (the patches) are mechanical and only T4B writes new production code. Authoring (prototypes P1/P2, authoring dispatches A and B, reviews, fixes) target <= ~50M.
AUTHORING COST: placeholder, to be measured by the controller and recorded in `additive_s2b_record.md`. The close-out records the
measured execution total and explains any overrun.

After T4 and T5 the controller runs the manifest UNFILTERED (`mutation-manifest.sh <wt>/leanncd <wt>/papers/additive_s2b_mutations_post.json`),
then the full `lake-build.sh <wt>/leanncd Tests` in the background (~25 minutes), expecting **8823 jobs for `Tests`** (measured on the 14-patch tree, §2), **Build completed
successfully** and `Semantics.AxiomAudit` printing only `propext`, `Classical.choice`, `Quot.sound`. Two Opus whole-branch
reviews in parallel, each appending to `papers/semantics/additive_s2b_review_final_<lens>.md`:
(a) semantics soundness: the `MaxPlus` instance and `0_K`/`1_K` assignment; empty-fiber and empty-reduction `∓inf`; the
independence caveat (shared `[Semiring K]`); `ExtVal`/`observe` round trips; the claim that `admitStatement_fields` is untouched
because admission is sort-free; the extensibility fixture really proves "one record + one entry";
(b) regression and differential: no pre-existing test edited (`git diff --stat main -- leanncd/test`), `compareSource` still
refuses tropical loudly, the sorted flag cannot wrongly reject a valid program (§3 rows 9-13), no condition masks a native
divergence, §3 starred cells all closed.
One fix dispatch per finding group.

Merge: `ExitWorktree` keep, then `/usr/bin/git -C /Users/williammacready/code/python/pyncd merge --no-ff worktree-additive-s2b-tropical-carriers`
(local `main` only), confirm `git diff --stat main worktree-additive-s2b-tropical-carriers` is empty, remove the worktree,
`git branch -d`. Do NOT push; say `main` is ahead of `origin/main`. The prototype scratch branches (`proto-s2b-*`) remain: ask
before `-D`.

## 6. Parked (one line each; see the §2 table for owners)

Harness merge; tropical receipt re-check; tropical Program/Global-model theorems; extent-0 `∓inf` into production probe;
`observeTensors`/`observeTensorsAt` dedup; sortSelection origin locator; toy carrier through the Core leg; cross-sort casts and
S3a/S3b; a real fourth carrier (DSL key); f32 tropical production comparison.
