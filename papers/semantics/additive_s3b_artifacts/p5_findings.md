# P5 findings (T5: the bool -> tropical read cast, both backends)

Branch proto-s3b-p5 (from proto-s3b-p4 ccf9f745): 84c9455c `T5-01 production`, 6b0cb23b `T5-02 tests`.
Patches: T5-01-production.patch (8 files, +79/-20), T5-02-tests.patch (3 files, +265/-6); both
`git apply --check -R` clean at the tip. Mutations: p5_mutations.json (15 entries, manifest `--check` OK).

## (a) Corrections to audit/design
1. The statement's sort is NOT read from `algebras`/`algebraOf` in either backend; the minimal mechanism
   was sufficient. Reference: `combineFor`/`algebraForAgg` already select the tropical algebra from
   `rhs.agg` (max/min), so "tropical statement" = `agg != .sum` in BOTH backends; the source is bool iff
   `isPredicateDest decls src` (reference) / the source slot's `TensorSignature.dtype = .bool` (plan).
   No new parameter reaches `evalScheduled`/`evalPlain`/`evalScan`/`prepareEvalPlan` (the p4 (f) note that
   they would need `algebras` / `checked` was an over-estimate for T5; T6 is different, see (f)).
2. Equivalent mutant: in the REFERENCE, casting a bool source in a REAL statement is bit-identical
   (true -> unit1 = 1.0, false -> unit0 = 0.0 = the raw value), so "cast applied for real statements"
   cannot be killed on the reference side; the proposed M5 is plan-side (checker rejects the cast under a
   real algebra) and M5b (reference casts REAL sources) kills the nearby shape.
3. `bias` is a reserved token under `import LeanNCD.Eval.Entry` (DSL syntax): a raw `AffineMap` literal
   `{ coeffs := .., bias := .. }` does not parse in a test that imports Entry; use `AffineMap.mk`.
4. The scan plan path resolves a predicate STATE's dtype from the sigs (`stateDtypes`), so a bool state read
   by a tropical step is cast too (both backends: `isPredicateDest` on the state name; plan: capture slot
   dtype). Not exercised by a test (the scan fixtures read bool EXTERNALS in base and step).
5. The audit's claim that GN4's value is preserved holds exactly: observed `[[3,4],[3,4]]`, expectation
   unchanged.

## (b) Tests flipped (old -> new)
- GnnScatterTest GN4: red (`[[4,5],[4,5]]`, identity cast) -> green, original expectation `[[3,4],[3,4]]`;
  only the deferral comment was replaced. No other test changed value.
- RC10 stayed green: its expectation still has the literal `0` at `G[0,1]` (state init is T6), so it flips
  when T6 lands (not red now).

## (c) Red-target classification, full `Tests` build
`Tests`: 8824 jobs; ONE red target: Semantics.SourceSortedDifferentialTest, 19 error sites (unchanged
count): (ii) deferred -> T7. (i) T5-owned and fixed: GnnScatterTest (GN4). (iii) UNEXPECTED: none.
`LeanNCD` library: 8614 jobs, green on the first try (no name clash).

## Production design (as shipped)
- Reference: `gatherRead` gains a trailing `cast : Float -> Float := id` applied to the in-bounds value only;
  `gatherCast zero one castOf` is the new core (`gather` = `gatherCast` with the identity, kept for GatherTest);
  `evalAssignSeeded` gains a trailing defaulted `castOf`; `boolReadCast decls c agg` (Contract.lean, after
  `combineFor`) is the map; passed from `evalAssignDtypedSeeded` (plain, scan base/step, scan scatter) and
  `evalScatter`'s compute half (`gatherCast`).
- Plan: `ReadPlan.boolToTropical : Bool := false` (defaults: the `oobPolicy` literals in tests compile unedited:
  `rg -c oobPolicy test` totals 99 matching lines over 16 files); `residualizeAssignment` gains
  `isBoolSlot : TensorSlot -> Bool` (no default) and sets the field for BARE reads when `agg != .sum`; the four
  callers pass `fun s => (sigsNow[s]?).any (·.dtype == .bool)`. `ScalarKernelOps` gained `isTrue : α -> Bool`
  (`v != 0`), `gatherFactorWith` takes `one` (decoded `factorId`) and casts true -> `factorId`, false ->
  `reduceId` (= `pad`); f32 uses `float32Ops` constants, bits verified by the f32 leg of every fixture.
- Checker: new `PlanError.castNotAdmitted (termIndex factorIndex : Nat)`: cast requires source dtype `.bool`,
  `unary = none` and a tropical algebra (`factorOp = .add`, `reduceOp` max/min). Adding the constructor needed
  NO other edit (no exhaustive `match` on `PlanError` besides the derived instances).
- Truth convention: stored value `!= 0` is true (no existing code tests a stored bool value; `.bool true`
  decodes to 1.0, Iverson uses its own predicate). Differs from `== 1.0` only on non-0/1 values.

## (d) Fixtures (all new, in test/Eval/Plan/BoolCastTest.lean; run reference, plan f64, plan f32 and compare)
a1/a2 bare read max/min (donor GN4, negative X); f1/f2 all-false row -inf/+inf; b1/b2 under `sqrt`
(cast under unary would be `sqrt(-inf)` = domain error); c1 bool->real, c2/c3 real->max/min neighbours;
g1/g2 out-of-bounds pad not cast (`axis i : ℕ = 3` is needed, else the size system rejects the shift);
d1/d2 scatter compute half (donor S11), d3/d4 scan base + step (donor RC10, 1-D variant with all cells
written); e: 7 raw-plan `#guard`s (2 accepts with cast, 2 accept neighbours, 3 `castNotAdmitted 0 0`
rejects: non-bool source, real algebra, unary read). Registered in lakefile.toml `Tests` globs.
Not authored (budget): a `GatherTest` guard on `gatherCast` directly; a bool-STATE-read scan fixture.

## (e) Budget
About 52 tool calls; context peak roughly 200k (each Edit echoed the intent-layer hook text, which was the
largest avoidable cost). No hand mutation runs.

## (f) For the T6 author (scan state init at 0_K)
- Reference: `Eval/Scan.lean` allocates state with `DenseTensor.zeros` (~L318) and nothing there sees the
  checked program; `evalScan` takes `decls`. The state's sort must come from `algebraOf` (p4 (f), (g)):
  thread the `algebras` map (or a `String -> SortAlgebra`) into `evalScan` the way p4 described.
- Checked plan: `Eval/Plan/Scan.lean` ~L742, 780, 788 allocate the state at the carrier zero; the scan entry
  points do not receive `CheckedScheduledProgram.algebraOf` today (only `prepareEvalPlan` Step 0 / `evalScheduled`
  hold `checked`); `compileScan` gets `declEnv` only. T6 must pass the state's `SortAlgebra`, or a precomputed
  per-state `reduceId`, into the scan block plan (new field on the scan step) rather than re-deriving it.
- A NEUTRAL base statement (agg `sum`, one read, no contraction) gets its algebra from `algebraForDest destDtype
  rhs.agg` at Compile.lean ~L1103 (`agg = .sum` => real) and the reference's `combineFor decls nm rhs.agg`;
  its OOB pad is therefore the REAL 0 even when the state is tropical via its recurrence. The T5 cast also keys
  on the statement's own `agg`, so a neutral base reading a predicate is NOT cast; if T6 changes the neutral
  base to adopt the state's sort it must change `agg` -> sort in `boolReadCast` (reference) and the `tropical`
  flag in `residualizeAssignment` (plan) together, and the plan's `algebraForDest` call.
