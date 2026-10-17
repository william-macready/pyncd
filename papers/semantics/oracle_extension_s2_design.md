# S2 design: oracle extension (affine write slots, exact tropical carriers) and prepare-time B3

Status: brainstormed 2026-10-17, awaiting user review of this note. Not a plan. Parent:
`additive_production_decision_note.md` §E (slice outline) and `additive_collection_slice1_record.md` (parked list).

## 1. Purpose

S2 exists so that S3 (scatter-collision ⊕, tropical sorts, out-of-range write error, deletion of
`CollisionReduce` / `ScatterOpts.fill`) can be claimed validated against an independent exact reference.
Today the Source oracle cannot express those programs, so S3's claims are held back.

## 2. Decisions (user, 2026-10-17)

1. **Cut: three separate pieces.** (i) prepare-time B3 on the Direct path, no plan document; (ii) S2a affine
   write slots, sum only, Full path; (iii) S2b tropical carriers for single-sort programs. S2a and S2b each get
   their own plan, S2b only after S2a lands (CLAUDE.md Rule 13).
2. **S2a proof depth: middle path.** Generalise `AdmittedOutput` to a destination map plus UID support and extend
   the Source- and Program-level correspondence proofs. The raw-parse chain (`RawCorrespondence`,
   `RawSemanticConnection`) keeps its bare-slot hypotheses: affine statements get the Program/fiber theorems and
   the executed core leg, but no "raw parse preserves slots" theorem. This gap is to be documented in the
   Source AGENTS node.
3. **Scatter options in the oracle.** `fill` must equal `0_K` of the statement's sort (S2a: real sum, so
   `fill = 0`); `reduce ∈ {sum, rejectCollisions}`. `fill ≠ 0_K` and `reduce ∈ {overwrite, max, min}` are refused:
   S3 deletes those options. `0_K` for tropical sorts is ∓∞, which `ScatterOpts.fill : Int` cannot express.

## 3. Verified facts the design rests on

- The oracle refuses `.scatter` (`Admission.lean` `admitStatement`), `.affine` LHS slots (`outputIndices`),
  `agg ≠ .sum`, Iverson and unary factors. Its carrier is `ℚ` (`Oracle.lean`); correspondence proofs are
  instantiated at `RationalReference`; `NumericalProfile` is bounded-integer (`limit = 2^20`).
- `AdmittedSource.program` builds `Program (fun _ => K)` with `[Semiring K]`: single sort (index `Unit`). The
  decision note's "`Program.lean:52` already per sort" does not match the code. Mixed real/tropical programs would
  need a sort-family change.
- `Program.destination` is a total typed coordinate, so an affine write is admissible only if its image over the
  whole source box lies inside the destination's declared shape; otherwise it is a static `writeOutOfRange` refusal.
- `Correspondence.lean:64-124` and `ProgramCorrespondence.lean:29-45` use the output slots almost only as the
  predicate `output.slots.project x = p`; the heavy dependence on bare slots is in `RawCorrespondence` /
  `RawSemanticConnection` (`BareOutputSlots`, `RawOutputSlots`).
- Reference evaluator silently skips out-of-range scatter writes (`Eval/Scatter.lean:77` guard). Collisions under
  `rejectCollisions` throw `scatterCollision`; `sum` adds.
- Mathlib: `#synth CommSemiring (Tropical (WithTop ℚ))` succeeds (min-plus). `Tropical (WithTop ℚᵒᵈ)` (max-plus) did
  NOT synthesize in a quick probe (Mathlib's order classes have been reworked); not investigated further.

## 4. S2a: affine write slots (sum only)

1. One mechanism for every non-bare write: the destination is a list of integer-affine forms over the statement's
   axes from `idxAffineForm` (`.const`, `.scale`, `.shift`, multi-axis `.affine`). This covers repeated free axes
   (`Y[i,i]`), which `slotsBecomeScatter` already treats as scatter. The bare case is the single-axis, coefficient-1
   special case.
2. `AdmittedOutput` carries a destination map and its UID support (axes the forms mention). Axes appearing only in
   reads stay term-local contractions.
3. Admission: `.scatter` (options per §2.3) and hand-built `.assign` with affine slots are admitted; image must lie
   in the destination shape (`writeOutOfRange`); reads stay bare (affine read slots, i.e. convolution/padding, are out
   of S2 scope); scan slots and `freeNorm` stay refused.
4. Oracle: each destination coordinate sums the contributions of every source coordinate whose image equals it; an
   empty fiber is 0. Several statements writing one tensor sum (as in S1).
5. New structural known-difference conditions (S1 pattern; S3a converts them to agreement): `rejectCollisions` with a
   real collision (production errors, oracle sums); multi-writer scatter (production refuses `multiWriterScatter`).
6. Differential coverage: non-colliding scatter, `reduce := sum`, diagonal writes and constant slots should agree on
   all four legs today. These fixtures are the first validation of S3a's target semantics.
7. **First plan task is a probe (UNVERIFIED):** a destination declared with an extent that disagrees with the one
   production derives from the source axis sizes (`outExtent`, e.g. declared 6 vs derived 8 for `S[2*i]`, `|i| = 4`).
   Production may already reject this as a size conflict, may skip, or may agree. Record each leg's behaviour as a
   fixture; if it differs from the oracle's static refusal, document it as a known difference. No condition is
   pre-declared for it.

## 5. B3 prepare-time rejection (Direct path)

- New arm `InputSignatureError.definedName (name : String)` (`Eval/Plan/Error.lean`, next to `missingSignature`).
- In `prepareEvalPlan` Step B, before the `extNames` loop: `definedNames.find? sig.tensors.contains` throws
  `.inputSignature (.definedName nm)`. `definedNames` is `(sched.stmts.flatMap ScanStmt.writes).eraseDups` over the
  collected schedule (public, private `T#k`, collector, scan scratch), the same set as runtime B3; hoist it above
  Step B so the existing use at `Compile.lean` ~1578 shares the binding. Iterating `definedNames` (not the HashMap) gives
  a deterministic first offender and matches runtime "refused first".
- `prepareEvalPlan` is the single choke point for the f64 and f32 paths; the `ofDenseInputs*ForDecls` constructors do
  not see the schedule and cannot enforce it.
- Verification: fixtures for a public output (f64 and f32), a private `T#1` from a multi-writer program, scan scratch;
  a positive control (exactly the required entries still prepares); mutation cycles (check removed, iteration order
  broken); update `Plan/AGENTS.md`, the `InputSignatureError` doc comment, and the PARKED rows in the slice-1 plan and
  record. Only three code sites mention `missingSignature` today; confirm no exhaustive matcher by building.
- Cost ~1 dispatch; large but not whole-library rebuild.

## 6. S2b: tropical carriers (sketch; planned only after S2a lands)

- Scope: single-sort programs. All `agg = sum` is real, all `max` is max-plus, all `min` is min-plus; a mix is refused
  (`mixedSorts`). Cross-sort casts (e.g. max-pool feeding a linear layer) are out of S2b and need a sort-family change;
  list as a separate later item.
- Carrier: min-plus is `Tropical (WithTop ℚ)`. Max-plus: the plan prototype chooses between an own `WithBot ℚ` type with
  proved semiring laws and max-plus as min-plus transported along negation. Inputs stay finite rationals; outputs may be
  ∓∞ (empty fibers, empty reduction domains).
- Oracle abstracted over a carrier record (zero, one, ⊕, ⊗, embedding of input rationals); the real instance must
  reproduce every existing oracle fixture unchanged. Core leg: `AdmittedSource.program` at the tropical `K` with an
  empty primitive registry (unary operators stay refused).
- `NumericalProfile`: `expectedBits` for ∓∞; the bounded-integer envelope is written for products, tropical values are
  sums, so the bound rules need revisiting.
- Known differences until S3b: multi-factor max/min terms (production max-times, oracle max-plus; single-factor agrees);
  tropical scatter (production refuses via `checkScatterFill`, oracle gives a value); max-aggregated scatter with
  `reduce := sum`. §2.3's rule for tropical statements needs revisiting: admit `reduce` matching `agg`, or
  `rejectCollisions`.

## 7. Sequencing and what each unlocks

B3 (independent, any time) -> S2a plan, execute, land -> S2b plan, execute, land.
S2a unlocks S3a (scatter ⊕, delete `fill`/`CollisionReduce`, range error); S2b unlocks S3b (tropical sorts, casts,
constants).

## 8. Open items for the plans

- Process weight: B3 = Direct path; S2a = Full path (`slice-plan` §0); S2b decided at its own plan.
- Budgets are unmeasured. The decision note's ~150M+ covers S2a+S2b together; each plan must state and measure its own
  against Rule 6.
- Documentation to update with S2a: `Semantics/Source` AGENTS node (affine fragment, raw-chain gap), the path doc
  (`lean_executable_semantics_path.md` additive sections), gap audit G04/F01, and the decision note §E rows.
