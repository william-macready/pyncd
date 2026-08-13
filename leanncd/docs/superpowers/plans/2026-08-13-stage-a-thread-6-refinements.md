# Stage A thread 6 — close the three unclaimed low-risk refinements

**Status:** not started, drafted 2026-08-13

## Goal

`papers/jax_evalplan_architecture.md` §7.1 ("Stage A: recommended low-risk refinements") lists
eight refinements. Five are unbuilt or out of scope for this slice. Three have their *behavior*
already correct and tested, just not yet closed as their own named type/API — §7.6 thread 6 names
these as the next task, explicitly zero-dependency and parallel-safe against every other thread.
This plan closes all three, in `leanncd/LeanNCD/Eval/Plan/`:

1. **§7.1 row 2 — explicit named fold functions.** `Dense.lean`'s `runDenseAssignAt` already
   implements the exact ordered fold behavior §2.2 specifies, inlined in nested `for` loops rather
   than as three named functions (`factorFold`/`reductionFold`/`termFold`).
2. **§7.1 row 3 — closed `reference64SumProduct`.** `Types.lean`'s `NumericMode` has exactly one
   constructor today (`reference64`) but is named/framed as an open 64-bit tag, not §2.2's closed
   sum-product contract.
3. **§7.1 row 4 — length-correct required-input bindings.** `Compile.lean`'s `prepareEvalPlan`
   already builds one `SlotBinding` per required name into a plain `Array` (`Prepared.lean`'s
   `PlanBindings.requiredInputs`) — no evidence that the array is complete, slot-matching, and
   name-unique; `Adapter.lean`'s `pack` re-derives and checks this on every call instead.

Each closes independently; a reviewer could accept any one while rejecting the others, so they are
three separate tasks with three separate verification/merge cycles, not one.

## Fixed design decisions

- **Row 2 keeps `ContractionAlgebra` generic.** The three named functions take `ContractionAlgebra`
  as a parameter and fold over it (mirroring the existing `applyOp`/`admittedAlgebra` design), not
  hardcoded `+`/`×`. Only one algebra is ever actually admitted (`checkAssign`'s `algebraNotAdmitted`
  guard), but Stage A's own text says preserve behavior — row 2 is about naming the fold discipline,
  not collapsing the algebra's generality. That collapse is not part of this plan (see Non-goals).
- **Row 3 is a rename, not a restructuring.** `NumericMode.reference64` becomes
  `NumericMode.reference64SumProduct`. `ContractionAlgebra` itself is untouched — its "open scalar
  operators" are already excluded by `checkAssign`'s existing `algebraNotAdmitted` runtime guard, not
  by this rename. The adoption test ("All current numeric fixtures bit-exact") only makes sense if
  this task changes zero runtime behavior.
- **Row 4's real design, verified compiling below:** replace `PlanBindings.requiredInputs : Array
  SlotBinding` with a private-constructor `RequiredBindings`, built once by a new `checkBindings`
  smart constructor inside `prepareEvalPlan`, carrying a proof that its bindings' slots are a
  **permutation** of `raw.inputSlots` (order-independent) plus a proof that its names are pairwise
  distinct. **Order-independent is the load-bearing detail**: `Adapter.lean`'s own doc comment says
  resolution is "by NAME through `requiredInputs` — never by array position," and `AdapterTest.lean`
  Check 5 exists specifically to catch a `pack` that resolves by position. A naive positional-equality
  proof (`bindings.map (·.slot) = inputSlots`) would make Check 5's reordering fixture *inexpressible*
  and would make the whole name-indirection design pointless. `List.Perm` was checked and correctly
  allows reordering while still forcing same-multiset, same-length, no-duplicate-slot — see the
  verified snippet under Task 3.
- **Row 4 forces a real, unavoidable consequence, not a maybe:** once `RequiredBindings` has a
  private constructor, `AdapterTest.lean`'s Checks 6–8 (duplicate/extra/missing `requiredInputs`,
  built today via `{ prepared.bindings with requiredInputs := ... }` struct-update syntax) **cannot
  compile anymore** — the malformed states they construct are no longer expressible outside
  `Prepared.lean`'s module. This is not an incidental breakage to work around; it is Stage A's own
  stated goal for this row ("Eliminated invalid state: Missing or extra prepared input names"). Task 3
  must replace Checks 6–8 with equivalent adversarial tests aimed at `checkBindings` itself (feed it a
  malformed raw `Array SlotBinding` directly and confirm the typed rejection), and must remove
  `InputBindingError`'s now-unreachable `duplicateRequiredBinding`/`extraRequiredBinding`/
  `missingRequiredBinding` constructors and the `pack` logic that produced them (CLAUDE.md's "changes
  create orphans → remove what YOUR change made unused" applies directly: these three constructors
  exist only to report a state this same task makes unconstructable). Check 5 (reordering) must be
  preserved unchanged — it should still pass, proving the Perm choice over positional equality was
  correct.
- **`materializedNames` is untouched.** Row 4's own "Required migration" column says "preserve
  materialized arrays" — only `requiredInputs` changes shape.
- **No change to `PositionalInputError`, `PlanError`, `CapabilityError`, or any interpreter other
  than Dense.** Rows 2/3/4 are Dense/Types/Prepared/Compile/Adapter-only; JAX codegen
  (`experiments/jax_bridge/`) is untouched.

## Task 1: Named operational folds in `Dense.lean`

Extract three named private functions from `runDenseAssignAt`'s inlined loops, matching §2.2's
pseudocode exactly:

- `factorFold (alg : ContractionAlgebra) (xs : List Float) : Float` — left fold over
  `applyOp alg.factorOp`, starting from `constFloat alg.factorId`.
- `reductionFold (alg : ContractionAlgebra) (xs : List Float) : Float` — left fold over
  `applyOp alg.reduceOp`, starting from `constFloat alg.reduceId`.
- `termFold (alg : ContractionAlgebra) (xs : List Float) : Float` — same shape as `reductionFold`
  (§2.2/`ContractionAlgebra`'s own doc comment: term-combination and reduction intentionally share
  one op/identity pair).

Verified compiling (`check-snippet.sh`) against the real `applyOp`/`constFloat`/`ContractionAlgebra`:

```lean
def factorFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.factorOp) (constFloat alg.factorId)

def reductionFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)

def termFold (alg : ContractionAlgebra) (xs : List Float) : Float :=
  xs.foldl (applyOp alg.reduceOp) (constFloat alg.reduceId)
```

Also verified compiling — two small lemmas pinning these to §2.2's own recursive equations (this is
the "small equivalence proof" §7.1 row 2 calls for; it targets the *documented spec*, which is the
more meaningful target than the old inline code):

```lean
example (alg : ContractionAlgebra) : factorFold alg [] = constFloat alg.factorId := rfl
example (alg : ContractionAlgebra) (xs : List Float) (x : Float) :
    factorFold alg (xs ++ [x]) = applyOp alg.factorOp (factorFold alg xs) x := by
  simp [factorFold, List.foldl_append]
```

Add the same pair of equations for `reductionFold`/`termFold` (identical proof shape, swap
`factorOp`/`factorId` for `reduceOp`/`reduceId`).

Refactor `runDenseAssignAt` (`Dense.lean:76-101`) to build each term's per-coordinate factor-value
list and call `factorFold`, build each term's per-reduction-coordinate value list and call
`reductionFold`, and build the whole term-accumulator list and call `termFold` — replacing the
`prod`/`termAcc`/`acc` running-mutable-accumulator pattern with list construction plus fold. Keep the
existing `iter` coordinate-assembly logic (context/output/reduction position writes) exactly as is;
only the final combination step changes from inline running accumulation to a named fold call.

### Task 1 verification

No new fixtures — the refactor is behavior-preserving over the *existing* corpus. Run:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Confirm the full existing suite stays green and, in particular, that these already-bit-exact
fixtures still assert the same values unchanged: `KernelDenseTest.lean` (all `algebra :=
admittedAlgebra` fixtures), `GraphDenseTest.lean`, `DifferentialTest.lean`'s `enumPrograms` sweep, and
`Eval.Portfolio`'s numeric `[N]` cases. If any of these changes even one bit, the refactor is wrong —
Stage A's own text ("preserve behavior") makes the untouched test suite the equivalence oracle for
this task, on top of the two `rfl`/`simp` equations above.

Update `leanncd/AGENTS.md`'s `Plan/` table row for `Dense.lean` (currently: "Dense interpreter for
one checked operation... `runDenseAssignAt`... `runDenseAssign`...") to also name
`factorFold`/`reductionFold`/`termFold`.

## Task 2: Rename `reference64` to `reference64SumProduct`

Rename the sole `NumericMode` constructor (`Types.lean:42-44`) and update its doc comment to state
the closed-contract framing §2.2 already describes (ordered sum-product over binary64, not "use
64-bit floats").

Exact call sites (`grep -rn "reference64\b" leanncd/LeanNCD leanncd/test`, confirmed above,
excluding `reference64Transcendental`/`reference64SumProduct` which are prose-only today):

- `LeanNCD/Eval/Plan/Types.lean:43` — the constructor declaration.
- `LeanNCD/Eval/Plan/Check.lean:111` — `unless raw.numericMode == .reference64 do ...`.
- `LeanNCD/Eval/Plan/Compile.lean:239` — `numericMode := .reference64` in `prepareEvalPlan`.
- `test/Eval/Plan/GraphCheckTest.lean:36,70,143` — fixture construction and the
  `numericModeNotAdmitted` `#guard`; line 141's comment also names `reference64` in prose.
- `test/Eval/Plan/GraphDenseTest.lean:48,66,98,140,222` — fixture construction.
- `test/Eval/Plan/ContractTest.lean:185` — a comment naming `reference64`, update in prose only.
- `test/Eval/Plan/KernelCheckTest.lean`, `KernelDenseTest.lean` — these use `admittedAlgebra`, not
  the `NumericMode` constructor directly; no `reference64` identifier there, no change needed.

Do **not** touch `leanncd/experiments/jax_bridge/*.py` — their "reference64" occurrences are prose
describing the general numeric convention, not references to the Lean identifier being renamed.

Update `leanncd/LeanNCD/Eval/AGENTS.md`'s `Plan/` subtree table: the `Types.lean` row currently says
"static specialization vocabulary — `ScalarDType`, `TensorSignature`, `InputSignature`"; it does not
mention `NumericMode` at all today, so no rename-specific edit is needed there, but confirm this
while editing (if a later pass added a mention, update it).

### Task 2 verification

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

This must be the entire verification: a clean rename changes zero test assertions (every `#guard`
comparing `.reference64` values compares two renamed values, so equality/inequality outcomes are
unchanged) and zero runtime behavior. If any fixture's expected value needs to change, the rename
was not behavior-preserving and something else is wrong.

## Task 3: Length-correct `RequiredBindings`

### 3.1 New type, verified compiling

`Prepared.lean` gains a private-constructor `RequiredBindings` and a `BindingsError`/`checkBindings`
pair (module-level placement TBD by the implementer — `Prepared.lean` itself, or a new
`Prepared.lean`-adjacent file if that reads cleaner; both are fine, this plan does not mandate one).

Verified compiling end-to-end against the real `TensorSlot`/`SlotBinding` (`check-snippet.sh`):

```lean
inductive BindingsError
  | notAPermutation (expectedSlots observedSlots : Array TensorSlot)
  deriving DecidableEq, BEq, Repr

structure RequiredBindings where private mk ::
  inputSlots : Array TensorSlot
  bindings   : Array SlotBinding
  aligned    : (bindings.map (·.slot)).toList.Perm inputSlots.toList
  deriving Repr

def checkBindings (inputSlots : Array TensorSlot) (bindings : Array SlotBinding) :
    Except BindingsError RequiredBindings :=
  if h : (bindings.map (·.slot)).toList.Perm inputSlots.toList then
    .ok { inputSlots, bindings, aligned := h }
  else
    .error (.notAPermutation inputSlots (bindings.map (·.slot)))
```

Verified compiling — the two properties that justify the design (Perm to a duplicate-free list
forces the permuted list duplicate-free too; reordering stays legal):

```lean
example (rb : RequiredBindings) (hnd : rb.inputSlots.toList.Nodup) :
    (rb.bindings.map (·.slot)).toList.Nodup :=
  rb.aligned.nodup_iff.mpr hnd

example (rb : RequiredBindings) :
    (rb.bindings.reverse.map (·.slot)).toList.Perm rb.inputSlots.toList := by
  have h1 : rb.bindings.reverse.map (·.slot) = (rb.bindings.map (·.slot)).reverse := by
    simp [Array.map_reverse]
  rw [h1, Array.toList_reverse]
  exact (List.reverse_perm _).trans rb.aligned
```

Add a second failure constructor `BindingsError.duplicateName (name : String)` and a name-uniqueness
check (`(bindings.map (·.name)).toList.Nodup`, decidable via `String`'s existing `DecidableEq`) inside
`checkBindings` alongside the `Perm` check — this is the "name-uniqueness evidence" §7.1 row 4's
proof-burden column names explicitly, and it is a genuinely separate property from slot-Perm: two
different slots could in principle share one name (a distinct malformation from anything
`InputBindingError` names today), and closing row 4 means closing both, not only the one `pack`
happened to check for already.

`PlanBindings.requiredInputs : Array SlotBinding` becomes `PlanBindings.requiredInputs :
RequiredBindings`; `materializedNames` is unchanged.

### 3.2 Wire into `prepareEvalPlan`

`Compile.lean`'s Step D already builds `requiredInputsAcc : Array SlotBinding` and
`inputSlotsAcc : Array TensorSlot` in the same `for nm in extOrder do` loop — they are positionally
(hence also as a permutation) aligned by construction today, so `checkBindings inputSlotsAcc
requiredInputsAcc` should never actually fail for compiler-produced input. Call it in Step E/F
(alongside the existing `checkPlan` call), following the exact `lift*`-helper pattern already used
for `liftCapability`/`liftShape`/`liftPlanError`:

- add a `bindings (cause : BindingsError)` arm to `PlanCompileCause` (`Error.lean:86-91`) —
  `BindingsError` needs the same `DecidableEq, BEq, Repr, Inhabited` deriving the sibling error types
  have, which is straightforward (`Array TensorSlot`/`String` payloads both already have
  `DecidableEq`);
- add a `liftBindings` helper mirroring `liftCapability`/`liftShape`/`liftPlanError`
  (`Compile.lean:81-94`);
- call `checkBindings` and thread its result into `PreparedPlan.bindings.requiredInputs` at the
  point `prepareEvalPlan` currently assembles `{ requiredInputs := requiredInputsAcc, ... }`
  (`Compile.lean:243`).

### 3.3 Simplify `pack`, remove the now-unreachable `InputBindingError` constructors

Once `PlanBindings.requiredInputs : RequiredBindings` is guaranteed complete/slot-matching/name-unique
by construction, `Adapter.lean`'s `pack` (`Adapter.lean:29-53`) no longer needs to build a `slotName`
`HashMap` while separately guarding against duplicate/extra/missing slots — it can build the
slot→name correspondence directly from `RequiredBindings.bindings`, trusting the invariant, the same
way `runDensePlan`/`runDenseAssignAt` already trust `checkPlan`'s invariants rather than
re-validating them. Remove `InputBindingError.missingRequiredBinding`,
`.duplicateRequiredBinding`, and `.extraRequiredBinding` (`Error.lean:110-112`) and the `pack` code
that produced them; keep `missingEnvBinding`/`shapeMismatch`/`storageMismatch` exactly as they are —
those are genuine runtime concerns about the caller-supplied `env`, not about `requiredInputs`'
internal shape, and `RequiredBindings` says nothing about them.

### 3.4 Migrate the affected tests

- `AdapterTest.lean` Checks 6, 7, 8 (`AdapterTest.lean:169-202`, the duplicate/extra/missing-binding
  cases) **must be deleted or rewritten** — they construct their fixtures via `{ prepared.bindings
  with requiredInputs := ... }`, which cannot compile once `requiredInputs` has a private
  constructor. Replace them with adversarial tests directly against `checkBindings`: build a raw
  `Array SlotBinding` with a duplicate slot, one with an extra slot not in `inputSlots`, one shorter
  than `inputSlots`, and one with a duplicated name across two different slots; confirm each is
  rejected with the expected `BindingsError` constructor. This preserves row 4's own adoption test
  ("Missing/extra/name-order and repeated-materialization tests") — it relocates the coverage to the
  new construction boundary instead of `pack`'s now-unreachable runtime guard.
- `AdapterTest.lean` Check 5 (reordering, `AdapterTest.lean:150-168`) **must keep passing unchanged**
  — this is the test proving the `Perm` choice (over a naive positional-equality proof) was correct.
  If this check fails to even compile after the type change, the design has regressed to positional
  equality and must be fixed before proceeding.
- `CompileTest.lean:222-223`'s `#guard` comparing `(...).map (·.bindings.requiredInputs) ==
  (...).map (·.bindings.requiredInputs)` needs `.bindings.requiredInputs.bindings` instead —
  `RequiredBindings` has no derived `BEq` (same established precedent as `PreparedPlan` itself, per
  `Prepared.lean`'s own doc comment: private-constructor types compare through field projections, not
  whole-struct equality).

Update `leanncd/LeanNCD/Eval/AGENTS.md`'s `Prepared.lean` row (currently: "source-name-keyed bindings
around a checked plan — `PreparedPlan`") to also name `RequiredBindings`/`checkBindings`.

### Task 3 verification

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Must pass with:

- `AdapterTest.lean` Check 5 unchanged and still passing (reordering remains legal and still resolves
  by name, not position — re-run the file's own documented mutation check, patching `pack` to resolve
  by array position instead of `.slot`, and confirm it still fails exactly Check 5 the same way the
  existing comment describes);
- new `checkBindings`-boundary tests covering duplicate-slot, extra-slot, missing-slot, and
  duplicate-name rejection, each asserting the specific `BindingsError` constructor and payload
  (mutation-test each: confirm the well-formed case both fixtures are derived from still succeeds);
- `CompileTest.lean`'s determinism `#guard`s passing on `.bindings.requiredInputs.bindings`;
- the full corpus (`DifferentialTest.lean`'s `enumPrograms` sweep, `Eval.Portfolio`) green, proving
  no `prepareEvalPlan`-produced plan ever hits `checkBindings`'s failure branch in practice.

## Whole-branch review gate

After all three tasks:

1. review the complete branch against this plan, not only each task's diff;
2. confirm Task 1's refactor changed no test-visible numeric output (diff the full test-suite output
   before/after if there's any doubt);
3. confirm Task 2 touched only identifier names and doc-comment prose, no logic;
4. confirm Task 3's `RequiredBindings` cannot be constructed with a duplicate slot, an extra slot, a
   missing slot, or a duplicate name from outside `Prepared.lean` — try it in a scratch file and
   confirm the private constructor blocks it;
5. confirm `InputBindingError`'s three removed constructors have zero remaining references anywhere
   (`grep -rn "missingRequiredBinding\|duplicateRequiredBinding\|extraRequiredBinding"`);
6. confirm both `AGENTS.md` edits (Task 1, Task 3) landed;
7. confirm `papers/jax_evalplan_architecture.md` §7.1's table needs no further edit (the table
   already describes the *target* state these tasks build toward; if any row's wording turns out to
   no longer match the shipped design — e.g. if `duplicateName` checking was dropped — fix the table,
   don't leave it describing something that wasn't built); and
8. full `lake build` green.

## Explicit non-goals and follow-up

This slice does not:

- collapse `ContractionAlgebra`'s generality now that only one algebra is admitted (row 3's own
  scope is a rename, not that collapse — a real future refinement, not this one);
- touch §7.1 rows 1, 5, 6, 7, or 8 (distinct slot namespaces, private validated executable
  constructors, evidence-indexed backend kernels, snapshot/next-state types, derived step graph
  interface) — those remain unbuilt, per §7.6's sequencing (rows 5/3/4 come after this thread, not
  as part of it);
- exploit `RequiredBindings.aligned`/name-uniqueness inside `runDensePlan`/`checkPlan` or any other
  consumer beyond `pack` — this plan's blast radius is `Prepared.lean`/`Compile.lean`/`Adapter.lean`
  and their direct tests, nothing in `Check.lean`/`Dense.lean`'s graph-level checking;
- change `PlanBindings.materializedNames`'s type, or any JAX/PyTorch codegen path.

If a future slice wants to build on this, the natural next step per §7.6 is row 5 (compact/
evidence-indexed kernels + PyTorch backend) — already reordered ahead of Wave F/nonlinearity by
thread 2's measurement, and explicitly unblocked by this thread regardless of order.
