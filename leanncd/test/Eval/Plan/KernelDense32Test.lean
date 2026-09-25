import LeanNCD.Eval.Plan.Dense
import Eval.Plan.KernelDenseTest   -- every plan here is one of its plans with the dtype/algebra changed
import Eval.Nonlin32Test           -- fixture 2.4 reuses its platform witness lane lists (f32 slice
                                    -- Task 2, conflict-scan note C5), qualified rather than opened:
                                    -- its own helper names (`L`, `lanes`, `lane`, ...) are generic
                                    -- enough to risk shadowing this file's own local definitions.

/-!
# Native binary32 local execution (f32 slice, Task 3)

Fixtures 1-10, 12, 13 and 16 of Task 3. Every one is a `KernelDenseTest` plan with ONLY the
signature dtypes, the algebra, and the buffers changed, so a difference in outcome is attributable
to the carrier and nothing else.

**Every expectation is an exact IEEE-754 binary32 BIT PATTERN, compared through `Float32.toBits`.**
`BEq Float32` is IEEE comparison — it identifies `+0` with `-0` and makes every NaN unequal to
itself — so it is not propositional equality and is never used to assert a value here. Buffers are
likewise built from `Float32.ofBits`, not from decimal literals, so the input to each claim is as
exact as its output.

Each expected value was produced by a compiled `Float32` probe (`check-snippet.sh`) performing the
same fold this worker performs, not read back from this worker's own output; the discriminating ones
(fixtures 2, 3, 4, 11, 12) additionally have a binary64 contrast that differs, so they distinguish
native per-operation binary32 rounding from a widened computation with a late narrowing.
-/

namespace LeanNCD.Eval.Plan.KernelDense32Test
open LeanNCD.Eval LeanNCD.Eval.Plan

/-- A native binary32 tensor from exact bit patterns. -/
def t32 (shape : List Nat) (bits : Array UInt32) : DenseTensor32 :=
  { shape := shape, data := bits.map Float32.ofBits }

/-- Run a plan through the BINARY32 checker and the BINARY32 local worker. -/
def run32 (sigs : Array TensorSignature) (a : AssignPlan) (store : Array DenseTensor32) :
    Except String DenseTensor32 :=
  match checkAssignF32 sigs a with
  | .error e => .error s!"check failed: {repr e}"
  | .ok c => match runDenseAssign32 c store with
             | .error e => .error s!"run failed: {repr e}"
             | .ok d => .ok d

/-- The exact bits of every output element. -/
def bitsOf : Except String DenseTensor32 → Option (Array UInt32)
  | .ok d => some (d.data.map Float32.toBits)
  | .error _ => none

/-! ## Fixture 1: signed zero, subnormals, and native constant decoding

`identityPlan`'s `Y[i] := X[i]` over a buffer holding `+0`, `-0`, and the least positive subnormal.
-/

def identitySigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[3], dtype := .f32 } ]

def f32Identity : AssignPlan :=
  { KernelDenseTest.identityPlan with algebra := admittedAlgebraF32 }

def f32IdentityStore : Array DenseTensor32 :=
  #[ t32 [3] #[0x00000000, 0x80000000, 0x00000001], t32 [3] #[] ]

-- `+0` stays `+0`; the least positive subnormal (bits `1`) survives the seeded identity assignment
-- exactly, which is the real content of the third lane — a worker that flushed subnormals to zero
-- would return bits `0` here. This lane does NOT catch a widen-to-binary64-and-narrow-back worker:
-- a binary32 subnormal widens exactly and narrows back to itself
-- (`(Float32.ofBits 1).toFloat.toFloat32.toBits = 1`), so that shortcut is left to fixture 2's
-- reduction, where the intermediate rounding differs.
--
-- The `-0` lane returns `+0`, and that is CORRECT rather than a lost sign: the sum-product algebra
-- seeds its reduction and term folds with `+0` (`admittedAlgebraF32.reduceId = .f32 0x00000000`),
-- and IEEE-754 round-to-nearest gives `(+0) + (-0) = +0`. This fixture therefore does NOT claim the
-- assignment preserves negative zero; see the separate decoding claim just below for the fact that
-- the CONSTANT `-0` is carried bit-exactly.
#guard bitsOf (run32 identitySigs32 f32Identity f32IdentityStore) == some #[0, 0, 1]

-- `Float32.ofBits`/`toBits` round-trips negative zero bit-exactly. That is a fact about the Lean
-- primitive `float32Ops.decodeConst` calls for a `ScalarConst.f32`, not a test of `decodeConst`
-- itself (which is private, and which the seeded assignment above cannot observe for `-0`). The
-- decoder's own use is observed through the algebra identities in fixtures 5–8: fixtures 5 and 6
-- output the decoded `factorId`/`reduceId` constants exactly, while fixtures 7 and 8 output
-- `A[i]·(∓1)`, which is correct only when the decoded `∓∞` seed is.
#guard (Float32.ofBits 0x80000000).toBits == 0x80000000

-- ... and this is why every assertion in this file goes through `toBits`: IEEE comparison cannot
-- tell the two zeros apart, so a `BEq Float32`-based fixture would pass either way.
#guard (Float32.ofBits 0x80000000) == (Float32.ofBits 0x00000000)

/-! ## Fixture 2: reduction rounds at every step

`contractPlan`'s reduction shape with `readA` and the output axis removed: one `readB`-shaped source
reduced to a scalar destination. `[16777216, 1, -16777216]` folded left to right from the `+0` seed
is `((0 + 16777216) + 1) + (-16777216)`, and the middle add ROUNDS AWAY in binary32 (16777217 is not
representable), so the result is `+0`. The same three values in binary64 give `1`. This is the
plan's central discriminator: a whole-computation binary64 implementation that narrows only at the
end returns binary32 `1`, not `0`.
-/

def redSigs32 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f32 }, { shape := #[], dtype := .f32 } ]

def redRead : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def f32ReductionRounding : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[]
  , terms := #[{ iterationShape := #[3], contextPos := #[], outputPos := #[], reductionPos := #[0]
               , factors := #[.read redRead] }]
  , algebra := admittedAlgebraF32 }

def f32ReductionStore : Array DenseTensor32 :=
  #[ t32 [3] #[1266679808, 1065353216, 3414163456], t32 [] #[] ]

#guard bitsOf (run32 redSigs32 f32ReductionRounding f32ReductionStore) == some #[0]

/-- The SAME one-factor scalar reduction as an ordinary binary64 plan: the donor for the contrast
    below and for fixture 13's storage-kind door. -/
def redSigs64 : Array TensorSignature :=
  #[ { shape := #[3], dtype := .f64 }, { shape := #[], dtype := .f64 } ]

def f64ReductionDonor : AssignPlan :=
  { f32ReductionRounding with algebra := admittedAlgebra }

def f64ReductionStore : Array DenseTensor :=
  #[ { shape := [3], data := #[16777216.0, 1.0, -16777216.0] }, { shape := [], data := #[] } ]

-- The binary64 worker on the same three values returns `1`, not `0` — every intermediate is exactly
-- representable in binary64. Without this control, fixture 2's `0` could be an arithmetic accident
-- rather than binary32 rounding.
#guard (match checkAssign redSigs64 f64ReductionDonor with
        | .error _ => none
        | .ok c => (runDenseAssign c f64ReductionStore).toOption.map DenseTensor.data)
  == some #[1.0]

/-! ## Fixture 3: multiplication rounds

Two scalar factors `4097 × 4097`. The exact integer product is `16785409`, which needs 25 significand
bits and is not a binary32 value; the correctly-rounded binary32 product is `16785408`, bits
`1266683904`. -/

def scalarSigs32 : Array TensorSignature :=
  #[ { shape := #[], dtype := .f32 }, { shape := #[], dtype := .f32 }
   , { shape := #[], dtype := .f32 } ]

def scalarRead (slot : TensorSlot) : ReadPlan :=
  { sourceSlot := slot, map := { coeffs := #[], bias := #[] }
  , sourceShape := #[], oobPolicy := .zeroPad }

def f32MultiplicationRounding : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[]
  , terms := #[{ iterationShape := #[], contextPos := #[], outputPos := #[], reductionPos := #[]
               , factors := #[.read (scalarRead 0), .read (scalarRead 1)] }]
  , algebra := admittedAlgebraF32 }

def mulStore : Array DenseTensor32 :=
  #[ t32 [] #[1166018560], t32 [] #[1166018560], t32 [] #[] ]

#guard bitsOf (run32 scalarSigs32 f32MultiplicationRounding mulStore) == some #[1266683904]

-- The binary64 product of the same two values is the EXACT integer `16785409`, so narrowing that one
-- product would also land on `16785408` — this fixture pins that the multiply itself is binary32,
-- but it is `EvalPlan32Test`'s fixture 11 that additionally CONSUMES the rounded intermediate and so
-- separates native f32 from a widened whole-graph computation.
#guard (4097.0 * 4097.0 : Float) == 16785409.0

/-! ## Fixture 4: the factor fold is left-associated in stored order

`factorOrderPlan`'s three scalar factors, with binary32 bits chosen so the declared left fold and a
right-associated one differ by one ULP. -/

def factorOrderSigs32 : Array TensorSignature :=
  #[ { shape := #[], dtype := .f32 }, { shape := #[], dtype := .f32 }
   , { shape := #[], dtype := .f32 }, { shape := #[1], dtype := .f32 } ]

def f32FactorOrder : AssignPlan :=
  { KernelDenseTest.factorOrderPlan with algebra := admittedAlgebraF32 }

def factorOrderStore32 : Array DenseTensor32 :=
  #[ t32 [] #[3252982345], t32 [] #[3252982345], t32 [] #[3276275712], t32 [1] #[] ]

-- Declared order `[a, b, c]`, folded `((1 · a) · b) · c`. A right-associated fold of the same three
-- values produces `3357503571` — one ULP lower — so this bit pattern is the fold ORDER's own claim,
-- not merely the product's.
#guard bitsOf (run32 factorOrderSigs32 f32FactorOrder factorOrderStore32) == some #[3357503572]

/-! ## Fixtures 5 and 6: the two binary32 sum-product identities, independently

`efpPlan`'s empty factor product can only return `factorId`; `zerdPlan`'s zero-extent reduction
domain can only return `reduceId`. Each therefore pins exactly one identity. -/

def efpSigs32 : Array TensorSignature := #[ { shape := #[3], dtype := .f32 } ]
def f32Efp : AssignPlan := { KernelDenseTest.efpPlan with algebra := admittedAlgebraF32 }
def efpStore32 : Array DenseTensor32 := #[ t32 [3] #[] ]

-- Fixture 5: the factor loop never runs, so the product stays at `factorId` = binary32 `1`.
#guard bitsOf (run32 efpSigs32 f32Efp efpStore32) == some #[1065353216, 1065353216, 1065353216]

def zerdSigs32 : Array TensorSignature :=
  #[ { shape := #[2], dtype := .f32 }, { shape := #[2], dtype := .f32 } ]
def f32Zerd : AssignPlan := { KernelDenseTest.zerdPlan with algebra := admittedAlgebraF32 }
def zerdStore32 : Array DenseTensor32 := #[ t32 [2] #[1088421888, 1090519040], t32 [2] #[] ]

-- Fixture 6: the reduction fold never executes, so the term contributes `reduceId` = binary32 `+0`,
-- regardless of the source's values (`[7, 8]` here).
#guard bitsOf (run32 zerdSigs32 f32Zerd zerdStore32) == some #[0, 0]

/-! ## Fixtures 7 and 8: the two binary32 tropical identities, independently

`contractPlan` under the max and min algebras. In each the seed is LOAD-BEARING: with all-negative
column values a `+0` max seed would win every column, and with all-positive column values a `+0` min
seed would win every column. -/

def contractSigs32 : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f32 }, { shape := #[3], dtype := .f32 }
   , { shape := #[4], dtype := .f32 } ]

def f32MaxContract : AssignPlan :=
  { KernelDenseTest.contractPlan with algebra := admittedAlgebraF32Max }
def f32MinContract : AssignPlan :=
  { KernelDenseTest.contractPlan with algebra := admittedAlgebraF32Min }

/-- `A = [10, 100, 1000, 10000]`, `B = [-1, -2, -3]`. -/
def storeNegB32 : Array DenseTensor32 :=
  #[ t32 [4] #[1092616192, 1120403456, 1148846080, 1176256512]
   , t32 [3] #[3212836864, 3221225472, 3225419776]
   , t32 [4] #[] ]

/-- `A = [10, 100, 1000, 10000]`, `B = [1, 2, 3]`. -/
def storeAB32 : Array DenseTensor32 :=
  #[ t32 [4] #[1092616192, 1120403456, 1148846080, 1176256512]
   , t32 [3] #[1065353216, 1073741824, 1077936128]
   , t32 [4] #[] ]

-- Fixture 7: `max_j A[i]·B[j]` with every product negative is `A[i]·(-1)`, i.e.
-- `[-10, -100, -1000, -10000]`. Only the `0xff800000` (`−∞`) seed makes this right; a `+0` seed
-- would return `[0, 0, 0, 0]`.
#guard bitsOf (run32 contractSigs32 f32MaxContract storeNegB32)
  == some #[3240099840, 3267887104, 3296329728, 3323740160]

-- Fixture 8: `min_j A[i]·B[j]` with every product positive is `A[i]·1`, i.e.
-- `[10, 100, 1000, 10000]`. Only the `0x7f800000` (`+∞`) seed makes this right.
#guard bitsOf (run32 contractSigs32 f32MinContract storeAB32)
  == some #[1092616192, 1120403456, 1148846080, 1176256512]

/-! ## Fixture 9: the out-of-bounds pad is the carrier's zero, not the reduction identity

`oobMaxPlan`: `Y[i] := max_j A[i,j]` with `j` ranging over three values but `A` only two columns
wide. The `j = 2` read is out of bounds and pads with native `+0`, which is a FACTOR value — it
flows through `factorOp` and enters the max fold as a genuine term value. With all-negative valid
data that padded `+0` therefore WINS. -/

def oobSigs32 : Array TensorSignature :=
  #[ { shape := #[2, 2], dtype := .f32 }, { shape := #[2], dtype := .f32 } ]

def f32OobMax : AssignPlan :=
  { KernelDenseTest.oobMaxPlan with algebra := admittedAlgebraF32Max }

/-- `A = [[-1, -2], [-3, -4]]`. -/
def oobStore32 : Array DenseTensor32 :=
  #[ t32 [2, 2] #[3212836864, 3221225472, 3225419776, 3229614080], t32 [2] #[] ]

-- Zero-pad beats every valid (negative) value, as binary32 `+0`. If the pad were the reduction
-- identity `−∞` instead, this would return `[-1, -3]`.
#guard bitsOf (run32 oobSigs32 f32OobMax oobStore32) == some #[0, 0]

/-! ## Fixture 10: Iverson predicates become native one/zero

`truePredPlan`/`falsePredPlan` — `contractPlan` with a coordinate-independent Iverson factor wedged
between its two reads. A true predicate contributes native `1` and leaves the product untouched; a
false one contributes native `+0` and annihilates the whole term. -/

def f32TruePred : AssignPlan :=
  { KernelDenseTest.truePredPlan with algebra := admittedAlgebraF32 }
def f32FalsePred : AssignPlan :=
  { KernelDenseTest.falsePredPlan with algebra := admittedAlgebraF32 }

-- ΣB = 6, so the true case is `A[i]·6` = `[60, 600, 6000, 60000]`, all exact in binary32 — the
-- product bits are UNCHANGED by the predicate factor.
#guard bitsOf (run32 contractSigs32 f32TruePred storeAB32)
  == some #[1114636288, 1142292480, 1169915904, 1198153728]

-- ... and the false case annihilates every term to native `+0`.
#guard bitsOf (run32 contractSigs32 f32FalsePred storeAB32) == some #[0, 0, 0, 0]

-- Control: the same plan WITHOUT the predicate produces the true case's bits, so fixture 10's true
-- case really is "unchanged" rather than coincidentally equal.
#guard bitsOf (run32 contractSigs32 { KernelDenseTest.contractPlan with
    algebra := admittedAlgebraF32 } storeAB32)
  == some #[1114636288, 1142292480, 1169915904, 1198153728]

/-! ## Fixture 12: the TERM fold is left-associated in array order

Fixture 2's three values as three SEPARATELY STORED terms rather than three reduction coordinates of
one term, so this pins the outer term fold where fixture 2 pins the inner reduction fold. Left fold
gives `+0`; a right-associated term fold gives binary32 `1` (bits `1065353216`). -/

def termOrderSigs32 : Array TensorSignature :=
  #[ { shape := #[], dtype := .f32 }, { shape := #[], dtype := .f32 }
   , { shape := #[], dtype := .f32 }, { shape := #[1], dtype := .f32 } ]

def f32TermOrder : AssignPlan :=
  { KernelDenseTest.fosPlan with algebra := admittedAlgebraF32 }

def termOrderStore32 : Array DenseTensor32 :=
  #[ t32 [] #[1266679808], t32 [] #[1065353216], t32 [] #[3414163456], t32 [1] #[] ]

#guard bitsOf (run32 termOrderSigs32 f32TermOrder termOrderStore32) == some #[0]

/-! ## Fixture 13: the binary32 local worker's storage-kind door

Fixture 2's BINARY64 donor, handed straight to the binary32 local entries with arguments that are
ALSO invalid in those workers' own pre-existing terms — a wrong-rank context coordinate for
`runDenseAssignAt32`, an empty store for both. The required answer is
`storageKindMismatch .float32 .float64` in every case, i.e. the storage guard fires BEFORE
`validateContext` and before `validateStore`.

Ordering is the point, not presence: a guard installed after either pre-existing check would still
"reject a binary64 plan", but would report a context or missing-slot cause for a plan this worker
must never look at. The binary32 controls beneath each case show which cause that would have been. -/

def f64Donor : Option CheckedAssignPlan :=
  (checkAssign redSigs64 f64ReductionDonor).toOption

def f32Donor : Option CheckedAssignPlan :=
  (checkAssignF32 redSigs32 f32ReductionRounding).toOption

def atErr32 (c : Option CheckedAssignPlan) (ctx : List Int) (store : Array DenseTensor32) :
    Option PositionalInputError :=
  match c with
  | none => none
  | some c => match runDenseAssignAt32 c ctx store with
              | .error e => some e
              | .ok _ => none

def assignErr32 (c : Option CheckedAssignPlan) (store : Array DenseTensor32) :
    Option PositionalInputError :=
  match c with
  | none => none
  | some c => match runDenseAssign32 c store with
              | .error e => some e
              | .ok _ => none

-- `runDenseAssignAt32`: wrong-rank context AND an empty store; the storage kind is reported.
#guard atErr32 f64Donor [5] #[] == some (.storageKindMismatch .float32 .float64)

-- Control, the binary32 sibling over the same shapes: the pre-existing context check reports.
#guard atErr32 f32Donor [5] #[] == some (.contextShapeMismatch #[] [5])

-- `runDenseAssign32` (the empty-context wrapper) with an empty store: still the storage kind, so the
-- wrapper inherits the deep guard rather than needing its own.
#guard assignErr32 f64Donor #[] == some (.storageKindMismatch .float32 .float64)

-- Control: the binary32 sibling reaches `validateStore` and reports the missing slot.
#guard assignErr32 f32Donor #[] == some (.missingSlot 0 0)

/-! ## Fixture 16: `f32 → bool` and `bool → f32` in one native Float32 store

`ScalarDType.bool` is an algebra tag over whichever real carrier the graph selects, so in a binary32
graph a Boolean destination or source lives in the SAME `Array Float32` store as the real tensors —
no Float buffer, no conversion. `admittedAlgebraBool`'s `.bool true`/`.bool false` identities are
decoded to THIS carrier's exact one/zero, and Boolean-tagged runtime values keep literal `min`/`max`
behavior: they are neither validated as binary nor coerced to exact zero/one. `0.25` and `0.75`
(bits `1048576000`/`1061158912`) are chosen precisely because a coercing implementation would return
`0` or `1` instead. -/

def boolTwoSigs32 : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f32 }, { shape := #[4], dtype := .f32 }
   , { shape := #[4], dtype := .bool } ]

/-- Slot 0 all `0.25`, slot 1 all `0.75`, both native binary32. -/
def nonBinaryStore32 : Array DenseTensor32 :=
  #[ t32 [4] #[1048576000, 1048576000, 1048576000, 1048576000]
   , t32 [4] #[1061158912, 1061158912, 1061158912, 1061158912]
   , t32 [4] #[] ]

-- Across TERMS the Boolean algebra disjoins with `max`:
-- `max(false = +0, min(true = 1, 0.25), min(true = 1, 0.75)) = 0.75`.
#guard bitsOf (run32 boolTwoSigs32 KernelDenseTest.trueFalseTermsBool nonBinaryStore32)
  == some #[1061158912, 1061158912, 1061158912, 1061158912]

-- Within ONE term the factor fold conjoins with `min`, selecting the smaller value where the term
-- fold above selects the larger: `min(min(true = 1, 0.25), 0.75) = 0.25`, then `max(+0, 0.25)`.
#guard bitsOf (run32 boolTwoSigs32 KernelDenseTest.conjNonBinaryBool nonBinaryStore32)
  == some #[1048576000, 1048576000, 1048576000, 1048576000]

/-- The reverse direction: a binary32 REAL destination reading a `bool`-tagged source. -/
def boolSourceSigs32 : Array TensorSignature :=
  #[ { shape := #[4], dtype := .bool }, { shape := #[4], dtype := .f32 } ]

def boolSourceToF32 : AssignPlan :=
  { contextShape := #[], destinationSlot := 1, outputShape := #[4]
  , terms := #[KernelDenseTest.termReading KernelDenseTest.readS0]
  , algebra := admittedAlgebraF32 }

def boolSourceStore32 : Array DenseTensor32 :=
  #[ t32 [4] #[1048576000, 1048576000, 1048576000, 1048576000], t32 [4] #[] ]

-- `0.25` flows through unchanged: gathering is dtype-blind, so a Boolean-tagged buffer is not
-- silently rounded to `{0, 1}` on its way into a real binary32 destination.
#guard bitsOf (run32 boolSourceSigs32 boolSourceToF32 boolSourceStore32)
  == some #[1048576000, 1048576000, 1048576000, 1048576000]

/-! ## Checked binary32 inline unary factors, end to end (f32 slice, Task 2)

`checkAssignF32` now admits an inline unary read structurally, and `float32Ops.applyUnary`
(`Dense.lean`) applies it for real through `UnaryOp.applyChecked32` — every fixture below runs the
FULL checked-plan pipeline (`run32`: `checkAssignF32` then `runDenseAssign32`), never
`applyChecked32` directly, so a checker regression or a plan-wiring bug would show up here too. -/

def unaryF32Sigs2 : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f32 }, { shape := #[4], dtype := .f32 } ]

/-- `KernelDenseTest.unaryPlan op bias`, retagged binary32. -/
def f32UnaryPlan (op : UnaryOp) (bias : Int) : AssignPlan :=
  { KernelDenseTest.unaryPlan op bias with algebra := admittedAlgebraF32 }

/-! ### Fixture 2.2: the domain-partial ops over `unaryPow2Store`, retagged

`unaryPow2Store`'s four values (`[1, 2, 4, 8]`, all exact in binary32) as native bits, run through
each of the three domain-partial ops (`log`, `sqrt`, `recip`) at bias 0. Every lane is in-domain, so
this pins the ARITHMETIC alone (no pad, no rejection). Expected bits agree with
`Nonlin32Test.unaryBits` at these same inputs — the checked plan's algebra multiplies by `factorId`
= binary32 `1`, so `Y[i] = op(X[i])` exactly; not re-derived independently, since both paths bottom
out in the same `UnaryOp.applyChecked32`. -/

def f32UnaryPow2Store : Array DenseTensor32 :=
  #[ t32 [4] #[1065353216, 1073741824, 1082130432, 1090519040], t32 [4] #[] ]

#guard bitsOf (run32 unaryF32Sigs2 (f32UnaryPlan .log 0) f32UnaryPow2Store) ==
  some #[0, 1060205080, 1068593688, 1074075026]
#guard bitsOf (run32 unaryF32Sigs2 (f32UnaryPlan .sqrt 0) f32UnaryPow2Store) ==
  some #[1065353216, 1068827891, 1073741824, 1077216499]
#guard bitsOf (run32 unaryF32Sigs2 (f32UnaryPlan .recip 0) f32UnaryPow2Store) ==
  some #[1065353216, 1056964608, 1048576000, 1040187392]

/-! ### Fixture 2.3: pad-then-apply

`unaryPlan .exp 1` retagged, over `[0, 3.0, -2.5, -0.25]`. The final read (`X[3+1] = X[4]`) is out
of bounds, so it zero-pads to native `+0` BEFORE `exp` runs, giving `exp(+0) = 1` (`1065353216`).
An apply-before-pad reading would apply `exp` only to in-bounds reads and pad the RESULT, so
`exp` would never run on that read. The lane would then be `+0` (bits `0`). -/

def f32PadStore : Array DenseTensor32 :=
  #[ t32 [4] #[0, 1077936128, 3223322624, 3196059648], t32 [4] #[] ]

#guard bitsOf (run32 unaryF32Sigs2 (f32UnaryPlan .exp 1) f32PadStore) ==
  some #[1101049646, 1034427438, 1061642109, 1065353216]

/-! ### Fixture 2.4: worker witnesses (PLATFORM-DEPENDENT)

`unaryPlan op 0` retagged, over `Nonlin32Test`'s own platform witness lanes for `exp`/`log`/`sin`/
`cos` (conflict-scan note C5: the SAME lane lists, not a second hand-typed copy) — every output lane
must equal the native binary32 routine applied directly to that lane, AND at least one lane must
separate that native result from binary64-then-narrow on this platform's libm, the same
precondition `Nonlin32Test.witness` enforces, so this fixture could not pass vacuously if the two
carriers ever agreed everywhere. -/

private def witness32 (label : String) (op : UnaryOp) (native : Float32 → Float32)
    (wide : Float → Float) (lanes : List UInt32) : Lean.Elab.Command.CommandElabM Unit := do
  let x (b : UInt32) := Float32.ofBits b
  unless lanes.any (fun b => (native (x b)).toBits != (wide (x b).toFloat).toFloat32.toBits) do
    throwError s!"{label}: no lane separates native binary32 from binary64-then-narrow on this \
platform's libm; choose new witness lanes (the fixture would otherwise pin nothing)"
  let store : Array DenseTensor32 := #[ t32 [4] lanes.toArray, t32 [4] #[] ]
  match bitsOf (run32 unaryF32Sigs2 (f32UnaryPlan op 0) store) with
  | none => throwError s!"{label}: run32 failed"
  | some got =>
      let expected := lanes.toArray.map (fun b => (native (x b)).toBits)
      unless got == expected do
        throwError s!"{label}: checked-plan output is not the native binary32 routine: \
{repr got} vs {repr expected}"

run_cmd witness32 "exp" .exp Float32.exp Float.exp LeanNCD.Eval.Nonlin32Test.expLanes
run_cmd witness32 "log" .log Float32.log Float.log LeanNCD.Eval.Nonlin32Test.logLanes
run_cmd witness32 "sin" .sin Float32.sin Float.sin LeanNCD.Eval.Nonlin32Test.sinLanes
run_cmd witness32 "cos" .cos Float32.cos Float.cos LeanNCD.Eval.Nonlin32Test.cosLanes

/-- `posErrOf` (`KernelDenseTest.lean`)'s binary32 sibling: the checked plan's runtime failure, or
    `none` if either phase succeeds/is skipped. -/
def posErrOf32 (sigs : Array TensorSignature) (a : AssignPlan) (store : Array DenseTensor32) :
    Option PositionalInputError :=
  match checkAssignF32 sigs a with
  | .error _ => none
  | .ok c => match runDenseAssign32 c store with
             | .error e => some e
             | .ok _ => none

/-! ### Fixture 2.5: domain payloads

Three runtime domain violations, each pinning `unaryDomain32`'s exact payload against
`unaryPlan .sqrt 0`/`.recip 0` retagged. -/

-- `sqrt` over `[1, -4, -9, 4]`: the FIRST violation (`-4`) wins, not the second (`-9`).
def f32SqrtBadStore : Array DenseTensor32 :=
  #[ t32 [4] #[1065353216, 3229614080, 3239051264, 1082130432], t32 [4] #[] ]

#guard posErrOf32 unaryF32Sigs2 (f32UnaryPlan .sqrt 0) f32SqrtBadStore ==
  some (.unaryDomain32 .sqrt 3229614080 0)

-- `recip` over `[2, 0, 4, 8]`.
def f32RecipBadStore : Array DenseTensor32 :=
  #[ t32 [4] #[1073741824, 0, 1082130432, 1090519040], t32 [4] #[] ]

#guard posErrOf32 unaryF32Sigs2 (f32UnaryPlan .recip 0) f32RecipBadStore ==
  some (.unaryDomain32 .recip 0 0)

-- `recip` over `[2, -0, 4, 8]`: the payload is the gathered value's OWN bits, sign included — `-0`,
-- not `+0`.
def f32RecipNegZeroStore : Array DenseTensor32 :=
  #[ t32 [4] #[1073741824, 2147483648, 1082130432, 1090519040], t32 [4] #[] ]

#guard posErrOf32 unaryF32Sigs2 (f32UnaryPlan .recip 0) f32RecipNegZeroStore ==
  some (.unaryDomain32 .recip 2147483648 0)

/-! ### Fixture 2.6: pad-then-apply, on the REJECTING side

`unaryPlan .log 1` retagged, over `unaryPow2Store`'s bits: the final read (`X[3+1] = X[4]`) is out
of bounds and zero-pads to `+0` BEFORE `log` runs, so `log(+0)` is a genuine domain violation.
An apply-before-pad reading would never call `log` on that read, because it pads the RESULT to `+0`
after the fact. So it would report no error at all. -/

#guard posErrOf32 unaryF32Sigs2 (f32UnaryPlan .log 1) f32UnaryPow2Store ==
  some (.unaryDomain32 .log 0 0)

/-! ### Fixture 2.7: slot locator

`unaryPlan .sqrt 0`, retargeted at `sourceSlot := 1`/`destinationSlot := 2` over a three-entry
`.f32` table whose slot 0 is an unread `#[4]` input — so the reported slot (`1`) is distinguishable
from a constant `0` the checker or worker might otherwise default to. -/

def slotLocatorSigs32 : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f32 }, { shape := #[4], dtype := .f32 }, { shape := #[4], dtype := .f32 } ]

def slotLocatorRead : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[1]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad, unary := some .sqrt }

def f32SlotLocatorPlan : AssignPlan :=
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4], contextPos := #[], outputPos := #[0], reductionPos := #[]
               , factors := #[.read slotLocatorRead] }]
  , algebra := admittedAlgebraF32 }

/-- Slot 0: an unread `#[4]` input (its values never matter). Slot 1: `[1, -4, 4, 9]`. Slot 2: the
    destination. -/
def slotLocatorStore32 : Array DenseTensor32 :=
  #[ t32 [4] #[0, 0, 0, 0]
   , t32 [4] #[1065353216, 3229614080, 1082130432, 1091567616]
   , t32 [4] #[] ]

#guard posErrOf32 slotLocatorSigs32 f32SlotLocatorPlan slotLocatorStore32 ==
  some (.unaryDomain32 .sqrt 3229614080 1)

end LeanNCD.Eval.Plan.KernelDense32Test
