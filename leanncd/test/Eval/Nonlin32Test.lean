import LeanNCD.Eval.Nonlin

/-!
# Native binary32 nonlinearities and unary domain (F32-B, Task 1)

Fixtures 1.2–1.8 of `papers/f32b_evalplan.md` Task 1, over `PointwiseFn.apply32`,
`AxiswiseFn.applyCore32`, and `UnaryOp.applyChecked32`. (Fixture 1.1, the binary64 golden table,
lives in `NonlinTest`.)

**Every expectation is an exact IEEE-754 binary32 bit pattern, compared through `Float32.toBits`**,
except NaN lanes, which are asserted with `isNaN` because IEEE-754 does not fix a NaN's payload.
`BEq Float32` is IEEE comparison (`+0 == -0`, `NaN != NaN`), so it never asserts a value here.

"Narrowed" means binary64-then-narrow: widen the tensor, run the binary64 function, round once.
Every discriminating value below is asserted TOGETHER with its narrowed contrast, so each fixture
proves it separates native per-operation binary32 rounding from a late narrowing rather than
assuming it.

Fixture 1.8 is the only fixture here whose inputs depend on the platform libm (plan §3.6).
-/

namespace LeanNCD.Eval.Nonlin32Test
open LeanNCD LeanNCD.Eval

/-- A 1-D binary32 tensor from exact bit patterns. -/
def v32 (bits : List UInt32) : DenseTensor32 := ⟨[bits.length], bits.toArray.map Float32.ofBits⟩

/-- A 1-D binary32 row from binary64 literals that are all EXACTLY representable in binary32
    (every literal passed here is a small dyadic or an integer below 2²⁴), so narrowing them is
    exact and the row is the one written. -/
def row32 (xs : List Float) : DenseTensor32 := ⟨[xs.length], xs.toArray.map Float.toFloat32⟩

/-- The exact bits of every element. -/
def bitsOf (t : DenseTensor32) : Array UInt32 := t.data.map Float32.toBits

/-- Binary64-then-narrow: widen `t`, apply the binary64 function `f`, narrow the result once.
    `private`: no cross-file caller (checked repo-wide) — every other file's own narrowed-contrast
    helper (`narrowLane`, `narrowAll`, the `Adapter32Test`/`KernelDense32Test` twins) is its own. -/
private def narrowed (f : DenseTensor → DenseTensor) (t : DenseTensor32) : DenseTensor32 :=
  let w := f ⟨t.shape, t.data.map Float32.toFloat⟩
  ⟨w.shape, w.data.map Float.toFloat32⟩

/-- Exact-bits comparison with one allowance: a NaN lane matches any NaN. -/
def sameBits32 (xs ys : Array Float32) : Bool :=
  xs.size == ys.size && (xs.zip ys).all fun (x, y) =>
    if x.isNaN then y.isNaN else x.toBits == y.toBits

def pointwiseFns : List PointwiseFn := [.relu, .sigmoid, .tanh, .gelu, .leakyrelu]
def axiswiseFns : List AxiswiseFn := [.softmax, .normalize, .l2normalize]

/-! ## Direct formulas (shared by fixtures 1.2 and 1.3)

Each pointwise function written out directly over `Float32`, WITHOUT the module's private
`NonlinScalarOps` record, so an agreement is between two independently spelled formulas. `gelu32`
spells its two constants as literal bits (`√(2/π)` = `0x3f4c422a`, `0.044715` = `0x3d372713`), as
does `leaky32` its slope (`0.01` = `0x3c23d70a`); the remaining literals (`0`, `0.5`, `1`, `3`) are
exact in binary32. -/

def relu32 (x : Float32) : Float32 := max 0.0 x
/-- `sigmoid` with its one transcendental passed in. Fixture 1.8's composite witness also uses it,
    to substitute a narrowed `exp`. -/
def sig32With (exp : Float32 → Float32) (x : Float32) : Float32 := 1.0 / (1.0 + exp (-x))
def sig32 : Float32 → Float32 := sig32With Float32.exp
/-- `gelu` with its cube (`pow x 3`) passed in. Fixture 1.8's composite witness also uses it. -/
def gelu32With (pow : Float32 → Float32 → Float32) (x : Float32) : Float32 :=
  0.5 * x * (1.0 + Float32.tanh (Float32.ofBits 0x3f4c422a *
    (x + Float32.ofBits 0x3d372713 * pow x 3.0)))
def gelu32 : Float32 → Float32 := gelu32With Float32.pow
def leaky32 (x : Float32) : Float32 := if x ≥ 0.0 then x else Float32.ofBits 0x3c23d70a * x

/-- `private`: no cross-file caller (checked repo-wide); this fixture's own independent formula,
    never reused as a production dispatch table. -/
private def direct : PointwiseFn → Float32 → Float32
  | .relu => relu32 | .sigmoid => sig32 | .tanh => Float32.tanh | .gelu => gelu32
  | .leakyrelu => leaky32

/-! ## Fixture 1.2: binary32 pointwise lanes

Lanes `L`: `0.7f`, `1058161516`, `-1.1875`, `-1.25`, `-0`, `NaN`, `2.0`. -/

-- `private`: no cross-file caller (checked repo-wide) — unlike `expLanes`/`logLanes`/`sinLanes`/
-- `cosLanes` below, which fixtures 2.4/2.10 do reuse qualified.
private def L : List UInt32 :=
  [1060320051, 1058161516, 3214409728, 3214934016, 2147483648, 2143289344, 1073741824]
private def lanes : DenseTensor32 := v32 L

/-- Native bits of lane `i` of `pf.apply32`. `private`: no cross-file caller. -/
private def lane (pf : PointwiseFn) (i : Nat) : UInt32 := (bitsOf (pf.apply32 lanes))[i]!
/-- Narrowed-contrast bits of lane `i` (binary64 `pf.apply`, then one rounding). -/
def narrowLane (pf : PointwiseFn) (i : Nat) : UInt32 :=
  (bitsOf (narrowed pf.apply lanes))[i]!

-- Every lane, every function, against the direct formula (NaN lanes match any NaN).
#guard pointwiseFns.all fun pf =>
  sameBits32 (pf.apply32 lanes).data (lanes.data.map (direct pf))

-- The four discriminating lanes, each with its narrowed contrast (plan §2.6): `sigmoid` at lanes
-- 0–1 (an `expf` step), `gelu` at `-1.1875` (lane 2), `leakyrelu` at `-1.25` (lane 3, one `×`).
#guard (lane .sigmoid 0, lane .sigmoid 1) == (1059786330, 1059297860)
#guard (narrowLane .sigmoid 0, narrowLane .sigmoid 1) == (1059786331, 1059297859)
#guard lane .gelu 2 == 3188661568 && narrowLane .gelu 2 == 3188661569
#guard lane .leakyrelu 3 == 3159149772 && narrowLane .leakyrelu 3 == 3159149773

-- Semantic lanes, identical in both carriers: `relu` of `-1.1875`, `-1.25`, `-0`, `NaN` is
-- `+0, +0, -0, +0` (`maxOfLe` returns `x` exactly when `0 ≤ x`); `-0` passes through `tanh`,
-- `gelu`, and `leakyrelu`; `sigmoid(-0) = 0.5`.
#guard (List.range 4).map (fun k => lane .relu (k + 2)) == [0, 0, 2147483648, 0]
#guard [PointwiseFn.tanh, .gelu, .leakyrelu].all fun pf => lane pf 4 == 2147483648
#guard lane .sigmoid 4 == 1056964608

-- NaN propagates through every function except `relu`.
#guard [PointwiseFn.sigmoid, .tanh, .gelu, .leakyrelu].all fun pf =>
  ((pf.apply32 lanes).data[5]!).isNaN

/-! ## Fixture 1.3: independent-formula sweep

On the 64-point grid `(i − 32)/8 + 1/16`, `i < 64` (every point exact in binary32), each
`PointwiseFn.apply32` equals its direct formula bit for bit. -/

-- `private`: no cross-file caller (checked repo-wide).
private def grid : DenseTensor32 :=
  ⟨[64], (List.range 64).toArray.map fun i => ((i.toFloat - 32.0) / 8.0 + 0.0625).toFloat32⟩

#guard pointwiseFns.all fun pf =>
  bitsOf (pf.apply32 grid) == grid.data.map (fun x => (direct pf x).toBits)

/-! ## Fixture 1.4: binary32 axiswise discriminators

Each unmasked row's native bits, with the narrowed contrast (plan §2.6). -/

def applyAll32 (fn : AxiswiseFn) (t : DenseTensor32) : Array UInt32 :=
  bitsOf (fn.applyCore32 0 (fun _ => true) t)
def narrowAll (fn : AxiswiseFn) (t : DenseTensor32) : Array UInt32 :=
  bitsOf (narrowed (fn.applyCore 0 (fun _ => true)) t)

-- softmax [0, 0, 2.5]: the `exp(-2.5)` step separates the two.
#guard applyAll32 .softmax (row32 [0, 0, 2.5]) == #[1032873795, 1032873795, 1062987311]
#guard narrowAll .softmax (row32 [0, 0, 2.5]) == #[1032873796, 1032873796, 1062987311]
-- normalize [2²⁴, 1, 1]: native binary32 absorbs each `+ 1` into `2²⁴`.
#guard applyAll32 .normalize (row32 [16777216, 1, 1]) == #[1065353216, 864026624, 864026624]
#guard narrowAll .normalize (row32 [16777216, 1, 1]) == #[1065353214, 864026622, 864026622]
-- l2normalize [4097, 4097]: `4097²` is not exact in binary32.
#guard applyAll32 .l2normalize (row32 [4097, 4097]) == #[1060439284, 1060439284]
#guard narrowAll .l2normalize (row32 [4097, 4097]) == #[1060439283, 1060439283]

/-! ## Fixture 1.5: axiswise fold order and masking -/

-- The softmax sum is a LEFT fold. A right fold gives `[1031490511, 1031490511, 1040514972,
-- 1061115550]` on this row (narrowing happens to agree with native here, so this row pins order,
-- not carrier; `[0, 0, 2.5]` above does not separate the fold orders).
#guard applyAll32 .softmax (row32 [0, 0, 0.75, 2.5]) ==
  #[1031490512, 1031490512, 1040514973, 1061115551]

-- A masked entry is excluded from the row MAXIMUM: with position 0 (`1000`) masked, the max is
-- `2.5`. Were the masked `1000` admitted to the max, every `exp` would underflow and the row would
-- collapse to `[0, 0, 0]`. (Narrowed gives `[0, 1033591689, 1064080527]`.)
#guard bitsOf (AxiswiseFn.softmax.applyCore32 0 (fun c => c != [0]) (row32 [1000, 0, 2.5])) ==
  #[0, 1033591688, 1064080527]

-- An all-masked row is all `+0` for every axiswise function.
#guard axiswiseFns.all fun fn =>
  bitsOf (fn.applyCore32 0 (fun _ => false) (row32 [1, 2])) == #[0, 0]

/-! ## Fixture 1.6: unary domain parity

For all six ops and nine boundary bit patterns (`±0`, `±` least subnormal, `±1`, `±∞`, `NaN`), the
binary32 domain rule accepts exactly when the binary64 one does on the widened value. -/

def unaryOps : List UnaryOp := [.log, .exp, .sin, .cos, .sqrt, .recip]
def boundaryBits : List UInt32 :=
  [0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x3f800000, 0xbf800000, 0x7f800000,
   0xff800000, 0x7fc00000]

#guard unaryOps.all fun op => boundaryBits.all fun b =>
  let v := Float32.ofBits b
  (op.applyChecked32 v).toBool == (op.applyChecked v.toFloat).toBool

/-! ## Fixture 1.7: portable unary values

Lanes where native equals narrowed and the result is correctly rounded or exact (plan §2.6), so
these bits hold on any conforming libm. -/

/-- `applyChecked32` over each input, as output bits; `none` on any domain error. -/
def unaryBits (op : UnaryOp) (xs : List Float) : Option (List UInt32) :=
  xs.mapM fun x => (op.applyChecked32 x.toFloat32).toOption.map Float32.toBits

#guard unaryBits .log [1, 2, 4, 8] == some [0, 1060205080, 1068593688, 1074075026]
#guard unaryBits .sqrt [1, 2, 4, 8] == some [1065353216, 1068827891, 1073741824, 1077216499]
#guard unaryBits .recip [1, 2, 4, 8] == some [1065353216, 1056964608, 1048576000, 1040187392]
#guard unaryBits .exp [3.0, -2.5, -0.25, 0] ==
  some [1101049646, 1034427438, 1061642109, 1065353216]

/-! ## Fixture 1.8: libm witnesses (PLATFORM-DEPENDENT)

The witness pattern (plan §3.6): the implementation must equal the native binary32 routine on
every lane, AND at least one lane must be one where the native routine differs from
binary64-then-narrow on THIS platform's libm — otherwise the fixture could not tell the two apart,
and it says so instead of passing. If a libm change makes the precondition fail, re-run the plan
§8 witness search for new lanes; never weaken the precondition.

The native outputs are recorded here in comments ONLY (observed on the authoring platform). They
are deliberately not asserted: that would pin this libm's exact rounding error.

- `exp`  → `1067808354, 1068064150, 1068715284, 1068780010`
- `log`  → `893386747, 908066803, 912261095, 923795415`
- `sin`  → `1048714903, 1048734709, 1048758472, 1048885130`
- `cos`  → `1064615103, 1062293444, 1061004150, 1060050850`
- `tanh` → `1048281192, 1048655277, 1049659241, 1049693157`

The two COMPOSITE witnesses cover the record's `exp` and `pow` fields as `sigmoid` and `gelu` use
them. That `exp` is a different code path from `UnaryOp.applyChecked32`'s, which the `exp` witness
above covers. The portable composite lanes of fixtures 1.2–1.5 cannot tell native `expf`/`powf`
from that ONE primitive narrowed from binary64 with every other step still binary32 (§1.1). So the
alternative here is the direct formula with only that primitive narrowed. It is not the widened
formula.

- `sigmoid` (narrowed `exp`) → `1057489900, 1057490686, 1057493836, 1057500141`
- `gelu` (narrowed `pow`)    → `1058598916, 1061545720, 1062357744, 1062945309`
-/

/-- Fail unless `impl` equals `native` on every lane and some lane separates `native` from `alt`
    (described as `altName` in the failure message). -/
def witnessVs (label altName : String) (impl native alt : Float32 → Float32)
    (lanes : List UInt32) : Lean.Elab.Command.CommandElabM Unit := do
  let x (b : UInt32) := Float32.ofBits b
  unless lanes.any (fun b => (native (x b)).toBits != (alt (x b)).toBits) do
    throwError s!"{label}: no lane separates native binary32 from {altName} on this \
platform's libm; choose new witness lanes (the fixture would otherwise pin nothing)"
  unless lanes.all (fun b => (impl (x b)).toBits == (native (x b)).toBits) do
    throwError s!"{label}: implementation is not the native binary32 routine"

/-- `witnessVs` against binary64 `wide`-then-narrow of the whole routine. -/
def witness (label : String) (impl native : Float32 → Float32) (wide : Float → Float)
    (lanes : List UInt32) : Lean.Elab.Command.CommandElabM Unit :=
  witnessVs label "binary64-then-narrow" impl native (fun v => (wide v.toFloat).toFloat32) lanes

/-- `applyChecked32` as a total function for the witness (the witness lanes are all in-domain; a
    domain error would surface as a quiet NaN, which cannot equal a finite native output). -/
def viaChecked32 (op : UnaryOp) (v : Float32) : Float32 :=
  (op.applyChecked32 v).toOption.getD (Float32.ofBits 0x7fc00000)

def expLanes : List UInt32 := [1048801280, 1049583616, 1051496448, 1051680768]
def logLanes : List UInt32 := [1065353222, 1065353236, 1065353244, 1065353288]
def sinLanes : List UInt32 := [1048809472, 1048829952, 1048854528, 1048985600]
def cosLanes : List UInt32 := [1050177536, 1058869248, 1060933632, 1062293504]
def tanhLanes : List UInt32 := [1048600576, 1048842240, 1049923584, 1049960448]
def tanhVia32 (v : Float32) : Float32 := (PointwiseFn.tanh.apply32 ⟨[1], #[v]⟩).data[0]!

run_cmd witness "exp" (viaChecked32 .exp) Float32.exp Float.exp expLanes
run_cmd witness "log" (viaChecked32 .log) Float32.log Float.log logLanes
run_cmd witness "sin" (viaChecked32 .sin) Float32.sin Float.sin sinLanes
run_cmd witness "cos" (viaChecked32 .cos) Float32.cos Float.cos cosLanes
run_cmd witness "tanh" tanhVia32 Float32.tanh Float.tanh tanhLanes

/-- Lane `v` of `pf.apply32`, the production path through the module's `float32NonlinOps`. -/
def pointwiseVia32 (pf : PointwiseFn) (v : Float32) : Float32 := (pf.apply32 ⟨[1], #[v]⟩).data[0]!

-- The composite witnesses. The sigmoid lanes are in `[0.1254, 0.1279]`, where the separating step
-- is `exp(-x)`. The gelu lanes are in `[0.767, 1.015]`, where it is the cube `x³`.
def sigmoidExpLanes : List UInt32 := [1040214460, 1040227085, 1040277686, 1040378989]
def geluPowLanes : List UInt32 := [1061450927, 1064289633, 1065046830, 1065471434]

run_cmd (witnessVs "sigmoid (record exp)" "sigmoid with a binary64-then-narrow exp"
  (pointwiseVia32 .sigmoid) sig32 (sig32With fun v => (Float.exp v.toFloat).toFloat32)
  sigmoidExpLanes)
run_cmd (witnessVs "gelu (record pow)" "gelu with a binary64-then-narrow pow"
  (pointwiseVia32 .gelu) gelu32 (gelu32With fun a b => (a.toFloat ^ b.toFloat).toFloat32)
  geluPowLanes)

end LeanNCD.Eval.Nonlin32Test
