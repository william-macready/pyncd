import LeanNCD.Eval.Nonlin
namespace LeanNCD.Eval
open Std
private def t1 (xs : List Float) : DenseTensor := ⟨[xs.length], xs.toArray⟩
private def ax (nm : String) (u : Nat) : AxisSpec := { name := nm, uid := u, kind := .real }
-- relu:
#guard DenseTensor.approxEq (reluT (t1 [-1, 2, -3, 4])) (t1 [0, 2, 0, 4])
-- softmax of a single row sums to 1 (axisPos 0, all-included):
run_cmd do
  let y := softmaxT 0 (fun _ => true) (t1 [1, 2, 3])
  let s := y.data.foldl (· + ·) 0.0
  unless Float.abs (s - 1.0) < 1e-6 do throwError s!"softmax row should sum to 1, got {s}"
  -- monotone: larger logit ⇒ larger prob
  unless y.data[0]! < y.data[1]! && y.data[1]! < y.data[2]! do throwError "softmax not monotone"
-- normalize: [1,1,2] ⇒ [0.25,0.25,0.5]
#guard DenseTensor.approxEq (normalizeT 0 (fun _ => true) (t1 [1,1,2])) (t1 [0.25, 0.25, 0.5])
-- masked softmax: a 2×2 with a mask excluding the upper-triangle (toy) still sums to 1 per row over unmasked
run_cmd do
  -- t shape [2,2], axisPos 1 (the second axis), uids [q=1, s=2]; mask: s ≤ q (causal)
  let t : DenseTensor := ⟨[2,2], #[1.0, 2.0, 0.5, 1.5]⟩
  let mask : BoolExpr := .rel .le (.embed (.axis ⟨"s",2,.real⟩)) (.embed (.axis ⟨"q",1,.real⟩))
  let y := AxiswiseFn.apply .softmax 1 [1,2] (some mask) t
  -- row q=0: only s=0 unmasked ⇒ y[0,0]=1, y[0,1]=0 ; row q=1: both unmasked ⇒ sums to 1
  unless Float.abs (y.get! [0,0] - 1.0) < 1e-6 && Float.abs (y.get! [0,1] - 0.0) < 1e-6 do throwError "masked row0"
  unless Float.abs ((y.get! [1,0] + y.get! [1,1]) - 1.0) < 1e-6 do throwError "masked row1 sum"

-- 4d: resolveNonlin rejects a missing norm marker for an axiswise fn, and accepts pointwise/
-- identity unconditionally (no marker needed). Mirrors the two error messages evalPlain and
-- evalStmtSliceSeeded used to duplicate independently.
run_cmd do
  let i := ax "i" 1
  match resolveNonlin (.axiswise .softmax none) [.free i] [1] with
  | .error (.invalidNormAxis .notMarked) => pure ()
  | .error e => throwError s!"4d: wrong error for missing norm marker: {e}"
  | .ok _    => throwError "4d: expected rejection of axiswise nonlin with no marked norm axis"
run_cmd do
  let i := ax "i" 1
  match resolveNonlin (.pointwise .relu) [.free i] [1] with
  | .error e => throwError s!"4d: pointwise resolution should never need a norm axis, got {e}"
  | .ok (.pointwise .relu) => pure ()
  | .ok _ => throwError "4d: expected .pointwise .relu to resolve unchanged"

-- F32-B fixture 1.1 — the binary64 golden bit table. Every value below was captured from the
-- PRE-refactor `Eval/Nonlin.lean` (the `Float`-only `reluT` … `l2normalizeT` bodies), before the
-- formulas were generalized over a carrier. The legacy evaluator, the checked workers, and the
-- scan-unroll oracle all call these same functions, so none of them can notice a change to the
-- shared binary64 math; this table is the one independent pin that the refactor changed nothing.

/-- Exact-bits comparison with one allowance: a NaN lane matches any NaN, because IEEE-754 does not
    fix the payload a NaN-producing primitive returns. Every other lane — including `-0` — is
    compared bit for bit. -/
private def sameBits64 (xs : Array Float) (bits : Array UInt64) : Bool :=
  xs.size == bits.size && (xs.zip bits).all fun (x, b) =>
    if x.isNaN then (Float.ofBits b).isNaN else x.toBits == b

private def goldenPts : DenseTensor := ⟨[5], #[-1.25, -0.0, 0.7, 2.0, 0.0 / 0.0]⟩
private def goldenPointwise : List (PointwiseFn × Array UInt64) :=
  [ (.relu,      #[0, 9223372036854775808, 4604480259023595110, 4611686018427387904, 0])
  , (.sigmoid,   #[4597191638388367573, 4602678819172646912, 4604193719948776566,
                   4606108734329616841, 9221120237041090560])
  , (.tanh,      #[13829187916169686510, 9223372036854775808, 4603618880536915601,
                   4606858408046085076, 9221120237041090560])
  , (.gelu,      #[13817306155275007250, 9223372036854775808, 4602954170467180171,
                   4611481544619399846, 9221120237041090560])
  , (.leakyrelu, #[13801731418039622042, 9223372036854775808, 4604480259023595110,
                   4611686018427387904, 9221120237041090560]) ]
#guard goldenPointwise.all fun (pf, bits) => sameBits64 (pf.apply goldenPts).data bits

private def goldenRow : DenseTensor := ⟨[3], #[0.5, 1.0, 2.5]⟩
private def maskPos1 (c : List Nat) : Bool := c != [1]
private def goldenAxiswise : List (AxiswiseFn × Array UInt64 × Array UInt64) :=
  [ (.softmax,
      #[4591843061051816868, 4595085808842274168, 4604805641613501230],
      #[4593253896426369454, 0, 4606108734329616841])
  , (.normalize,
      #[4593671619917905920, 4598175219545276416, 4603804719079489536],
      #[4595172819793696085, 0, 4605681218924227243])
  , (.l2normalize,
      #[4595745948572889240, 4600249548200259736, 4606397629898218687],
      #[4596233848715572764, 0, 4607007505076573091]) ]
#guard goldenAxiswise.all fun (fn, all, masked) =>
  sameBits64 (fn.applyCore 0 (fun _ => true) goldenRow).data all &&
  sameBits64 (fn.applyCore 0 maskPos1 goldenRow).data masked
end LeanNCD.Eval
