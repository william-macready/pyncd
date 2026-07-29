import LeanNCD.DSL.Elab

namespace LeanNCD
open Lean Elab

run_cmd do
  let b ← Command.liftTermElabM <| LeanNCD.elabTLBoolExpr (← `(tl_bool_expr| s ≤ q))
  match b with | .rel .le _ _ => pure () | _ => throwError s!"expected ≤ rel, got {repr b}"

run_cmd do
  let r ← Command.liftTermElabM <| LeanNCD.elabTLRHS (← `(tl_rhs| softmax(where s ≤ q)(Q[q, d] · K[s, d])))
  match r.nonlin with | .axiswise .softmax (some _) => pure () | _ => throwError "expected masked softmax"
  match r.body.terms with
  | [t] => unless t.factors.length == 2 do throwError "expected two factors"
  | _   => throwError "expected one product term"

run_cmd do
  -- Iverson factor + plain read in a product
  let p ← Command.liftTermElabM <| LeanNCD.elabTLProdTerm (← `(tl_prod_term| W[i, k] · X[k, j]))
  unless p.factors.length == 2 do throwError "expected two factors"

-- Regression: UNMASKED softmax/normalize over a sum must parse (the masked `softmax(where …)`
-- rule shares a `softmax (` prefix; `atomic("(" "where")` left-factoring lets the bare token win).
run_cmd do
  let r ← Command.liftTermElabM <| LeanNCD.elabTLRHS (← `(tl_rhs| softmax(A[i] + B[i])))
  match r.nonlin with | .axiswise .softmax none => pure () | _ => throwError "expected unmasked softmax"
  unless r.body.terms.length == 2 do throwError "expected two sum terms under unmasked softmax"

run_cmd do
  let r ← Command.liftTermElabM <| LeanNCD.elabTLRHS (← `(tl_rhs| normalize(A[i])))
  match r.nonlin with | .axiswise .normalize none => pure () | _ => throwError "expected unmasked normalize"

/-! ## Two closed nonlin keyword categories (Spike 3b)

`tl_nonlin` is the union of two closed keyword categories, `tl_pointwise_kw` and
`tl_axiswise_kw`; only the axiswise production carries the optional `(where …)` mask.  The tests
below pin (a) the keyword→enum map for *every* keyword, (b) mask retention on every axiswise
keyword, (c) that `tl_rhs`'s `tl_nonlin "(" tl_sum_expr ")"` composes over BOTH sub-categories,
and (d) that a pointwise mask is not even parseable. -/

-- (a) Every keyword maps to its own enum constructor, asserted as an EQUALITY against the
-- expected `Nonlin` — a swapped mapping (or a keyword falling through to a default) fails here.
run_cmd do
  let cases : List (Syntax × Nonlin) :=
    [ (← `(tl_nonlin| relu),        .pointwise .relu)
    , (← `(tl_nonlin| sigmoid),     .pointwise .sigmoid)
    , (← `(tl_nonlin| tanh),        .pointwise .tanh)
    , (← `(tl_nonlin| gelu),        .pointwise .gelu)
    , (← `(tl_nonlin| leakyrelu),   .pointwise .leakyrelu)
    , (← `(tl_nonlin| softmax),     .axiswise .softmax none)
    , (← `(tl_nonlin| normalize),   .axiswise .normalize none)
    , (← `(tl_nonlin| l2normalize), .axiswise .l2normalize none) ]
  for (stx, expected) in cases do
    let got ← Command.liftTermElabM <| LeanNCD.elabTLNonlin stx
    unless got == expected do throwError s!"expected {repr expected}, got {repr got}"

-- (b) The mask survives on every axiswise keyword (and only ever on axiswise ones).
run_cmd do
  let masked : List (Syntax × AxiswiseFn) :=
    [ (← `(tl_nonlin| softmax( where s ≤ q)),     .softmax)
    , (← `(tl_nonlin| normalize( where s ≤ q)),   .normalize)
    , (← `(tl_nonlin| l2normalize( where s ≤ q)), .l2normalize) ]
  for (stx, fn) in masked do
    match ← Command.liftTermElabM <| LeanNCD.elabTLNonlin stx with
    | .axiswise fn' (some (.rel .le _ _)) =>
        unless fn' == fn do throwError s!"expected {repr fn}, got {repr fn'}"
    | n => throwError s!"expected masked {repr fn} with a ≤ mask, got {repr n}"

-- (c) `tl_rhs` composes over BOTH sub-categories: a bare POINTWISE keyword followed by `(sum)`
-- must still parse (the softmax/normalize cases above cover the axiswise side).
run_cmd do
  let r ← Command.liftTermElabM <| LeanNCD.elabTLRHS (← `(tl_rhs| relu(W[i, j] · x[j])))
  match r.nonlin with | .pointwise .relu => pure () | _ => throwError "expected relu over a sum"
  match r.body.terms with
  | [t] => unless t.factors.length == 2 do throwError "expected two factors under relu"
  | _   => throwError "expected one product term under relu"

-- (d) NEGATIVE: `relu(where …)` is unrepresentable.  With two categories this is a *parse* error,
-- not an elaboration error — so the diagnostic is a blunt "expected …" from the parser rather than
-- a tailored "relu takes no mask" (the trade-off recorded in the Spike 3b plan).  A quotation of
-- unparseable syntax would fail the build outright, so the check runs the category parser on a
-- string.  The masked/unmasked `softmax` lines are positive controls: they prove the mechanism
-- accepts what it should, so the `relu` rejection is not vacuous.
run_cmd do
  let env ← getEnv
  let parses (cat : Name) (s : String) : Bool :=
    (Lean.Parser.runParserCategory env cat s).toOption.isSome
  unless parses `tl_nonlin "softmax(where s ≤ q)" do
    throwError "control: masked softmax should parse as tl_nonlin"
  unless parses `tl_nonlin "relu" do
    throwError "control: bare relu should parse as tl_nonlin"
  if parses `tl_nonlin "relu(where s ≤ q)" then
    throwError "relu(where …) must NOT parse: pointwise nonlinearities take no mask"
  -- ... and it stays rejected in the position it would actually be written, at `tl_rhs`.
  unless parses `tl_rhs "relu(W[i, j] · x[j])" do
    throwError "control: relu over a sum should parse as tl_rhs"
  if parses `tl_rhs "relu(where s ≤ q)(A[i])" then
    throwError "relu(where …)(…) must NOT parse as tl_rhs"

end LeanNCD
