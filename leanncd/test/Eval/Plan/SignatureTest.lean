import LeanNCD.Eval.Plan.Signature
import LeanNCD.Eval.Entry

/-!
# Wave C C1 signature-boundary tests

Covers `papers/wave_c_evalplan_proposal.md` §A.5's six test bullets for the static signature
boundary: signature conversion, existing-shape-test parity, corpus parity, an
`explicitSizes`-only extent, a pinned-size/input conflict, and warning preservation across a
later failure.
-/

namespace LeanNCD.Eval.Plan.SignatureTest
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std

private def conversionInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2, 3], #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0]⟩

#guard (InputSignature.ofDenseInputs conversionInputs).tensors["X"]? ==
  some ({ shape := #[2, 3], dtype := .f64 } : TensorSignature)
#guard (InputSignature.ofDenseInputs conversionInputs).tensors["Missing"]? == none

-- Task 4.3, fixture 1: `conversionInputs`, with `X` declared a predicate — `ofDenseInputsForDecls`
-- derives `bool` for it, not `f64`.
#guard (InputSignature.ofDenseInputsForDecls [.predicate "X" []] conversionInputs).tensors["X"]? ==
  some ({ shape := #[2, 3], dtype := .bool } : TensorSignature)

-- Task 4.3, fixture 2: the SAME fixture with no declaration at all — `f64`, and the existing
-- `ofDenseInputs` guard just above stays byte-for-byte unchanged (it is not declaration-aware and
-- this task does not touch it).
#guard (InputSignature.ofDenseInputsForDecls [] conversionInputs).tensors["X"]? ==
  some ({ shape := #[2, 3], dtype := .f64 } : TensorSignature)

-- Task 4.3, fixture 3: `GnnScatterTest`'s GN2 shape (`predicate edge(i, j); H[i, f] := edge[i, j]
-- · X[j, f]`, `test/Eval/Portfolio/GnnScatterTest.lean`) compiled to a schedule, then its
-- declaration-aware signature constructed directly from `sched.decls`: `edge` (declared predicate)
-- is `bool`, `X` (undeclared) is `f64`.
private def gn2Prog : TLProgram := tlprog!{ predicate edge(i, j)
  H[i, f] := edge[i, j] · X[j, f] }

private def gn2Inputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "edge" ⟨[2, 2], #[0.0, 1.0, 1.0, 0.0]⟩).insert
    "X" ⟨[2, 2], #[1.0, 2.0, 3.0, 4.0]⟩

run_cmd do
  match gn2Prog.compileToScheduled.run 0 with
  | .error e _ => throwError s!"GN2 clone compile failed: {repr e}"
  | .ok sched _ =>
      let sig := InputSignature.ofDenseInputsForDecls sched.decls gn2Inputs
      unless sig.tensors["edge"]?.map (·.dtype) == some .bool do
        throwError s!"GN2 clone: edge dtype wrong: {repr (sig.tensors["edge"]?)}"
      unless sig.tensors["X"]?.map (·.dtype) == some .f64 do
        throwError s!"GN2 clone: X dtype wrong: {repr (sig.tensors["X"]?)}"

/-- Run both shape-inference adapters over the same schedule and concrete inputs, and assert
    their outcomes agree exactly — the Gate's own criterion, applied directly rather than
    re-derived by hand. -/
private def parityCheck (sched : ScheduledProgram) (inputs : HashMap String DenseTensor) :
    Except String Unit := do
  let allStmts : List Stmt := sched.stmts.flatMap (fun
    | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
  let sig := InputSignature.ofDenseInputs inputs
  match inferAxisSizes sched.explicitSizes inputs allStmts,
        inferAxisSizesFromSignature sched.explicitSizes sig allStmts with
  | .ok (sizes1, warns1), .ok (sizes2, warns2) =>
      unless decide (sizes1.toList = sizes2.toList) do
        throw s!"sizes diverged: {sizes1.toList} vs {sizes2.toList}"
      unless decide (warns1 = warns2) do
        throw s!"warnings diverged: {warns1} vs {warns2}"
  | .error e1, .error e2 =>
      -- `EvalError` has no `DecidableEq` (its `.unaryDomain` case carries a `Float`, which has
      -- none either — confirmed empirically, not assumed), so structural `=` does not typecheck
      -- here; compare via the existing byte-for-byte `ToString EvalError` renderer instead. Every
      -- error this helper actually sees is `inferAxisSizesCore`'s own `.shape` variant (the only
      -- one it ever throws — see `Eval/SizeInfer.lean`), whose `ShapeError` DOES derive
      -- `DecidableEq`, so the rendered text is a faithful, lossless stand-in for structural
      -- equality in every case this test corpus exercises.
      unless decide (toString e1.error = toString e2.error) do
        throw s!"errors diverged: {e1.error} vs {e2.error}"
      unless decide (e1.warnings = e2.warnings) do
        throw s!"error-path warnings diverged: {e1.warnings} vs {e2.warnings}"
  | .ok _, .error e2 => throw s!"env-based path succeeded but signature-based path failed: {e2.error}"
  | .error e1, .ok _ => throw s!"signature-based path succeeded but env-based path failed: {e1.error}"

private def parityProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def parityInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩

run_cmd do
  match parityProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"parity-case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched parityInputs with
      | .error e => throwError s!"parity mismatch (existing shape case): {e}"
      | .ok () => pure ()

-- Category 2b — sizeless-axis parity: giving the assertion real teeth.
--
-- Every fixture above pins its axes via `axis i : ℕ = n`, so `sched.explicitSizes` already seeds
-- every axis's size before either adapter's shape lookup ever runs — confirmed empirically:
-- temporarily swapping `parityCheck`'s derived signature for an empty one still passes
-- `parityProg`, `multiFactorProg`, `chainedProg`, and `unusedAxisProg` unchanged; only
-- `conflictProg` (which fails for an unrelated reason — the pinned/actual-shape mismatch) notices.
-- The two fixtures below instead declare a bare `axis i : ℕ` (no `= n` — legal grammar per
-- `DSL/Syntax.lean`'s `tl_axis_decl_item : ident ":" tl_axis_kind`), so `i`'s size can ONLY come
-- from a read against the tensor's actual shape, through the exact adapter this slice re-plumbed.

private def bareAxisSizelessProg : TLProgram := tlprog!{
  axis i : ℕ
  Y[i] := X[i]
}

private def bareAxisSizelessInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩

run_cmd do
  match bareAxisSizelessProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"bare-axis sizeless case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched bareAxisSizelessInputs with
      | .error e => throwError s!"parity mismatch (bare-axis sizeless case): {e}"
      | .ok () => pure ()

-- Same idea routed through the affine constraint solver rather than the bare-axis fast path: `i`
-- is sizeless while `j` is pinned, and `X`'s read position `2 * i + j` resolves `i`'s size only by
-- combining the read's actual dimension with `j`'s already-known size.
private def affineSizelessProg : TLProgram := tlprog!{
  axis i : ℕ
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
}

private def affineSizelessInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X"
    ⟨[9], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]⟩

run_cmd do
  match affineSizelessProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"affine sizeless case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched affineSizelessInputs with
      | .error e => throwError s!"parity mismatch (affine sizeless case): {e}"
      | .ok () => pure ()

-- Category 3 — parity across a small hand-written corpus.
--
-- Route decision: `test/Eval/PropertyOracle/Gen.lean` was read first, per the brief. Its only
-- non-`private` declaration is `enumPrograms : List (TLProgram × HashMap String DenseTensor)` — a
-- single bulk enumerator (`one ++ two ++ yDepPrograms ++ contractPrograms ++
-- contractMultiTermPrograms`, up to 5000 entries per its own contract test). Every named,
-- individually-meaningful sub-list feeding it (`contractPrograms`, `yDepPrograms`,
-- `contractMultiTermPrograms`, `stmtChoices`, etc.) is `private` to `Gen.lean` and so is not
-- accessible from this file, and picking specific numeric indices out of `enumPrograms` itself
-- would mean relying on undocumented, cap-dependent positional offsets (`twoStmtCap`,
-- `cappedTwoStmt`) to guess which index is "the multi-factor one" or "the chained one" — brittle
-- and opaque, exactly the case the brief calls out as not easily sliceable. So this follows the
-- brief's fallback: two hand-written `tlprog!` fixtures, in the same explicit-axis style as
-- `parityProg`/`conflictProg` above, covering multiple factors in one term (a contraction, not
-- covered by category 2's single-factor affine read) and a chained two-statement program
-- (`chainedProg`, below — see its own comment for what it actually exercises at this layer).

private def multiFactorProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis j : ℕ = 3
  H[i] := A[i, j] · B[j]
}

private def multiFactorInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "A" ⟨[2, 3], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩).insert
    "B" ⟨[3], #[1.0, 1.0, 1.0]⟩

run_cmd do
  match multiFactorProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"corpus multi-factor case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched multiFactorInputs with
      | .error e => throwError s!"parity mismatch (corpus multi-factor case): {e}"
      | .ok () => pure ()

-- Nominal coverage only, at this layer: `i` is pinned (`= 4`), and the read of `Y` (an
-- intermediate, never present in `inputs`/the signature) contributes zero read positions on
-- either adapter's path — `shapeOf "Y"` returns `none` for both. So this exercises `parityCheck`
-- over a multi-statement schedule, not a chained producer/consumer's shape-driven inference; that
-- coverage is what `bareAxisSizelessProg`/`affineSizelessProg` above actually provide.
private def chainedProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  Y[i] := P[i]
  Z[i] := Y[i]
}

private def chainedInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "P" ⟨[4], #[10.0, 20.0, 30.0, 40.0]⟩

run_cmd do
  match chainedProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"corpus chained-program case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched chainedInputs with
      | .error e => throwError s!"parity mismatch (corpus chained-program case): {e}"
      | .ok () => pure ()

private def conflictProg : TLProgram := tlprog!{
  axis k : ℕ = 2
  Z[k] := W[k]
}

-- W's actual shape (5) conflicts with k's pinned size (2) from the `axis k : ℕ = 2` declaration.
private def conflictInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "W" ⟨[5], #[0.0, 0.0, 0.0, 0.0, 0.0]⟩

run_cmd do
  match conflictProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"conflict-case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched conflictInputs with
      | .error e => throwError s!"parity mismatch (pinned-size conflict case): {e}"
      | .ok () => pure ()
      -- Also confirm this case actually IS a conflict, not an accidentally-passing fixture:
      let allStmts := sched.stmts.flatMap (fun
        | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
      match inferAxisSizes sched.explicitSizes conflictInputs allStmts with
      | .ok _ => throwError "conflict-case fixture does not actually conflict — fix the fixture"
      | .error _ => pure ()

-- Category 4 — an extent known only through `explicitSizes`.

private def unusedAxisProg : TLProgram := tlprog!{
  axis i : ℕ = 2
  axis unused : ℕ = 5
  Y[i] := X[i]
}

private def unusedAxisInputs : HashMap String DenseTensor :=
  ({} : HashMap String DenseTensor).insert "X" ⟨[2], #[1.0, 2.0]⟩

-- `unused` is declared with a pinned size but never appears in any read — its size can only ever
-- come from `explicitSizes` (the seed), never from a signature entry. Confirm both adapters still
-- carry it through to their output `sizes` map unchanged.
run_cmd do
  match unusedAxisProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"unused-axis-case compile failed: {repr e}"
  | .ok sched _ =>
      match parityCheck sched unusedAxisInputs with
      | .error e => throwError s!"parity mismatch (explicitSizes-only extent case): {e}"
      | .ok () => pure ()
      -- `unused`'s UID is whatever the compiler assigned it; find it via `sched.explicitSizes`
      -- itself (the seed the fixture's own `axis unused : ℕ = 5` declaration produced) rather than
      -- hand-guessing a UID number.
      let unusedEntries := sched.explicitSizes.toList.filter (fun (_, sz) => sz == 5)
      match unusedEntries with
      | [(uid, _)] =>
          let sig := InputSignature.ofDenseInputs unusedAxisInputs
          match inferAxisSizesFromSignature sched.explicitSizes sig
              (sched.stmts.flatMap (fun
                | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])) with
          | .ok (sizes, _) =>
              unless sizes[uid]? == some 5 do
                throwError s!"unused axis's seeded size was not preserved: {repr (sizes[uid]?)}"
          | .error e => throwError s!"unused-axis-case eval failed: {e}"
      | _ => throwError s!"expected exactly one explicitSizes entry of size 5, got {unusedEntries.length}"

-- Category 6 — warnings retained when a later shape constraint fails.

private def warningsThenFailProg : TLProgram := tlprog!{
  axis i : ℕ = 4
  axis j : ℕ = 3
  Y[i, j] := X[2 * i + j]
  axis k : ℕ = 2
  Z[k] := W[k]
}

-- X undersized (shape [6], needs up to index 8) triggers a paddedAccess warning on Y's read;
-- W's shape (5) then conflicts with k's pinned size (2), throwing AFTER that warning was already
-- accumulated. Positions are collected from all statements up front, in declaration order, so
-- Y's warning is added to `warns` before Z's position is even reached in the per-position loop —
-- confirm it survives into the returned `EvalFailure.warnings`, via both adapters.
private def warningsThenFailInputs : HashMap String DenseTensor :=
  (({} : HashMap String DenseTensor).insert "X" ⟨[6], #[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]⟩).insert
    "W" ⟨[5], #[0.0, 0.0, 0.0, 0.0, 0.0]⟩

run_cmd do
  match warningsThenFailProg.compileToScheduled.run 0 with
  | .error e _ => throwError s!"warnings-then-fail-case compile failed: {repr e}"
  | .ok sched _ =>
      let allStmts := sched.stmts.flatMap (fun
        | .plain s => [s] | .scan _ _ b r _ => b ++ r | .scanPre _ _ _ => [])
      let sig := InputSignature.ofDenseInputs warningsThenFailInputs
      match inferAxisSizes sched.explicitSizes warningsThenFailInputs allStmts,
            inferAxisSizesFromSignature sched.explicitSizes sig allStmts with
      | .error e1, .error e2 =>
          unless !e1.warnings.isEmpty do
            throwError "expected the env-based path to retain the earlier padded-access warning"
          unless decide (e1.warnings = e2.warnings) do
            throwError s!"warning lists diverged between adapters: {e1.warnings} vs {e2.warnings}"
      | .ok _, _ => throwError "expected both adapters to fail on the pinned-size conflict"
      | _, .ok _ => throwError "expected both adapters to fail on the pinned-size conflict"

end LeanNCD.Eval.Plan.SignatureTest
