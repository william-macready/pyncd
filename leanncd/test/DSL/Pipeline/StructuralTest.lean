-- test/DSL/Pipeline/StructuralTest.lean
import LeanNCD.DSL.Compile
namespace LeanNCD
-- matmul: Y[i,j] := W[i,k]·X[k,j].  After assignUIDs: no axis uid is 0, and the
-- two `k` occurrences share one uid while i,j,k are pairwise distinct.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }
  let p : TLProgram := { decls := [], stmts := [
    .assign "Y" [ .free (ax "i"), .free (ax "j") ]
      { body := { terms := [ { factors := [
            .read "W" [ .axis (ax "i"), .axis (ax "k") ],
            .read "X" [ .axis (ax "k"), .axis (ax "j") ] ] } ] },
        nonlin := .identity } ] }
  match assignUIDs p |>.run 0 with
  | .ok lp _ =>
      let uids := lp.stmts.flatMap Stmt.uids
      unless uids.all (· ≠ 0) do throwError s!"found zero UID: {uids}"
      -- i,j,k → exactly 3 distinct uids
      unless uids.eraseDups.length == 3 do throwError s!"expected 3 distinct axis uids, got {uids.eraseDups}"
  | .error e _ => throwError s!"assignUIDs errored: {repr e}"

-- matmul Y[i,j] := W[i,k]·X[k,j]: W,X are external inputs; Y is produced (not external).
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }
  let p : TLProgram := { decls := [], stmts := [
    .assign "Y" [ .free (ax "i"), .free (ax "j") ]
      { body := { terms := [ { factors := [
            .read "W" [ .axis (ax "i"), .axis (ax "k") ],
            .read "X" [ .axis (ax "k"), .axis (ax "j") ] ] } ] },
        nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .ok rp _ =>
      unless decide ("W" ∈ rp.extNames) && decide ("X" ∈ rp.extNames) do
        throwError "W,X should be external"
      unless ¬ decide ("Y" ∈ rp.extNames) do throwError "Y must not be external (it is produced)"
  | .error e _ => throwError s!"resolveDecls errored (only unsupportedElementType or duplicateTensorDecl is possible): {repr e}"

-- a `tensor` decl lands in env.
run_cmd do
  let p : TLProgram := { decls := [ .tensor "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .ok rp _ => unless rp.env.contains "A" do throwError "env missing declared A"
  | .error e _ => throwError s!"errored: {repr e}"

/-! ### f32 Task 1, fixture 4: `.typedTensor .f32` is an ordinary tensor-bearing declaration

The clone of "a `tensor` decl lands in env" above, with the declaration's only change being the
constructor. Three claims, matching the donor family: it lands in the `DeclEnv`; its axis list is
its RANK for read-arity purposes; and a second tensor-bearing declaration of the same name is a
`duplicateTensorDecl` exactly as for `.tensor`. -/

private def axF32 : AxisSpec := { name := "i", uid := 0, kind := .real }

-- lands in env
run_cmd do
  let p : TLProgram := { decls := [ .typedTensor .f32 "A" [axF32] ], stmts := [
    .assign "A" [.free axF32]
      { body := { terms := [{ factors := [.read "X" [.axis axF32]] }] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .ok rp _ => unless rp.env.contains "A" do throwError "env missing declared f32 A"
  | .error e _ => throwError s!"errored: {repr e}"

-- rank: the declaration's one axis is what a read of `A` must match. A rank classifier that
-- forgot `.typedTensor` (returning 0) would reject the correct rank-1 read below instead.
run_cmd do
  let p : TLProgram := { decls := [ .typedTensor .f32 "A" [axF32] ], stmts := [
    .assign "A" [.free axF32]
      { body := { terms := [{ factors := [.read "X" [.axis axF32]] }] }, nonlin := .identity },
    .assign "Z" [.free axF32]
      { body := { terms := [{ factors := [.read "A" [.axis axF32]] }] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls >>= checkReadRanks) |>.run 0 with
  | .ok _ _ => pure ()
  | .error e _ => throwError s!"rank-1 read of a rank-1 f32 declaration was rejected: {repr e}"

run_cmd do
  let p : TLProgram := { decls := [ .typedTensor .f32 "A" [axF32] ], stmts := [
    .assign "A" [.free axF32]
      { body := { terms := [{ factors := [.read "X" [.axis axF32]] }] }, nonlin := .identity },
    .assign "Z" [.free axF32]
      { body := { terms := [{ factors := [.read "A" [.axis axF32, .axis axF32]] }] }
      , nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls >>= checkReadRanks) |>.run 0 with
  | .error (.rankMismatch "A" 1 2) _ => pure ()
  | .error e _ => throwError s!"wrong error for an over-indexed f32 declaration: {repr e}"
  | .ok _ _    => throwError "expected rankMismatch for A[i,i] against `tensor f32 A(i)`"

-- duplicate-name behaviour, both same-kind and mixed against the untyped spelling
run_cmd do
  let p : TLProgram := { decls := [ .typedTensor .f32 "A" [], .typedTensor .f32 "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error (f32-then-f32): {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for a doubly-declared f32 tensor"

run_cmd do
  let p : TLProgram := { decls := [ .tensor "A" [], .typedTensor .f32 "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error (tensor-then-f32): {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for tensor-then-f32"

-- Task 4.1 fixture 1: a name declared `tensor` TWICE ⇒ duplicateTensorDecl (not last-wins).
run_cmd do
  let p : TLProgram := { decls := [ .tensor "A" [], .tensor "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error: {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for a doubly-declared tensor"

-- Task 4.1 fixture 2: the same for two `predicate` decls of one name.
run_cmd do
  let p : TLProgram := { decls := [ .predicate "A" [], .predicate "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error: {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for a doubly-declared predicate"

-- Task 4.1 fixture 3: MIXED kinds, both orders — this is the disagreement Boolean admission cannot
-- tolerate (a `DeclEnv` lookup would see the last decl, a linear `decls` scan the first).
run_cmd do
  let p : TLProgram := { decls := [ .tensor "A" [], .predicate "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error (tensor-then-predicate): {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for tensor-then-predicate"

run_cmd do
  let p : TLProgram := { decls := [ .predicate "A" [], .tensor "A" [] ], stmts := [
    .assign "A" [] { body := { terms := [] }, nonlin := .identity } ] }
  match (assignUIDs p >>= resolveDecls) |>.run 0 with
  | .error (.duplicateTensorDecl "A") _ => pure ()
  | .error e _ => throwError s!"wrong error (predicate-then-tensor): {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for predicate-then-tensor"

/-! ### f32 Task 1, fixture 5: the schedule-wide storage-kind classifier

The same declaration-environment donor shape as the fixtures above, pushed one layer further:
its declarations are built into a `DeclEnv` through the shared `buildDeclEnv` and handed to
`scheduleStorageKind` together with the schedule's statements. -/

private def axS : AxisSpec := { name := "i", uid := 7, kind := .real }

private def readsOf (names : List String) : RHSExpr :=
  { body := { terms := [{ factors := names.map (fun nm => .read nm [.axis axS]) }] }
  , nonlin := .identity }

/-- Classify one hand-built (decls, single-statement) schedule. Reports `buildDeclEnv`'s own
    failure as a distinct outcome so a malformed fixture can never read as a storage verdict. -/
private def storageOf (decls : List Decl) (dest : String) (reads : List String) :
    Except String (Except String StorageKind) :=
  match buildDeclEnv decls with
  | .error e => .error s!"buildDeclEnv rejected the fixture's decls: {repr e}"
  | .ok env  => .ok (scheduleStorageKind env [.plain (.assign dest [.free axS] (readsOf reads))])

-- (a) an f32-plus-predicate used graph selects `.float32`: the predicate is precision-neutral and
--     inherits the f32 the real names establish, rather than contributing an f64 constraint.
run_cmd do
  match storageOf [.typedTensor .f32 "Y" [axS], .typedTensor .f32 "X" [axS], .predicate "P" [axS]]
      "Y" ["X", "P"] with
  | .error m => throwError m
  | .ok (.ok .float32) => pure ()
  | .ok r => throwError s!"f32-plus-predicate graph: expected .ok .float32, got {repr r}"

-- (b) the same graph in the untyped spelling selects `.float32`: plain `tensor` is the binary32
--     default (the f32 default flip), so it agrees with the f32 spelling in (a).
run_cmd do
  match storageOf [.tensor "Y" [axS], .tensor "X" [axS], .predicate "P" [axS]] "Y" ["X", "P"] with
  | .error m => throwError m
  | .ok (.ok .float32) => pure ()
  | .ok r => throwError s!"untyped-plus-predicate graph: expected .ok .float32, got {repr r}"

-- (b') the same graph with the EXPLICIT binary64 spelling selects `.float64`.
run_cmd do
  match storageOf [.typedTensor .f64 "Y" [axS], .typedTensor .f64 "X" [axS], .predicate "P" [axS]]
      "Y" ["X", "P"] with
  | .error m => throwError m
  | .ok (.ok .float64) => pure ()
  | .ok r => throwError s!"f64-plus-predicate graph: expected .ok .float64, got {repr r}"

-- (c) a bool-only graph constrains nothing and defaults to `.float64`.
run_cmd do
  match storageOf [.predicate "Y" [axS], .predicate "X" [axS]] "Y" ["X"] with
  | .error m => throwError m
  | .ok (.ok .float64) => pure ()
  | .ok r => throwError s!"bool-only graph: expected the .float64 default, got {repr r}"

-- (d) three real names whose USED-name order is `A` (f32), then `B` (f64), then `C` (f64), reading
--     into an unrelated f32 destination `D`. The rejection must name `B` — the FIRST name that
--     disagrees with the f32 `A` established — not `C` (a second, later conflict against the same
--     `A`) and not `A` (which a DECLARATION-order scan would name, since the declarations below are
--     deliberately ordered `C`, `B`, `A`).
run_cmd do
  match storageOf
      [ .typedTensor .f64 "C" [axS], .typedTensor .f64 "B" [axS], .typedTensor .f32 "A" [axS]
      , .typedTensor .f32 "D" [axS] ]
      "D" ["A", "B", "C"] with
  | .error m => throwError m
  | .ok (.error "B") => pure ()
  | .ok r => throwError s!"three-real-name graph: expected .error \"B\", got {repr r}"

-- lowerArith
-- Upsample: Out[2*i, 2*j] := X[i,j] — affine LHS ⇒ reclassified to Stmt.scatter, injective (no error).
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 1, kind := .real }
  let upsample : Stmt := .assign "Out"
    [ .affine (.scale 2 (ax "i")), .affine (.scale 2 (ax "j")) ]
    { body := { terms := [ { factors := [ .read "X" [ .axis (ax "i"), .axis (ax "j") ] ] } ] },
      nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [upsample], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ =>
      match lp.stmts with
      | [ .scatter "Out" _ _ ] => pure ()
      | _ => throwError s!"expected one Stmt.scatter for Out, got {repr lp.stmts}"
  | .error e _ => throwError s!"lowerArith errored: {repr e}"

-- Plain matmul assign is left as Stmt.assign. (Distinct uids per axis, as `assignUIDs` produces —
-- i/j must NOT share a uid, else the LHS `Y[i,j]` looks like a diagonal `Y[i,i]` write.)
run_cmd do
  let ax (nm : String) : AxisSpec :=
    { name := nm, uid := (if nm == "i" then 1 else if nm == "j" then 2 else 3), kind := .real }
  let mm : Stmt := .assign "Y" [ .free (ax "i"), .free (ax "j") ]
    { body := { terms := [ { factors := [ .read "W" [.axis (ax "i"), .axis (ax "k")],
                                            .read "X" [.axis (ax "k"), .axis (ax "j")] ] } ] },
      nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [mm], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ => match lp.stmts with
                | [ .assign "Y" _ _ ] => pure ()
                | _ => throwError "matmul assign should remain Stmt.assign"
  | .error e _ => throwError s!"errored: {repr e}"

-- A constant LHS coord is no longer refused (D5: the `overlappingScatter` guard is gone): it is
-- reclassified to a `Stmt.scatter` whose slot is the unit-axis placement `0 + 1·u`, and the synthetic
-- axis `u` (its name is display only, nothing reads it) is declared pinned to size 1. (Was: `.error (.overlappingScatter "Z")`.)
run_cmd do
  let collapse : Stmt := .assign "Z" [ .affine (.const 0) ]
    { body := { terms := [ { factors := [ .read "X" [ .const 0 ] ] } ] }, nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [collapse], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ =>
      match lp.stmts, lp.decls with
      | [ .scatter "Z" [ .affine (.affine 0 [(1, u)]) ] _ ], [ .axis u' (some 1) ] =>
          unless u == u' do
            throwError s!"slot axis {repr u} is not the declared synthetic axis {repr u'}"
      | s, d => throwError s!"expected one unit-axis scatter + one pinned decl, got {repr s} / {repr d}"
  | .error e _ => throwError s!"constant LHS must lower, got {repr e}"

-- A non-constant affine slot next to an `iterAt` is NOT rewritten (only a CONSTANT slot is lowered, see
-- the next two pins): it stays as written, with no synthetic decl. Donor: the `.assign` fixture above
-- plus an iteration slot.
run_cmd do
  let l : AxisSpec := { name := "l", uid := 4, kind := .nat }
  let j : AxisSpec := { name := "j", uid := 5, kind := .nat }
  let st : Stmt := .assign "S" [ .iterAt l 0, .affine (.scale 2 j) ]
    { body := { terms := [ { factors := [ .read "X" [ .const 0 ] ] } ] }, nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [st], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ =>
      match lp.stmts, lp.decls with
      | [ .scatter "S" [ .iterAt _ 0, .affine (.scale 2 _) ] _ ], [] => pure ()
      | s, d => throwError s!"scan-slot statement must keep its slots, got {repr s} / {repr d}"
  | .error e _ => throwError s!"errored: {repr e}"

-- F3-b stage 1: a scan statement that carries a RAW constant slot is lowered like a top-level one. Donor:
-- the top-level `collapse` pin above plus an iteration slot. The slot becomes the unit-axis placement
-- `3 + 1·u` (`.affine 3 [(1, u)]`) and exactly one `.axis u (some 1)` is declared, with `u` the same axis
-- in slot and decl. (Was `.error (.overlappingScatter "S")`.)
run_cmd do
  let l : AxisSpec := { name := "l", uid := 4, kind := .nat }
  let st : Stmt := .assign "S" [ .iterAt l 0, .affine (.const 3) ]
    { body := { terms := [ { factors := [ .read "X" [ .const 0 ] ] } ] }, nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [st], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ =>
      match lp.stmts, lp.decls with
      | [ .scatter "S" [ .iterAt _ 0, .affine (.affine 3 [(1, u)]) ] _ ], [ .axis u' (some 1) ] =>
          unless u == u' do
            throwError s!"slot axis {repr u} is not the declared synthetic axis {repr u'}"
      | s, d => throwError s!"expected a scan scatter with a unit-axis placement + one pinned decl, got {repr s} / {repr d}"
  | .error e _ => throwError s!"scan statement with a constant slot must lower, got {repr e}"

-- The same for a HAND-BUILT `.scatter` (the `.scatter` arm of `lowerArith` calls `lowerConstSlots` too).
run_cmd do
  let l : AxisSpec := { name := "l", uid := 4, kind := .nat }
  let st : Stmt := .scatter "S" [ .iterAt l 0, .affine (.const 3) ]
    { body := { terms := [ { factors := [ .read "X" [ .const 0 ] ] } ] }, nonlin := .identity }
  let rp : ResolvedProgram :=
    { decls := [], stmts := [st], env := {}, extNames := ∅ }
  match lowerArith rp |>.run 0 with
  | .ok lp _ =>
      match lp.stmts, lp.decls with
      | [ .scatter "S" [ .iterAt _ 0, .affine (.affine 3 [(1, u)]) ] _ ], [ .axis u' (some 1) ] =>
          unless u == u' do
            throwError s!"slot axis {repr u} is not the declared synthetic axis {repr u'}"
      | s, d => throwError s!"hand-built scan scatter must lower its constant, got {repr s} / {repr d}"
  | .error e _ => throwError s!"errored: {repr e}"

-- The same through the whole pipeline (`compileToScheduled`), built from a surface scan program whose
-- base case has its free slot replaced by a constant (surface syntax cannot spell a raw constant slot:
-- a numeral is always `.iterAt`). The accept-neighbour is the unmodified program; both now compile.
private def scanSurface : TLProgram := tlprog!{ iter l = 3
  S[i, 0] := X[i]
  S[i, l + 1] := S[i, l] }

private def scanSurfaceConst : TLProgram :=
  { scanSurface with stmts := scanSurface.stmts.map fun
      | .assign nm [.free _, .iterAt a n] rhs => .assign nm [.affine (.const 3), .iterAt a n] rhs
      | s => s }

#guard match scanSurfaceConst.compileToScheduled.run 0 with
  | .ok _ _ => true
  | _ => false
#guard match scanSurface.compileToScheduled.run 0 with
  | .ok _ _ => true
  | _ => false

-- Coupled scan: G and H both recur over `l` (uid 9) ⇒ ONE ScanStmt.scan whose recur list
-- has BOTH G and H steps; each has a base case (no missingBaseCase).
run_cmd do
  let l : AxisSpec := { name := "l", uid := 9, kind := .nat }
  let j : AxisSpec := { name := "j", uid := 1, kind := .real }
  let rhs (nm : String) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm [ .axis j, .axis l ] ] } ] }, nonlin := .pointwise .relu }
  let gBase : Stmt := .assign "G" [ .free j, .iterAt l 0 ] { body := { terms := [] }, nonlin := .identity }
  let gRec  : Stmt := .assign "G" [ .free j, .iterNext l ] (rhs "G")
  let hBase : Stmt := .assign "H" [ .free j, .iterAt l 0 ] { body := { terms := [] }, nonlin := .identity }
  let hRec  : Stmt := .assign "H" [ .free j, .iterNext l ] (rhs "H")
  let lp : LoweredProgram := { decls := [], stmts := [gBase, gRec, hBase, hRec], env := {}, extNames := ∅ }
  match finalizeScans lp |>.run 0 with
  | .ok sp _ =>
      let scans := sp.stmts.filterMap (fun | .scan _ _ b r _ => some (b, r) | .plain _ => none | .scanPre _ _ _ => none)
      match scans with
      | [(base, recur)] =>
          unless recur.length == 2 do throwError s!"coupled scan recur should have 2 steps, got {recur.length}"
          unless base.length == 2 do throwError s!"coupled scan should have 2 base steps, got {base.length}"
      | _ => throwError s!"expected exactly one coupled ScanStmt.scan, got {scans.length}"
  | .error e _ => throwError s!"finalizeScans errored: {repr e}"

-- A recurrence with no matching base case ⇒ missingBaseCase.
run_cmd do
  let l : AxisSpec := { name := "l", uid := 9, kind := .nat }
  let orphan : Stmt := .assign "S" [ .iterNext l ]
    { body := { terms := [ { factors := [ .read "S" [ .axis l ] ] } ] }, nonlin := .identity }
  let lp : LoweredProgram := { decls := [], stmts := [orphan], env := {}, extNames := ∅ }
  match finalizeScans lp |>.run 0 with
  | .error (.missingBaseCase "S") _ => pure ()
  | .error e _ => throwError s!"wrong error: {repr e}"
  | .ok _ _ => throwError "expected missingBaseCase for orphan recurrence"

/-! ### Post-scan consumers

Classification is by ROLE, not by how a statement reads. A name is FED when a state's base or step
reads it, when it is a scan state's own name, or when a fed non-iteration statement reads it (closure
by name). A scan-dependent non-iteration statement whose name is fed is a per-step intermediate and
stays in the recurrence body; one whose name is not fed is post-scan: `finalizeScans` emits it as a
`.plain` node AFTER the scan nodes, and it may read states free or pinned (the scan axis is an ordinary
axis there). A post statement reading a per-step intermediate is `readsPerStepIntermediate`. The pins
are `layoutOf` renderings observed from a run. -/

private def finalizedOf (p : TLProgram) : FreshM ScanProgram :=
  (assignUIDs >=> resolveDecls >=> reclassifyIterSlots >=> checkReadRanks >=> checkDtypes >=>
    checkScatterNonlin >=> lowerArith >=> finalizeScans) p

/-- One token per outer node, in list order: `plain N`, or `scan base=[..] body=[..]` by LHS name. -/
private def renderLayout (sp : ScanProgram) : List String :=
  sp.stmts.map fun
    | .plain s => s!"plain {s.lhsName}"
    | .scan _ _ b r _ => s!"scan base={b.map Stmt.lhsName} body={r.map Stmt.lhsName}"
    | .scanPre nm _ _ => s!"pre {nm}"

private def layoutOf (p : TLProgram) : Except CompileError (List String) :=
  match (finalizedOf p).run 0 with
  | .ok sp _ => .ok (renderLayout sp)
  | .error e _ => .error e

private def postPin : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Zf[j]      := S[j, 2] }

private def postChain : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Inv[j]     := X[j]
  Zf[j]      := S[j, 2]
  Zf2[j]     := Zf[j] · Inv[j] }

private def postFreeRead : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Zr[j]      := S[j, l] }

private def postMixedFree : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Zm[j]      := S[j, 2] · S[j, l] }

private def postMixedInter : TLProgram := tlprog!{ iter l = 3
  H[j, 0]    := X[j]
  T[j]       := H[j, l]
  H[j, l +1] := T[j]
  M[j]       := H[j, 2] · T[j] }

private def postDemoted : TLProgram := tlprog!{ iter l = 3
  H[j, 0]    := X[j]
  Skip[j]    := H[j, 0]
  H[j, l +1] := Skip[j] }

private def postReadOut : TLProgram := tlprog!{ iter l = 3
  h[j, 0]    := h0[j]
  h[j, l +1] := A[j, k] · h[k, l]
  y[j, l]    := C[j, k] · h[k, l] }

-- The pinned read `Zf := S[j, 2]` is a post-scan consumer: a `.plain` node AFTER the scan, and the
-- scan body holds only the state recurrence.
#guard layoutOf postPin == .ok ["scan base=[S] body=[S]", "plain Zf"]
-- Chains of post statements stay post, in source order; a loop-invariant name (`Inv`, no scan
-- dependency) is read freely and stays a plain node BEFORE the scan.
#guard layoutOf postChain == .ok ["plain Inv", "scan base=[S] body=[S]", "plain Zf", "plain Zf2"]
-- Nothing feeds the recurrence from these, so they are post whatever the read pattern: a free read of
-- the state (`Zr`), a pinned and a free read mixed (`Zm`), and a read-out whose own LHS carries the scan
-- axis (`y`). A statement the recurrence itself reads (`Skip`) is fed and stays in the body.
#guard layoutOf postFreeRead == .ok ["scan base=[S] body=[S]", "plain Zr"]
#guard layoutOf postMixedFree == .ok ["scan base=[S] body=[S]", "plain Zm"]
#guard layoutOf postReadOut == .ok ["scan base=[h] body=[h]", "plain y"]
#guard layoutOf postDemoted == .ok ["scan base=[H] body=[Skip, H]"]
-- A post statement that reads a per-step intermediate (`T`, fed by the step, never published) is refused.
#guard layoutOf postMixedInter == .error (.readsPerStepIntermediate "M" "T")

-- Error precedence: the same program with no base case has two defects; the scan defect
-- (`missingBaseCase`) wins over `readsPerStepIntermediate`, which is checked after the component loop.
private def postMixedInterNoBase : TLProgram := tlprog!{ iter l = 3
  T[j]       := H[j, l]
  H[j, l +1] := T[j]
  M[j]       := T[j] }

#guard layoutOf postMixedInterNoBase == .error (.missingBaseCase "H")

-- Each conjunct of the `readsPerStepIntermediate` condition decided alone.
-- (b) `isScanDep r`: `W` is fed (the step reads it) but loop-invariant, so it stays a plain node and
-- the post statement `Z` reading it is accepted.
private def postReadsInvariantFed : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  W[j]       := X2[j]
  S[j, l +1] := S[j, l] · W[j]
  Z[j]       := S[j, 2] · W[j] }

#guard layoutOf postReadsInvariantFed == .ok ["plain W", "scan base=[S] body=[S]", "plain Z"]

-- (c) multi-hop closure: the chain is written in forward order, so backward discovery of `C`, `B`, `A`
-- as fed takes one pass per hop; all three land in the body.
private def postFedChain : TLProgram := tlprog!{ iter l = 3
  H[j, 0]    := X[j]
  C[j]       := H[j, l]
  B[j]       := C[j]
  A[j]       := B[j]
  H[j, l +1] := A[j] }

#guard layoutOf postFedChain == .ok ["scan base=[H] body=[C, B, A, H]"]

private def postIverScanAxis : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Zi[j]      := S[j, 2] · [l ≤ 1] }

private def postIverOtherAxis : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Zi[j]      := S[j, 2] · [j ≤ 1] }

private def postBaseRej : TLProgram := tlprog!{ iter l = 3
  G[j, 0]    := X[j]
  G[j, l +1] := G[j, l]
  Pc[j]      := G[j, 2]
  H[j, 0]    := Pc[j]
  H[j, l +1] := H[j, l] }

private def postBaseOk : TLProgram := tlprog!{ iter l = 3
  G[j, 0]    := X[j]
  G[j, l +1] := G[j, l]
  Pc[j]      := G[j, 2]
  H[j, 0]    := X[j]
  H[j, l +1] := H[j, l] }

private def postTwoRej : TLProgram := tlprog!{ iter l = 3
  iter m = 2
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Pc[j]      := S[j, 2]
  H[j, 0]    := X[j]
  H[j, m +1] := Pc[j] }

private def postTwoOk : TLProgram := tlprog!{ iter l = 3
  iter m = 2
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  Pc[j]      := S[j, 2]
  H[j, 0]    := X[j]
  H[j, m +1] := H[j, m] }

-- An Iverson predicate over the scan axis (`l`) does not matter: `Zi` feeds nothing, so it is post, as
-- with the predicate over an ordinary axis (`j`).
#guard layoutOf postIverScanAxis == .ok ["scan base=[S] body=[S]", "plain Zi"]
#guard layoutOf postIverOtherAxis == .ok ["scan base=[S] body=[S]", "plain Zi"]
-- Feeding by a BASE case: `H`'s base reads `Pc` (which only reads `G` pinned), so `Pc` is fed and sits
-- in the body; without that base read, `Pc` is post.
#guard layoutOf postBaseRej == .ok ["scan base=[G, H] body=[G, Pc, H]"]
#guard layoutOf postBaseOk == .ok ["scan base=[G, H] body=[G, H]", "plain Pc"]
-- Feeding across TWO scans: the recurrence of the `m`-scan reads `Pc`, which depends on the `l`-scan only,
-- so `Pc` is fed and sits in the `l`-scan body (the per-component case is parked); when the `m`-scan
-- does not read it, `Pc` is post.
#guard layoutOf postTwoRej == .ok ["scan base=[S] body=[S, Pc]", "scan base=[H] body=[H]"]
#guard layoutOf postTwoOk == .ok ["scan base=[S] body=[S]", "scan base=[H] body=[H]", "plain Pc"]

-- New fixtures. State-name rule decided ALONE: the step does not read its own state, yet a second
-- writer of `S` is per-step (so it is refused, not made post and failed later as `multiWriterScan`).
private def postStateNameNoSelfRead : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := X2[j]
  S[j, l]    := maxreduce(Y[j, l]) }

private def postStateNameSelfRead : TLProgram := tlprog!{ iter l = 3
  S[j, 0]    := X[j]
  S[j, l +1] := maxreduce(S[j, l] · A[j, k])
  S[j, l]    := maxreduce(Y[j, l]) }

-- Spanning applies to per-step statements only: a not-fed statement reading two scans' states is post.
private def postTwoStates : TLProgram := tlprog!{ iter l = 3
  iter m = 2
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  H[j, 0]    := X[j]
  H[j, m +1] := H[j, m]
  Z[j]       := S[j, 2] · H[j, 1] }

private def postTwoStatesFed : TLProgram := tlprog!{ iter l = 3
  iter m = 2
  S[j, 0]    := X[j]
  S[j, l +1] := S[j, l]
  H[j, 0]    := X[j]
  H[j, m +1] := Z[j]
  Z[j]       := S[j, 2] · H[j, 1] }

-- A free state read times an external `W[l]` is post when nothing feeds on it, per-step when the step does.
private def postFreeSumC : TLProgram := tlprog!{ iter l = 3
  H[j, 0]    := X[j]
  H[j, l +1] := H[j, l]
  Y[j]       := H[j, l] · W[l] }

private def postFreeSumCFed : TLProgram := tlprog!{ iter l = 3
  H[j, 0]    := X[j]
  Y[j]       := H[j, l] · W[l]
  H[j, l +1] := Y[j] }

#guard layoutOf postStateNameNoSelfRead == .error (.scanProjectionUnsupported "S")
#guard layoutOf postStateNameSelfRead == .error (.scanProjectionUnsupported "S")
-- Spanning is a per-step error only: the not-fed `Z` is post after both scans; once the `m`-step reads it,
-- it is per-step and spans two components (the per-component closure is parked).
#guard layoutOf postTwoStates == .ok ["scan base=[S] body=[S]", "scan base=[H] body=[H]", "plain Z"]
#guard layoutOf postTwoStatesFed ==
  .error (.shapeMismatch "Z: per-step intermediate spans multiple scan components" "a single scan component")
#guard layoutOf postFreeSumC == .ok ["scan base=[H] body=[H]", "plain Y"]
#guard layoutOf postFreeSumCFed == .ok ["scan base=[H] body=[Y, H]"]

private def lowered (nonIter : String) : LoweredProgram :=
  let l : AxisSpec := { name := "l", uid := 9, kind := .nat }
  let j : AxisSpec := { name := "j", uid := 1, kind := .real }
  let rd (nm : String) (ix : List IdxExpr) : RHSExpr :=
    { body := { terms := [ { factors := [ .read nm ix ] } ] }, nonlin := .identity }
  { decls := [], env := {}, extNames := ∅, stmts := [
      .assign "S" [ .free j, .iterAt l 0 ] (rd "X" [ .axis j ]),
      .assign "S" [ .free j, .iterNext l ] (rd "S" [ .axis j, .axis l ]),
      .assign nonIter [ .free j ] (rd "S" [ .axis j, .const 2 ]) ] }

private def layoutOfLowered (lp : LoweredProgram) : Except CompileError (List String) :=
  match (finalizeScans lp).run 0 with
  | .ok sp _ => .ok (renderLayout sp)
  | .error e _ => .error e

-- State-name rule: a non-iteration statement that WRITES a scan state's own name while reading it
-- pinned. This shape cannot come from `tlprog!` (`S[j] := S[j, 2]` is already a `rankMismatch` in an
-- earlier phase), so the pin is at the `finalizeScans` level on a hand-built `LoweredProgram`. The
-- statement stays in the body (second `S` below); under another name it is post.
#guard layoutOfLowered (lowered "S") == .ok ["scan base=[S] body=[S, S]"]
#guard layoutOfLowered (lowered "Zf") == .ok ["scan base=[S] body=[S]", "plain Zf"]
-- (a) `!stateNames.contains r`: a post statement `Z` reads `S`, which is both a scan state and has a
-- non-iteration writer. Reading a state is not reading a per-step intermediate, so it is accepted.
private def loweredStateReadByPost : LoweredProgram :=
  let j : AxisSpec := { name := "j", uid := 1, kind := .real }
  let lp := lowered "S"
  { lp with stmts := lp.stmts ++ [
      .assign "Z" [ .free j ]
        { body := { terms := [ { factors := [ .read "S" [ .axis j, .const 2 ] ] } ] }, nonlin := .identity } ] }

#guard layoutOfLowered loweredStateReadByPost == .ok ["scan base=[S] body=[S, S]", "plain Z"]
-- checkReadRanks: declared tensor read with matching rank passes through.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }
  let p : TLProgram := {
    decls := [.tensor "W" [ax "i", ax "k"]],
    stmts := [.assign "Y" [.free (ax "i")]
      { body := { terms := [{ factors := [
            .read "W" [.axis (ax "i"), .axis (ax "k")] ] }] },
        nonlin := .identity }] }
  match (assignUIDs p >>= resolveDecls >>= checkReadRanks) |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"should not error on correct rank: {repr e}"

-- checkReadRanks: declared tensor read with wrong rank ⇒ rankMismatch.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }
  let p : TLProgram := {
    decls := [.tensor "W" [ax "i", ax "k"]],   -- declared rank 2
    stmts := [.assign "Y" [.free (ax "i")]
      { body := { terms := [{ factors := [
            .read "W" [.axis (ax "i")] ] }] },  -- read rank 1
        nonlin := .identity }] }
  match (assignUIDs p >>= resolveDecls >>= checkReadRanks) |>.run 0 with
  | .error (.rankMismatch "W" 2 1) _ => pure ()
  | .error e _                       => throwError s!"wrong error: {repr e}"
  | .ok _ _                          => throwError "expected rankMismatch for wrong-rank read"

-- Declared destinations use their raw syntactic LHS rank, not the published rank of an
-- undeclared intermediate.
run_cmd do
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  let j : AxisSpec := { name := "j", uid := 2, kind := .real }
  let rp : ResolvedProgram :=
    { decls := [.tensor "Y" [i, j]]
    , env := ({} : DeclEnv).insert "Y" (.tensor "Y" [i, j])
    , extNames := ∅
    , stmts := [.assign "Y" [.free i] { body := { terms := [] }, nonlin := .identity }] }
  match checkReadRanks rp |>.run 0 with
  | .error (.rankMismatch "Y" 2 1) _ => pure ()
  | .error e _ => throwError s!"wrong declared destination under-rank error: {repr e}"
  | .ok _ _ => throwError "expected declared destination under-rank rejection"

run_cmd do
  let i : AxisSpec := { name := "i", uid := 1, kind := .real }
  let j : AxisSpec := { name := "j", uid := 2, kind := .real }
  let rp : ResolvedProgram :=
    { decls := [.tensor "Y" [i]]
    , env := ({} : DeclEnv).insert "Y" (.tensor "Y" [i])
    , extNames := ∅
    , stmts := [.assign "Y" [.free i, .free j] { body := { terms := [] }, nonlin := .identity }] }
  match checkReadRanks rp |>.run 0 with
  | .error (.rankMismatch "Y" 1 2) _ => pure ()
  | .error e _ => throwError s!"wrong declared destination over-rank error: {repr e}"
  | .ok _ _ => throwError "expected declared destination over-rank rejection"

-- Task 4.1 fixture 4: the SAME wrong-rank read, plus duplicate `W` declarations. `resolveDecls`
-- runs before `checkReadRanks`, so the duplicate declaration is reported and the (still present,
-- still wrong) read rank is never reached — the distinguishing fixture for that order.
run_cmd do
  let ax (nm : String) : AxisSpec := { name := nm, uid := 0, kind := .real }
  let p : TLProgram := {
    decls := [.tensor "W" [ax "i", ax "k"], .tensor "W" [ax "i", ax "k"]],   -- declared TWICE
    stmts := [.assign "Y" [.free (ax "i")]
      { body := { terms := [{ factors := [
            .read "W" [.axis (ax "i")] ] }] },  -- read rank 1, still wrong
        nonlin := .identity }] }
  match (assignUIDs p >>= resolveDecls >>= checkReadRanks) |>.run 0 with
  | .error (.duplicateTensorDecl "W") _ => pure ()
  | .error e _ => throwError s!"expected duplicateTensorDecl before rankMismatch, got: {repr e}"
  | .ok _ _    => throwError "expected duplicateTensorDecl for doubly-declared W"

-- checkReadRanks: external tensor with consistent read arity passes through.
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let readX n : Factor := .read "X" (List.replicate n (.axis ax))
  let mkStmt (nm : String) (n : Nat) : Stmt :=
    .assign nm [] { body := { terms := [{ factors := [readX n] }] }, nonlin := .identity }
  let rp : ResolvedProgram := {
    decls := [], env := {}, extNames := insert "X" ∅,
    stmts := [mkStmt "A" 2, mkStmt "B" 2] }
  match checkReadRanks rp |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"consistent external reads should not error: {repr e}"

-- checkReadRanks: external tensor with conflicting read arities ⇒ rankMismatch.
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let readX n : Factor := .read "X" (List.replicate n (.axis ax))
  let mkStmt (nm : String) (n : Nat) : Stmt :=
    .assign nm [] { body := { terms := [{ factors := [readX n] }] }, nonlin := .identity }
  let rp : ResolvedProgram := {
    decls := [], env := {}, extNames := insert "X" ∅,
    stmts := [mkStmt "A" 2, mkStmt "B" 1] }   -- first read rank 2, second rank 1
  match checkReadRanks rp |>.run 0 with
  | .error (.rankMismatch "X" 2 1) _ => pure ()
  | .error e _                       => throwError s!"wrong error: {repr e}"
  | .ok _ _                          => throwError "expected rankMismatch for inconsistent external reads"

-- checkReadRanks: over-indexed read of a produced-but-undeclared intermediate ⇒ rankMismatch
-- (Track A #1 guard: T produced rank 1, read at arity 2, no declaration to justify the higher rank).
run_cmd do
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  let k : AxisSpec := { name := "k", uid := 1, kind := .real }
  let rp : ResolvedProgram := {
    decls := [], env := {}, extNames := insert "A" ∅,
    stmts := [
      .assign "T" [.free i]
        { body := { terms := [{ factors := [.read "A" [.axis i]] }] }, nonlin := .identity },
      .assign "Y" [.free i, .free k]
        { body := { terms := [{ factors := [.read "T" [.axis i, .axis k]] }] }, nonlin := .identity } ] }
  match checkReadRanks rp |>.run 0 with
  | .error (.rankMismatch "T" 1 2) _ => pure ()
  | .error e _                       => throwError s!"wrong error: {repr e}"
  | .ok _ _                          => throwError "expected rankMismatch for over-indexed intermediate read"

-- checkReadRanks: reading the produced intermediate at its produced rank passes.
run_cmd do
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  let rp : ResolvedProgram := {
    decls := [], env := {}, extNames := insert "A" ∅,
    stmts := [
      .assign "T" [.free i]
        { body := { terms := [{ factors := [.read "A" [.axis i]] }] }, nonlin := .identity },
      .assign "Y" [.free i]
        { body := { terms := [{ factors := [.read "T" [.axis i]] }] }, nonlin := .identity } ] }
  match checkReadRanks rp |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"correct-arity intermediate read should pass: {repr e}"

-- checkReadRanks: reading an affine-LHS (→ scatter) producer at its SLOT rank passes the guard —
-- the produced rank of an affine LHS is its slot count (e.g. Out[2*i,2*i] ⇒ 2), not its free-axis
-- count (0). Regression for the guard's scatter-rank handling.
run_cmd do
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  let a : AxisSpec := { name := "a", uid := 2, kind := .real }
  let b : AxisSpec := { name := "b", uid := 3, kind := .real }
  let rp : ResolvedProgram := {
    decls := [], env := {}, extNames := insert "X" ∅,
    stmts := [
      .assign "Out" [.affine (.scale 2 i), .affine (.scale 2 i)]
        { body := { terms := [{ factors := [.read "X" [.axis i]] }] }, nonlin := .identity },
      .assign "Z" [.free a, .free b]
        { body := { terms := [{ factors := [.read "Out" [.axis a, .axis b]] }] }, nonlin := .identity } ] }
  match checkReadRanks rp |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"reading affine-scatter output at slot rank should pass: {repr e}"

-- checkDtypes: real-kinded axis in iterAt slot ⇒ iterAxisNotNat.
run_cmd do
  let l : AxisSpec := { name := "l", uid := 1, kind := .real }  -- ← real, not nat
  let s : Stmt := .assign "H" [.iterAt l 0]
    { body := { terms := [] }, nonlin := .identity }
  let rp : ResolvedProgram := { decls := [], env := {}, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .error (.iterAxisNotNat "l") _ => pure ()
  | .error e _                     => throwError s!"wrong error: {repr e}"
  | .ok _ _                        => throwError "expected iterAxisNotNat for real-kinded iterAt axis"

-- checkDtypes: nat-kinded axis in iterAt slot passes through.
run_cmd do
  let l : AxisSpec := { name := "l", uid := 1, kind := .nat }
  let s : Stmt := .assign "H" [.iterAt l 0]
    { body := { terms := [] }, nonlin := .identity }
  let rp : ResolvedProgram := { decls := [], env := {}, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"nat iterAt should not error: {repr e}"

-- checkDtypes: nat-kinded axis in freeNorm slot ⇒ normAxisNotReal.
run_cmd do
  let m : AxisSpec := { name := "m", uid := 2, kind := .nat }  -- ← nat, not real
  let s : Stmt := .assign "S" [.freeNorm m]
    { body := { terms := [] }, nonlin := .axiswise .softmax none }
  let rp : ResolvedProgram := { decls := [], env := {}, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .error (.normAxisNotReal "m") _ => pure ()
  | .error e _                      => throwError s!"wrong error: {repr e}"
  | .ok _ _                         => throwError "expected normAxisNotReal for nat-kinded freeNorm axis"

-- checkDtypes: predicate tensor with non-identity nonlin ⇒ predicateNonlin.
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let s : Stmt := .assign "P" [.free ax]
    { body := { terms := [] }, nonlin := .pointwise .relu }  -- ← relu on a predicate
  let env : DeclEnv := ({} : Std.HashMap String Decl).insert "P" (.predicate "P" [ax])
  let rp : ResolvedProgram := { decls := [], env, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .error (.predicateNonlin "P") _ => pure ()
  | .error e _                      => throwError s!"wrong error: {repr e}"
  | .ok _ _                         => throwError "expected predicateNonlin for relu on predicate output"

-- checkDtypes: predicate tensor with identity nonlin passes through.
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let s : Stmt := .assign "P" [.free ax]
    { body := { terms := [] }, nonlin := .identity }
  let env : DeclEnv := ({} : Std.HashMap String Decl).insert "P" (.predicate "P" [ax])
  let rp : ResolvedProgram := { decls := [], env, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .ok _ _    => pure ()
  | .error e _ => throwError s!"predicate with identity should not error: {repr e}"

-- Task 4.1 fixture 6: MaxReduceTest's predicate max-aggregation rejection, made pointwise as well.
-- Both invariants are violated; nonlinearity is checked FIRST, so `predicateNonlin` is the reported
-- diagnostic — the distinguishing fixture for that order (shared by `checkDtypes` and
-- `prepareEvalPlan`'s direct-schedule check through `checkPredicateOutput`).
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let s : Stmt := .assign "P" [.free ax]
    { body := { terms := [] }, nonlin := .pointwise .relu, agg := .max }
  let env : DeclEnv := ({} : Std.HashMap String Decl).insert "P" (.predicate "P" [ax])
  let rp : ResolvedProgram := { decls := [], env, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .error (.predicateNonlin "P") _ => pure ()
  | .error e _ => throwError s!"expected predicateNonlin before predicateAgg, got: {repr e}"
  | .ok _ _    => throwError "expected predicateNonlin for a pointwise max-agg predicate output"

-- S3b T4: `checkDtypes` (the SOURCE pipeline) carries the same per-statement tropical rule as
-- `checkScheduledDtypes`. Donor: fixture 6 above (programmatic statement, hand-built `DeclEnv`).
-- A max/min-annotated statement with a non-identity nonlinearity is `tropicalNonlin`.
private def tropicalStmtResult (nm : String) (nl : Nonlin) (ag : AggOp) (pred : Bool := false) :
    Except CompileError Unit :=
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let s : Stmt := .assign nm [.free ax]
    { body := { terms := [{ factors := [.read "X" [.axis ax]] }] }, nonlin := nl, agg := ag }
  let env : DeclEnv :=
    if pred then ({} : Std.HashMap String Decl).insert nm (.predicate nm [ax]) else {}
  let rp : ResolvedProgram := { decls := [], env, extNames := ∅, stmts := [s] }
  match checkDtypes rp |>.run 0 with
  | .ok _ _    => .ok ()
  | .error e _ => .error e

#guard tropicalStmtResult "M" (.pointwise .relu) .max == .error (.tropicalNonlin "M")
#guard tropicalStmtResult "M" (.pointwise .relu) .min == .error (.tropicalNonlin "M")
#guard tropicalStmtResult "M" (.axiswise .softmax none) .max == .error (.tropicalNonlin "M")
-- neighbours: the same nonlinearity on a `sum`, and `max`/`min` with identity, are accepted
#guard tropicalStmtResult "M" (.pointwise .relu) .sum == .ok ()
#guard tropicalStmtResult "M" .identity .max == .ok ()
#guard tropicalStmtResult "M" .identity .min == .ok ()
-- a predicate destination is `bool`, not tropical: relu + max reports the predicate rule, which runs
-- first (`predicateNonlin`, then `predicateAgg`), never `tropicalNonlin`
#guard tropicalStmtResult "P" (.pointwise .relu) .max (pred := true) == .error (.predicateNonlin "P")
#guard tropicalStmtResult "P" .identity .max (pred := true) == .error (.predicateAgg "P")

-- The `TLProgram.compile` path reaches the same rule (a programmatic statement: `relu(maxreduce ..)`
-- has no surface form).
run_cmd do
  let ax : AxisSpec := { name := "i", uid := 1, kind := .real }
  let p : TLProgram :=
    { decls := [.tensor "M" [ax]]
    , stmts := [.assign "M" [.free ax]
        { body := { terms := [{ factors := [.read "X" [.axis ax]] }] }
        , nonlin := .pointwise .relu, agg := .max }] }
  match p.compile |>.run 0 with
  | .error (.tropicalNonlin "M") _ => pure ()
  | .error e _ => throwError s!"compile: wrong error: {repr e}"
  | .ok _ _    => throwError "compile: expected tropicalNonlin, compile succeeded"

private def baseScatterScan : TLProgram := tlprog!{
  iter l = 3
  S[2 * i, 0] := X[i]
  S[i, l + 1] := S[i, l]
}

private def recurScatterScan : TLProgram := tlprog!{
  iter l = 3
  S[i, 0] := X[i]
  S[2 * i, l + 1] := S[i, l]
}

-- Compatibility only: the former guard's diagnostic remains a constructible serialized value.
#guard (CompileError.scatterInScan "retained") == .scatterInScan "retained"

-- The source-shaped affine assignment reaches `lowerArith`, becomes `.scatter`, and survives
-- `finalizeScans` in the base list.
#guard match baseScatterScan.compileToScheduled.run 0 with
  | .ok { stmts := [.scan _ _ [.scatter ..] [.assign ..] _], .. } _ => true
  | _ => false

-- The same reachability is pinned independently for the recurrence list.
#guard match recurScatterScan.compileToScheduled.run 0 with
  | .ok { stmts := [.scan _ _ [.assign ..] [.scatter ..] _], .. } _ => true
  | _ => false

end LeanNCD
