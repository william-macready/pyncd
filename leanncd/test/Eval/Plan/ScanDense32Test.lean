import Eval.Plan.ScanTest
import Eval.PropertyOracle.ScanUnroll
import LeanNCD.Eval.Plan.Adapter32

/-!
# Native binary32 scans (plan level, graph level, source level) — landed by F32-C — and an
# independent binary32 scan oracle (the S-B unrolling run through the CHECKED binary32 path).

Production test coverage for `papers/f32c_evalplan.md`; values below were observed against the built tree.
-/

namespace LeanNCD.Eval.Plan.ScanDense32Test
open LeanNCD LeanNCD.Eval LeanNCD.Eval.Plan Std
open LeanNCD.Eval.Plan.ScanTest (outerSigs outerSigsF32 linearScan linearScanF32 baseBlock stepBlock stepBlockF32)
open LeanNCD.PropertyOracle (unrollScanNode reconstructHistory Unrolled)

def causeTag : PlanCompileCause → String
  | .inputSignature e => s!"inputSignature {repr e}"
  | .capability e => s!"capability {repr e}"
  | .shape _ => "shape"
  | .scan e => s!"scan {repr e}"
  | .invalidPlan e => s!"invalidPlan {repr e}"
  | .bindings e => s!"bindings {repr e}"
  | .nonlin e => s!"nonlin {repr e}"
  | .sourceInvariant e => s!"sourceInvariant {repr e}"

def bits32 (r : Except PositionalInputError (Array DenseTensor32)) (slot : Nat) : Option (List UInt32) :=
  match r with
  | .ok st => some ((st.getD slot default).data.toList.map Float32.toBits)
  | .error _ => none
def bits64 (r : Except PositionalInputError (Array DenseTensor)) (slot : Nat) : Option (List UInt64) :=
  match r with
  | .ok st => some ((st.getD slot default).data.toList.map Float.toBits)
  | .error _ => none
def err32 (r : Except PositionalInputError (Array DenseTensor32)) : Option PositionalInputError :=
  match r with | .error e => some e | .ok _ => none
def err64 (r : Except PositionalInputError (Array DenseTensor)) : Option PositionalInputError :=
  match r with | .error e => some e | .ok _ => none

/-! ## Part A — plan level. Donor: `ScanTest.linearScan` / `ScanTest.linearScanF32` (f32 fixture 10).
`S[0] := S0`, `S[l+1] := S[l] + X[l]`, `S0 = 2^24`, `X = [1,1,1]`: binary32 absorbs every `+1`
(`2^24 + 1` rounds to even, `2^24`), binary64 does not. -/

def store32 : Array DenseTensor32 :=
  #[⟨[], #[16777216.0]⟩, ⟨[3], #[1.0, 1.0, 1.0]⟩, ⟨[3], #[0.0, 0.0, 0.0]⟩]
def store64 : Array DenseTensor :=
  #[⟨[], #[16777216.0]⟩, ⟨[3], #[1.0, 1.0, 1.0]⟩, ⟨[3], #[0.0, 0.0, 0.0]⟩]

def c32 : Option CheckedScanPlan := (checkScanPlanF32 outerSigsF32 linearScanF32).toOption
def c64 : Option CheckedScanPlan := (checkScanPlan outerSigs linearScan).toOption

-- A1: accepted, stamped `.float32`, native bits
#guard c32.map (·.storageKind) == some LeanNCD.StorageKind.float32
#guard (c32.bind fun c => bits32 (runDenseScan32 outerSigsF32 c store32) 2)
  == some [0x4B800000, 0x4B800000, 0x4B800000]
-- A2: binary64 contrast — the same plan in binary64 keeps every `+1`
#guard c64.map (·.storageKind) == some LeanNCD.StorageKind.float64
#guard (c64.bind fun c => bits64 (runDenseScan outerSigs c store64) 2)
  == some [0x4170000000000000, 0x4170000010000000, 0x4170000020000000]
-- A3: guard first at both scan doors (the last two also violate the signature tie and store arity,
-- so a guard placed after the tie would report `signatureContextMismatch` instead)
#guard (c32.bind fun c => err64 (runDenseScan outerSigsF32 c store64))
  == some (.storageKindMismatch .float64 .float32)
#guard (c64.bind fun c => err32 (runDenseScan32 outerSigs c store32))
  == some (.storageKindMismatch .float32 .float64)
#guard (c64.bind fun c => err32 (runDenseScan32 outerSigsF32 c #[]))
  == some (.storageKindMismatch .float32 .float64)
#guard (c32.bind fun c => err64 (runDenseScan outerSigs c #[]))
  == some (.storageKindMismatch .float64 .float32)
-- A4: the binary32 checker refuses binary64 evidence at the state and at a block
#guard (match checkScanPlanF32 outerSigs linearScan with | .error e => some e | .ok _ => none)
  == some (.stateDtypeNotAdmitted 0 2 .f64)
#guard (match checkScanPlanF32 outerSigsF32 { linearScanF32 with baseBlock := baseBlock } with
        | .error e => some e | .ok _ => none)
  == some (.baseBlockError (.storageKindNotAdmitted .float64))
-- A5: block level
def b32 : Option CheckedPlanBlock := (checkPlanBlockF32 stepBlockF32).toOption
def b64 : Option CheckedPlanBlock := (checkPlanBlock stepBlock).toOption
#guard b32.map (·.storageKind) == some LeanNCD.StorageKind.float32
#guard b64.map (·.storageKind) == some LeanNCD.StorageKind.float64
#guard (b32.bind fun b => err64 (runDenseBlock b [0] #[])) == some (.storageKindMismatch .float64 .float32)
#guard (b64.bind fun b => err32 (runDenseBlock32 b [0] #[])) == some (.storageKindMismatch .float32 .float64)
#guard (match checkPlanBlockF32 stepBlock with | .error e => some e | .ok _ => none)
  == some (.storageKindNotAdmitted .float64)
-- A6: an all-`bool` block constrains no carrier and is admitted under `.float32`
def boolOnlyBlock : RawPlanBlock :=
  { contextShape := #[], tensorSigs := #[{ shape := #[], dtype := .bool }]
  , inputs := #[0], steps := #[], outputs := #[0] }
#guard ((checkPlanBlockF32 boolOnlyBlock).toOption.map (·.storageKind)) == some LeanNCD.StorageKind.float32
#guard ((checkPlanBlock boolOnlyBlock).toOption.map (·.storageKind)) == some LeanNCD.StorageKind.float64

/-! ## Part B — graph level. Donor: `GraphCheckTest.f32ScanPlan` (same scan as `linearScanF32`). -/

def f32LinearPlan : RawEvalPlan :=
  { tensorSigs := outerSigsF32, inputSlots := #[0, 1], steps := #[.scan linearScanF32] }
def g32 : Option CheckedEvalPlan := (checkPlan f32LinearPlan).toOption
#guard g32.map (·.storageKind) == some LeanNCD.StorageKind.float32
#guard (g32.bind fun c => bits32 (runDensePlan32 c #[store32[0]!, store32[1]!]) 2)
  == some [0x4B800000, 0x4B800000, 0x4B800000]
#guard (g32.bind fun c => err64 (runDensePlan c #[store64[0]!, store64[1]!]))
  == some (.storageKindMismatch .float64 .float32)

/-! ## Part C — source level (`prepareEvalPlan` → `runPreparedDense32`).
Donors: C1/C2 `CompileTest.f32ScanProg`; C3 `ScanUnroll.contractionCase` (S-B) with f32 decls;
C4 new (predicate-only scan in an f32 program). -/

def lA : AxisSpec := ⟨"l", 1, .nat⟩
def jA : AxisSpec := ⟨"j", 2, .real⟩
def kA : AxisSpec := ⟨"k", 3, .real⟩
def oA : AxisSpec := ⟨"o", 4, .real⟩

/-- clone of `CompileTest.f32ScanProg`, with an optional recurrence nonlinearity. -/
def linProg (nl : Nonlin) : ScheduledProgram :=
  { decls := [ .iter lA 3, .typedTensor .f32 "S0" [], .typedTensor .f32 "X" [lA]
             , .typedTensor .f32 "S" [lA] ]
  , stmts := [.scan "S" [lA]
      [ .assign "S" [.iterAt lA 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := .identity } ]
      [ .assign "S" [.iterNext lA]
          { body := { terms := [ { factors := [.read "S" [.axis lA]] }
                               , { factors := [.read "X" [.axis lA]] } ] }
          , nonlin := nl } ]
      false ]
  , env := {}, extNames := insert "S0" (insert "X" (∅ : Finset String))
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

def linIn : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "S0" ⟨[], #[16777216.0]⟩).insert "X" ⟨[3], #[1.0, 1.0, 1.0]⟩

/-- clone of `ScanUnroll.contractionCase` (S-B), binary32 declarations. -/
def scatProg : ScheduledProgram :=
  let base : Stmt := .scatter "S" [.affine (.scale 2 jA), .iterAt lA 0]
    { body := { terms := [{ factors := [.read "X" [.axis jA, .axis kA], .read "W" [.axis kA]] }] },
      nonlin := .identity }
    { fill := 0, reduce := .rejectCollisions }
  let recur : Stmt := .assign "S" [.free oA, .iterNext lA]
    { body := { terms := [{ factors := [.read "S" [.axis oA, .axis lA]] }] }, nonlin := .identity }
  { decls := [.axis jA (some 3), .axis kA none, .axis oA (some 6), .iter lA 2,
              .typedTensor .f32 "X" [jA, kA], .typedTensor .f32 "W" [kA], .typedTensor .f32 "S" [oA, lA]]
  , stmts := [.scan "S" [lA] [base] [recur] false], env := {}
  , extNames := insert "X" (insert "W" ∅)
  , explicitSizes := ((({} : HashMap UID Nat).insert jA.uid 3).insert oA.uid 6).insert lA.uid 2 }

def scatIn : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "X" ⟨[3, 2], #[16777216.0, 1.0, 2.0, 20.0, 3.0, 30.0]⟩).insert
    "W" ⟨[2], #[1.0, 1.0]⟩

/-- a predicate-only scan inside an f32 program (block tables are bool-only). -/
def predProg : ScheduledProgram :=
  { decls := [ .iter lA 3, .predicate "P0" [], .predicate "P" [lA], .typedTensor .f32 "Y" []
             , .typedTensor .f32 "Z" [] ]
  , stmts := [ .plain (.assign "Z" [] { body := { terms := [{ factors := [.read "Y" []] }] }, nonlin := .identity })
             , .scan "P" [lA]
      [ .assign "P" [.iterAt lA 0] { body := { terms := [{ factors := [.read "P0" []] }] }, nonlin := .identity } ]
      [ .assign "P" [.iterNext lA] { body := { terms := [{ factors := [.read "P" [.axis lA]] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "P0" (insert "Y" ∅)
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }

def predIn : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "P0" ⟨[], #[1.0]⟩).insert "Y" ⟨[], #[3.0]⟩

def run32 (p : ScheduledProgram) (inputs : NamedDenseEnv32) (nm : String) : Except String (List UInt32) := do
  let sig ← (InputSignature.ofDenseInputs32ForDecls p.decls inputs).mapError (fun e => s!"sig {repr e}")
  let prepared ← match prepareEvalPlan p sig with
    | .ok x => pure x | .error f => throw s!"PREPARE REJECTED {causeTag f.cause}"
  match runPreparedDense32 prepared inputs with
  | .error e => throw s!"run {repr e.cause}"
  | .ok r => match r.env[nm]? with
    | some t => pure (t.data.toList.map Float32.toBits)
    | none => throw "missing"

/-- Independent oracle: unroll the one scan, declare every undeclared leaf `tensor f32`, run the
    scan-free program through the CHECKED binary32 path, reconstruct history (exact widening), and
    narrow back. -/
def oracle32 (p : ScheduledProgram) (inputs : NamedDenseEnv32) : Except String (String × List UInt32) := do
  match p.stmts with
  | [sc@(.scan _ _ base recur _)] =>
      let sizeStmts := (base ++ recur).map (fun
        | .scatter nm slots rhs _ => Stmt.assign nm slots rhs
        | s => s)
      let env64 : HashMap String DenseTensor :=
        inputs.fold (fun m k v => m.insert k ⟨v.shape, v.data.map Float32.toFloat⟩) {}
      let sizes ← match inferAxisSizes (declaredAxisSizes p.decls) env64 sizeStmts with
        | .ok (sizes, _) => pure sizes
        | .error e => throw s!"size inference failed: {e.error}"
      let un ← unrollScanNode sizes p.decls sc
      let leafSizes := un.sizes.foldl (fun m (u, n) => m.insert u n) sizes
      let declared : List String := un.decls.filterMap (fun | .predicate n _ => some n | _ => none)
      let st0 ← match un.geom.states with | st :: _ => pure st | [] => throw "no states"
      let stateFor (nm : String) := (un.geom.states.find? (fun st => (nm.splitOn ("_" ++ st.name ++ "_")).length > 1
        || nm == "%Z_" ++ st.name)).getD st0
      let axesOf : Stmt → List AxisSpec := fun
        | .assign _ slots _ => slots.filterMap (fun | .free a => some a | .freeNorm a => some a | _ => none)
        | .scatter nm .. => (stateFor nm).sliceAxes
        | _ => []
      let leafDecls := un.stmts.filterMap (fun s =>
        if declared.contains s.lhsName then none else some (Decl.typedTensor .f32 s.lhsName (axesOf s)))
      let leafStmts := un.stmts.map ScanStmt.plain
      let allDecls := p.decls ++ un.axisDecls ++ un.decls ++ leafDecls
      let ls : ScheduledProgram := { p with stmts := leafStmts, decls := allDecls, explicitSizes := leafSizes }
      let sig ← (InputSignature.ofDenseInputs32ForDecls ls.decls inputs).mapError (fun e => s!"sig {repr e}")
      let prepared ← match prepareEvalPlan ls sig with
        | .ok x => pure x | .error f => throw s!"leaf PREPARE REJECTED {causeTag f.cause}"
      let r ← match runPreparedDense32 prepared inputs with
        | .ok r => pure r | .error e => throw s!"leaf run {repr e.cause}"
      let leaf64 : HashMap String DenseTensor :=
        r.env.fold (fun m k v => m.insert k ⟨v.shape, v.data.map Float32.toFloat⟩) {}
      let st := st0
      let h ← reconstructHistory un st leaf64
      pure (st.name, h.data.toList.map (fun x => x.toFloat32.toBits))
  | _ => throw "one scan expected"


def reluIn : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "S0" ⟨[], #[16777216.0]⟩).insert "X" ⟨[3], #[1.0, -67108864.0, 1.0]⟩

#guard (run32 (linProg .identity) linIn "S").toOption == some [0x4B800000, 0x4B800000, 0x4B800000]
#guard (run32 scatProg scatIn "S").toOption ==
  some [0x4B800000, 0x4B800000, 0, 0, 0x41B00000, 0x41B00000, 0, 0, 0x42040000, 0x42040000, 0, 0]
#guard (run32 predProg predIn "P").toOption == some [0x3F800000, 0x3F800000, 0x3F800000]
-- C2: relu in the recurrence body (lane 2: identity `2^24 - 2^26 = -3·2^24`, relu `+0`)
#guard (run32 (linProg .identity) reluIn "S").toOption == some [0x4B800000, 0x4B800000, 0xCC400000]
#guard (run32 (linProg (.pointwise .relu)) reluIn "S").toOption == some [0x4B800000, 0x4B800000, 0]

/-! C5–C7 pin the four nonlinear result-slot dtypes `compileScan` now takes from the destination
(base/step × pointwise/axiswise). Donor: `ScanCompileTest.softmaxMarkerFirst` (C6, C7) and C1 (C5). -/
def linProgB (baseNl : Nonlin) : ScheduledProgram :=
  { linProg .identity with stmts := [.scan "S" [lA]
      [ .assign "S" [.iterAt lA 0]
          { body := { terms := [{ factors := [.read "S0" []] }] }, nonlin := baseNl } ]
      [ .assign "S" [.iterNext lA]
          { body := { terms := [ { factors := [.read "S" [.axis lA]] }
                               , { factors := [.read "X" [.axis lA]] } ] }
          , nonlin := .identity } ]
      false ] }
def negIn : NamedDenseEnv32 :=
  (({} : NamedDenseEnv32).insert "S0" ⟨[], #[-1.0]⟩).insert "X" ⟨[3], #[1.0, 1.0, 1.0]⟩

def softProg (baseNl stepNl : Nonlin) : ScheduledProgram :=
  { decls := [ .iter lA 3, .axis jA (some 2), .typedTensor .f32 "X" [jA], .typedTensor .f32 "S" [lA, jA] ]
  , stmts := [.scan "S" [lA]
      [ .assign "S" [.iterAt lA 0, (if baseNl == .identity then .free jA else .freeNorm jA)]
          { body := { terms := [{ factors := [.read "X" [.axis jA]] }] }, nonlin := baseNl } ]
      [ .assign "S" [.iterNext lA, (if stepNl == .identity then .free jA else .freeNorm jA)]
          { body := { terms := [{ factors := [.read "S" [.axis lA, .axis jA]] }] }, nonlin := stepNl } ]
      false ]
  , env := {}, extNames := insert "X" ∅
  , explicitSizes := ((({} : HashMap UID Nat).insert lA.uid 3).insert jA.uid 2) }
def softIn : NamedDenseEnv32 := ({} : NamedDenseEnv32).insert "X" ⟨[2], #[0.0, 1.0]⟩

-- C5: base relu (`S0 = -1`), against the identity base
#guard (run32 (linProgB (.pointwise .relu)) negIn "S").toOption == some [0, 0x3F800000, 0x40000000]
#guard (run32 (linProgB .identity) negIn "S").toOption == some [0xBF800000, 0, 0x3F800000]
-- C6: step softmax; C7: base softmax
#guard (run32 (softProg .identity (.axiswise .softmax none)) softIn "S").toOption ==
  some [0, 0x3F800000, 0x3E89B2B1, 0x3F3B26A8, 0x3EC5E131, 0x3F1D0F67]
#guard (run32 (softProg (.axiswise .softmax none) .identity) softIn "S").toOption ==
  some [0x3E89B2B1, 0x3F3B26A8, 0x3E89B2B1, 0x3F3B26A8, 0x3E89B2B1, 0x3F3B26A8]

/-! ## Part D — the independent oracle agrees bit for bit with the scan worker. -/
def agrees (p : ScheduledProgram) (inputs : NamedDenseEnv32) : Bool :=
  match run32 p inputs "S", oracle32 p inputs with
  | .ok a, .ok (_, b) => a == b
  | _, _ => false
#guard agrees (linProg .identity) linIn
#guard agrees (linProg (.pointwise .relu)) reluIn
#guard agrees scatProg scatIn

/-! ## Part E — a graph whose ONLY real tensor is scan-local scratch (F32-C final review, finding 1).
The outer table is predicate-only (`P0`, `P`); the one real tensor is the step block's scratch `T`,
which no outer signature names. `T := P[l]; P[l+1] := T` relays `P0 = 1` through scratch. Before
the fix, `checkPlan` took `deriveStorageKind`'s `.float64` DEFAULT for the bool-only outer table, ran
the binary64 scan checker, and its step block refused the f32 scratch (`storageKindNotAdmitted
.float32`) through `invalidPlan` — though Step 0b had already derived `.float32` for the schedule. -/
def scratchProg (tDecl : Decl) : ScheduledProgram :=
  { decls := [ .iter lA 3, .predicate "P0" [], .predicate "P" [lA], tDecl ]
  , stmts := [ .scan "P" [lA]
      [ .assign "P" [.iterAt lA 0] { body := { terms := [{ factors := [.read "P0" []] }] }, nonlin := .identity } ]
      [ .assign "T" [] { body := { terms := [{ factors := [.read "P" [.axis lA]] }] }, nonlin := .identity }
      , .assign "P" [.iterNext lA] { body := { terms := [{ factors := [.read "T" []] }] }, nonlin := .identity } ]
      false ]
  , env := {}, extNames := insert "P0" ∅
  , explicitSizes := (({} : HashMap UID Nat).insert lA.uid 3) }
def scratchIn : NamedDenseEnv32 := ({} : NamedDenseEnv32).insert "P0" ⟨[], #[1.0]⟩
def scratchIn64 : NamedDenseEnv := ({} : NamedDenseEnv).insert "P0" ⟨[], #[1.0]⟩
def scratchPrep32 : Option PreparedPlan :=
  let p := scratchProg (.typedTensor .f32 "T" [])
  (InputSignature.ofDenseInputs32ForDecls p.decls scratchIn).toOption.bind
    fun sig => (prepareEvalPlan p sig).toOption

-- E1: admitted as binary32, and runs natively to the relayed `1.0` at every history entry
#guard scratchPrep32.map (·.plan.storageKind) == some LeanNCD.StorageKind.float32
#guard (run32 (scratchProg (.typedTensor .f32 "T" [])) scratchIn "P").toOption
  == some [0x3F800000, 0x3F800000, 0x3F800000]
-- E2: the kind comes from the scratch's DECLARED dtype, not from "bool-only outer ⇒ binary32":
-- the same program with `tensor T` (f64) stays binary64
#guard (let p := scratchProg (.tensor "T" [])
        (InputSignature.ofDenseInputsForDecls p.decls scratchIn64).toOption.bind
          fun sig => (prepareEvalPlan p sig).toOption.map (·.plan.storageKind))
  == some LeanNCD.StorageKind.float64

/- E3: the fallback never admits real f32/f64 mixing (owned by F32-E, plan §1.2). Each control
edits E1's own compiled plan, so the edit is the only difference. -/
def scratchRaw : RawEvalPlan := (scratchPrep32.map (·.plan.raw)).getD default
def checkErr (r : RawEvalPlan) : Option PlanStepError :=
  match checkPlan r with | .error e => some e | .ok _ => none
def f64Sig : TensorSignature := { shape := #[], dtype := .f64 }
-- (a) f32 AND f64 slots directly visible in the outer table: `mixedStorageKinds`, as before
#guard checkErr { scratchRaw with
    tensorSigs := scratchRaw.tensorSigs ++ #[{ shape := #[], dtype := .f32 }, f64Sig]
  , inputSlots := scratchRaw.inputSlots ++ #[2, 3] }
  == some (.assign (.mixedStorageKinds 3 .f32 .f64))
-- (b) a real outer slot stays authoritative: one f64 outer input makes the graph binary64, and the
-- f32 scratch is refused by its own block's gate rather than overriding the outer table
#guard checkErr { scratchRaw with
    tensorSigs := scratchRaw.tensorSigs.push f64Sig, inputSlots := scratchRaw.inputSlots.push 2 }
  == some (.scan 0 (.stepBlockError (.storageKindNotAdmitted .float32)))
-- (c) bool-only outer table, blocks that disagree: the FIRST real block slot (an f64 base-block
-- input) sets the kind, and the f32 step block is refused
#guard checkErr { scratchRaw with steps := scratchRaw.steps.map fun
    | .scan s => .scan { s with baseBlock := { s.baseBlock with
        tensorSigs := s.baseBlock.tensorSigs.push f64Sig, inputs := s.baseBlock.inputs.push 2 } }
    | st => st }
  == some (.scan 0 (.stepBlockError (.storageKindNotAdmitted .float32)))
-- (d) at the source level, the same scratch beside an f64 outer tensor is a mixed schedule,
-- refused at Step 0b as a typed capability error (naming `T`, the first name disagreeing with `Y`)
#guard (let p0 := scratchProg (.typedTensor .f32 "T" [])
        let p : ScheduledProgram :=
          { p0 with decls := p0.decls ++ [.tensor "Y" [], .tensor "Z" []]
                  , stmts := .plain (.assign "Z" [] { body := { terms := [{ factors := [.read "Y" []] }] }
                                                    , nonlin := .identity }) :: p0.stmts
                  , extNames := insert "Y" p0.extNames }
        match (InputSignature.ofDenseInputsForDecls p.decls (scratchIn64.insert "Y" ⟨[], #[3.0]⟩)) with
        | .error _ => none
        | .ok sig => match prepareEvalPlan p sig with
          | .error f => some f.cause | .ok _ => none)
  == some (.capability (.unsupportedDtype "T: mixed f32/f64 storage in one schedule"))

end LeanNCD.Eval.Plan.ScanDense32Test
