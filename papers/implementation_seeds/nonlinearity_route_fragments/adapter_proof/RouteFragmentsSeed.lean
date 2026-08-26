import LeanNCD.Bridge.Agreement

/-!
# Task 1 route-fragment adapter seed

This durable seed models the planned logical-schedule → checked physical-route boundary without
changing production.  Production must transplant declarations from this file; it must not import it.
-/

namespace LeanNCD.NonlinearityRouteFragmentsSeed

open Std

/-- Tensor names visible in a declaration. Axis declarations are deliberately excluded. -/
def declaredTensorName? : Decl → Option String
  | .tensor nm _ | .predicate nm _ | .linear nm _ _ => some nm
  | .axis _ _ | .iter _ _ => none

/-- Complete route-name inventory: declarations, writes, and tensor reads (including unary reads). -/
def routeNameInventory (sp : ScheduledProgram) : List String :=
  (sp.decls.filterMap declaredTensorName? ++
    sp.stmts.flatMap (fun sc => sc.writes ++ sc.reads)).eraseDups

def maxSourceNameLength : List String → Nat
  | [] => 0
  | nm :: names => max nm.length (maxSourceNameLength names)

/-- The executable collision-free name definition used by physicalization. -/
def routeName (names : List String) (ordinal : Nat) : String :=
  String.ofList (List.replicate (maxSourceNameLength names + ordinal + 1) '#')

@[simp] theorem routeName_length (names : List String) (ordinal : Nat) :
    (routeName names ordinal).length = maxSourceNameLength names + ordinal + 1 := by
  simp [routeName, String.length]

theorem length_le_maxSourceNameLength {nm : String} {names : List String}
    (h : nm ∈ names) : nm.length ≤ maxSourceNameLength names := by
  induction names generalizing nm with
  | nil => simp at h
  | cons hd tl ih =>
      rw [List.mem_cons] at h
      cases h with
      | inl heq =>
          subst nm
          exact Nat.le_max_left _ _
      | inr hmem =>
          exact le_trans (ih hmem) (Nat.le_max_right _ _)

theorem routeName_longer {nm : String} {names : List String} (h : nm ∈ names)
    (ordinal : Nat) : nm.length < (routeName names ordinal).length := by
  have hle := length_le_maxSourceNameLength h
  rw [routeName_length]
  omega

theorem routeName_not_mem (names : List String) (ordinal : Nat) :
    routeName names ordinal ∉ names := by
  intro h
  have := routeName_longer h ordinal
  omega

theorem routeName_injective (names : List String) :
    Function.Injective (routeName names) := by
  intro a b h
  have hl := congrArg String.length h
  simp only [routeName_length] at hl
  omega

structure RouteFragment where
  logicalIndex : Nat
  firstStep : Nat
  lastStep : Nat
  internalName : Option String
  deriving DecidableEq, Repr

structure PhysicalizeAcc where
  stmts : List ScanStmt
  fragments : List RouteFragment

/-- Degrade the axiswise marker only on the private producer. -/
def producerSlots (slots : List LHSSlot) : List LHSSlot :=
  slots.map fun
    | .freeNorm a => .free a
    | slot => slot

/-- Physicalize one top-level logical node. Scans and `scanPre` are opaque one-step fragments. -/
def physicalizeOne (sourceNames : List String) (logicalIndex firstStep : Nat)
    (sc : ScanStmt) : List ScanStmt × RouteFragment :=
  match sc with
  | .plain (.assign nm slots rhs) =>
      match rhs.nonlin with
      | .identity =>
          ([sc], ⟨logicalIndex, firstStep, firstStep, none⟩)
      | nonlin =>
          let internal := routeName sourceNames logicalIndex
          let producer : Stmt := .assign internal (producerSlots slots)
            { body := rhs.body, nonlin := .identity, agg := rhs.agg }
          let consumer : Stmt := .assign nm slots
            { body := { terms := [{ factors :=
                [.read internal (slots.filterMap LHSSlot.toReadIdx)] }] },
              nonlin := nonlin, agg := .sum }
          ([.plain producer, .plain consumer],
            ⟨logicalIndex, firstStep, firstStep + 1, some internal⟩)
  | _ => ([sc], ⟨logicalIndex, firstStep, firstStep, none⟩)

/-- One fold step, named separately so the coverage proof can reuse its exact executable body. -/
def physicalizeStep (sourceNames : List String) (acc : PhysicalizeAcc)
    (pair : ScanStmt × Nat) : PhysicalizeAcc :=
  let (emitted, fragment) := physicalizeOne sourceNames pair.2 acc.stmts.length pair.1
  { stmts := acc.stmts ++ emitted, fragments := acc.fragments ++ [fragment] }

/-- One left-to-right pass. It does not call `schedule`. -/
def physicalizeRaw (sp : ScheduledProgram) : PhysicalizeAcc :=
  let sourceNames := routeNameInventory sp
  sp.stmts.zipIdx.foldl (physicalizeStep sourceNames)
    { stmts := [], fragments := [] }

private theorem physicalizeFold_fragmentCount (sourceNames : List String)
    (pairs : List (ScanStmt × Nat)) (acc : PhysicalizeAcc) :
    (pairs.foldl (physicalizeStep sourceNames) acc).fragments.length =
      acc.fragments.length + pairs.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons pair tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [physicalizeStep, Nat.add_assoc]

theorem physicalizeRaw_fragmentCount (sp : ScheduledProgram) :
    (physicalizeRaw sp).fragments.length = sp.stmts.length := by
  unfold physicalizeRaw
  rw [physicalizeFold_fragmentCount]
  simp

def generatedRouteNames (fragments : List RouteFragment) : List String :=
  fragments.filterMap (·.internalName)

def routeNamesFresh (sourceNames : List String) (fragments : List RouteFragment) : Bool :=
  let generated := generatedRouteNames fragments
  generated.all (fun nm => !sourceNames.contains nm) &&
    generated.eraseDups.length == generated.length

/-- One or two physical steps exactly, contiguous from the previous fragment's exit. -/
def fragmentWidth : ScanStmt → Nat
  | .plain (.assign _ _ rhs) => if rhs.nonlin == .identity then 1 else 2
  | _ => 1

def checkFragmentAt (state : Bool × Nat)
    (entry : (ScanStmt × RouteFragment) × Nat) : Bool × Nat :=
  let (ok, cursor) := state
  let ((logical, fragment), index) := entry
  let width := fragmentWidth logical
  let internalShapeOk :=
    if width == 2 then fragment.internalName.isSome else fragment.internalName.isNone
  (ok && fragment.logicalIndex == index && fragment.firstStep == cursor &&
    fragment.lastStep + 1 == cursor + width && internalShapeOk, cursor + width)

def fragmentLayoutOk (logical physical : List ScanStmt)
    (fragments : List RouteFragment) : Bool :=
  if logical.length != fragments.length then false
  else
    let result := (logical.zip fragments).zipIdx.foldl checkFragmentAt (true, 0)
    result.1 && result.2 == physical.length

/-- Every fragment exits at the logical output; nonlinear entries publish only their private name. -/
def fragmentExitsOk (logical physical : List ScanStmt)
    (fragments : List RouteFragment) : Bool :=
  (logical.zip fragments).all fun (logicalStmt, fragment) =>
    let exitOk := (physical.getD fragment.lastStep default).outputs == logicalStmt.outputs
    match fragment.internalName with
    | none => exitOk
    | some internal =>
        (physical.getD fragment.firstStep default).outputs == [internal] && exitOk

/-- Checked, proof-carrying package. Its evidence cannot be discarded by a successful constructor. -/
structure PhysicalRouteProgram where
  logical : ScheduledProgram
  scheduled : ScheduledProgram
  fragments : List RouteFragment
  sourceNames : List String
  sourceInventory : sourceNames = routeNameInventory logical
  exactPhysicalization :
    let raw := physicalizeRaw logical
    scheduled.stmts = raw.stmts ∧ fragments = raw.fragments
  declarationsPreserved : scheduled.decls = logical.decls
  environmentPreserved : scheduled.env = logical.env
  externalsPreserved : scheduled.extNames = logical.extNames
  explicitSizesPreserved : scheduled.explicitSizes = logical.explicitSizes
  fragmentCount : fragments.length = logical.stmts.length
  layoutChecked : fragmentLayoutOk logical.stmts scheduled.stmts fragments = true
  exitsChecked : fragmentExitsOk logical.stmts scheduled.stmts fragments = true
  freshNames : routeNamesFresh sourceNames fragments = true
  topological : routableInOrder scheduled.stmts = true

/-- The only seed constructor for `PhysicalRouteProgram`: build exactly, then check freshness/topology. -/
def physicalizeForRoute (logical : ScheduledProgram) :
    Except CompileError PhysicalRouteProgram := do
  let raw := physicalizeRaw logical
  let sourceNames := routeNameInventory logical
  let scheduled : ScheduledProgram :=
    { logical with stmts := raw.stmts }
  if hLayout : fragmentLayoutOk logical.stmts scheduled.stmts raw.fragments then
    if hExits : fragmentExitsOk logical.stmts scheduled.stmts raw.fragments then
      if hFresh : routeNamesFresh sourceNames raw.fragments then
        if hTopo : routableInOrder scheduled.stmts then
          return {
            logical, scheduled, fragments := raw.fragments, sourceNames
            sourceInventory := rfl
            exactPhysicalization := ⟨rfl, rfl⟩
            declarationsPreserved := rfl
            environmentPreserved := rfl
            externalsPreserved := rfl
            explicitSizesPreserved := rfl
            fragmentCount := physicalizeRaw_fragmentCount logical
            layoutChecked := hLayout
            exitsChecked := hExits
            freshNames := hFresh
            topological := hTopo
          }
        else
          throw (.cyclicDataflow "physicalizeForRoute: physical fragment topology failed")
      else
        throw (.shapeMismatch "physicalizeForRoute: private route-name freshness failed"
          "fresh pairwise-distinct route names")
    else
      throw (.shapeMismatch "physicalizeForRoute: fragment exit check failed"
        "logical output at every fragment exit")
  else
    throw (.shapeMismatch "physicalizeForRoute: fragment layout check failed"
      "contiguous nonempty physical partition")

/-- Compatibility adapter: current `schedule` accepts `LinearProgram`; the planned production change
will make it accept this logical post-`finalizeScans` shape directly. -/
def scheduleLogical (sp : ScanProgram) : FreshM ScheduledProgram :=
  schedule { decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }

/-- Planned logical public boundary: notably, no `splitNonlins`. -/
def compileToScheduled (p : TLProgram) : FreshM ScheduledProgram :=
  assignUIDs p >>= resolveDecls >>= reclassifyIterSlots >>= checkReadRanks >>= checkDtypes >>=
    checkScatterNonlin >>= checkScatterNoScan >>= lowerArith >>= finalizeScans >>= scheduleLogical

/-- Public-logical-route-shaped wrapper: checked physicalization followed by unchanged `routeCore`. -/
def route (logical : ScheduledProgram) : FreshM ThreadedComposed := do
  match physicalizeForRoute logical with
  | .error e => throw e
  | .ok physical =>
      let nExternal := physical.scheduled.extNames.card
      match routeCore physical.scheduled with
      | .ok (steps, routing) =>
          let tc : ThreadedComposed := { steps, routing, nExternal }
          if tc.wellFormedDom then return tc
          else throw (.shapeMismatch
            "route: wellFormedDom failed (unreferenced external slot or read-rank mismatch)"
            "wellFormedDom")
      | .error e => throw e

/-- Production-shaped source wrapper with one logical scheduling pass. -/
def compile (p : TLProgram) : FreshM ThreadedComposed :=
  compileToScheduled p >>= route

/-- Agreement donor: successful source compilation exposes the logical schedule, checked physical
package, and the three facts consumed by the existing `WellFormed` proof. -/
theorem compile_eq_physical_route {p : TLProgram} {s : Nat} {tc : ThreadedComposed} {s' : Nat}
    (h : (compile p).run s = .ok tc s') :
    ∃ (logical : ScheduledProgram) (s₁ : Nat) (physical : PhysicalRouteProgram),
      (compileToScheduled p).run s = .ok logical s₁ ∧
      physicalizeForRoute logical = .ok physical ∧
      routeCore physical.scheduled = .ok (tc.steps, tc.routing) ∧
      tc.nExternal = physical.scheduled.extNames.card ∧
      tc.wellFormedDom = true := by
  unfold compile at h
  rw [EStateM.run_bind] at h
  cases hcs : (compileToScheduled p).run s with
  | error e s₁ =>
      rw [hcs] at h
      simp at h
  | ok logical s₁ =>
      rw [hcs] at h
      dsimp only at h
      unfold route at h
      cases hp : physicalizeForRoute logical with
      | error e =>
          rw [hp] at h
          simp [EStateM.run, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      | ok physical =>
          rw [hp] at h
          dsimp only at h
          cases hrc : routeCore physical.scheduled with
          | error e =>
              rw [hrc] at h
              simp [EStateM.run, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
          | ok pair =>
              obtain ⟨steps, routing⟩ := pair
              rw [hrc] at h
              dsimp only at h
              split at h
              · rename_i hwf
                simp only [EStateM.run, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
                obtain ⟨htc, -⟩ := h
                subst htc
                exact ⟨logical, s₁, physical, rfl, hp, hrc, rfl, hwf⟩
              · simp [EStateM.run, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

/-- Public theorem shape donor. Only the internal witness changes; the result and explicit arguments
match production `LeanNCD.compile_wellFormed`. -/
theorem compile_wellFormed (p : TLProgram) (s : Nat) (tc : ThreadedComposed) (s' : Nat)
    (h : (compile p).run s = .ok tc s') : tc.WellFormed := by
  obtain ⟨_logical, _s₁, physical, _hlogical, _hphysical, hrc, hne, hwfd⟩ :=
    compile_eq_physical_route h
  exact ⟨hwfd, LeanNCD.wf_typeMatch hrc hwfd hne,
    LeanNCD.wf_singleOutput hrc, LeanNCD.wf_topo hrc hne⟩

example (p : TLProgram) (s : Nat) (tc : ThreadedComposed) (s' : Nat)
    (h : (compile p).run s = .ok tc s') : tc.WellFormed :=
  compile_wellFormed p s tc s' h

private def reluProgram : TLProgram :=
  tlprog!{ Y[i] := relu(X[i]) }

private def softmaxProgram : TLProgram :=
  tlprog!{ tensor Y(q, s)
           Y[q, s.] := softmax(X[q, s]) }

private def chainProgram : TLProgram :=
  tlprog!{ Y[i] := relu(X[i])
           Z[i] := Y[i] }

private def opaqueScanProgram : TLProgram :=
  tlprog!{ iter l = 3
           S[j, 0] := X[j]
           S[j, l + 1] := relu(S[j, l]) }

private def collisionProgram : TLProgram :=
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  { decls := [], stmts := [
      .assign "####" [.free i]
        { body := { terms := [{ factors := [.read "###" [.axis i]] }] },
          nonlin := .pointwise .relu, agg := .sum }] }

private def escapedPrefixCollisionProgram : TLProgram :=
  let i : AxisSpec := { name := "i", uid := 0, kind := .real }
  { decls := [], stmts := [
      .assign "%nl8" [.free i]
        { body := { terms := [{ factors := [.read "X" [.axis i]] }] },
          nonlin := .pointwise .relu, agg := .sum }] }

/-- Compare routed results while intentionally ignoring the obsolete split-mint counter. -/
private def compileOutcome :
    EStateM.Result CompileError Nat ThreadedComposed → Except CompileError ThreadedComposed
  | .ok tc _ => .ok tc
  | .error e _ => .error e

/-- Exact FreshM composition, including final state, at zero and nonzero starts. -/
#guard (compile reluProgram).run 0 == (compileToScheduled reluProgram >>= route).run 0
#guard (compile softmaxProgram).run 17 ==
  (compileToScheduled softmaxProgram >>= route).run 17
#guard (compile chainProgram).run 41 ==
  (compileToScheduled chainProgram >>= route).run 41

/-- Common-domain routed presentations remain exactly equal to the current split pipeline. -/
#guard compileOutcome ((compile reluProgram).run 3) ==
  compileOutcome ((TLProgram.compile reluProgram).run 3)
#guard compileOutcome ((compile softmaxProgram).run 11) ==
  compileOutcome ((TLProgram.compile softmaxProgram).run 11)
#guard compileOutcome ((compile chainProgram).run 29) ==
  compileOutcome ((TLProgram.compile chainProgram).run 29)
#guard compileOutcome ((compile opaqueScanProgram).run 47) ==
  compileOutcome ((TLProgram.compile opaqueScanProgram).run 47)

run_cmd do
  let checkTwo (label : String) (p : TLProgram) (state : Nat) := do
    match (compileToScheduled p).run state with
    | .error e _ => throwError s!"{label}: logical compile failed: {repr e}"
    | .ok logical s' =>
        if logical.stmts.length != 1 then
          throwError s!"{label}: expected one logical statement"
        if s' < state then
          throwError s!"{label}: FreshM state regressed from {state} to {s'}"
        match (compile p).run state with
        | .error e _ => throwError s!"{label}: routed compile failed: {repr e}"
        | .ok _ routedState =>
            if routedState != s' then
              throwError s!"{label}: route changed FreshM state {s'} → {routedState}"
        match physicalizeForRoute logical with
        | .error e => throwError s!"{label}: physicalization failed: {repr e}"
        | .ok physical =>
            if physical.scheduled.stmts.length != 2 then
              throwError s!"{label}: expected two physical statements"
  checkTwo "relu" reluProgram 9
  checkTwo "softmax" softmaxProgram 23

run_cmd do
  match (compileToScheduled chainProgram).run 31 with
  | .error e _ => throwError s!"chain: logical compile failed: {repr e}"
  | .ok logical _ =>
      match physicalizeForRoute logical with
      | .error e => throwError s!"chain: physicalization failed: {repr e}"
      | .ok physical =>
          if logical.stmts.length != 2 || physical.scheduled.stmts.length != 3 then
            throwError "chain: expected 2 logical / 3 physical statements"
          match routeCore physical.scheduled with
          | .error e => throwError s!"chain: routeCore failed: {repr e}"
          | .ok _ => pure ()

run_cmd do
  match (compileToScheduled opaqueScanProgram).run 5 with
  | .error e _ => throwError s!"opaque scan: logical compile failed: {repr e}"
  | .ok logical _ =>
      match physicalizeForRoute logical with
      | .error e => throwError s!"opaque scan: physicalization failed: {repr e}"
      | .ok physical =>
          match logical.stmts, physical.scheduled.stmts, physical.fragments with
          | [.scan ..], [.scan ..], [fragment] =>
              if fragment.firstStep != 0 || fragment.lastStep != 0 ||
                  fragment.internalName.isSome then
                throwError "opaque scan: expected one unchanged opaque fragment"
          | _, _, _ => throwError "opaque scan: node shape changed"

run_cmd do
  match (compileToScheduled collisionProgram).run 7 with
  | .error e _ => throwError s!"collision: logical compile failed: {repr e}"
  | .ok logical _ =>
      match physicalizeForRoute logical with
      | .error e => throwError s!"collision: physicalization failed: {repr e}"
      | .ok physical =>
          match generatedRouteNames physical.fragments with
          | [generated] =>
              if physical.sourceNames.contains generated then
                throwError "collision: generated route name occurs in source inventory"
              if generated.length ≤ maxSourceNameLength physical.sourceNames then
                throwError "collision: generated route name is not strictly longer"
          | _ => throwError "collision: expected exactly one generated route name"

run_cmd do
  match (compile escapedPrefixCollisionProgram).run 7 with
  | .ok _ _ => pure ()
  | .error e _ =>
      throwError s!"escaped %nl collision: collision-free seed unexpectedly failed: {repr e}"

end LeanNCD.NonlinearityRouteFragmentsSeed
