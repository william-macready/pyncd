import LeanNCD.Semantics.Plan.Memory

/- Concrete plan execution (spec Section 30.1), slice-1 profile: validated
   Start, singleton commands, and three kernels. `initZero` writes the
   accumulator identity; `acc` is TRANSACTIONAL: it evaluates every member
   body on the read view `readPub pc M` first and commits only if all
   succeed; `pub` is a role change that writes nothing. -/

namespace LeanNCD.Semantics.Program.Plan

open Executor

variable {K : S → Type} {σ : Declarations S} {r : Registry K}

/-- The logical destination address of an occurrence. -/
def OccRef.dest {P : Program K σ r} (x : OccRef P) : Address σ :=
  ⟨x.1.val, P.destination x.1 x.2.1 x.2.2⟩

/-- The destination as a defined address. -/
def OccRef.target {P : Program K σ r} (x : OccRef P) : DefAddr P :=
  ⟨x.1, P.destination x.1 x.2.1 x.2.2⟩

theorem OccRef.target_addr {P : Program K σ r} (x : OccRef P) : x.target.addr = x.dest := rfl

/-- Outcome of one concrete command. -/
inductive StepResult (P : Program K σ r)
  | ok (M : Memory K σ)
  | semFail (o : OccRef P)
  | stuck

/-- Outcome of a whole plan run; `pc` is where it stopped. -/
inductive PlanOutcome (P : Program K σ r)
  | done (pc : Nat) (M : Memory K σ)
  | failed (o : OccRef P) (pc : Nat) (M : Memory K σ)
  | stuck (pc : Nat) (M : Memory K σ)

variable {P : Program K σ r} (π : P.Plan)

/-- Slice-1 profile: every command is exactly one annotation (fusion of
    several annotations into one command is deferred, spec 32.3). -/
def Singleton : Prop := ∀ cmd ∈ π.commands, ∃ a, cmd = [a]

/-! ### Validated Start (mirrors `Executor.validate`/`runValidated`) -/

def validateInput (η : InputBinding (K := K) (σ := σ)) : Except σ.Tensor P.Input :=
  match h : π.tensors.find? (fun t => (η t).isSome != P.input t) with
  | some t => .error t
  | none => .ok ⟨η, by
      intro t
      have clean := List.find?_eq_none.mp h t (π.tensors_complete t)
      simpa using clean⟩

theorem validateInput_accepts (η : P.Input) : π.validateInput η.val = .ok η := by
  unfold validateInput
  split
  · rename_i t found
    have bad := List.find?_some found
    simp [η.property t] at bad
  · rfl

theorem validateInput_error (η : InputBinding (K := K) (σ := σ)) (t : σ.Tensor)
    (h : π.validateInput η = .error t) : (η t).isSome ≠ P.input t := by
  unfold validateInput at h
  split at h
  · rename_i found
    cases h
    simpa using List.find?_some found
  · contradiction

/-- Validated concrete initialisation: reject a misbound input, else `Start`. -/
def startValidated (η : InputBinding (K := K) (σ := σ)) :
    Except σ.Tensor (P.Input × Memory K σ) :=
  (π.validateInput η).map (fun input => (input, Start input))

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### Kernels -/

/-- Overwrite the slot of one defined address. -/
def writeDef (M : Memory K σ) (x : DefAddr P) (v : K (σ.signature x.1.val).sort) :
    Memory K σ :=
  Function.update M (place x.addr) (some v)

/-- `initZero S`: write the accumulator identity at each member's slot. -/
def execInit (S : List (DefAddr P)) (M : Memory K σ) : Memory K σ :=
  S.foldl (fun M x => writeDef M x 0) M

/-- A body value read from a partial store (the shape of `evalValue`). -/
def valueOn (p : PartialStore K σ) (x : OccRef P) : Option (K (σ.signature x.1.val).sort) :=
  match evalReady ops p (P.body x.1 x.2.1) x.2.2 with
  | .evaluated (some v) => some v
  | _ => none

def valuesOn (p : PartialStore K σ) : Values P := fun x => (valueOn ops p x).getD 0

/-- Evaluation phase: `none` when every member evaluated successfully; else the
    first member (list order) that is not ready (`stuck`) or undefined. -/
def scanGroup (p : PartialStore K σ) : List (OccRef P) → Option (StepResult P)
  | [] => none
  | x :: G =>
    match evalReady ops p (P.body x.1 x.2.1) x.2.2 with
    | .notReady => some .stuck
    | .evaluated none => some (.semFail x)
    | .evaluated (some _) => scanGroup p G

/-- Addition at an occurrence's sort (fixes the instance's index). -/
def addVal (x : OccRef P) (a b : K (σ.signature x.1.val).sort) : K (σ.signature x.1.val).sort :=
  a + b

/-- Add one member's value into its destination slot, which must be initialised. -/
def addAt (v : Values P) (M : Memory K σ) (x : OccRef P) : Option (Memory K σ) :=
  match M (place x.dest) with
  | some a => some (Function.update M (place x.dest) (some (addVal x a (v x))))
  | none => none

/-- `acc G`, transactional: evaluate all members on the read view, then commit. -/
def execAcc (pc : Nat) (G : List (OccRef P)) (M : Memory K σ) : StepResult P :=
  match scanGroup ops (π.readPub pc M) G with
  | some res => res
  | none =>
    match G.foldlM (addAt (valuesOn ops (π.readPub pc M))) M with
    | some M' => .ok M'
    | none => .stuck

/-- `pub B`: a role change. It writes nothing and requires every member's slot
    to be initialised (the N1 materialisation requirement). -/
def execPub (B : List (DefAddr P)) (M : Memory K σ) : StepResult P :=
  if B.all (fun x => (M (place x.addr)).isSome) then .ok M else .stuck

def execAnn (pc : Nat) (M : Memory K σ) : Ann P → StepResult P
  | .initZero S => .ok (execInit S M)
  | .acc G => π.execAcc ops pc G M
  | .pub B => execPub B M

/-- Slice 1 executes singleton commands only; anything else is stuck. -/
def stepCommand (pc : Nat) (M : Memory K σ) : Command P → StepResult P
  | [a] => π.execAnn ops pc M a
  | _ => .stuck

def stepPlan (pc : Nat) (M : Memory K σ) : StepResult P :=
  match π.commands[pc]? with
  | some cmd => π.stepCommand ops pc M cmd
  | none => .stuck

/-- Run the remaining commands from `pc`; structural in the command list. -/
def runFrom (pc : Nat) (M : Memory K σ) : List (Command P) → PlanOutcome P
  | [] => .done pc M
  | cmd :: rest =>
    match π.stepCommand ops pc M cmd with
    | .ok M' => runFrom (pc + 1) M' rest
    | .semFail o => .failed o pc M
    | .stuck => .stuck pc M

def runPlan (M : Memory K σ) : PlanOutcome P := π.runFrom ops 0 M π.commands

end LeanNCD.Semantics.Program.Plan
