import LeanNCD.Semantics.Plan.Memory

/- Concrete plan execution (spec Section 30.1), slice-1 to slice-3 profile: validated
   Start, commands (singleton or fused: `stepCommand` folds `execAnns` over the command's
   annotations), and three kernels. `initZero` writes the
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
inductive StepResult (P : Program K σ r) (A : Allocation P)
  | ok (M : Memory K A)
  | semFail (o : OccRef P)
  | stuck

/-- Outcome of a whole plan run; `pc` is where it stopped. -/
inductive PlanOutcome (P : Program K σ r) (A : Allocation P)
  | done (pc : Nat) (M : Memory K A)
  | failed (o : OccRef P) (pc : Nat) (M : Memory K A)
  | stuck (pc : Nat) (M : Memory K A)

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
    Except σ.Tensor (P.Input × Memory K π.allocation) :=
  (π.validateInput η).map (fun input => (input, π.Start input))

variable [DecidableEq σ.Tensor] [∀ t : P.Defined, AddCommMonoid (K (σ.signature t.val).sort)]
variable (ops : (s : S) → ScalarOps (K s))

/-! ### Kernels -/

/-- Overwrite the slot of one defined address. -/
def writeDef (M : Memory K π.allocation) (x : DefAddr P)
    (v : K (σ.signature x.1.val).sort) : Memory K π.allocation :=
  Function.update M (place π.allocation x.addr)
    (cast (congrArg (fun s => Option (K s)) (place_sort π.allocation x.addr).symm) (some v))

/-- `initZero S`: write the accumulator identity at each member's slot. -/
def execInit (S : List (DefAddr P)) (M : Memory K π.allocation) : Memory K π.allocation :=
  S.foldl (fun M x => π.writeDef M x 0) M

/-- A body value read from a partial store (the shape of `evalValue`). -/
def valueOn (p : PartialStore K σ) (x : OccRef P) : Option (K (σ.signature x.1.val).sort) :=
  match evalReady ops p (P.body x.1 x.2.1) x.2.2 with
  | .evaluated (some v) => some v
  | _ => none

def valuesOn (p : PartialStore K σ) : Values P := fun x => (valueOn ops p x).getD 0

/-- Evaluation phase: `none` when every member evaluated successfully; else the
    first member (list order) that is not ready (`stuck`) or undefined. -/
def scanGroup (A : Allocation P) (p : PartialStore K σ) :
    List (OccRef P) → Option (StepResult P A)
  | [] => none
  | x :: G =>
    match evalReady ops p (P.body x.1 x.2.1) x.2.2 with
    | .notReady => some .stuck
    | .evaluated none => some (.semFail x)
    | .evaluated (some _) => scanGroup A p G

/-- Addition at an occurrence's sort (fixes the instance's index). -/
def addVal (x : OccRef P) (a b : K (σ.signature x.1.val).sort) : K (σ.signature x.1.val).sort :=
  a + b

/-- Add one member's value into its destination slot, which must be initialised. -/
def addAt (v : Values P) (M : Memory K π.allocation) (x : OccRef P) :
    Option (Memory K π.allocation) :=
  match readSlot π.allocation M x.dest with
  | some a => some (π.writeDef M x.target (addVal x a (v x)))
  | none => none

/-- `acc G`, transactional: evaluate all members on the read view, then commit. -/
def execAcc (pc : Nat) (G : List (OccRef P)) (M : Memory K π.allocation) :
    StepResult P π.allocation :=
  match scanGroup ops π.allocation (π.readPub pc M) G with
  | some res => res
  | none =>
    match G.foldlM (π.addAt (valuesOn ops (π.readPub pc M))) M with
    | some M' => .ok M'
    | none => .stuck

/-- `pub B`: a role change. It writes nothing and requires every member's slot
    to be initialised (the N1 materialisation requirement). -/
def execPub (B : List (DefAddr P)) (M : Memory K π.allocation) : StepResult P π.allocation :=
  if B.all (fun x => (readSlot π.allocation M x.addr).isSome) then .ok M else .stuck

/-- `retire B`: clear the slot of each member (retirement frees the physical slot).
    Total: never `stuck`, like `execInit`. -/
def execRet (B : List (DefAddr P)) (M : Memory K π.allocation) : Memory K π.allocation :=
  B.foldl (fun M x => Function.update M (place π.allocation x.addr) none) M

def execAnn (pc : Nat) (M : Memory K π.allocation) : Ann P → StepResult P π.allocation
  | .initZero S => .ok (π.execInit S M)
  | .acc G => π.execAcc ops pc G M
  | .pub B => π.execPub B M
  | .retire B => .ok (π.execRet B M)

/-- Run a list of annotations from position `n` on the running memory.
    `semFail`/`stuck` propagate; the caller reports the pre-command memory. -/
def execAnns (n : Nat) (M : Memory K π.allocation) : List (Ann P) → StepResult P π.allocation
  | [] => .ok M
  | a :: as =>
    match π.execAnn ops n M a with
    | .ok M' => execAnns n.succ M' as
    | res => res

/-- A (possibly fused) command at command position `pc`: its annotations run at the
    expanded positions `offset pc, offset pc + 1, …` of `π.expand` (spec 29.3), each on
    the memory left by the previous one. Failure is transactional per command: the
    callers (`runFrom`) report the pre-command memory. -/
def stepCommand (pc : Nat) (M : Memory K π.allocation) (cmd : Command P) :
    StepResult P π.allocation :=
  π.expand.execAnns ops (π.offset pc) M cmd

/-- Prefix transport also requires the same physical allocation. -/
theorem execAnn_prefix {π π' : P.Plan} {pc pc' : Nat}
    (hA : π.allocation = π'.allocation) (h : π.prefixAnn pc = π'.prefixAnn pc')
    (M : Memory K π.allocation) (a : Ann P) :
    cast (congrArg (StepResult P) hA) (π.execAnn ops pc M a) =
      π'.execAnn ops pc' (cast (congrArg (Memory K) hA) M) a := by
  cases π with
  | mk ts hn hc cmds A =>
    cases π' with
    | mk ts' hn' hc' cmds' A' =>
      dsimp at hA
      subst A'
      let π : P.Plan := ⟨ts, hn, hc, cmds, A⟩
      let π' : P.Plan := ⟨ts', hn', hc', cmds', A⟩
      change π.prefixAnn pc = π'.prefixAnn pc' at h
      change π.execAnn ops pc M a = π'.execAnn ops pc' M a
      have hr : π.readPub pc = π'.readPub pc' := by
        funext M a
        have hp : π.Live pc a ↔ π'.Live pc' a := by
          simp only [Live, Pub, Ret, pubList, retList, h]
        unfold readPub
        by_cases hπ : π.Live pc a
        · rw [if_pos hπ, if_pos (hp.mp hπ)]
        · rw [if_neg hπ, if_neg (fun h' => hπ (hp.mpr h'))]
      have hadd : π.addAt = π'.addAt := by
        funext v M x
        rfl
      cases a <;> simp only [execAnn, execAcc, hr, hadd]
      all_goals dsimp [π, π']
      all_goals try rfl
      split
      · rfl
      · split <;> rfl

/-- On a singleton command the generalised step is the slice-1 step, for ANY plan:
    this is what keeps the slice-1 step lemmas' statements unchanged. -/
theorem stepCommand_single (pc : Nat) (M : Memory K π.allocation) (a : Ann P) :
    π.stepCommand ops pc M [a] = π.execAnn ops pc M a := by
  have h := execAnn_prefix ops (π := π.expand) (π' := π) rfl
    (π.prefixAnn_eq_expand pc).symm M a
  change π.expand.execAnn ops (π.offset pc) M a = π.execAnn ops pc M a at h
  simp only [stepCommand, execAnns, h]
  cases π.execAnn ops pc M a <;> rfl

def stepPlan (pc : Nat) (M : Memory K π.allocation) : StepResult P π.allocation :=
  match π.commands[pc]? with
  | some cmd => π.stepCommand ops pc M cmd
  | none => .stuck

/-- Run the remaining commands from `pc`; structural in the command list. -/
def runFrom (pc : Nat) (M : Memory K π.allocation) :
    List (Command P) → PlanOutcome P π.allocation
  | [] => .done pc M
  | cmd :: rest =>
    match π.stepCommand ops pc M cmd with
    | .ok M' => runFrom (pc + 1) M' rest
    | .semFail o => .failed o pc M
    | .stuck => .stuck pc M

def runPlan (M : Memory K π.allocation) : PlanOutcome P π.allocation :=
  π.runFrom ops 0 M π.commands

#print axioms validateInput_accepts
#print axioms validateInput_error
#print axioms execAnn_prefix
#print axioms stepCommand_single

end LeanNCD.Semantics.Program.Plan
