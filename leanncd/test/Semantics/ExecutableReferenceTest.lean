import LeanNCD.Semantics.RationalReference

namespace LeanNCD.Semantics.ExecutableReferenceFixtures

open Program Program.Executor RationalReference

@[reducible] def shape : Shape := [⟨41, 3⟩]

@[reducible] def declarations : Declarations Unit :=
  ⟨Unit, fun _ => 7, fun a b _ => by cases a; cases b; rfl,
    fun _ => ⟨(), shape⟩⟩

def point (i : Fin 3) : Coord shape := (i, ())

/- Donors: CollectionModelFixtures.duplicate/partialProgram and
   ReferenceMachineFixtures.cycleP. Only the closed reference registry changes. -/
@[reducible] def program (n : Nat)
    (body : (Γ : Type) → Fin n → Expr Carrier declarations registry Γ (.scalar ())) :
    Program Carrier declarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => n
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => point 0
  body := fun _ s => body _ s

def tag (n : Nat) (body) (s : Fin n) :
    (program n body).Occurrence ⟨(), rfl⟩ := ⟨s, ⟨0, rfl⟩⟩

def schedule (n : Nat) (body) : Schedule (program n body) where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := (List.finRange n).map (fun s => .occurrence ⟨(), rfl⟩ (tag n body s)) ++
    [.publication ⟨(), rfl⟩ (point 0), .publication ⟨(), rfl⟩ (point 1),
      .publication ⟨(), rfl⟩ (point 2)]
  keys_nodup := by
    classical
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply List.Nodup.map _ (List.nodup_finRange n)
      intro s u h
      have eq : tag n body s = tag n body u := by simpa using h
      exact congrArg Sigma.fst eq
    · simp [point, List.nodup_cons, Key.publication.injEq, Prod.mk.injEq]
    · intro a ha b hb eq
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> cases eq
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have ev : v = 0 := Subsingleton.elim _ _
      subst v
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩
    | publication t p =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      apply List.mem_append_right
      fin_cases i <;> simp [point]

def duplicateBody (Γ : Type) (_ : Fin 2) :
    Expr Carrier declarations registry Γ (.scalar ()) := .lit 2

def failureBody (Γ : Type) (_ : Fin 1) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  .binary .mul (.lit 0) (.prim (r := registry) Primitive.reciprocal (fun _ => .lit 0))

def strictPolicy : ReadPolicy ℚ shape where
  resolve := fun raw =>
        if h : 0 ≤ raw 0 ∧ raw 0 < 3 then
          .at (⟨(raw 0).toNat, by change (raw 0).toNat < 3; omega⟩, ())
        else .reject
  inBounds := by
        rintro ⟨i, u⟩
        cases u
        simp [Coord.raw, shape]

def selfRead (Γ : Type) : Expr Carrier declarations registry Γ (.scalar ()) :=
  .read () ⟨strictPolicy, fun _ => Coord.raw (point 0), fun _ => .at (point 0),
    fun _ => strictPolicy.inBounds _⟩

def blockedBody (Γ : Type) (_ : Fin 1) := selfRead Γ

def summarize (n : Nat)
    (body : (Γ : Type) → Fin n → Expr Carrier declarations registry Γ (.scalar ())) :
    String × Nat × List (Option ℚ) × Nat :=
  let P := program n body
  match runValidated P ops (schedule n body) (fun _ => none) with
  | .error _ => ("invalid-input", 0, [], 0)
  | .ok result =>
    let outcome := result.result.outcome
    let snapshot := match outcome with
      | .complete c _ | .blocked c _ _ | .exhausted c | .failed _ _ c => c
    (outcome.kind, result.result.events.length,
      [snapshot.published ⟨(), point 0⟩, snapshot.published ⟨(), point 1⟩,
        snapshot.published ⟨(), point 2⟩],
      (snapshot.pending ⟨(), rfl⟩).card)

def checkSmoke (name : String) (actual expected : String × Nat × List (Option ℚ) × Nat) :
    IO Unit := do
  IO.println s!"{name}: {repr actual}"
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

#eval checkSmoke "duplicate" (summarize 2 duplicateBody)
  ("complete", 5, [some 4, some 0, some 0], 0)
#eval checkSmoke "ready-failure" (summarize 1 failureBody)
  ("failed", 1, [none, none, none], 1)
#eval checkSmoke "blocked" (summarize 1 blockedBody)
  ("blocked", 2, [none, some 0, some 0], 1)

def check {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) :
    IO Unit := do
  IO.println s!"{name}: {repr actual}"
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

abbrev Row := String × Nat × Nat × Nat × Nat × Option ℚ

def eventRow {P : Program Carrier declarations registry} (e : Event P) : Row :=
  match e with
  | .contribution t o v =>
    ("contribution", declarations.uid t.val, o.1.val, o.2.val.val,
      (P.destination t o.1 o.2).1.val, some v)
  | .publication t p v => ("publication", declarations.uid t.val, 0, 0, p.1.val, some v)
  | .undefined t o =>
    ("undefined", declarations.uid t.val, o.1.val, o.2.val.val,
      (P.destination t o.1 o.2).1.val, none)

def vectorStore {P : Program Carrier declarations registry} (c : P.Running) :=
  [c.published ⟨(), point 0⟩, c.published ⟨(), point 1⟩, c.published ⟨(), point 2⟩]

def snapshot {P : Program Carrier declarations registry} (outcome : Outcome P ops) :
    P.Running :=
  match outcome with
  | .complete c _ | .blocked c _ _ | .exhausted c | .failed _ _ c => c

def noInput (P : Program Carrier declarations registry) (h : ∀ t, P.input t = false) :
    P.Input := ⟨fun _ => none, by intro t; simp [h t]⟩

/- Group 1: clone ReferenceMachineFixtures.valuationP and
   CollectionModelFixtures.collision; duplicate valuations share one statement. -/
@[reducible] def tagged : Program Carrier declarations registry where
  tensors := inferInstance
  input := fun _ => false
  output := fun _ => false
  output_defined := by intros; rfl
  statements := fun _ => 2
  valuations := fun _ _ => 2
  guard := fun _ _ _ => true
  destination := fun _ _ _ => point 1
  body := fun _ s => .lit (if s = 0 then 2 else 5)

def taggedSchedule : Schedule tagged where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := [.publication ⟨(), rfl⟩ (point 1),
    .occurrence ⟨(), rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .occurrence ⟨(), rfl⟩ ⟨0, ⟨1, rfl⟩⟩,
    .occurrence ⟨(), rfl⟩ ⟨1, ⟨0, rfl⟩⟩, .occurrence ⟨(), rfl⟩ ⟨1, ⟨1, rfl⟩⟩,
    .publication ⟨(), rfl⟩ (point 0), .publication ⟨(), rfl⟩ (point 2)]
  keys_nodup := by
    simp [List.nodup_cons, Key.publication.injEq, Key.occurrence.injEq,
      point]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      fin_cases s <;> fin_cases v <;> simp
    | publication t p =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      fin_cases i <;> simp [point]

def taggedResult := run tagged ops taggedSchedule (noInput tagged (fun _ => rfl))
def taggedReverse := run tagged ops taggedSchedule.reverse (noInput tagged (fun _ => rfl))

#eval check "tagged-trace" (taggedResult.events.map eventRow)
  [("contribution", 7, 0, 0, 1, some 2), ("contribution", 7, 0, 1, 1, some 2),
   ("contribution", 7, 1, 0, 1, some 5), ("contribution", 7, 1, 1, 1, some 5),
   ("publication", 7, 0, 0, 1, some 14), ("publication", 7, 0, 0, 0, some 0),
   ("publication", 7, 0, 0, 2, some 0)]
#eval check "tagged-whole-store"
  (taggedResult.outcome.kind, vectorStore (snapshot taggedResult.outcome),
    taggedReverse.outcome.kind, vectorStore (snapshot taggedReverse.outcome))
  ("complete", [some 0, some 14, some 0], "complete", [some 0, some 14, some 0])

def taggedCandidate : Store Carrier declarations :=
  fun a => if a.2.1 = 1 then 14 else 0
def taggedAdmitted : tagged.AdmEnv ops taggedCandidate := by
  intro t o
  rcases o with ⟨s, v⟩
  fin_cases s <;> rfl
#eval check "tagged-equations"
  ([tagged.collect ops taggedCandidate taggedAdmitted ⟨(), rfl⟩ (point 0),
    tagged.collect ops taggedCandidate taggedAdmitted ⟨(), rfl⟩ (point 1),
    tagged.collect ops taggedCandidate taggedAdmitted ⟨(), rfl⟩ (point 2)],
    [taggedCandidate ⟨(), point 0⟩, taggedCandidate ⟨(), point 1⟩,
      taggedCandidate ⟨(), point 2⟩])
  ([0, 14, 0], [0, 14, 0])

def zeroBody (Γ : Type) (_ : Fin 1) :
    Expr Carrier declarations registry Γ (.scalar ()) := .lit 0
#eval checkSmoke "zero-contribution" (summarize 1 zeroBody)
  ("complete", 4, [some 0, some 0, some 0], 0)
#eval checkSmoke "empty-fiber" (summarize 0 (fun _ s => nomatch s))
  ("complete", 3, [some 0, some 0, some 0], 0)

@[reducible] def excluded : Program Carrier declarations registry :=
  { program 1 failureBody with
    guard := fun _ _ _ => false
    destination := fun _ _ _ => point 0
    body := fun _ s => failureBody _ s }
def excludedSchedule : Schedule excluded where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := [.publication ⟨(), rfl⟩ (point 0), .publication ⟨(), rfl⟩ (point 1),
    .publication ⟨(), rfl⟩ (point 2)]
  keys_nodup := by simp [List.nodup_cons, Key.publication.injEq, point]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o => exact False.elim (Bool.false_ne_true o.2.property)
    | publication t p =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      fin_cases i <;> simp [point]
def excludedResult := run excluded ops excludedSchedule (noInput excluded (fun _ => rfl))
#eval check "guard-excluded-undefined"
  (excludedResult.outcome.kind, excludedResult.events.length,
    vectorStore (snapshot excludedResult.outcome))
  ("complete", 3, [some 0, some 0, some 0])

/- Clone CollectionModelFixtures.reciprocalProgram, not a linearity assumption. -/
def reciprocalBody (Γ : Type) (s : Fin 2) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  .prim (r := registry) Primitive.reciprocal (fun _ => .lit (if s = 0 then 2 else 4))
def squareBody (Γ : Type) (_ : Fin 1) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  .prim (r := registry) Primitive.square (fun _ => .lit 3)
def reciprocalCandidate : Store Carrier declarations := fun _ => 3 / 4
def reciprocalAdmitted : (program 2 reciprocalBody).AdmEnv ops reciprocalCandidate := by
  intro t o
  rcases o with ⟨s, v⟩
  fin_cases s <;> rfl
#eval check "nonlinear-boundary"
  (summarize 2 reciprocalBody,
    (program 2 reciprocalBody).collect ops reciprocalCandidate reciprocalAdmitted
      ⟨(), rfl⟩ (point 0),
    interpret ops reciprocalCandidate
      (.prim (r := registry) Primitive.reciprocal (fun _ => .lit 6)) ())
  (("complete", 5, [some (3 / 4), some 0, some 0], 0), 3 / 4, some (1 / 6))
#eval checkSmoke "primitive-square" (summarize 1 squareBody)
  ("complete", 4, [some 9, some 0, some 0], 0)

/- Group 2: clone ReferenceMachineFixtures.scalarRole/scalarInput and
   CollectionModelFixtures.roleProgram/presentEmpty/omittedEmpty/extraDefined. -/
@[reducible] def scalarDeclarations : Declarations Unit :=
  ⟨Fin 3, fun t => t.val, fun _ _ h => Fin.ext h, fun _ => ⟨(), []⟩⟩
@[reducible] def scalarRole (bad : Bool) : Program Carrier scalarDeclarations registry where
  tensors := inferInstance
  input := fun t => t == 0
  output := fun t => t == 1
  output_defined := by intro t h; fin_cases t <;> simp_all
  statements := fun _ => 1
  valuations := fun _ _ => 1
  guard := fun _ _ _ => true
  destination := fun _ _ _ => ()
  body := fun t _ => if bad && t.val == 2 then
    .prim (r := registry) Primitive.reciprocal (fun _ => .lit 0)
    else .lit (if t.val == 1 then 2 else 3)

def scalarSchedule (bad : Bool) : Schedule (scalarRole bad) where
  tensors := [0, 1, 2]
  tensors_nodup := by decide
  tensors_complete := by intro t; fin_cases t <;> simp
  keys := [.occurrence ⟨1, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .publication ⟨1, rfl⟩ (),
    .occurrence ⟨2, rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .publication ⟨2, rfl⟩ ()]
  keys_nodup := by simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨t, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hs : s = 0 := Subsingleton.elim _ _
      have hv' : v = 0 := Subsingleton.elim _ _
      subst s; subst v
      fin_cases t <;> simp_all [scalarRole]
      change true = false at ht
      contradiction
    | publication t p =>
      rcases t with ⟨t, ht⟩
      cases p
      fin_cases t <;> simp_all [scalarRole]
      change true = false at ht
      contradiction

def scalarBinding : InputBinding (K := Carrier) (σ := scalarDeclarations) :=
  fun t => if t = 0 then some (fun _ => 7) else none
def scalarInput (bad : Bool) : (scalarRole bad).Input :=
  ⟨scalarBinding, by intro t; fin_cases t <;> rfl⟩
def scalarResult (bad : Bool) := run (scalarRole bad) ops (scalarSchedule bad) (scalarInput bad)
def scalarSummary (bad : Bool) :=
  let result := scalarResult bad
  let c := match result.outcome with
    | .complete c _ | .blocked c _ _ | .exhausted c | .failed _ _ c => c
  (result.outcome.kind, result.events.length,
    [c.published ⟨0, ()⟩, c.published ⟨1, ()⟩, c.published ⟨2, ()⟩])
#eval check "scalar-input-nonoutput" (scalarSummary false)
  ("complete", 4, [some 7, some 2, some 3])
#eval check "internal-nonoutput-failure" (scalarSummary true)
  ("failed", 3, [some 7, some 2, none])

def validationRow (schedule : Schedule (scalarRole false))
    (η : InputBinding (K := Carrier) (σ := scalarDeclarations)) : String × Nat :=
  match runValidated (scalarRole false) ops schedule η with
  | .error t => ("error", t.val)
  | .ok result => (result.result.outcome.kind, 99)
def extraDefined : InputBinding (K := Carrier) (σ := scalarDeclarations) :=
  fun t => if t = 1 then some (fun _ => 9) else scalarBinding t
def simultaneous : InputBinding (K := Carrier) (σ := scalarDeclarations) :=
  fun t => if t = 0 then none else some (fun _ => 9)
#eval check "input-validation-order"
  [validationRow (scalarSchedule false) (fun _ => none),
    validationRow (scalarSchedule false) extraDefined,
    validationRow (scalarSchedule false) simultaneous,
    validationRow (scalarSchedule false).reverse simultaneous]
  [("error", 0), ("error", 1), ("error", 0), ("error", 2)]

@[reducible] def emptyDeclarations : Declarations Unit :=
  ⟨Unit, fun _ => 7, fun a b _ => by cases a; cases b; rfl, fun _ => ⟨(), [⟨41, 0⟩]⟩⟩
@[reducible] def emptyRole (inputFlag : Bool) : Program Carrier emptyDeclarations registry where
  tensors := inferInstance
  input := fun _ => inputFlag
  output := fun _ => false
  output_defined := by intros _ h; contradiction
  statements := fun _ => 0
  valuations := fun _ s => nomatch s
  guard := fun _ s => nomatch s
  destination := fun _ s => nomatch s
  body := fun _ s => nomatch s
def emptySchedule (inputFlag : Bool) : Schedule (emptyRole inputFlag) where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := []
  keys_nodup := by simp
  keys_complete := by
    intro k
    cases k with
    | occurrence t o => exact Fin.elim0 o.1
    | publication t p => exact Fin.elim0 p.1
def presentEmpty : InputBinding (K := Carrier) (σ := emptyDeclarations) :=
  fun _ => some (fun p => Fin.elim0 p.1)
def emptyRow (inputFlag : Bool) (η : InputBinding (K := Carrier) (σ := emptyDeclarations)) :=
  match runValidated (emptyRole inputFlag) ops (emptySchedule inputFlag) η with
  | .error _ => ("error", 0)
  | .ok result => (result.result.outcome.kind, result.result.events.length)
#eval check "empty-input-and-defined"
  [emptyRow true presentEmpty, emptyRow true (fun _ => none), emptyRow false (fun _ => none)]
  [("complete", 0), ("error", 0), ("complete", 0)]

def taggedFuel (fuel : Nat) :=
  runFuel tagged ops taggedSchedule fuel (.running (tagged.initial (noInput tagged (fun _ => rfl))))
#eval check "fuel-boundaries"
  (initialBudget tagged,
    (taggedFuel 6).outcome.kind, (taggedFuel 7).outcome.kind,
    (taggedFuel 8).outcome.kind, (taggedFuel 9).outcome.kind, (taggedFuel 0).outcome.kind)
  (8, "exhausted", "complete", "complete", "complete", "exhausted")
example : tagged.stateMeasure (.running (tagged.initial (noInput tagged (fun _ => rfl)))) = 8 := by
  rw [← initialBudget_agrees tagged]
  decide
#eval check "zero-fuel-terminal"
  ((runFuel tagged ops taggedSchedule 0 taggedResult.outcome.state).outcome.kind,
    (runFuel (scalarRole true) ops (scalarSchedule true) 0
      (scalarResult true).outcome.state).outcome.kind)
  ("complete", "failed")

/- Group 3: clone ReferenceMachineFixtures.dependentP/cycleP/waitingBad;
   ranks are supplied on coordinates of ONE tensor. -/
def readAt (Γ : Type) (i : Fin 3) : Expr Carrier declarations registry Γ (.scalar ()) :=
  .read () ⟨strictPolicy, fun _ => Coord.raw (point i), fun _ => .at (point i),
    fun _ => strictPolicy.inBounds _⟩
def chainBody (Γ : Type) (s : Fin 2) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  if s = 0 then .lit 3 else .binary .add (readAt Γ 1) (.lit 1)
@[reducible] def routed
    (body : (Γ : Type) → Fin 2 → Expr Carrier declarations registry Γ (.scalar ())) :
    Program Carrier declarations registry :=
  { program 2 body with destination := fun _ s _ => if s = 0 then point 1 else point 2 }
def routedSchedule (body) : Schedule (routed body) where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := [.occurrence ⟨(), rfl⟩ ⟨1, ⟨0, rfl⟩⟩, .publication ⟨(), rfl⟩ (point 2),
    .occurrence ⟨(), rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .publication ⟨(), rfl⟩ (point 1),
    .publication ⟨(), rfl⟩ (point 0)]
  keys_nodup := by simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq, point]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases s <;> simp
    | publication t p =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      fin_cases i <;> simp [point]
def chainInput := noInput (routed chainBody) (fun _ => rfl)
def chainResult := run (routed chainBody) ops (routedSchedule chainBody) chainInput
def chainCertificate : (routed chainBody).RankCertificate where
  rank := fun a => a.2.1.val
  decreases := by
    rintro a b ⟨t, ⟨s, v⟩, rfl, hb⟩
    rcases t with ⟨⟨⟩, ht⟩
    fin_cases s <;> simp [routed, program, chainBody, readAt, footprint, point] at hb ⊢
    subst b
    decide
example := run_ranked_dichotomy (routed chainBody) ops (routedSchedule chainBody)
  chainCertificate chainInput
#eval check "coordinate-ranked-chain"
  (chainResult.outcome.kind, vectorStore (snapshot chainResult.outcome),
    chainResult.events.map eventRow)
  ("complete", [some 0, some 3, some 4],
    [("contribution", 7, 0, 0, 1, some 3), ("publication", 7, 0, 0, 1, some 3),
     ("contribution", 7, 1, 0, 2, some 4), ("publication", 7, 0, 0, 2, some 4),
     ("publication", 7, 0, 0, 0, some 0)])

def cycleBody (Γ : Type) (s : Fin 2) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  if s = 0 then
    .binary .mul (.lit 0) (.prim (r := registry) Primitive.reciprocal (fun _ => readAt Γ 2))
  else readAt Γ 1
def cycleResult := run (routed cycleBody) ops (routedSchedule cycleBody)
  (noInput (routed cycleBody) (fun _ => rfl))
def observationRow {P : Program Carrier declarations registry} :
    Observation P → String × Nat × Nat × Nat × Nat × List (Nat × Nat) × Option ℚ
  | .unavailable t o missing =>
    ("unavailable", declarations.uid t.val, o.1.val, o.2.val.val,
      (P.destination t o.1 o.2).1.val,
      missing.map (fun a => (declarations.uid a.1, a.2.1.val)), none)
  | .ready t o v =>
    ("ready", declarations.uid t.val, o.1.val, o.2.val.val,
      (P.destination t o.1 o.2).1.val, [], v)
def cycleObservations :=
  match cycleResult.outcome with
  | .blocked _ diagnostics _ => diagnostics.map observationRow
  | _ => []
#eval check "strict-zero-cycle-locators"
  (cycleResult.outcome.kind, vectorStore (snapshot cycleResult.outcome), cycleObservations)
  ("blocked", [some 0, none, none],
    [("unavailable", 7, 1, 0, 2, [(7, 1)], none),
     ("unavailable", 7, 0, 0, 1, [(7, 2)], none)])

def failureAfterBody (Γ : Type) (s : Fin 2) :
    Expr Carrier declarations registry Γ (.scalar ()) :=
  if s = 0 then .lit 2 else
    .prim (r := registry) Primitive.reciprocal (fun _ => .lit 0)
def failureAfterSchedule : Schedule (program 2 failureAfterBody) where
  tensors := [()]
  tensors_nodup := by simp
  tensors_complete := by intro t; cases t; simp
  keys := [.publication ⟨(), rfl⟩ (point 2),
    .occurrence ⟨(), rfl⟩ ⟨0, ⟨0, rfl⟩⟩, .occurrence ⟨(), rfl⟩ ⟨1, ⟨0, rfl⟩⟩,
    .publication ⟨(), rfl⟩ (point 0), .publication ⟨(), rfl⟩ (point 1)]
  keys_nodup := by simp [List.nodup_cons, Key.occurrence.injEq, Key.publication.injEq, point]
  keys_complete := by
    intro k
    cases k with
    | occurrence t o =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases o with ⟨s, ⟨v, hv⟩⟩
      have hv' : v = 0 := Subsingleton.elim _ _
      subst v
      fin_cases s <;> simp
    | publication t p =>
      rcases t with ⟨⟨⟩, ht⟩
      rcases p with ⟨i, u⟩
      cases u
      fin_cases i <;> simp [point]
def failureAfterResult := run (program 2 failureAfterBody) ops failureAfterSchedule
  (noInput (program 2 failureAfterBody) (fun _ => rfl))
#eval check "failure-retained-snapshot"
  (failureAfterResult.outcome.kind, failureAfterResult.events.map eventRow,
    vectorStore (snapshot failureAfterResult.outcome),
    (snapshot failureAfterResult.outcome).accumulators ⟨(), rfl⟩ (point 0),
    ((snapshot failureAfterResult.outcome).pending ⟨(), rfl⟩).card)
  ("failed",
    [("publication", 7, 0, 0, 2, some 0), ("contribution", 7, 0, 0, 0, some 2),
     ("undefined", 7, 1, 0, 0, none)],
    [none, none, some 0], 2, 1)
#eval check "ready-observations"
  ((observations (program 2 failureAfterBody) ops failureAfterSchedule
    ((program 2 failureAfterBody).initial
      (noInput (program 2 failureAfterBody) (fun _ => rfl)))).map observationRow)
  [("ready", 7, 0, 0, 0, [], some 2), ("ready", 7, 1, 0, 0, [], none)]
#print axioms chainCertificate

def replay {P : Program Carrier declarations registry} (start : P.MachineState) :
    List (Event P) → P.MachineState
  | [] => start
  | e :: es =>
    match start with
    | .running c => replay (e.effect P c) es
    | .failed t o c => .failed t o c
def replayRow (s : tagged.MachineState) :=
  match s with
  | .running c => ("running", vectorStore c, (c.pending ⟨(), rfl⟩).card)
  | .failed _ _ c => ("failed", vectorStore c, (c.pending ⟨(), rfl⟩).card)
#eval check "trace-effect-replay"
  (replayRow (replay (.running (tagged.initial (noInput tagged (fun _ => rfl))))
    taggedResult.events))
  ("running", [some 0, some 14, some 0], 0)

end LeanNCD.Semantics.ExecutableReferenceFixtures
