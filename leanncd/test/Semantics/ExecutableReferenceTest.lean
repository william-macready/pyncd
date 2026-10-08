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

end LeanNCD.Semantics.ExecutableReferenceFixtures
