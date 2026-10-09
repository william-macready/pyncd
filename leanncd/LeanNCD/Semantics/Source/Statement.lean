import LeanNCD.Semantics.Source.Admission

namespace LeanNCD.Semantics.Source

variable {K : Type} [Semiring K] {σ : Declarations Unit}
  {r : Registry (fun _ : Unit => K)}

def reductionReads : (bound : Shape) → (Coord bound → List (Address σ)) →
    List (Address σ)
  | [], reads => reads ()
  | a :: rest, reads =>
    (List.finRange a.extent).flatMap fun i => reductionReads rest (fun p => reads (i, p))

theorem footprint_product (reads : List (Read ctx σ)) (env : Γ → Coord ctx) (γ : Γ) :
    footprint (product (K := K) (r := r) reads env) γ =
      reads.map (fun read => ⟨read.tensor, read.slots.project (env γ)⟩) := by
  induction reads with
  | nil => rfl
  | cons read reads ih =>
    simp [product, readExpr, footprint, ih]

theorem footprint_contract (bound : Shape) (reads : List (Read ctx σ))
    (env : Γ → Coord bound → Coord ctx) (γ : Γ) :
    footprint (contract (K := K) (r := r) bound reads env) γ =
      reductionReads bound
        (fun p => reads.map (fun read => ⟨read.tensor, read.slots.project (env γ p)⟩)) := by
  induction bound generalizing Γ with
  | nil => exact footprint_product reads (fun γ => env γ ()) γ
  | cons a rest ih =>
    simp only [contract, footprint, reductionReads]
    congr 1
    funext i
    exact ih (fun γ p => env γ.1 (γ.2, p)) (γ, i)

def Term.environment (term : Term source out σ) (x : Coord out.axes)
    (p : Coord term.partition.bound) : Coord term.partition.context.axes :=
  term.partition.context_axes.symm ▸
    (appendEquiv out.axes term.partition.bound).symm (x, p)

def Term.body (term : Term source out σ) (env : Γ → Coord out.axes) :
    Expr (fun _ => K) σ r Γ (.scalar ()) :=
  contract term.partition.bound term.operands (fun γ => term.environment (env γ))

def Term.value (term : Term source out σ) (ρ : Store (fun _ => K) σ)
    (x : Coord out.axes) : K :=
  ∑ p : Coord term.partition.bound, operandProduct ρ term.operands (term.environment x p)

def Term.readAddresses (term : Term source out σ)
    (v : Coord term.partition.context.axes) : List (Address σ) :=
  List.ofFn fun i => ⟨(term.sourceReads.get i).read.tensor, (term.reads i).slots.project v⟩

def Term.readFootprint (term : Term source out σ) (x : Coord out.axes) : List (Address σ) :=
  reductionReads term.partition.bound (fun p => term.readAddresses (term.environment x p))

theorem Term.interpret_body (term : Term source out σ) (ρ : Store (fun _ => K) σ)
    (env : Γ → Coord out.axes) (γ : Γ) :
    interpret semiringOps ρ (term.body (r := r) env) γ = some (term.value ρ (env γ)) :=
  interpret_contract ρ term.partition.bound term.operands
    (fun γ => term.environment (env γ)) γ

theorem Term.footprint_body (term : Term source out σ) (env : Γ → Coord out.axes) (γ : Γ) :
    footprint (term.body (K := K) (r := r) env) γ = term.readFootprint (env γ) := by
  simpa [Term.body, Term.readFootprint, Term.readAddresses, Term.operands,
    LocalizedRead.read, List.map_ofFn] using
    footprint_contract (K := K) (r := r) term.partition.bound term.operands
      (fun γ => term.environment (env γ)) γ

theorem Term.readAddresses_pullback (term : Term source out σ) (v : UIDVal source) :
    term.readAddresses
      (uidCoordEquiv term.partition.context (indexPullback term.partition.embedding.map v)) =
      term.sourceReads.map
        (fun read => ⟨read.read.tensor, read.read.slots.project (uidCoordEquiv source v)⟩) := by
  unfold Term.readAddresses
  conv_rhs => rw [← List.ofFn_get term.sourceReads, List.map_ofFn]
  congr 1
  funext i
  congr 1
  exact term.read_projection i v

def sumBody (terms : List (Term source out σ)) (env : Γ → Coord out.axes) :
    Expr (fun _ => K) σ r Γ (.scalar ()) :=
  match terms with
  | [] => .lit 0
  | term :: terms => .binary .add (term.body env) (sumBody terms env)

theorem interpret_sumBody (terms : List (Term source out σ)) (ρ : Store (fun _ => K) σ)
    (env : Γ → Coord out.axes) (γ : Γ) :
    interpret semiringOps ρ (sumBody (r := r) terms env) γ =
      some ((terms.map (fun term => term.value ρ (env γ))).sum) := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    have ht := term.interpret_body (r := r) ρ env γ
    unfold interpret at ht ih
    simp [sumBody, interpret, evalWith, ht, ih,
      ScalarOps.combine, semiringOps]

theorem footprint_sumBody (terms : List (Term source out σ))
    (env : Γ → Coord out.axes) (γ : Γ) :
    footprint (sumBody (K := K) (r := r) terms env) γ =
      terms.flatMap (fun term => term.readFootprint (env γ)) := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [sumBody, footprint, Term.footprint_body, List.flatMap_cons, ih]

def AdmittedStatement.body (statement : AdmittedStatement source)
    (env : Γ → Coord statement.output.context.axes) :
    Expr (fun _ => K) source.table.declarations r Γ (.scalar ()) :=
  sumBody statement.terms env

def AdmittedStatement.destination (statement : AdmittedStatement source)
    (x : Coord statement.output.context.axes) :
    Coord (source.table.declarations.signature statement.output.tensor).axes :=
  statement.output.slots.project x

theorem AdmittedStatement.interpret_body (statement : AdmittedStatement source)
    (ρ : Store (fun _ => K) source.table.declarations)
    (env : Γ → Coord statement.output.context.axes) (γ : Γ) :
    interpret semiringOps ρ (statement.body (r := r) env) γ =
      some ((statement.terms.map (fun term => term.value ρ (env γ))).sum) :=
  interpret_sumBody statement.terms ρ env γ

theorem AdmittedStatement.footprint_body (statement : AdmittedStatement source)
    (env : Γ → Coord statement.output.context.axes) (γ : Γ) :
    footprint (statement.body (K := K) (r := r) env) γ =
      statement.terms.flatMap (fun term => term.readFootprint (env γ)) :=
  footprint_sumBody statement.terms env γ

theorem AdmittedStatement.destination_pullback (statement : AdmittedStatement source)
    (v : UIDVal source.context) :
    statement.destination
      (uidCoordEquiv statement.output.context
        (indexPullback statement.output.embedding.map v)) =
      statement.output.sourceSlots.project (uidCoordEquiv source.context v) :=
  statement.output.projection v

end LeanNCD.Semantics.Source
