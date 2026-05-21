# Lean 4 Encoding of the NCD Category Framework

This document describes a Lean 4 formalisation of the categorical framework introduced in *Weaves, Wires, and Morphisms* (Abbott & Zardini, 2026). The goal is to show how the core structures — the product category framework, the axis-stride category **St**, and the array-broadcasted category **Br** — can be expressed as inhabitants of a small typeclass hierarchy built around two definitions: `SmallCategory` and `PROP`.

## Contents

1. [Two-layer architecture](#two-layer-architecture)
2. [Layer 1 — Mathematical Encoding](#layer-1--mathematical-encoding)
   - [1. SmallCategory](#1-smallcategory)
   - [2. PROP](#2-prop)
   - [3. Numeric](#3-numeric)
   - [4. St — Semantic Category via Stride Matrices](#4-st--semantic-category-via-stride-matrices)
   - [5. Br — Free Category over Broadcasted Base Morphisms](#5-br--free-category-over-broadcasted-base-morphisms)
   - [6. Design Contrast](#6-design-contrast)
   - [7. The St → Br Embedding](#7-the-st--br-embedding)
   - [8. Correspondence with the Python Implementation](#8-correspondence-with-the-python-implementation)
   - [9. Paper Definitions in Lean](#9-paper-definitions-in-lean)
3. [Layer 2 — Representation](#layer-2--representation)
   - [1. `DynamicName`](#1-dynamicname)
   - [2. `UID` and the `TermM` monad](#2-uid-and-the-termm-monad)
   - [3. `WithUID` — the generic decoration](#3-withuid--the-generic-decoration)
   - [4. `TermTraversable` — replacing `deep_reconstruct`](#4-termtraversable--replacing-deep_reconstruct)
   - [5. `Context` — pure functional union-find](#5-context--pure-functional-union-find)
   - [6. Correspondence with the Python Term System](#6-correspondence-with-the-python-term-system)
   - [7. What Layer 2 leaves unchanged](#7-what-layer-2-leaves-unchanged)
4. [Summary](#summary)

---

## Two-layer architecture

The formalisation separates into two independent layers that address different concerns. Understanding this separation is the key to reading everything that follows.

**Layer 1 — Mathematical Encoding** formalises the categorical structure: what objects and morphisms *are*, what laws they satisfy, and how they compose. Its types — `Axis`, `StMat`, `BrBase`, `BrMorph` — are pure mathematical objects. They carry no display information, no unique identity beyond structural equality, and no notion of "these two axes are the same symbolic variable". Layer 1 can be used as-is for formal proof.

**Layer 2 — Representation** adds three things on top of Layer 1 without touching any mathematical content:

1. **Naming.** A `DynamicName` can be attached to any Layer 1 value for LaTeX rendering and diagram display. It is purely aesthetic.

2. **Identity.** A `UID` makes a Layer 1 value uniquely identifiable. Two `Axis` values that are structurally different records but carry the same UID are the *same symbolic axis* — they are degrees of freedom that have been equated. This is the mechanism behind `FreeNumeric` and unnamed `RawAxis` values in pyncd.

3. **Alignment.** A `Context` (a union-find over UIDs) records which UIDs have been equated and provides a substitution that replaces every member of an equivalence class with a single canonical representative. This is what happens during `@` composition when two morphisms share axes.

The relationship between the layers is a wrapping, not an extension. Every Layer 1 type `α` gains a Layer 2 decorated counterpart `WithUID α` that bundles a `UData` (UID + optional name) with the Layer 1 value. The mathematical content — the PROP laws, the `StMat` arithmetic, the `BrMorph` list structure — is entirely in the `.val` field and is never altered by Layer 2 operations.

The Python implementation conflates these layers via inheritance (`Axis` extends `UTerm` which extends `Term`). Lean 4 keeps them separate by composition, which makes the boundary explicit and keeps Layer 1 independently verifiable.

---

## Layer 1 — Mathematical Encoding

### 1. SmallCategory

Following [Holtzen (2025)](https://sholtzen.dev/articles/leancat-1.html), categories are encoded as a Lean 4 typeclass parameterised by an object type `ob : Type`.

```lean
class SmallCategory (ob : Type) : Type 1 where
  hom     : ob → ob → Type
  id      : ∀ x, hom x x
  comp    : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z
  id_comp : ∀ {X Y} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : hom X Y), comp f (id Y) = f
  assoc   : ∀ {W X Y Z} (f : hom W X) (g : hom X Y) (h : hom Y Z),
              comp (comp f g) h = comp f (comp g h)

infixl:65 " ⟶ " => SmallCategory.hom
notation:65 a " ∘ " b => SmallCategory.comp b a
```

Three design points are worth noting.

**Objects as types.** The object type `ob` is an element of Lean's `Type`, so it can itself be a Lean program — a list, a record, an inductive. Both **St** and **Br** exploit this: their objects are `List`-based structures, so the monoidal product on objects is definitionally list concatenation.

**Morphisms as semantic types.** For **St**, morphisms will be stride matrices; for **Br**, morphisms will be a free-list construction. In both cases the morphism type carries enough structure that the category laws are either immediate from ring axioms (St) or from list induction (Br), with no quotient required.

**Laws are propositions.** `id_comp`, `comp_id`, and `assoc` are propositional equalities to be discharged by tactics. For Br all three reduce to `rfl` or one-step induction.

**Python counterpart.** Python has no typeclass encoding for `SmallCategory`. Categories emerge implicitly from the `@` operator and `Composed` wrapper; the laws `id_comp`, `comp_id`, and `assoc` are never stated or enforced in the Python codebase.

---

### 2. PROP

Both **St** and **Br** are *product categories*: their objects are finite products of lone objects, and the monoidal product is tuple concatenation (theory.md §3). This places them in a more specific structure than a general monoidal category — they are **PROPs** (PRoduct and Permutation categories): strict symmetric monoidal categories in which every object is a tensor power of a generator.

```lean
class PROP (ob : Type) extends SmallCategory ob where
  /-- The generating lone-object type (= L in the paper). -/
  gen    : Type
  /-- Objects are lists of generators. -/
  toList : ob → List gen
  ofList : List gen → ob
  /-- Monoidal product = list concatenation. -/
  tensor : ob → ob → ob := fun a b => ofList (toList a ++ toList b)
  unit   : ob            := ofList []
  /-- Strictness: associator and unitors are definitional equalities. -/
  tensor_assoc  : ∀ a b c : ob, tensor (tensor a b) c = tensor a (tensor b c)
  tensor_unit_l : ∀ a : ob, tensor unit a = a
  tensor_unit_r : ∀ a : ob, tensor a unit = a
  /-- Symmetric structure: swap is always a morphism. -/
  swap : ∀ a b : ob, hom (tensor a b) (tensor b a)
  /-- Tensoring morphisms (bifunctoriality). -/
  tensorHom : ∀ {a b c d : ob}, hom a b → hom c d → hom (tensor a c) (tensor b d)
```

For both **St** and **Br**, `ob = List gen`, so `toList = id` and `ofList = id`. The three strictness laws reduce to `List.append_assoc`, `List.nil_append`, and `List.append_nil`, all dischargeable by `simp`. The `swap` morphism is a `Rearrangement` that interleaves or separates the two sub-lists.

The PROP typeclass earns its keep in three ways.

1. **Generic rearrangements.** Any list permutation induces a morphism in any PROP. Proved once, it applies to both **St** and **Br**.

2. **The St → Br relationship.** The `reindexings` field inside a `Broadcasted` root morphism is exactly a family of **St** morphisms living inside a **Br** morphism. This is the data of a lax monoidal functor `St → Br`, expressible generically once both are PROP instances.

3. **Interchange.** The law $(f  ;  g) \otimes (h  ;  k) = (f \otimes h)  ;  (g \otimes k)$ holds in any PROP and can be proved once from `tensorHom` and `assoc`.

**Python counterpart.** No Python class corresponds to `PROP`. The shared monoidal structure is a paper-level concept: objects of both **St** and **Br** are `ProdObject[L]` terms (wrapping `tuple[L, ...]`) and the tensor product is implicitly tuple concatenation, but the strictness laws (`tensor_assoc`, `tensor_unit_l`, `tensor_unit_r`) and the `swap` morphism have no Python witness.

---

### 3. Numeric

Both **St** and **Br** rely on symbolic dimension expressions — axis sizes and stride coefficients are not concrete natural numbers but terms in a free commutative semiring. The right type for this is Mathlib's `MvPolynomial String ℕ` — multivariate polynomials over $\mathbb{N}$ with `String`-named indeterminates — which is already a `CommSemiring` by Mathlib's instance, requires no additional proof work, and covers the Python `Numeric` term hierarchy (`Integer`, `FreeNumeric`, `Addition`, `Multiplication`, `Power`) uniformly:

```lean
abbrev Numeric := MvPolynomial String ℕ
-- free variable s  ↦  MvPolynomial.X s     (a degree-1 monomial)
-- literal n        ↦  MvPolynomial.C ↑n    (a constant polynomial)
-- addition, multiplication ↦ ring operations
-- instance : CommSemiring Numeric           -- free from Mathlib
-- instance : DecidableEq Numeric            -- free from Mathlib
```

This is the minimal type that makes `StMat`'s category laws provable: it is the free commutative semiring on a `String`-indexed set of generators, which is exactly the algebraic structure that symbolic axis sizes inhabit. The `ring` tactic works immediately over any `CommSemiring`, so all three `StMat` laws discharge without any further setup.

Symbolic dimension variables correspond to the `FreeNumeric` UTerm in pyncd: a `FreeNumeric` is a unique, uninterpreted size that gets unified with a concrete value once an axis is configured. In Lean, `MvPolynomial.X s` plays the same role — `s` is a name, and the polynomial carries no interpretation until it is evaluated by substituting concrete values for the indeterminates.

---

### 4. St — Semantic Category via Stride Matrices

**St** instantiates PROP with `gen = Axis`. Its objects are shapes (lists of axes) and its morphisms are affine coordinate transforms, stored as stride matrices over `Numeric`.

#### Objects

```lean
structure Axis where
  name : Option String
  size : Numeric      -- symbolic; filled in at configuration time

abbrev StObj := List Axis  -- a shape = an ordered list of axes
```

**Python counterparts.** `Axis` corresponds to the abstract `Axis` `UTerm` subclass (backed by `RawAxis`), which additionally carries `uid: UID[Axis]` for alignment — the UID is Layer 2 and is absent from the Lean `Axis` record. `StObj = List Axis` corresponds to `ProdObject[Axis]` (a `Term` wrapping `content: tuple[Axis, ...]`).

#### Morphisms

A morphism `dom → cod` in **St** is a matrix $\Lambda \in \mathbb{N}^{|cod| \times |dom|}$ of `Numeric` coefficients (plus a bias vector). Each row $j$ gives the linear combination of input coordinates that produces output coordinate $j$:

$$\bigl(\Pi_{i} e_i\bigr)  ;  \eta = \Pi_{j}\Bigl(v^\eta_j + \textstyle\sum_{i} \Lambda^\eta_{ji} \cdot e_i\Bigr)$$

Using Mathlib's `Matrix` type for the coefficient block gives the composition law for free:

```lean
structure StMat (dom cod : StObj) where
  coeffs : Matrix (Fin cod.length) (Fin dom.length) Numeric
  bias   : Fin cod.length → Numeric

def StMat.id (a : StObj) : StMat a a where
  coeffs := 1        -- Matrix.one : Matrix (Fin n) (Fin n) Numeric
  bias _ := 0

def StMat.comp (f : StMat a b) (g : StMat b c) : StMat a c where
  coeffs := g.coeffs * f.coeffs                               -- Matrix.mul
  bias i := Matrix.dotProduct (g.coeffs i) f.bias + g.bias i -- ∑_k g[i,k] * f.bias[k] + g.bias[i]
```

`Matrix.mul` from Mathlib is `(A * B) i j = ∑_k A i k * B k j`, matching the standard formula. `Matrix.dotProduct v w = ∑_k v k * w k` handles the bias update.

**Python counterpart.** `StMat` corresponds to `StrideMorphism[A]`. Python bundles codomain axes and coefficient rows as `_cod_stride: Prod[tuple[Axis, Prod[Numeric]]]` rather than separating them into a `Matrix` type with a distinct `bias` vector; bounds are checked at construction via `from_matrix` rather than enforced by `Fin` indices. Composition of two `StrideMorphism`s multiplies their coefficient matrices directly, matching `StMat.comp`.

#### Category instance

```lean
instance St : PROP StObj where
  gen    := Axis
  toList := id
  ofList := id
  hom    := StMat
  id     := StMat.id
  comp   := StMat.comp
  -- Coefficient laws: Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc (Mathlib).
  -- Bias laws: dotProduct linearity, discharged by ring over CommSemiring Numeric.
  id_comp       := by intro _ _ f; simp [StMat.comp, StMat.id, Matrix.one_mul,
                                          Matrix.dotProduct_zero]
  comp_id       := by intro _ _ f; simp [StMat.comp, StMat.id, Matrix.mul_one,
                                          Matrix.dotProduct, Finset.sum_ite_eq']
  assoc         := by intro _ _ _ _ f g h; simp [StMat.comp, Matrix.mul_assoc,
                                                   Matrix.dotProduct_mulVec]; ring
  tensor_assoc  := by simp [List.append_assoc]
  tensor_unit_l := by simp
  tensor_unit_r := by simp [List.append_nil]
  swap a b      := ⟨Matrix.reindex ..., fun i => 0⟩   -- permutation matrix, zero bias
  tensorHom f g :=                                      -- block-diagonal
    { coeffs := Matrix.fromBlocks f.coeffs 0 0 g.coeffs
      bias   := Fin.append f.bias g.bias }
```

All six laws discharge using Mathlib's `Matrix` API: `Matrix.one_mul`, `Matrix.mul_one`, and `Matrix.mul_assoc` handle the coefficient block; `ring` over `CommSemiring Numeric` closes the bias terms. `Matrix.fromBlocks` constructs the block-diagonal for `tensorHom`; `Matrix.reindex` produces the permutation matrix for `swap`.

---

### 5. Br — Free Category over Broadcasted Base Morphisms

**Br** instantiates PROP with `gen = ArrayType`. Because there is no single canonical way to compose two arbitrary broadcasted operations into a third, **Br** morphisms are represented as a free list — the Lean 4 analog of `Composed[Array[B,A], Broadcasted[B,A]]` in pyncd. This makes all three category laws trivial list lemmas, with no `sorry`.

#### Br Objects

```lean
inductive DType
  | reals
  | nat : Numeric → DType           -- Natural(max_value)

structure ArrayType where
  dtype : DType
  shape : StObj                     -- shape lives in Ob(St)

abbrev BrObj := List ArrayType      -- a product of arrays
```

**Python counterparts.** `DType` corresponds to `Datatype` / `Reals` / `Natural` (where `Natural` stores `max_value: Numeric`); `ArrayType` corresponds to `Array[B, A]`, parametric over `B: Datatype` and a list of axes `A`; `BrObj = List ArrayType` corresponds to `ProdObject[Array[B,A]]`.

#### Base morphisms — Broadcasted

A single `BrBase` is the root morphism of **Br**, corresponding to `Broadcasted` in pyncd. It bundles one base operation together with its reindexings (from **St**), input weaves, and output weaves.

```lean
inductive WeaveSlot
  | fixed : Axis → WeaveSlot   -- retained axis: the reindexing selects a value for this axis at each degree step
  | tiled : WeaveSlot           -- contracted axis: the base op processes the full extent of this axis

abbrev Weave := List WeaveSlot

def Weave.targetAxes (w : Weave) : StObj :=
  w.filterMap fun | .fixed a => some a | _ => none

structure BrBase (dom cod : BrObj) where
  op           : String
  degree       : StObj                          -- shared loop shape P
  inputWeaves  : Fin dom.length → Weave
  outputWeaves : Fin cod.length → Weave
  -- Each reindexing is a St morphism P → (target axes of that input's weave).
  -- This is the locus where St lives inside Br.
  reindexings  : ∀ i : Fin dom.length,
                   StMat degree (inputWeaves i).targetAxes
```

The `reindexings` field precisely captures the four cases from the paper: identity, deletion (broadcast), duplication (diagonal), and affine scaling (strided convolution). Each is a different `StMat`.

**Python counterparts.** `WeaveSlot.fixed a` (retained axis) corresponds to `WeaveMode.TILED` in Python's `Weave._shape` — both mark a slot that the outer reindexing loop fills at runtime. `WeaveSlot.tiled` (contracted axis) corresponds to a concrete `Axis` object in `Weave._shape` — both indicate an axis the base op processes in full. The naming is inverted across the boundary: Python `TILED` = Lean `fixed`; Python concrete `Axis` slot = Lean `tiled`. `Weave` corresponds to `Weave[B, A]` (Python additionally stores `datatype: B`, which Lean omits). `BrBase` corresponds to `Broadcasted[B, A, O]` — `op` maps to `operator: O`, `degree` to `Broadcasted.degree()`, `inputWeaves`/`outputWeaves` to `input_weaves`/`output_weaves`, and `reindexings` to `reindexings: Prod[StrideCategory[A]]`.

#### Morphisms — free list

```lean
inductive BrMorph : BrObj → BrObj → Type
  | nil  : (a : BrObj) → BrMorph a a
  | cons : BrBase a b → BrMorph b c → BrMorph a c

def BrMorph.comp : BrMorph a b → BrMorph b c → BrMorph a c
  | .nil _,     g => g
  | .cons f fs, g => .cons f (BrMorph.comp fs g)
```

This is exactly the free category on `BrBase`: morphisms are lists of base operations threaded sequentially (with `nil` as the empty identity), and composition is list concatenation.

**Python counterparts.** `BrMorph.nil a` corresponds to an identity `Rearrangement` (permutation = `(0,1,2,...)`); `BrMorph.cons f fs` corresponds to `Composed[L, M]`, which stores `content: tuple[M, ...]` — a flat tuple rather than a linked list. Both representations are syntactic; two structurally distinct expressions can denote equal category-theoretic morphisms.

#### Br Category instance

```lean
instance Br : PROP BrObj where
  gen    := ArrayType
  toList := id
  ofList := id
  hom    := BrMorph
  id     := .nil
  comp   := BrMorph.comp
  -- nil ++ g = g definitionally:
  id_comp := by intros; rfl
  -- f ++ nil = f, by induction on f:
  comp_id := by
    intro _ _ f; induction f with
    | nil _      => rfl
    | cons _ _ ih => simp [BrMorph.comp, ih]
  -- list concatenation is associative, by induction on f:
  assoc := by
    intro _ _ _ _ f _ _; induction f with
    | nil _      => rfl
    | cons _ _ ih => simp [BrMorph.comp, ih]
  tensor_assoc  := by simp [List.append_assoc]
  tensor_unit_l := by simp
  tensor_unit_r := by simp [List.append_nil]
  swap a b      := .cons ⟨"swap", [], ..., ...⟩ (.nil _)
  tensorHom f g := ...   -- run f and g in parallel via ProductOfMorphisms
```

No `sorry` appears. The category laws are discharged by `rfl` or one-step structural induction, because list concatenation is already associative and `nil` is already a two-sided unit — definitionally.

---

### 6. Design Contrast

The two instances exhibit a complementary split.

| | **St** | **Br** |
| --- | --- | --- |
| Generator type | `Axis` | `ArrayType` |
| Root morphism | `StMat` (stride matrix) | `BrBase` (operator + reindexings) |
| Composition | `Matrix.mul` + `dotProduct` | list concatenation |
| Category law proofs | Mathlib (`Matrix.mul_assoc`, `ring`) | `rfl` / list induction |
| St inside Br | — | `reindexings` field of `BrBase` |

**St is semantic.** A stride morphism is the denotation of a coordinate transform, not a syntax tree. Composition collapses immediately to a single `Matrix.mul` call. The laws are proved using Mathlib's `Matrix` API together with `ring` over `CommSemiring Numeric` (supplied by `MvPolynomial String ℕ`).

**Br is syntactic (free).** A composed sequence of broadcasted operations is stored as a list; there is no canonical "simplified form" for an arbitrary composition. The laws are free gifts from list algebra. The price is that symbolic reasoning about Br morphisms requires pattern-matching over the list rather than inspecting a single record.

This split mirrors the Python implementation exactly: `StrideMorphism` instances are composed by directly multiplying their coefficient matrices, while `Broadcasted` instances are composed by wrapping them in `Composed([b1, b2, ...])`.

---

### 7. The St → Br Embedding

Because both **St** and **Br** are PROP instances, the relationship between them is expressible as a monoidal functor.

```lean
structure MonoidalFunctor (C D : PROP) where
  obj    : C.ob → D.ob
  map    : C.hom a b → D.hom (obj a) (obj b)
  map_id : map (SmallCategory.id a) = SmallCategory.id (obj a)
  map_comp : map (f ∘ g) = map f ∘ map g
  -- monoidal coherence
  map_tensor : map (C.tensorHom f g) = D.tensorHom (map f) (map g)
  map_unit   : obj C.unit = D.unit
```

The embedding sends a **St** morphism $\eta : P \to Q$ to the **Br** morphism consisting of a single `BrBase` with identity operator, one input array (a scalar array indexed by $Q$), one output array (indexed by $P$), and `reindexings = [η]`. This makes explicit that **Br** generalises **St**: every pure index transform is a degenerate broadcasted operation with no actual computation.

---

### 8. Correspondence with the Python Implementation

The Lean encoding targets the *mathematical* layer of the framework — what the paper calls $\Gamma$, the set of mathematical entities — while the Python implementation also contains a *representation* layer $G$ (the term system). Understanding where the two layers sit is the key to reading the correspondence table below.

**Layer 1 — mathematical entities (encoded in both Lean and Python)**
Objects, morphisms, and the categorical structure that relates them. This is what `SmallCategory`, `PROP`, `StMat`, and `BrBase` formalise.

**Layer 2 — representation / term system (Python: `Term`/`UTerm` hierarchy; Lean: Layer 2 of this document)**
In Python, a grammar of `Term` and `UTerm` subclasses in [data_structure/Term.py](../data_structure/Term.py) provides: frozen dataclass identity, a `TermDirectory` for serialisation, `DynamicName` for LaTeX/diagram rendering, `UID` integers for axis identity tracking, and `Context` / `EqualityClass` (a union-find over UIDs) for the axis alignment that `@` composition triggers. The Lean equivalents are described in Layer 2 below.

#### Correspondence table

| Lean | Python | Notes |
| --- | --- | --- |
| `SmallCategory ob` | implicit (no base class) | Python categories are not a typeclass; the laws are not stated |
| `PROP ob` | `ProductCategory` (paper §3) | No Python class; the shared monoidal structure is a paper-level concept only |
| `List gen` (objects) | `ProdObject[L]` | Python wraps `tuple[L,...]` in a Term dataclass; Lean uses `List` directly |
| `Numeric = MvPolynomial String ℕ` | `Numeric` (abstract), `Integer`, `Addition`, `Multiplication`, `Power` | Python has n-ary `Addition`/`Multiplication` and `Power`; Lean aliases the Mathlib type `MvPolynomial String ℕ`, which is the free commutative semiring on `String` generators and already carries all required instances. |
| `MvPolynomial.X s` | `FreeNumeric` | Python `FreeNumeric` is a `UTerm` carrying a random integer `UID`; Lean uses `MvPolynomial.X s` (a degree-1 monomial). UIDs enable unification via `Context`; Lean uses symbolic names and `Context` separately. |
| `Axis` | `Axis` (abstract UTerm), `RawAxis` | Python carries `uid: UID[Axis]` for alignment; Lean carries only `name` and `size` |
| `StObj = List Axis` | `ProdObject[Axis]` | Python: `content: tuple[Axis,...]` inside a Term; Lean: bare list |
| `StMat (dom cod)` | `StrideMorphism[A]` | See §8.2 below |
| `DType` | `Datatype`, `Reals`, `Natural` | Near 1:1; Python `Natural` stores `max_value: Numeric` |
| `ArrayType` | `Array[B, A]` | Python parametric over `B: Datatype` and `A: Axis`; Lean uses a flat record |
| `BrObj = List ArrayType` | `ProdObject[Array[B,A]]` | Same object-wrapper difference as for St |
| `WeaveSlot` | `Axis \| WeaveMode.TILED` | Python encodes slots as a union type in `Weave._shape: Prod[A \| WeaveMode]`; Lean uses an inductive. Convention inverted: Python `TILED` = Lean `.fixed` (retained); Python concrete `Axis` slot = Lean `.tiled` (contracted) |
| `Weave` | `Weave[B, A]` | Python also stores `datatype: B`; Lean's `Weave` is shape-only |
| `BrBase (dom cod)` | `Broadcasted[B, A, O]` | See §8.3 below |
| `BrMorph.nil` | identity `Rearrangement` (mapping = `(0,1,2,...)`) | Python identity is a Rearrangement with the identity permutation; Lean `nil` is a single constructor |
| `BrMorph.cons f fs` | `Composed[L, M]` | Python stores `content: tuple[M, ...]`; Lean uses a linked list |
| `PROP.tensorHom` | `ProductOfMorphisms[L, M]` | Python stores as a data wrapper (`content: tuple[M,...]`); Lean is a typeclass operation producing a morphism |
| `PROP.swap` | `Rearrangement` (swap permutation) | Python rearrangements are first-class morphisms; Lean `swap` is a typeclass field |
| `Block[L,M]` (Python) | *not encoded* | `Block` is display metadata (`title`, `fill_color`, `repetition`); semantically transparent, not part of the mathematical encoding |
| `Context` / `EqualityClass` | Layer 2 `Context` | UID union-find for axis alignment; described in Layer 2 §5 |
| `MonoidalFunctor St Br` | implicit in `Broadcasted.reindexings` | Python embeds St inside Br via the `reindexings: Prod[StrideCategory[A]]` field; Lean makes this a first-class functor |

#### StMat vs StrideMorphism

Both represent the same affine coordinate transform $(\Pi_i e_i) ; \eta = \Pi_j(v^\eta_j + \sum_i \Lambda^\eta_{ji} \cdot e_i)$.

| Aspect | Python `StrideMorphism` | Lean `StMat` |
| --- | --- | --- |
| Domain | `_dom: Prod[Axis]` — runtime tuple | `dom : StObj` — compile-time index type |
| Codomain + coefficients | `_cod_stride: Prod[tuple[Axis, Prod[Numeric]]]` — axis and its coefficient row bundled together | `coeffs : Matrix (Fin cod.length) (Fin dom.length) Numeric` and `bias : Fin cod.length → Numeric` — separated; `Matrix` indexing enforces bounds |
| Matrix bounds | checked at construction / `from_matrix` call | enforced by `Fin` — index-out-of-bounds is a type error |
| Composition | coefficient matrices multiplied directly (`from_matrix` on the result) | `StMat.comp` uses `Matrix.mul` for coefficients; `cod` of `f` must equal `dom` of `g` at the type level |
| Law proofs | not stated | `Matrix.mul_assoc` + `ring` over `MvPolynomial String ℕ`; no `sorry` |
| Name / display | `name: DynamicName \| None` | not encoded (Layer 2) |

Using Mathlib's `Matrix` type rather than a bare function `Fin m → Fin n → Numeric` gives immediate access to the standard library of matrix lemmas. In particular, `Matrix.mul_assoc` directly discharges the associativity obligation for coefficients, and `Matrix.fromBlocks` constructs the block-diagonal for `tensorHom` without manual index arithmetic.

#### BrBase vs Broadcasted

| Aspect | Python `Broadcasted[B,A,O]` | Lean `BrBase (dom cod)` |
| --- | --- | --- |
| Operator | `operator: O` (an `Operator` subclass instance) | `op : String` (simplified; Python operators carry signature logic) |
| Degree | computed by `degree()` as `iallequals(m.dom() for m in reindexings)` at runtime | `degree : StObj` — an explicit field, checked at construction |
| Input weaves | `input_weaves: Prod[Weave[B,A]]` — length must match `dom.length` at runtime | `inputWeaves : Fin dom.length → Weave` — `Fin`-indexed, length match is a type error |
| Output weaves | `output_weaves: Prod[Weave[B,A]]` — same | `outputWeaves : Fin cod.length → Weave` — same |
| Reindexings | `reindexings: Prod[StrideCategory[A]]` — one St morphism per input; `degree()` checks they all share the same domain | `reindexings : ∀ i : Fin dom.length, StMat degree (inputWeaves i).targetAxes` — the domain is `degree`, the codomain must equal the target axes of weave `i`; both enforced by the type |

The most significant difference is in `reindexings`. Python computes `degree` lazily via `iallequals` (which raises if the reindexings disagree), and there is no static guarantee that each reindexing's codomain matches its weave's target axes. Lean encodes both constraints in the type of the field: the `∀ i` quantifier ensures one reindexing per input slot, `degree` fixes the shared domain, and `(inputWeaves i).targetAxes` is the exact required codomain.

#### The five morphism forms

Python's `ProdCategory[L, M]` is a recursive type alias with five forms. Their Lean counterparts are spread across different parts of the encoding.

| Python form | Where it lives in Lean |
| --- | --- |
| `M` (root morphism — `StrideMorphism` or `Broadcasted`) | The payload of `BrMorph.cons`; equivalently, `BrBase` for Br and `StMat` for St |
| `Rearrangement[L]` | A special `StMat` (permutation matrix) in St; a `BrBase` with identity operator in Br; also the `PROP.swap` typeclass field |
| `Composed[L, M]` | `BrMorph` itself — the linked-list structure *is* the composition chain |
| `ProductOfMorphisms[L, M]` | `PROP.tensorHom` — a typeclass operation, not a data constructor |
| `Block[L, M]` | Not encoded — display metadata only |

The most important shift is `Composed`. Python stores composition as a data wrapper (a tuple of morphisms), which means two expressions that are equal as category-theoretic composites — `Composed([f, Composed([g, h])])` and `Composed([f, g, h])` — are structurally distinct Python objects. Lean's free-list `BrMorph` representation has the same property (it is, after all, a syntax tree), but the category laws prove that the two are equal as morphisms — the list structure is not observable from outside the category.

---

### 9. Paper Definitions in Lean

This section works through the paper's definition hierarchy (§§3–4 of *Weaves, Wires, and Morphisms*) and records what each mathematical statement becomes in the Lean encoding, and what Lean adds that the paper leaves informal.

#### 9.1 Product categories (paper §3)

The paper defines $\mathbf{Prod}[L, M]$ as a monoidal category whose objects are finite products of lone objects and whose monoidal product is tuple concatenation. The `PROP` typeclass encodes this directly.

| Paper | Lean | How it is captured |
| --- | --- | --- |
| Lone-object type $L$ | `PROP.gen : Type` | A typeclass field; filled by `Axis` for St, `ArrayType` for Br |
| Object $A = \Pi_{i \in I} L_i$ | `a : List gen` | A list of generators; `List.length` gives $\lvert I \rvert$ |
| Unit object $\mathbf{1} = \Pi_{\emptyset}$ | `[] : List gen` | The empty list, equal to `PROP.unit` |
| Monoidal product $A \otimes B$ | `a ++ b` | List concatenation; `PROP.tensor a b := ofList (toList a ++ toList b)` |
| Strict associativity $(A \otimes B) \otimes C = A \otimes (B \otimes C)$ | `PROP.tensor_assoc` | Proved by `simp [List.append_assoc]` |
| Strict unitality $\mathbf{1} \otimes A = A$ | `PROP.tensor_unit_l` | Proved by `simp` |
| Root morphism $m \in M$ | `BrBase a b` / `StMat a b` | The concrete payload type; one per category |
| Sequential composition $f  ;  g$ | `SmallCategory.comp f g` | The `comp` field of the `SmallCategory` typeclass |
| Parallel product $f \otimes g$ | `PROP.tensorHom f g` | A typeclass operation; for St it builds a block-diagonal matrix |
| Bifunctoriality $(f  ;  g) \otimes (h  ;  k) = (f \otimes h)  ;  (g \otimes k)$ | Theorem from `tensorHom` + `assoc` | Not a typeclass field — derivable |
| Rearrangement $[\mu]_{(A_i)} : \Pi_I A_i \to \Pi_J A_{\mu(j)}$ | `PROP.swap` (binary); permutation `StMat` (St) | For St, $[\mu]$ is the matrix with $\Lambda_{ji} = \mathbb{1}[\mu(j) = i]$ and $v = 0$ |
| Identity morphism $\text{id}_A$ | `SmallCategory.id a` | `BrMorph.nil a` for Br; `StMat.id a` for St |
| Category axioms (id, assoc) | `id_comp`, `comp_id`, `assoc` | Propositions proved by tactics; `rfl`/induction for Br, `ring` for St |

The paper states "St and Br are product categories" as a claim; Lean makes it a proof obligation. Providing the `PROP` instance forces the author to exhibit the identity, composition, and bifunctoriality witnesses and prove the six equational laws.

#### 9.2 The axis-stride category St (paper Def 8)

Def 8 introduces **St** as a Cartesian product category. Its objects are axes and products of axes; its morphisms are finite affine transforms.

**Objects.** An axis $A$ carries a UID and a size $|A| \in \mathbb{N}$ (itself a symbolic `Numeric`). In Lean, the UID is dropped (it belongs to Layer 2) and an axis is just a name–size pair:

$$A \in \text{Ob}\mathbf{St} \;\longleftrightarrow\; \texttt{a : Axis}$$

A shape $\Pi_{i \in I} A_i$ is $\texttt{List Axis}$, with $|I|$ given by `List.length`.

**Morphisms.** A finite affine transform $\eta : \Pi_{i \in I} A_i \to \Pi_{j \in J} B_j$ is specified by a coefficient matrix $\Lambda^\eta \in \mathbb{N}^{J \times I}$ and a bias $v^\eta \in \mathbb{N}^J$:

$$\bigl(\Pi_i e_i\bigr)  ;  \eta = \Pi_j\Bigl(v^\eta_j + \textstyle\sum_i \Lambda^\eta_{ji} \cdot e_i\Bigr)$$

In Lean this becomes:

| Paper | Lean | Note |
| --- | --- | --- |
| $\eta : \Pi_I A_i \to \Pi_J B_j$ | `StMat (dom cod : StObj)` | The dom/cod types index the matrix dimensions |
| $\Lambda^\eta \in \mathbb{N}^{J \times I}$ | `coeffs : Matrix (Fin cod.length) (Fin dom.length) Numeric` | Mathlib `Matrix`; `Fin` bounds make out-of-range indexing a type error |
| $v^\eta \in \mathbb{N}^J$ | `bias : Fin cod.length → Numeric` | Kept separate from `coeffs` |
| $\text{id}_A$ (identity transform) | `StMat.id` with `coeffs = Matrix.one`, `bias = 0` | `Matrix.one` is the identity matrix; `Matrix.one_mul`/`mul_one` discharge the unit laws |
| $\eta  ;  \theta$ (composition) | `StMat.comp f g` | `coeffs := g.coeffs * f.coeffs` (Matrix.mul); `bias i := dotProduct (g.coeffs i) f.bias + g.bias i` |
| Associativity of $;$ | `PROP.assoc` proved by `Matrix.mul_assoc` + `ring` | Coefficients: `Matrix.mul_assoc`; bias: distributivity of `dotProduct`, discharged by `ring` |

**What Lean adds.** The paper states the composition formula and asserts associativity. Lean requires a proof: with `Numeric := MvPolynomial String ℕ` and `coeffs : Matrix _ _ Numeric`, associativity of the coefficient block is `Matrix.mul_assoc` from Mathlib (no tactic needed), and the bias identity follows from `ring` over the `CommSemiring Numeric` instance that Mathlib provides for `MvPolynomial`. All three laws discharge without any `sorry`.

#### 9.3 Reindexing and batch lift (paper Defs 10–11)

These two definitions describe how a base operation is lifted to run over a degree shape P (a product of one or more loop axes).

**Def 10 — Reindexing.** A reindexing $[a, \eta] : [a, \text{dom}(\eta)] \to [a, \text{cod}(\eta)]$ applies a stride transform $\eta \in \mathbf{St}$ to the shape of an array $[a, \cdot]$ while leaving the datatype $a$ unchanged. In the Lean encoding this is not a standalone morphism type but a sub-component of `BrBase`: the `reindexings` field provides one `StMat` per input, mapping the shared degree $P$ to the input's tiling axes.

**Def 11 — Batch lift.** A batch lift $[f, P]$ runs base operation $f$ once for each coordinate $p \in P$ (the *degree*). In the Lean encoding $P$ is `BrBase.degree : StObj` and the "running once per coordinate" is expressed structurally: the `reindexings` field supplies, for each input $i$, the stride transform $\eta_i : P \to Q_i$ that selects which slice of input $i$ to read at each loop step $p$.

| Paper | Lean | Note |
| --- | --- | --- |
| Degree shape $P$ | `BrBase.degree : StObj` | Explicit field; shared by all reindexings |
| Reindexing $\eta_i : P \to Q_i$ | `reindexings i : StMat degree (inputWeaves i).targetAxes` | The domain is always `degree`; the codomain is the target axes of weave $i$, computed from `inputWeaves` |
| "All reindexings share domain $P$" | Enforced by the type of `reindexings` | In Python this is checked at runtime by `iallequals`; in Lean it is a compile-time constraint |

#### 9.4 Weaves (paper Def 12)

A weave classifies each axis of an array as either a *target* (retained) axis — selected by the reindexing at each degree step — or a *tiling* (contracted) axis processed over its full extent by the base op.

| Paper | Lean | Note |
| --- | --- | --- |
| $w_i = 1$ (target axis) | `WeaveSlot.fixed a` | Retained axis: the reindexing maps a degree coordinate to this axis at each step |
| $w_i = 0$ (tiling axis) | `WeaveSlot.tiled` | Contracted axis: a sentinel — no reindexing row targets it; the base op processes its full extent |
| Weave $(w_i)_{i \in I}$ | `Weave := List WeaveSlot` | One slot per axis of the array |
| Target axes $A$ (sub-shape selected by reindexing) | `Weave.targetAxes w` | `w.filterMap (·.fixed?)` — extracts all `.fixed` slots |
| Tiling axes $Q$ (sub-shape processed by base op) | `Fin domain − targetAxes` | Not computed separately; implicit in the `tiled` slots |
| Unweave permutation $\Omega_w$ | Not encoded | Would be a derived `StMat` permuting target axes to the front; needed for the full $\text{dom}(F)$ formula |

The paper computes $\text{dom}(F)$ for a broadcasted operation $F$ via the unweave permutation $\Omega_{s_i}$, which gathers all target axes before all tiling axes. The Lean encoding does not yet compute `dom` from `inputWeaves`; it accepts `dom` as an index parameter to `BrBase` and relies on the user supplying a consistent value. A complete encoding would add a derived function:

```lean
def BrBase.inferDom (b : BrBase dom cod) : BrObj :=
  List.ofFn fun i =>
    let w := b.inputWeaves i
    let tilingAxes := b.reindexings i |>.cod
    ⟨dom[i].dtype, w.targetAxes ++ tilingAxes⟩
```

and a well-formedness condition `b.inferDom = dom`.

#### 9.5 Broadcasted operations (paper Def 13)

Def 13 assembles Defs 9–12 into the root morphism of **Br**:

$$F : \Pi_{i \in I}\!\left[a_i,\text{dom}\!\left([\Omega_{s_i}]_{A_i \otimes Q_i}\right)\right] \longrightarrow \Pi_{j \in J}\!\left[b_j,\text{dom}\!\left([\Omega_{t_j}]_{B_j \otimes P}\right)\right]$$

| Paper ingredient | Lean field in `BrBase` | Type |
| --- | --- | --- |
| Base operator | `op` | `String` (simplified; full encoding would be a type of operator signatures) |
| Index set $I$ (inputs) | `Fin dom.length` | Implicit in `dom : BrObj` |
| Index set $J$ (outputs) | `Fin cod.length` | Implicit in `cod : BrObj` |
| Datatypes $a_i$ | `dom[i].dtype` | `DType` |
| Degree $P$ | `degree` | `StObj` |
| Input weaves $(s_i)_{i \in I}$ | `inputWeaves` | `Fin dom.length → Weave` |
| Output weaves $(t_j)_{j \in J}$ | `outputWeaves` | `Fin cod.length → Weave` |
| Reindexings $(\eta_i)_{i \in I}$ | `reindexings` | `∀ i, StMat degree (inputWeaves i).targetAxes` |
| Full domain type $[a_i, \text{dom}(\Omega_{s_i})]$ | `dom[i]` | `ArrayType` — encoding assumes it is supplied consistently with the weave |

#### 9.6 What Lean formalises that the paper leaves informal

| Paper claim | Status in Lean |
| --- | --- |
| "St is a (product) category" | **Proved**: `instance St : PROP StObj` with all six laws discharged |
| "Br is a (product) category" | **Proved**: `instance Br : PROP BrObj` with all six laws discharged |
| Bifunctoriality of $\otimes$ | **Derivable** from `PROP.tensorHom` and `assoc` |
| Matrix bounds for $\Lambda^\eta$ | **Enforced by type**: `Matrix (Fin cod.length) (Fin dom.length) Numeric` |
| All reindexings share domain $P$ | **Enforced by type**: `∀ i, StMat degree ...` fixes `degree` as the domain |
| Reindexing codomain matches weave | **Enforced by type**: `(inputWeaves i).targetAxes` is the required codomain |
| $\text{dom}(F)$ is consistent with weaves | **Not yet enforced**: requires `inferDom` plus a well-formedness proof |
| Composition of `StMat` is associative | **Proved**: `Matrix.mul_assoc` (coefficients) + `ring` (bias) |
| Composition of `BrMorph` is associative | **Proved** by list induction; holds definitionally |
| `Numeric` forms a commutative semiring | **Provided by Mathlib**: `Numeric := MvPolynomial String ℕ` |

All obligations in the framework are discharged. `CommSemiring Numeric` is provided by the alias `Numeric := MvPolynomial String ℕ`, the free commutative semiring on `String`-named generators, which already carries the required instance in Mathlib. With this in place:

- The coefficient block of `StMat.comp` is `Matrix.mul`, and `StMat.assoc` for coefficients is `Matrix.mul_assoc` — a Mathlib theorem, not a tactic proof.
- The bias terms in `StMat.assoc` reduce to a `ring` goal over `CommSemiring Numeric`; `ring` closes it immediately.
- `BrMorph` laws remain structural (list induction, `rfl`) and require no arithmetic at all.

The only remaining informal item is `dom(F)` consistency — the well-formedness condition that the supplied `dom : BrObj` agrees with what the weaves and reindexings imply. This is a structural property of `BrBase` construction rather than an arithmetic one, and is left as a future addition (see §9.4 for the `inferDom` sketch).

---

## Layer 2 — Representation

### 1. `DynamicName`

`DynamicName` is a structured name for display purposes. It translates directly from Python as a recursive inductive:

```lean
structure DynamicNameSettings where
  bold     : Bool := false
  overline : Bool := false
  absolute : Bool := false   -- renders as |name|

inductive DynamicName where
  | mk : (body     : Option String)
       → (subscript : Option DynamicName)
       → (settings  : Option DynamicNameSettings)
       → DynamicName

def DynamicName.toLaTeX : DynamicName → String
  | .mk none _ _          => ""
  | .mk (some b) none s   => applySettings s b
  | .mk (some b) (some sub) s =>
      applySettings s b ++ "_{"
        ++ (sub.lineage.map (fun d => d.toLaTeX) |>.intercalate "") ++ "}"

def DynamicName.lineage : DynamicName → List DynamicName
  | .mk none _ _            => []
  | .mk _ none _  as d      => [d]
  | .mk _ (some sub) _ as d => d :: sub.lineage
```

Python's `DynamicName.from_str "h_i"` convention (underscore splits body from subscript) becomes a smart constructor:

```lean
def DynamicName.ofStr (s : String) : DynamicName :=
  match s.splitOn "_" with
  | []     => .mk none none none
  | [b]    => .mk (some b) none none
  | b :: rest => .mk (some b) (some (DynamicName.ofStr (rest.intercalate "_"))) none
```

**Python counterpart.** `DynamicName` is a near 1:1 translation of the Python class of the same name. `DynamicNameSettings` directly translates `bold`, `overline`, and `absolute`. `DynamicName.ofStr` corresponds to `DynamicName.from_str` (both split on `_` to build subscript chains). See §6 for the full correspondence table.

---

### 2. `UID` and the `TermM` monad

In Python, UIDs are random integers generated as a construction side-effect (`random.randint`). Lean 4 is pure; fresh generation requires threading state explicitly. The representation monad is a simple counter:

```lean
abbrev UID := ℕ

structure UData where
  uid  : UID
  name : Option DynamicName

abbrev TermM := StateM ℕ

def freshUData : TermM UData := do
  let n ← get
  set (n + 1)
  return ⟨n, none⟩

def UData.stamp (d : UData) (name : DynamicName) : UData :=
  { d with name := some name }
```

Any code that constructs a new symbolic axis or free numeric variable runs in `TermM`. Code that only *uses* existing values (composition, evaluation, proof) is pure and stays in `TermM`-free context. This makes the boundary between "constructing new degrees of freedom" and "reasoning about existing ones" syntactically visible in the types.

The choice of a counter rather than random integers makes term construction reproducible and testable. UIDs carry no semantic content — only the equality or inequality of two UIDs matters, not their absolute values.

---

### 3. `WithUID` — the generic decoration

Python uses inheritance to attach identity to Layer 1 types. Lean 4 uses a generic wrapper:

```lean
structure WithUID (α : Type*) where
  data : UData
  val  : α       -- the Layer 1 value, unchanged

instance : Functor WithUID where
  map f w := { w with val := f w.val }

def WithUID.stamp (name : DynamicName) (w : WithUID α) : WithUID α :=
  { w with data := w.data.stamp name }
```

Concrete decorated types are aliases:

```lean
abbrev UAxis        := WithUID Axis
abbrev UFreeNumeric := WithUID Numeric
```

**Python counterparts.** `UAxis := WithUID Axis` corresponds to `Axis` (which extends `UTerm` via inheritance — the Python `Axis` *is* a `UTerm`, whereas `UAxis` *wraps* an `Axis` in a separate struct); `UFreeNumeric := WithUID Numeric` corresponds to `FreeNumeric` (a `UTerm` subclass carrying no fields beyond `uid`).

Construction always runs in `TermM`:

```lean
def UAxis.fresh (size : Numeric) : TermM UAxis := do
  return ⟨← freshUData, ⟨none, size⟩⟩

def UAxis.named (name : String) (size : Numeric) : TermM UAxis := do
  let d ← freshUData
  return ⟨d.stamp (DynamicName.ofStr name), ⟨some name, size⟩⟩
```

The Layer 1 `Axis` record is never modified. Proofs about `StMat` laws, for instance, refer only to `Axis` values and are oblivious to `UData`.

---

### 4. `TermTraversable` — replacing `deep_reconstruct`

Python's `deep_reconstruct` traverses any `Term` tree by inspecting `__dataclass_fields__` at runtime. Lean 4 has no runtime reflection; each type that contains decorated subterms needs an explicit traversal instance.

```lean
/-- Map a function over all UData fields reachable from a value. -/
class TermTraversable (T : Type*) where
  traverseUID : (UData → UData) → T → T
```

Instances for the decorated Layer 1 types:

```lean
instance : TermTraversable UAxis where
  traverseUID f a := { a with data := f a.data }

instance : TermTraversable (List UAxis) where
  traverseUID f axes := axes.map (TermTraversable.traverseUID f)

instance : TermTraversable (WithUID Numeric) where
  traverseUID f n := { n with data := f n.data }
```

For compound types that contain decorated subterms at multiple sites:

```lean
instance : TermTraversable (BrBase dom cod) where
  traverseUID f b := { b with
    degree      := TermTraversable.traverseUID f b.degree
    inputWeaves := fun i => TermTraversable.traverseUID f (b.inputWeaves i) }
```

The verbosity compared to Python's one-liner is the cost; the gain is that the Lean compiler checks exhaustiveness — a new decorated field added to `BrBase` causes a compile error in this instance until the traversal is updated.

---

### 5. `Context` — pure functional union-find

Python's `Context` is a mutable list of `EqualityClass`es. The Lean 4 version is a pure functional structure. Since axis alignment is the primary use case, and all aligned values share type `UAxis`, a per-type context is sufficient in practice:

```lean
/-- A single equivalence class: a set of UIDs with one canonical decorated value. -/
structure EqClass (α : Type*) where
  bucket    : Finset UID
  canonical : WithUID α   -- representative chosen by largest UID, as in Python

/-- A context is a disjoint list of equality classes. -/
structure Context (α : Type*) where
  classes : List (EqClass α)

def Context.empty : Context α := ⟨[]⟩

/-- Merge a new class into the context, unioning with any overlapping classes. -/
def Context.merge (ctx : Context α) (cls : EqClass α) : Context α :=
  let overlapping := ctx.classes.filter (fun c => ¬ c.bucket.Disjoint cls.bucket)
  let merged : EqClass α := overlapping.foldl
    (fun acc c => ⟨acc.bucket ∪ c.bucket,
                   if acc.canonical.data.uid ≥ c.canonical.data.uid
                   then acc.canonical else c.canonical⟩)
    cls
  ⟨merged :: ctx.classes.filter (fun c => c.bucket.Disjoint cls.bucket)⟩

/-- Substitute all members of every class with their canonical representative. -/
def Context.apply [TermTraversable α] (ctx : Context α) (target : α) : α :=
  ctx.classes.foldl (fun t cls =>
    TermTraversable.traverseUID
      (fun d => if d.uid ∈ cls.bucket then cls.canonical.data else d) t)
    target
```

`Context.merge` corresponds to Python's `Context.append_bucket`. `Context.apply` has the same name in Python and the same semantics: substitute every UID in each class with its canonical representative throughout a term tree. The canonical representative is the member with the largest UID, matching Python's `max(..., key=lambda uterm: uterm.uid)`.

---

### 6. Correspondence with the Python Term System

#### Overall table

| Lean | Python | Notes |
| --- | --- | --- |
| `WithUID α` | `UTerm` (via inheritance) | Python attaches identity by subclassing `UTerm`; Lean wraps the Layer 1 value in a generic struct |
| `UData` | `UID[T]` | Python's `UID` bundles type, integer id, and optional name; Lean's `UData` bundles a counter id and an optional `DynamicName` — the type is carried by `WithUID`'s type parameter `α` |
| `UID = ℕ` | `UID._id : int` (random) | Python generates UIDs via `random.randint`; Lean uses a monotone counter in `TermM`. Both satisfy the only requirement: two UIDs are equal iff they identify the same symbolic entity. |
| `TermM = StateM ℕ` | implicit side-effect at construction | Python mutates a global random source; Lean threads a counter through a state monad. Construction of new degrees of freedom is syntactically marked in Lean by the `TermM` return type. |
| `DynamicName` | `DynamicName` | Near 1:1. Both are recursive structures with `body`, `subscript`, and display settings. |
| `DynamicNameSettings` | `DynamicNameSettings` | Direct translation: `bold`, `overline`, `absolute`. |
| `DynamicName.ofStr` | `DynamicName.from_str` | Python splits on `_` to build subscript chains; Lean `ofStr` does the same. |
| `WithUID.stamp` / `UData.stamp` | `DynamicName.capture` | Python's `capture` reconstructs the target with a new UID `_name`; Lean's `stamp` updates `UData.name` in place on the wrapper. |
| `TermTraversable` typeclass | `deep_reconstruct` | Python traverses any `Term` tree via `__dataclass_fields__` reflection; Lean requires an explicit instance per type. See §6.2. |
| `EqClass α` | `EqualityClass[T]` | Both hold a set of UIDs and a canonical representative. Python picks the representative by `max(uid)`. Lean does the same. |
| `Context α` | `Context` | Both are collections of disjoint equality classes. Python stores a heterogeneous list; Lean is per-type. See §6.3. |
| `Context.merge` | `Context.append_bucket` | Both merge a new class into the collection, unioning with any overlapping existing classes. |
| `Context.apply` | `Context.apply` | Both substitute every member of each class with its canonical representative throughout a term tree. |
| `UAxis := WithUID Axis` | `Axis` (extends `UTerm`) | In Python, `Axis` *is* a UTerm; in Lean, `UAxis` *wraps* an `Axis`. The Layer 1 `Axis` record is untouched. |
| `UFreeNumeric := WithUID Numeric` | `FreeNumeric` | Python `FreeNumeric` is a `UTerm` subclass with no fields beyond `uid`; Lean `UFreeNumeric` wraps a `Numeric.var` value. |
| — | `Term` base class | No Lean equivalent. Python's `Term` provides `reconstruct`, `keys`, `dict`, and `TermDirectory` registration. Lean has no need for runtime introspection; `TermTraversable` covers the traversal use case, and typeclass resolution covers dispatch. |
| — | `TermDirectory` | No Lean equivalent. Python maintains a global `{classname: Type}` dict for serialisation. Lean would use typeclass resolution for any serialisation layer. |

#### UID and UTerm: inheritance vs composition

As noted in §3, Python attaches identity via **inheritance** (`Axis` extends `UTerm` extends `Term`) while Lean uses **composition** (`UAxis = WithUID Axis`). The consequence for proof: a Lean lemma over `Axis` cannot accidentally mention `UData`; the compiler enforces the separation. In Python, `uid` is silently present on every `Axis` and simply ignored during mathematical reasoning.

The more subtle difference is **UID generation**. Python generates UIDs as random integers at construction — a side-effect invisible in the type. Two calls to `RawAxis()` produce distinct objects regardless of their fields. Lean makes this explicit: constructing a `UAxis` requires running in `TermM`, and the counter value at that point determines the UID. Two values from different `TermM` runs are incomparable until their UIDs are explicitly unified via `Context`.

#### `deep_reconstruct` vs `TermTraversable`

Python's `deep_reconstruct(target, func)` applies `func` to every subterm of `target` by inspecting `target.__dataclass_fields__` at runtime. It works uniformly across all `Term` subclasses with no per-type code.

Lean has no runtime reflection. `TermTraversable` is an explicit typeclass:

```lean
class TermTraversable (T : Type*) where
  traverseUID : (UData → UData) → T → T
```

Each type that contains `UData` fields must provide an instance listing exactly which fields to traverse. This is verbose — Python's one-liner becomes one instance per type — but the Lean compiler checks exhaustiveness. If a new `UData`-bearing field is added to `BrBase`, the existing `TermTraversable (BrBase dom cod)` instance fails to compile until it is updated. Python's `deep_reconstruct` would silently traverse the new field without any notification.

The two approaches reflect a general tradeoff between generic programming via reflection (Python, concise but unverified) and generic programming via typeclasses (Lean, explicit but compiler-checked).

#### `Context`: mutable list vs pure functional

Python's `Context` is a mutable object. `append_bucket` modifies `self.equality_classes` in place by merging overlapping classes. Callers share a single `Context` instance and observe each other's mutations.

Lean's `Context α` is an immutable record. `Context.merge` returns a new `Context` with the merged class; the original is unchanged. This means axis alignment during composition must be threaded explicitly — the `Context` produced by one step is passed as an argument to the next, rather than being accumulated in a shared mutable store.

The practical consequence is that Lean composition returning an aligned result has type `StObj → StObj → TermM (BrMorph a b × Context UAxis)` rather than mutating a global context. This is more verbose but makes the data flow explicit and allows multiple independent alignments to coexist without interference.

---

### 7. What Layer 2 leaves unchanged

The point of the wrapping architecture is that Layer 1 stays untouched. The following table shows which obligations belong to which layer:

| Concern | Layer |
| --- | --- |
| PROP laws, category axioms | Layer 1 — proved once, referenced by Layer 2 |
| `StMat` composition and `ring` obligations | Layer 1 |
| `BrMorph` list-induction laws | Layer 1 |
| UID generation, freshness | Layer 2 — `TermM` monad |
| Naming and LaTeX rendering | Layer 2 — `DynamicName` |
| Axis alignment after composition | Layer 2 — `Context.apply` |
| Decorated construction (`UAxis.fresh`) | Layer 2 — runs in `TermM` |
| Term traversal for substitution | Layer 2 — `TermTraversable` instances |

A proof that "stride matrix composition is associative" (`StMat.assoc`) lives entirely in Layer 1 and refers to `Axis` values, not `UAxis` values. A program that "computes the output shape after aligning two morphisms" lives in Layer 2 and calls `Context.apply`. Neither layer needs to look inside the other.

---

## Summary

The full typeclass hierarchy for the NCD framework in Lean 4 is:

```text
SmallCategory ob
    └── PROP ob
            ├── instance St  : PROP StObj    (gen = Axis,      hom = StMat)
            └── instance Br  : PROP BrObj    (gen = ArrayType, hom = BrMorph)
```

`SmallCategory` provides the categorical skeleton. `PROP` adds the strict symmetric monoidal structure that both **St** and **Br** share — list-concatenation as tensor product, swap morphisms, and bifunctoriality of `tensorHom`. The two concrete instances diverge: **St** uses Mathlib's `Matrix` type for coefficients and `MvPolynomial String ℕ` for scalars, so its laws are proved via `Matrix.mul_assoc` and `ring` with no `sorry`; **Br** uses the free-list construction whose laws are structural (`rfl`, list induction). The `reindexings` field in `BrBase` is the precise locus at which **St** lives inside **Br**, and the `MonoidalFunctor St Br` makes that embedding first-class.

Layer 2 sits on top of this hierarchy without modifying it, adding `WithUID` decoration, `DynamicName` rendering, and `Context`-based alignment. The boundary between the layers is enforced by type: Layer 1 types (`Axis`, `StMat`, `BrBase`) carry no `UData`; Layer 2 types (`UAxis`, `Context`) carry no category laws.
