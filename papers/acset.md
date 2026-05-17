# Separating Structure from Data in St via Acsets

## Reference

Patterson, Lynch, Fairbanks (2022). *Categorical Data Structures for Technical Computing*. Compositionality 4(5). [arXiv:2106.04703](https://arxiv.org/abs/2106.04703)

Their central construction is the **acset**: a schema category $\mathcal{S}$ separates combinatorial structure (a C-set / copresheaf) from typed data attributes, with data migration as adjoint triples along schema morphisms.

---

## Motivation

In a stride morphism $\Lambda : P \to Q$ there are two kinds of information:

| Kind | Examples |
| --- | --- |
| **Structure** | which axis slots exist; which input slots feed which output slots; the coefficient values $\Lambda_{ij}$ |
| **Data** | the concrete size of each axis slot ($\lvert A_i \rvert \in \mathbb{N}_{>0}$) |

The practical motivation: a computation graph (conv stride, dilation, window shift) is fixed at design time. Axis sizes vary across tensor instances. The acset pattern encodes exactly this split.

---

## Step 1: Define the Structural Category $\mathbf{St}_\sharp$

**Objects** — finite index sets $I$ (axis slot labels with no sizes attached).

**Morphisms** $\sigma : I \to J$ — $\mathbb{N}$-matrices with shape $I \times J$, i.e., the coefficient table $(\sigma_{ij})$ stripped of any size information. Composition = matrix multiplication; identities = identity matrices.

This is just **St** with all `Numeric` size fields erased. The category is well-defined because composition (matrix multiplication) depends only on the coefficient values, not on axis sizes.

---

## Step 2: Model St Objects as Acsets

Define schema $\mathcal{S}_{Ax}$ as the category with:
- One entity type: `Axis`
- One discrete attribute type: `Size` (= $\mathbb{N}_{>0}$)
- One attribute map: `size : Axis -> Size`

A **St object** (a product of axes) is an instance of $\mathcal{S}_{Ax}$: a finite set of axis slots each carrying a concrete size. Formally, this is a functor $F : |\mathcal{S}_{Ax}| \to \mathbf{Set}$ fixing `Size` $\mapsto \mathbb{N}_{>0}$.

---

## Step 3: Model St Morphisms as Acsets

Define schema $\mathcal{S}_{Str}$ with:
- Entity types: `DomAxis`, `CodAxis`, `Entry`
- Relation maps: `row : Entry -> DomAxis`, `col : Entry -> CodAxis`
- Attribute types: `Size` ($\mathbb{N}_{>0}$), `Coeff` ($\mathbb{N}$)
- Attribute maps: `dom_size : DomAxis -> Size`, `cod_size : CodAxis -> Size`, `coeff : Entry -> Coeff`

A **stride morphism** is an instance: sets of domain/codomain axis slots with sizes, and a set of entries (the support of $\Lambda$) carrying coefficients. A dense matrix uses `Entry` $= I \times J$ with the natural projections.

The structural part (the C-set under the acset) = the bipartite multigraph of slots and connections, without sizes or coefficients. The data = the attribute assignments.

---

## Step 4: Recover St via the Grothendieck Construction

Define a functor

$$D : \mathbf{St}_\sharp \to \mathbf{Disc}$$

where $\mathbf{Disc}$ is the category of discrete categories (sets with no non-identity morphisms), and $D(I) = \mathbb{N}_{>0}^I$ (the set of size assignments to axis slots in $I$).

For a morphism $\sigma : I \to J$ in $\mathbf{St}_\sharp$, domain and codomain sizes are **independent** — no constraint forces them to be related by $\sigma$ — so $D(\sigma)$ is trivial: it does not transform sizes. Sizes are pure attributes, not functorially related by morphisms. This is exactly why the acset model (attributes as a separate layer) fits better than a plain presheaf.

The **Grothendieck construction** $\int D$ then has:
- Objects: pairs $(I,\, s : I \to \mathbb{N}_{>0})$ — a slot set with sizes
- Morphisms $(I, s) \to (J, t)$: a matrix $\Lambda \in \mathbb{N}^{I \times J}$ (no compatibility condition between $s$ and $t$)

This recovers **St** up to isomorphism.

---

## Step 5: Schema Morphisms and Data Migration

Following the paper, a **schema morphism** $f : \mathcal{S} \to \mathcal{S}'$ induces an adjoint triple

$$\Sigma_f \dashv f^* \dashv \Pi_f$$

between instance categories. For St this means:

- **Pullback** ($f^*$): forget sizes — extract the structural skeleton of a morphism
- **Left adjoint** $\Sigma_f$: freely generate a sized morphism from a structural pattern
- **Right adjoint** $\Pi_f$: compute the tightest size assignment on the codomain compatible with $\sigma$ — relevant for shape inference in a neural network compiler

---

## Key Design Decision

There is one question to settle before implementation: **do the coefficients $\Lambda_{ij}$ belong to the structural layer or the data layer?**

| Choice | Structural morphism | Data |
| --- | --- | --- |
| **A** (sizes only as data) | full $\mathbb{N}$-matrix $\Lambda$ | axis sizes |
| **B** (support + data) | support graph (0/1) | sizes + coefficients |

Choice A matches the practical DL case (stride amounts are fixed at graph-compile time; sizes vary). Choice B gives a more uniform acset with fewer assumptions. The functoriality proof in [functor_proof.md](functor_proof.md) works for either, since associativity of matrix multiplication is structural in both.

---

## Next Steps

1. Settle the Choice A vs B question
2. Define `StSharp` as a Python dataclass — an `Axis` without `_size`, a `StridePattern` without `Numeric` coefficients
3. Define the acset schema $\mathcal{S}_{Str}$ and verify instances round-trip to current `StrideMorphism`
4. Extend to **Br**: the same split applies — `Array` shape as structural, element values as data — and the contravariant functor $[a,\cdot]$ acts purely on the structural layer
