# Separating Structure from Data in St and Br via Acsets

## Reference

Patterson, Lynch, Fairbanks (2022). *Categorical Data Structures for Technical Computing*. Compositionality 4(5). [arXiv:2106.04703](https://arxiv.org/abs/2106.04703)

Their central construction is the **acset**: a schema category $\mathcal{S}$ separates combinatorial structure (a C-set / copresheaf) from typed data attributes, with data migration as adjoint triples along schema morphisms.

---

## Motivation

The **acset pattern** separates combinatorial *structure* — which entities exist and how they connect — from typed *data* — values assigned freely to those entities. The same principle applies to both **St** and **Br**.

| | Structure | Data |
| --- | --- | --- |
| **St** morphism | support graph: which domain axes feed which codomain axes | axis sizes; transformation coefficients |
| **Br** morphism | arrays and their axes; reindexing support graph | axis sizes; reindexing coefficients; weave roles (`is_target`); input/output flags (`is_input`); datatype bounds (`max_value`) |

In both cases the connectivity is fixed at graph-compile time — which axes exist, which inputs feed which outputs, which axes are looped over. The numeric and Boolean values vary across instances. The acset pattern encodes exactly this split, and exposes the data layer as queryable and migratable via adjoint triples along schema morphisms.

---

## St

### The Schema $\mathcal{S}_{St}$

$\mathcal{S}_{St}$ models a stride morphism as a weighted directed multigraph on axis nodes: each nonzero entry of the coefficient matrix becomes an edge.

$$\texttt{Entry} \underset{\texttt{tgt}}{\overset{\texttt{src}}{\rightrightarrows}} \texttt{Axis} \xrightarrow{\texttt{size}} \mathbb{N}_{>0} \qquad \texttt{Entry} \xrightarrow{\texttt{coeff}} \mathbb{N}$$

Two entity types (`Axis`, `Entry`), two attribute types ($\mathbb{N}_{>0}$, $\mathbb{N}$), four maps. A single schema covers both St objects and St morphisms.

**Attributes (data):**

| Attribute | Type | What it captures |
| --- | --- | --- |
| `size` | `Axis → ℕ_{>0}` | axis size |
| `coeff` | `Entry → ℕ` | transformation coefficient |

The **C-set part** (structure) = the directed multigraph on `Axis` with edges `Entry` — the support graph of the stride morphism, with both size and coefficient values erased.

**St objects** are instances with `Entry` = ∅ — a set of axes with sizes and no morphism data. The 28×28 RGB image:

| `Axis` | `size` |
| --- | --- |
| $a_0$ | 28 |
| $a_1$ | 28 |
| $a_2$ | 3 |

**St morphisms** are instances where `Entry` ≠ ∅. For $\Lambda = \begin{pmatrix} 2 & 0 \\ 1 & 3 \end{pmatrix}$ with domain sizes $(4, 6)$ and codomain sizes $(5, 7)$:

| `Axis` | `size` |
| --- | --- |
| $a_0$ | 4 |
| $a_1$ | 6 |
| $a_2$ | 5 |
| $a_3$ | 7 |

| `Entry` | `src` | `tgt` | `coeff` |
| --- | --- | --- | --- |
| $e_0$ | $a_0$ | $a_2$ | 2 |
| $e_1$ | $a_1$ | $a_2$ | 1 |
| $e_2$ | $a_1$ | $a_3$ | 3 |

The zero entry $\Lambda_{01} = 0$ is absent — support is sparse by default. Domain = image of `src` = $\{a_0, a_1\}$; codomain = image of `tgt` = $\{a_2, a_3\}$. Since both domain and codomain axes live in the same `Axis` table, sizes are readable from any `Entry` by following `src` or `tgt`.

---

## Br

### The Schema $\mathcal{S}_{Br}$

$\mathcal{S}_{Br}$ shares the `Axis`-centred reindexing structure of $\mathcal{S}_{St}$ but replaces `Entry` with `Sample` and adds two new entity types — `Array` and `ArrayAxis` — to carry the full reindexing structure of a `Broadcasted` morphism.

In $\mathcal{S}_{St}$, the analogous entity type is called `Entry` because each row is a nonzero entry of a coefficient matrix. In $\mathcal{S}_{Br}$, the same structure plays a different role: each row specifies one axis-component of how a particular input array is **sampled** at each step of the degree loop. The triple (`src`, `tgt`, `coeff`) says "for array $X$, the index into axis `tgt` equals `coeff` times the degree index along axis `src`" — it is a sampling rule, not a matrix entry in the abstract algebraic sense. The name `Sample` reflects this: each row is one component of the sampling pattern that determines which slice of an input the base operation sees at each loop iteration.

$$\texttt{Sample} \underset{\texttt{tgt}}{\overset{\texttt{src}}{\rightrightarrows}} \texttt{Axis} \xleftarrow{\texttt{axis}} \texttt{ArrayAxis} \xrightarrow{\texttt{array}} \texttt{Array}$$

$$\texttt{Sample} \xrightarrow{\texttt{reindexing\_of}} \texttt{Array}$$

$$\texttt{Sample} \xrightarrow{\texttt{coeff}} \mathbb{N} \qquad \texttt{Axis} \xrightarrow{\texttt{size}} \mathbb{N}_{>0} \qquad \texttt{ArrayAxis} \xrightarrow{\texttt{is\_target}} \mathbb{B} \qquad \texttt{Array} \xrightarrow{\texttt{is\_input}} \mathbb{B} \qquad \texttt{Array} \xrightarrow{\texttt{max\_value}} \mathbb{N}$$

Four entity types, three attribute types ($\mathbb{N}$, $\mathbb{N}_{>0}$, $\mathbb{B}$), ten maps. `max_value` is a partial map defined only for `Natural`-typed arrays.

**Attributes (data):**

| Attribute | Type | What it captures |
| --- | --- | --- |
| `size` | `Axis → ℕ_{>0}` | axis size |
| `coeff` | `Sample → ℕ` | reindexing coefficient |
| `is_target` | `ArrayAxis → Bool` | target axis (True) or tiling / TILED (False) |
| `is_input` | `Array → Bool` | input array (True) or output array (False) |
| `max_value` | `Array → ℕ` | Natural datatype bound; partial — undefined for Real arrays |

The **C-set part** (structure) = the reindexing multigraph on `Axis` (analogous to `Entry ⇉ Axis` in $\mathcal{S}_{St}$), the bipartite graph linking each `ArrayAxis` to its `Array` and its `Axis`, and the `reindexing_of` map assigning each `Sample` to the array whose reindexing it belongs to.

**Example instance** — batched linear with a per-batch weight matrix $Y[b,j] = \sum_i X[b,i]\,W[b,i,j]$, degree $P = (b)$, reindexings $\eta_X = \mathrm{id}_{(b)}$ and $\eta_W = \mathrm{id}_{(b)}$ (both inputs sliced along $b$ at each loop step):

| `Axis` | `size` |
| --- | --- |
| $a_b$ | 32 |
| $a_i$ | 64 |
| $a_j$ | 128 |

| `Array` | `is_input` |
| --- | --- |
| $X$ | True |
| $W$ | True |
| $Y$ | False |

| `ArrayAxis` | `array` | `axis` | `is_target` |
| --- | --- | --- | --- |
| $xa_b$ | $X$ | $a_b$ | False |
| $xa_i$ | $X$ | $a_i$ | True |
| $wa_b$ | $W$ | $a_b$ | False |
| $wa_i$ | $W$ | $a_i$ | True |
| $wa_j$ | $W$ | $a_j$ | True |
| $ya_b$ | $Y$ | $a_b$ | False |
| $ya_j$ | $Y$ | $a_j$ | True |

| `Sample` | `src` | `tgt` | `coeff` | `reindexing_of` |
| --- | --- | --- | --- | --- |
| $s_0$ | $a_b$ | $a_b$ | 1 | $X$ |
| $s_1$ | $a_b$ | $a_b$ | 1 | $W$ |

Both $\eta_X$ and $\eta_W$ are the identity on $b$, so each contributes one sample. The two rows are identical in `src`, `tgt`, and `coeff` — only `reindexing_of` distinguishes them, which is exactly why that column is necessary. The degree $P = (b)$ is the image of `src` across all samples. Tiling axes of each array are the `ArrayAxis` rows where `is_target = False`; their reindexing coordinates are supplied by the `Sample` rows with matching `reindexing_of` via `tgt`.

---

## The Acset Framework

### The Grothendieck Construction

The schemas $\mathcal{S}_{St}$ and $\mathcal{S}_{Br}$ are type templates for individual instances. To see how all instances form a category, it helps to introduce a complementary notion — the **structural skeleton** $\mathbf{C}_\sharp$ (bold, with sharp subscript). This is a local notational convention, not from Patterson et al.

**$\mathbf{C}_\sharp$ — structural skeleton.** Given a category $\mathbf{C}$ whose morphisms carry both combinatorial structure and numeric/Boolean data, $\mathbf{C}_\sharp$ is the category obtained by erasing all data. Objects of $\mathbf{C}_\sharp$ are the label sets of $\mathbf{C}$-objects (axes, arrays) with sizes stripped; morphisms of $\mathbf{C}_\sharp$ are the combinatorial patterns of $\mathbf{C}$-morphisms (support graphs, connectivity) with all numeric and Boolean values erased. Composition is well-defined because it depends only on connectivity, never on values.

**Relationship to $\mathcal{S}$ instances.** An $\mathcal{S}_{St}$ instance $F$ has two parts: a C-set part (the `Axis`/`Entry` multigraph — one morphism of $\mathbf{St}_\sharp$) and an attribute part (`size`, `coeff`). Stripping the attributes from $F$ yields one morphism of $\mathbf{St}_\sharp$. The schema $\mathcal{S}$ is the fixed template for *one* morphism; $\mathbf{C}_\sharp$ is the category that *all* such structural skeletons collectively form.

For any category $\mathbf{C}$ whose morphisms carry both combinatorial structure and typed data, define a functor

$$D : \mathbf{C}_\sharp \to \mathbf{Disc}$$

assigning to each object its set of valid data assignments. Because data values are independent across domain and codomain, $D$ acts trivially on morphisms — data is never constrained by structure. The **Grothendieck construction** $\int D$ recovers $\mathbf{C}$: objects are (structural object, data assignment) pairs and morphisms are structural morphisms with no compatibility condition on data.

For **St**: $\mathbf{St}_\sharp$ has finite index sets as objects and $\mathbb{N}$-matrices (support + coefficients, sizes erased) as morphisms; $D(I) = \mathbb{N}_{>0}^I$ (size assignments). $\int D$ recovers **St**.

For **Br**: $\mathbf{Br}_\sharp$ has bare array products as objects and stripped `Broadcasted` patterns (array–axis connectivity and reindexing support graph, with all numeric and Boolean values erased) as morphisms; $D$ assigns sizes, coefficients, `is_target`, `is_input`, and `max_value`. $\int D$ recovers **Br**.

### Schema Morphisms and Data Migration

Following Patterson et al., a **schema morphism** $f : \mathcal{S} \to \mathcal{S}'$ induces an adjoint triple

$$\Sigma_f \dashv f^* \dashv \Pi_f$$

between instance categories, for any schema:

- **Restriction** ($f^*$): reindex an $\mathcal{S}'$-instance along $f$ to produce an $\mathcal{S}$-instance; when $f$ is the C-set inclusion this forgets all attribute data
- **Left adjoint** $\Sigma_f$: freely extend an $\mathcal{S}$-instance to an $\mathcal{S}'$-instance (left Kan extension)
- **Right adjoint** $\Pi_f$: compute the tightest $\mathcal{S}'$-instance compatible with an $\mathcal{S}$-instance (right Kan extension)

For $\mathcal{S}_{St}$: $\Pi_f$ computes the tightest axis-size assignment on the codomain given a stride pattern — the shape-inference operation in a neural network compiler.

For $\mathcal{S}_{Br}$: the same triple migrates sizes, coefficients, weave roles, and datatype bounds across schema morphisms between broadcasting patterns.

### Two-Level Structure/Data Split

The structure/data distinction operates at two levels in each category — they are complementary, not competing.

**Level 1 — structural skeleton / Grothendieck.** The structural category $\mathbf{C}_\sharp$ treats morphisms atomically: combinatorial content (support graphs, coefficients, connectivity) is structural; all numeric and Boolean values are data attached to objects via $D$. Functorial composition depends only on the structural layer.

**Level 2 — acset schema instances.** Within a single instance, the C-set part is graph connectivity only. All numeric and Boolean values are attributes. Two instances sharing the same connectivity have the same structural type regardless of their data values.

| Category | Level | Structural | Data |
| --- | --- | --- | --- |
| **St** | $\mathbf{St}_\sharp$ / Grothendieck | support + coefficients ($\mathbb{N}$-matrix) | axis sizes |
| **St** | $\mathcal{S}_{St}$ instance | directed multigraph | sizes, coefficients |
| **Br** | $\mathbf{Br}_\sharp$ / Grothendieck | array–axis connectivity, reindexing support | sizes, coefficients, `is_target`, `is_input`, `max_value` |
| **Br** | $\mathcal{S}_{Br}$ instance | Sample–Axis–ArrayAxis–Array connectivity graph | sizes, coefficients, `is_target`, `is_input`, `max_value` |

---

## Instances as Functors: Natural Transformation between St and Br

Each $\mathcal{S}_{St}$ instance is a functor $F : \mathcal{S}_{St} \to \mathbf{Set}$ — a copresheaf assigning entity sets to the schema's object types and functions to its maps. Similarly each $\mathcal{S}_{Br}$ instance is a functor $G : \mathcal{S}_{Br} \to \mathbf{Set}$. In the acset framework, **instances are functors**, and a morphism between two instances of the same schema is a natural transformation between those functors.

The $[a, \cdot]$ construction maps every **St** instance to a **Br** instance, and does so in a way that is compatible with instance morphisms. This compatibility is a **natural transformation** at the instance level.

### Schema Morphism Underlying $[a, \cdot]$

There is a schema morphism $\phi : \mathcal{S}_{St} \hookrightarrow \mathcal{S}_{Br}$ that sends the **St** entity types and maps into their counterparts in the **Br** schema:

| $\mathcal{S}_{St}$ | $\mathcal{S}_{Br}$ | Role |
| --- | --- | --- |
| `Axis` | `Axis` | identity — axis nodes are shared |
| `Entry` | `Sample` | reindexing coefficient rows |
| `src` | `src` | domain axis of each nonzero entry |
| `tgt` | `tgt` | codomain axis of each nonzero entry |
| `coeff` | `coeff` | linear coefficient value |
| `size` | `size` | axis size attribute |

Applying $\phi$ to an **St** instance $F$ via the restriction functor $\phi^* : \mathcal{S}_{Br}\text{-Inst} \to \mathcal{S}_{St}\text{-Inst}$ pulls back the `Axis`/`Sample` part of any **Br** instance to the `Axis`/`Entry` structure of an **St** instance. Going the other direction, the left Kan extension $\Sigma_\phi$ freely generates a **Br** instance from an **St** instance by:

1. Adding one input `Array` $[a, Q]$ (`is_input = True`) and one output `Array` $[a, P]$ (`is_input = False`)
2. Marking all `ArrayAxis` rows with `is_target = False` — every axis is a tiling axis, since $[a, \Lambda]$ is a pure reindexing with no base computation
3. Setting `reindexing_of` on every `Sample` to the input array $[a, Q]$

The result is exactly the `Broadcasted` acset structure of $[a, \Lambda] : [a, Q] \to [a, P]$.

### The Natural Transformation

Fix a datatype $a$. Define a map on instances:

$$\Phi_a : \mathcal{S}_{St}\text{-Inst} \to \mathcal{S}_{Br}\text{-Inst}, \qquad F \mapsto [a, F]$$

where $[a, F]$ is the **Br** instance constructed by $\Sigma_\phi$ extended with the two `Array` rows and `ArrayAxis`/`is_target` data above.

**$\Phi_a$ is a natural transformation** between the instance-level functors. Concretely: a morphism of **St** instances $\alpha : F_1 \Rightarrow F_2$ — a natural transformation assigning, for each entity type $X \in \mathcal{S}_{St}$, a function $\alpha_X : F_1(X) \to F_2(X)$ commuting with all schema maps — induces a morphism of **Br** instances $[a, \alpha] : [a, F_1] \Rightarrow [a, F_2]$ whose `Axis` and `Sample` components are $\alpha_{\texttt{Axis}}$ and $\alpha_{\texttt{Entry}}$, extended by identity on the two `Array` rows.

The naturality square for $\Phi_a$ at a schema morphism $f : \mathcal{S}_{St} \to \mathcal{S}_{St}$ (a structural transformation of **St** instances) is:

$$\begin{array}{ccc}
[a, F_1] & \xrightarrow{[a,\, \alpha]} & [a, F_2] \\
\downarrow{\scriptstyle \Phi_a} & & \downarrow{\scriptstyle \Phi_a} \\
[a, F_1] & \xrightarrow{[a,\, \alpha]} & [a, F_2]
\end{array}$$

and commutes by construction.

### Connection to Contravariant Functoriality

The instance-level natural transformation $\Phi_a$ is the acset expression of the contravariant functor $[a, \cdot] : \mathbf{St}^{op} \to \mathbf{Br}$ from the theory. The two levels correspond:

| Level | **St** | **Br** | Connection |
| --- | --- | --- | --- |
| Category-theoretic | shape $A \in \text{Ob}(\mathbf{St})$ | array $[a,A] \in \text{Ob}(\mathbf{Br})$ | object action of $[a,\cdot]$ |
| Category-theoretic | morphism $\eta : P \to Q$ | reindexing $[a,\eta] : [a,Q] \to [a,P]$ | contravariant morphism action |
| Acset/instance | $\mathcal{S}_{St}$-instance $F$ (a functor) | $\mathcal{S}_{Br}$-instance $[a,F]$ (a functor) | $\Phi_a(F) = \Sigma_\phi F$ |
| Acset/instance | instance morphism $\alpha : F_1 \Rightarrow F_2$ | induced morphism $[a,\alpha] : [a,F_1] \Rightarrow [a,F_2]$ | naturality of $\Phi_a$ |

The commutativity of $\Phi_a$'s naturality squares is the acset counterpart of the condition $[a, \Lambda \mathbin{;} M] = [a, M] \mathbin{;} [a, \Lambda]$ proved in `functor_proof.md`. Both say the same thing at different levels of abstraction: the pullback of a composed reindexing equals the composition of pullbacks in the reversed order.

---

## Next Steps

### St Instances

1. **Define `SStInstance`** as a Python dataclass with an `axis_table: dict[AxisId, Size]` and an `entry_table: dict[EntryId, tuple[AxisId, AxisId, Coeff]]`. `AxisId` and `EntryId` are opaque integer keys; domain and codomain axes live in the same `axis_table`, distinguished by their membership in the image of `src` vs `tgt`.

2. **Round-trip conversion.** Implement `StrideMorphism.to_instance() -> SStInstance` (flatten `_cod_stride` into `Entry` rows) and `SStInstance.to_stride_morphism() -> StrideMorphism` (reassemble coefficient matrix from `entry_table`, reconstruct `Axis` objects). Verify that `to_stride_morphism(to_instance(m)) == m` for the canonical examples: identity, duplication, projection, convolution shift.

3. **Instance morphisms.** Define `SStMorphism` — a pair of functions $(\alpha_{\texttt{Axis}}, \alpha_{\texttt{Entry}})$ commuting with `src`, `tgt`, `size`, and `coeff` — and verify it implements natural transformation between instance functors. This is the acset representation of a map between two stride morphisms that is compatible with the linear-transform structure.

4. **Composition of instances.** Implement `compose(f: SStInstance, g: SStInstance) -> SStInstance` by computing the matrix product of coefficient tables (with the shared axes identified). Verify it agrees with `StrideMorphism` composition.

### Br Instances

5. **Define `SBrInstance`** as a Python dataclass with four tables — `axis_table`, `array_table`, `array_axis_table`, `sample_table` — matching the schema $\mathcal{S}_{Br}$. Attributes: `size` on `Axis`, `is_input` and `max_value` on `Array`, `is_target` on `ArrayAxis`, `coeff` on `Sample`.

6. **Round-trip conversion.** Implement `Broadcasted.to_instance() -> SBrInstance` (unpack `input_weaves`, `output_weaves`, and `reindexings` into the four tables) and `SBrInstance.to_broadcasted() -> Broadcasted` (reassemble weave `_shape` tuples from `array_axis_table` rows ordered by `is_target`, reconstruct reindexings from `sample_table` grouped by `reindexing_of`). Verify round-trip for the batched linear and multi-head attention examples.

7. **Weave extraction.** Verify that for each `Array` row, the `ArrayAxis` rows with `is_target = False` reconstruct the `TILED` slots of the corresponding weave in the correct order, and the `is_target = True` rows reconstruct the concrete `Axis` objects. This is the acset representation of the weave boolean family $(w_i)_{i \in I}$.

8. **Instance morphisms.** Define `SBrMorphism` — natural transformations between `SBrInstance` functors — and verify the four component functions ($\alpha_{\texttt{Axis}}$, $\alpha_{\texttt{Array}}$, $\alpha_{\texttt{ArrayAxis}}$, $\alpha_{\texttt{Sample}}$) commute with all ten schema maps.

### Schema Morphism $\phi$ and $\Phi_a$

9. **Implement $\phi^*$** (restriction): given an `SBrInstance`, extract the `Axis` and `Sample` tables (discarding `Array`, `ArrayAxis`, `is_target`, `is_input`, `max_value`) to produce an `SStInstance`. Verify that $\phi^*([a, F]) = F$ for every `SStInstance` $F$ — restriction recovers the original **St** instance from its induced **Br** instance.

10. **Implement $\Phi_a$** (left Kan extension $\Sigma_\phi$ plus array decoration): given an `SStInstance` $F$ and a datatype $a$, produce the `SBrInstance` $[a, F]$ by adding two `Array` rows ($[a, Q]$ and $[a, P]$), one `ArrayAxis` row per axis (all `is_target = False`), and setting `reindexing_of` on every `Sample` to the input array. Verify $\phi^*(\Phi_a(F)) = F$ (round-trip) and that `SBrInstance.to_broadcasted()` on $\Phi_a(F)$ agrees with the reindexing morphism $[a, \Lambda]$ built directly from the corresponding `StrideMorphism`.

---

## Advantages of the Structure/Data Decomposition

### Practical and Implementation Advantages

**Structure as a compile-time artifact.** The structural skeleton — which axes exist, which entries connect them, which arrays and array-axis rows exist, which samples belong to which reindexing — is fixed at graph-compile time and independent of numeric values. The kernel template (loop structure, memory access patterns, which axes are tiling vs. target) can therefore be compiled once from the structural layer and reused across many instantiations with different sizes or coefficients. The acset split makes this separation explicit and type-enforced rather than implicit in coding conventions.

**Shape inference is $\Pi_\phi$.** The right Kan extension along a schema morphism is the canonical categorical notion of "tightest compatible extension." For **St**, given a set of size constraints (e.g., axis equalities imposed by `Context` during `@` composition), $\Pi_\phi$ computes the unique consistent size assignment — this is shape inference. Framing it as a Kan extension means it composes correctly across schema morphisms and is guaranteed to be canonical, replacing what would otherwise be a custom traversal written per operator.

**Model transformations are schema morphisms.** Common compiler operations — adding a batch dimension, fusing two operations, changing loop order, adding an output axis — are schema morphisms between instances, each with an automatically induced adjoint triple ($\Sigma_\phi \dashv \phi^* \dashv \Pi_\phi$). The left adjoint $\Sigma_\phi$ freely adds the new structure; the right adjoint $\Pi_\phi$ propagates constraints back. This replaces ad hoc mutation methods with a principled, composable vocabulary. The table below maps common operations to the appropriate adjoint:

| Operation | Adjoint | Direction |
| --- | --- | --- |
| Add a batch axis to all arrays | $\Sigma_\phi$ | extend freely |
| Shape inference from axis equalities | $\Pi_\phi$ | tightest compatible |
| Extract reindexing skeleton from a Br instance | $\phi^*$ | restriction |
| Forget sizes, keep connectivity | $\phi^*$ along size-forgetting schema morphism | restriction |

**Serialization decouples architecture from weights.** The structural C-set (graph connectivity) is the computation graph; the attribute tables (sizes, coefficients, `is_target`, `max_value`) are the data. These can be serialized and transmitted independently: the graph is compiled once and the data values are streamed separately. This maps directly to standard model checkpointing practice, but the acset framework gives it a formal justification rather than leaving it as a design convention.

**Testability.** Structural properties (correct connectivity, expected entity counts) and numeric properties (correct coefficient values, consistent sizes) can be tested independently. The structural skeleton is finite and enumerable for any given entity count, making it tractable for property-based testing and exhaustive verification at small scale.

**Pattern matching for optimization.** Operator fusion, kernel selection, and algebraic rewriting rules operate on the structural layer only: they need to know which axes feed which outputs, but not the sizes. The C-set representation makes this a graph-matching problem with a well-defined notion of isomorphism, rather than a bespoke traversal of the morphism term tree. Two instances are structurally isomorphic if and only if their entity sets are in bijection preserving all schema maps; this is decidable independent of attribute values.

---

### Theoretical Advantages

**Grothendieck construction gives a fibered category.** The structure/data split is not a software pattern — it is the Grothendieck integral $\int D$ of the data functor $D$ over the structural skeleton. The categorical axioms of **St** and **Br** decompose accordingly: structural composition depends only on graph connectivity; numeric composition (matrix multiplication for **St**, reindexing coefficient assembly for **Br**) acts in the fiber over the structural layer. Canonical projection functors — from **St** to the structural skeleton (forget data) and from **St** to data (evaluate at a structural object) — are consequences of the fibration, not additional constructions.

**The adjoint triple is automatic for every schema morphism.** Any schema morphism $\phi : \mathcal{S} \to \mathcal{S}'$ induces $\Sigma_\phi \dashv \phi^* \dashv \Pi_\phi$ between instance categories. This means every structural transformation between **St** or **Br** instances — not just the ones anticipated in advance — comes equipped with three data migration functors for free. Shape inference, free extension, and restriction are not separate constructions defined per use case; they are instances of a single categorical pattern applied to different schema morphisms.

**Colimit-based composition has a universal property.** Composition of two instances can be expressed as a pushout — the smallest instance into which both factor compatibly — giving composition a universal property. This is the formal counterpart of what the `Context` / UID unification system does during `@` composition: it identifies the shared boundary axes and produces the smallest consistent composite. Framing composition as a colimit connects it to the general theory of limits, making associativity and identity immediate from categorical axioms rather than custom proofs.

**The Yoneda lemma applies.** Since instances are copresheaves, every instance decomposes canonically as a colimit of representables. For $\mathcal{S}_{St}$, the representable on `Axis` is the single-axis instance and the representable on `Entry` is the single-entry (one nonzero coefficient in a $1 \times 1$ stride morphism). Any instance decomposes into a colimit of these atoms. This gives a principled vocabulary of primitive instances and guarantees that any property preserved by colimits holds for complex instances whenever it holds for the atoms.

**Connection to categorical databases.** The acset framework is an instance of Spivak's functorial data models, which connect directly to categorical query language (CQL). Queries over **St** and **Br** instances — "which axes are shared between two operations?", "which samples have coefficient greater than 1?", "what is the degree of this broadcasted operation?" — are schema morphisms whose data migration yields the answer. Standard results in database theory (completeness of CQL, semantics of joins and projections) carry over: joins of **St** instances correspond to the pushout computing composition, giving a relational-algebraic account of morphism composition without additional proof.

**$\Phi_a$ is coherent with $[a, \cdot]$ at both levels.** The category-theoretic contravariant functor $[a, \cdot] : \mathbf{St}^{op} \to \mathbf{Br}$ and the instance-level functor $\Phi_a : \mathcal{S}_{St}\text{-Inst} \to \mathcal{S}_{Br}\text{-Inst}$ are the same construction expressed at two levels of abstraction, connected by the Grothendieck projections. Any result proved at the category-theoretic level — such as the `pullback_comp` theorem — automatically implies the corresponding result at the instance level, and vice versa. The two-level structure makes results transportable between the abstract and the concrete without additional proof work.

**Natural transformations are the correct morphism concept.** When instances are copresheaves, the correct notion of map between instances is a natural transformation: a family of functions, one per entity type, commuting with all schema maps. This is more discriminating than term equality and more general than pointwise numeric equality. It is the notion under which composition, Kan extensions, and the adjoint triple are all well-behaved. Any weaker notion of morphism would break at least one of these properties.

**Connection to dependent type theory and formal verification.** The structure/data split is the categorical expression of the distinction between a type context (structural skeleton: which variables exist and how they relate) and a term (data assignment: values inhabiting those types). Schema morphisms are context morphisms (substitutions). This vocabulary maps directly onto Lean 4, where the type-theoretic and category-theoretic frameworks coincide. Proving properties of **St** and **Br** in Lean becomes a matter of instantiating general results about copresheaves and Kan extensions — the same framework used to establish `pullback_comp` — rather than developing bespoke proof strategies per construction.

---

## Integration with Tensor Logic

The pyncd categorical framework does not exist in isolation. `tensorLogicNCDIntegration.md` describes how tensor logic (Domingos 2025) serves as the primary user-facing interface for constructing pyncd morphisms. This connection clarifies the natural role for acset instances in the overall architecture and reveals a direct structural correspondence between `TensorEquation` and `SBrInstance`.

### Tensor Logic as the Construction Interface

Tensor logic is a programming language whose sole primitive is the tensor equation:

```
Y[i, j] = relu(W[i, k] X[k, j])
```

In the pyncd integration, each equation becomes a `TensorEquation(Operator)` — a frozen dataclass embedded as the `operator` field of a `Broadcasted` morphism. A `TensorProgram` collects equations, topologically sorts them, and produces a `Composed` of `Broadcasted[B, A, TensorEquation]` morphisms via `Context`-mediated axis unification (`to_morphism()`). Users write tensor equations; the pyncd term hierarchy is the internal representation generated from them.

This places terms and acset instances in a symmetric position: both are views derived from the same `TensorProgram` source, each suited to different downstream consumers.

### TensorEquation as a Proto-Acset

The `TensorEquation` dataclass has a direct, lossless mapping to the four tables of `SBrInstance`:

| `TensorEquation` field | `SBrInstance` table entry |
| --- | --- |
| `lhs_name` | One `Array` row with `is_input = False` |
| Each `(name, indices)` in `rhs` | One `Array` row with `is_input = True` |
| `(tensor, axis)` pair where `axis ∈ lhs_indices` | `ArrayAxis` row with `is_target = False` (degree / TILED) |
| `(tensor, axis)` pair where `axis ∉ lhs_indices` | `ArrayAxis` row with `is_target = True` (contracted) |
| Retained axis $i \in$ `lhs_indices` appearing in input $X$ | `Sample` row: `src` $= i$, `tgt` $= i$, `coeff` $= 1$, `reindexing_of` $= X$ |
| `operator` field | `operator_tag` attribute on the output `Array` row |

**Example: $Y[i,j] = W[i,k]\, X[k,j]$.** The degree is $(i, j)$ — the retained indices. The contracted axis $k$ appears in both $W$ and $X$ but not in the output. $W$ is indexed by degree axis $i$; $X$ by degree axis $j$.

**Axis table:**

| `Axis` | `size` |
| --- | --- |
| $i$ | `FreeNumeric` |
| $j$ | `FreeNumeric` |
| $k$ | `FreeNumeric` |

**Array table:**

| `Array` | `is_input` | `operator_tag` |
| --- | --- | --- |
| $Y$ | False | `Identity` |
| $W$ | True | — |
| $X$ | True | — |

**ArrayAxis table:**

| `ArrayAxis` | `array` | `axis` | `is_target` |
| --- | --- | --- | --- |
| $ya_i$ | $Y$ | $i$ | False |
| $ya_j$ | $Y$ | $j$ | False |
| $wa_i$ | $W$ | $i$ | False |
| $wa_k$ | $W$ | $k$ | True |
| $xa_k$ | $X$ | $k$ | True |
| $xa_j$ | $X$ | $j$ | False |

**Sample table:**

| `Sample` | `src` | `tgt` | `coeff` | `reindexing_of` |
| --- | --- | --- | --- | --- |
| $s_0$ | $i$ | $i$ | 1 | $W$ |
| $s_1$ | $j$ | $j$ | 1 | $X$ |

$W$ contributes degree axis $i$ (Sample $s_0$); $X$ contributes degree axis $j$ (Sample $s_1$). The contracted axis $k$ has no `Sample` rows — it is not part of any reindexing. Its `is_target = True` entries in the `ArrayAxis` table mark it as a target axis summed over by the base operation.

**Multi-equation programs.** A `TensorProgram` with multiple equations produces one `SBrInstance` per equation. The instances are linked by shared `Axis` UIDs: when `to_morphism()` calls `ctx.append_iter` to unify the `lhs_indices` of one equation with the corresponding `rhs` input axes of the next, both the term and the acset tables carry the same canonical UIDs. The acset representation of a `TensorProgram` is therefore a sequence of `SBrInstance` values connected by UID-shared `Axis` rows — exactly as `Composed` connects `Broadcasted` morphisms through shared domain and codomain objects.

**Strided convolutions.** For non-einsum reindexings (strided convolution, diagonal slice), `coeff` $\neq 1$ in the `Sample` rows. The existing `Sample.coeff` attribute handles this; no schema extension is needed.

### The operator_tag Attribute

The `TensorEquation.operator` field — which distinguishes an `Identity` reindexing from a `SoftMax`, `Elementwise`, `Linear`, or `Embedding` — maps to an `operator_tag` attribute on output `Array` rows. This requires one additive change to $\mathcal{S}_{Br}$:

$$\texttt{Array} \xrightarrow{\texttt{operator\_tag}} \texttt{OpTag}$$

defined as a partial map on output arrays (`is_input = False`); undefined for input arrays.

| `OpTag` | Pyncd class | Role |
| --- | --- | --- |
| `Identity` | `Identity()` | Pure reindexing — no base computation |
| `SoftMax` | `SoftMax()` | Normalisation along `NormAxis` |
| `Elementwise` | `Elementwise()` | Pointwise nonlinearity |
| `Normalize` | `Normalize()` | RMSNorm / LayerNorm |
| `Embedding` | `Embedding(...)` | Discrete lookup ($\mathbb{N} \to \mathbb{R}$) |
| `AdditionOp` | `AdditionOp()` | Elementwise addition |
| `WeightedTriangularLower` | `WeightedTriangularLower()` | Causal mask |
| `Linear` | `Linear(...)` | Weight matrix application |

This is an additive change: existing instances without `operator_tag` remain valid. No existing tables change structure. Adding a new operator subclass means adding one row to this table; no instance migration is required.

### The Dual-View Pipeline

With the tensor logic integration in place, the natural architecture is:

```
              Tensor Logic DSL
                     │
                     ▼
              TensorProgram
         (TensorEquation objects
          with shared Axis UIDs)
              ╱             ╲
             ▼               ▼
          Terms          SBrInstances
  (Composed of          (one per equation,
   Broadcasted)          linked by Axis UIDs)
             │               │
  ┌──────────┴──────┐  ┌─────┴─────────────────┐
  │ compilation     │  │ shape inference (Πφ)   │
  │ rendering       │  │ structural matching    │
  │ parallel        │  │ data migration         │
  │   composition   │  │ serialization          │
  │ block structure │  └───────────────────────┘
  └─────────────────┘
```

| Terms | Acset instances |
| --- | --- |
| Compilation: operator types, weave structure, code generation | Shape inference ($\Pi_\phi$, right Kan extension) |
| Rendering: `Block` metadata, `ProductOfMorphisms` layout | Structural pattern matching: kernel selection, fusion rules |
| Type-level operator (`Broadcasted[B, A, TensorEquation]`) | Data migration: adjoint triple across schema morphisms |
| Generated by `TensorProgram.to_morphism()` | Generated by proposed `TensorProgram.to_instance()` |

The two views are projections of `TensorProgram` optimised for different consumers. The same `Axis` UIDs appear in the term's `Weave` objects and in the acset's `ArrayAxis` rows: any `Context`-mediated unification during `to_morphism()` is automatically reflected in both, so the views remain consistent without a separate round-trip conversion.

### What Remains in the Term World

Two constructs sit above `TensorProgram.to_morphism()` and have no acset counterpart — by design, because they are precisely what tensor logic deliberately omits (`tensorLogicNCDIntegration.md §4.3`).

**Parallel product (`ProductOfMorphisms`).** Tensor logic has no notion of running two computations in parallel. In pyncd, `ProductOfMorphisms` applies two morphisms to disjoint inputs and concatenates the outputs — essential for multi-head attention where each head operates independently. `tensorLogicNCDIntegration.md §5.6` describes how this structure can be recovered automatically from the dependency DAG of a `TensorProgram` by identifying fork-join pairs; until that analysis is implemented, it is assembled by the caller above `to_morphism()`.

**Block structure.** `Block` carries display metadata (`title`, `fill_color`, `repetition`) that has no bearing on mathematical content. It belongs to the presentation layer — above both the term and the acset — and is added by the caller to group sub-expressions for rendering.

Both constructs sit above the tensor logic boundary cleanly. The term world handles them; the acset schema does not need to.
