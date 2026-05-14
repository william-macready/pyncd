# pyncd Codebase Overview

pyncd is a formal algebraic framework for expressing, compiling, and visualising deep learning models as categorical terms. A model is an algebraic expression built from a small set of construction rules; the same term simultaneously compiles to PyTorch and renders as a Neural Circuit Diagram.

Cross-references to the paper (Abbott & Zardini, arXiv:2604.07242) are given as **Paper: §X** (section) or **Paper: Def X** (definition).

---

## Architecture at a Glance

```
data_structure/          Core algebra: terms, categories, operators
construction_helpers/    Operator overloading for building morphisms
torch_compile/           Translation to PyTorch nn.Module
display/                 ASCII box rendering and colour output
graphs/                  Hypergraph conversion for algebraic manipulation
websocket_transfer/      Real-time WebSocket diagram streaming
data_transfer/           JSON serialisation / deserialisation
term_utilities/          Term inspection and configuration
utilities/               General-purpose functional helpers
data_structure_kernels/  GPU kernel and tiling abstractions
tests/                   Unit tests
papers/                  Theoretical documentation
```

---

## data_structure/

The mathematical foundation. Every other module depends on this one.

### [Term.py](../data_structure/Term.py)

**Paper:** §2 (The Term System)

The root of the type hierarchy. Defines:

- **`Term`** — frozen dataclass base for all algebraic entities. Identity is determined by content. Corresponds to the paper's *construction rules* $T_c$: the output embeds its inputs, guaranteeing a recovery function $\hat{T}_c$.
- **`UTerm`** — adds a `UID` field; identity is tracked by the UID regardless of other field values. Directly implements the paper's *UTerm* concept: things that need to be tracked across an expression independently of their field values.
- **`UID[T]`** — a randomly-generated integer identifier with an optional human-readable name and a `_type` field recording which `UTerm` subclass it identifies. Implements the paper's *unique identifier* (§2).
- **`TermDirectory` / `EnumDirectory`** — registries that map class names to constructors, used for JSON round-tripping. No direct paper equivalent (infrastructure).
- **`DynamicName`** — display name with subscript support for pretty-printing axes. No direct paper equivalent (display only).

Placeholder terms use UIDs as free variables. Two terms composed with `@` have their boundary axes unified by declaring their UIDs equal in a `Context` (a union-find over UIDs). The paper describes this as *autoalignment* (§5.1.1): `Context.append_iter` unifies the codomain axes of the left morphism with the domain axes of the right.

### [Numeric.py](../data_structure/Numeric.py)

**Paper:** §2 / Def 8 (axis sizes)

Symbolic arithmetic for axis sizes that may not be known at definition time:

- **`FreeNumeric`** — a UTerm representing an unknown integer (like a symbolic variable). Implements the paper's symbolic axis size $|A|$ before it is assigned a concrete value; it is a UTerm so its identity is tracked independently across an expression.
- **`Integer`** — a concrete integer. The resolved form of $|A| \in \mathbb{N}$ (Def 8).
- **`Addition`, `Multiplication`, `Power`** — expression tree nodes with full operator overloading. Support derived size expressions such as $|A| \cdot |B|$ for a merged axis.
- **`Equality`** — declares two numerics equal, used during configuration. Implements the equality constraint propagated by `NumericConfig.assign()`.

### [ProductCategory.py](../data_structure/ProductCategory.py)

**Paper:** §3 (The Product Category Framework), Def 6 (elemental categories)

Implements the product category framework shared by both **St** and **Br**:

- **`ProdObject[L]`** — a finite product of lone objects (a tuple of `L`). Wraps `content: Prod[L]`. Implements the paper's product object $\Pi_{i \in I} A_i$ (§3). The empty product is the unit object $\mathbf{1}$.
- **`Morphism[L]`** — abstract base requiring `dom()` and `cod()` returning `ProdObject[L]`. Supports `@` (sequential composition), `*` (parallel product), and `>>` (batch lift). The abstract root morphism of any product category (§3).
- **`Composed[L, M]`** — sequential composition; `content: Prod[M]` with `dom = content[0].dom()`, `cod = content[-1].cod()`. Implements $;$ (§3).
- **`ProductOfMorphisms[L, M]`** — parallel product; stacks morphisms vertically. Implements $\otimes$ (§3); satisfies bifunctoriality $(f;g)\otimes(h;k) \equiv (f\otimes h);(g\otimes k)$.
- **`Rearrangement[L]`** — permutes inputs via a mapping $\mu : J \to I$. Directly implements the rearrangement $[\mu]_{(A_i)_{i\in I}}$ (§3); deletion ($\text{count}[\mu](i)=0$) and copying ($\text{count}[\mu](i)>1$) are both special cases.
- **`Block[L, M]`** — organisational wrapper (loop tags, aesthetic grouping) that preserves domain/codomain. Corresponds to the paper's *Block* construction (§3); transparent to categorical semantics.
- **`BlockTag`** — UTerm carrying a title, colour, and repeat count for rendering. Carries the display metadata associated with a Block.

### [StrideCategory.py](../data_structure/StrideCategory.py)

**Paper:** Def 8 (The Axis-Stride Category St)

The axis-stride category **St**:

- **`Axis`** — lone object in **St**; a UTerm with a `size: Numeric` and display name. Directly implements the paper's *axis* $A$ with UID and size $|A| \in \mathbb{N}$ (Def 8). The UID serves as the axis's identity across an expression; the size is a `FreeNumeric` until configured.
- **`StrideMorphism[A]`** — root morphism; an affine map $\eta : \Pi_i A_i \to \Pi_j B_j$ represented by a matrix $\Lambda$ and offset $v$. Action: $\Pi_i a_i \cdot \eta = \Pi_j (v_j + \sum_i \Lambda_{ij} a_i)$. Implements the paper's *finite linear transform* (Def 8). The `_cod_stride` field bundles codomain axes with their coefficient rows to keep them in lockstep.
- **`StrideCategory[A]`** — type alias for the product category over `Axis` and `StrideMorphism`. Represents **St** itself.

### [BroadcastedCategory.py](../data_structure/BroadcastedCategory.py)

**Paper:** Defs 9–13 (The Array-Broadcasted Category Br)

The array-broadcasted category **Br**:

- **`Datatype`** — abstract base. Concrete: `Reals()` ($\mathbb{R}$), `Natural` (with template for $\mathbb{N}_n$). Implements $a \in \mathbf{Dt}$ (Def 9).
- **`Array[B, A]`** — lone object in **Br**; a pair `(datatype: B, _shape: Prod[A])`. Directly implements the paper's array $[a, A]$ (Def 9): datatype $a$ paired with shape $A \in \text{Ob}(\mathbf{St})$.
- **`WeaveMode`** — enum with one value `TILED`, used as a sentinel in weave shapes. Encodes the $w_i = 0$ (tiling) case of the paper's Boolean weave family (Def 12); a concrete `Axis` in the same `_shape` field encodes $w_i = 1$ (target).
- **`Weave[B, A]`** — encodes which axes of an array are tiling (looped over by the degree) vs. target (operated on by the base op). `_shape: Prod[A | WeaveMode]` interleaves concrete axes and `TILED` sentinels. Directly implements the paper's *weave* $(w_i)_{i \in I}$ (Def 12), with the associated permutation $\Omega_w$ implicitly encoded by position.
  - `target()` — extracts the target-only array type.
  - `select_degree()` / `select_target()` — partition items by slot type (separating the Boolean family into its two components).
  - `imprint()` — fills `TILED` slots with concrete degree axes to reconstruct the full shape (implements the canonical split reconstruction).
- **`Operator`** — abstract base for base operations. Subclasses implement `.template()` classmethods. Corresponds to the *base operation* $f$ ingredient of Def 13.
- **`Broadcasted[B, A, O]`** — root morphism in **Br**; a broadcasted operation specified by:
  - `operator: O` — the base computation $f$ (Def 13, ingredient 1).
  - `input_weaves: Prod[Weave]` — one per input; marks tiling vs. target axes (Def 13, ingredient 3).
  - `output_weaves: Prod[Weave]` — one per output (Def 13, ingredient 4).
  - `reindexings: Prod[StrideMorphism]` — one per input; $\eta_i : P \to Q_i$ selects the input slice at each degree coordinate (Def 13, ingredient 2 / Def 10).
  - `degree()` — the shared loop domain $P$, recovered as the common domain of all reindexings (Def 13).
  - `dom()` / `cod()` — computed from weaves and reindexings; implements the type formula $F : \Pi_{i \in I}[a_i, \text{dom}([\Omega_{s_i}]_{A_i \otimes Q_i})] \to \Pi_{j \in J}[b_j, \text{dom}([\Omega_{t_j}]_{B_j \otimes P})]$.

### [Operators.py](../data_structure/Operators.py)

**Paper:** §"Concrete Operators" / Def 13

Concrete `Operator` subclasses; each implements `.template()` producing a `Broadcasted` with placeholder axes. All appear in the paper's operator table:

| Class | Description | Paper |
| --- | --- | --- |
| `Elementwise` | Pointwise operation; degree = full shape, no target axes | Def 13; $P$ = full shape, all TILED |
| `Identity` | Identity map | Rearrangement special case |
| `SoftMax` | Softmax over a specified axis | Concrete Operators table |
| `Einops` | General Einstein summation from a signature string | Concrete Operators table; retained indices become degree $P$ |
| `Linear` | Learned linear map $Y = XW + b$; degree empty | Concrete Operators table; $P = \mathbf{1}$, all axes target |
| `Embedding` | Integer-indexed lookup table | Concrete Operators table; input datatype `Natural` (Def 9) |
| `AdditionOp` | Elementwise addition | Concrete Operators table |
| `Normalize` | RMSNorm | Concrete Operators table |
| `WeightedTriangularLower` | Masked attention score weighting | Concrete Operators table |
| `ReLU` | Rectified linear unit | Elementwise nonlinearity |
| `Dropout` | Training-time dropout | Elementwise nonlinearity |

### [TensorLogic.py](../data_structure/TensorLogic.py)

**Paper:** index notation used throughout (e.g. reindexing table in §"Broadcasting")

Index-notation interface for writing equations and converting them to `Broadcasted` morphisms:

- **`TensorEquation`** — one equation: `lhs_name`, `lhs_indices`, a list of RHS tensors, an operator. `.bc_signature()` produces a `Broadcasted` by: (1) computing retained (output) indices as the degree $P$; (2) building input weaves with `TILED` for retained axes; (3) building reindexings as rearrangements from $P$ to each input's retained axes. This mechanically constructs Def 13 from index notation.
- **`TensorProgram`** — a sequence of equations. `.to_morphism()` unifies axis UIDs across equations and returns a `Composed` of `Broadcasted`s. Implements multi-step tensor programs as a `Composed` morphism (§3).

### [TensorDSL.py](../data_structure/TensorDSL.py)

**Paper:** syntactic sugar over index notation; no dedicated section

High-level Python DSL over `TensorLogic`:

- **`TL`** — registry; supports `tl.Y[i,j] = tl.W[i,k] * tl.X[k,j]` syntax via `__getattr__` / `__setattr__`.
- **`TensorProxy`** — represents an unindexed tensor in the registry.
- **`IndexedTensor`** — a tensor with indices applied; supports `*`, `+`, `softmax()`.
- **`RHSExpression`** — accumulates a product/sum of indexed tensors into a `TensorEquation`.

---

## construction_helpers/

Operator overloading and compositional helpers that let users write models as algebraic expressions.

### [composition.py](../construction_helpers/composition.py)

**Paper:** §5.1.1 (Autoalignment via `@`)

Implements the `@` operator (sequential composition):

- **`align_axes()`** — given two adjacent morphisms, identifies shared boundary axes by UID and builds a `Context` to unify them. Directly implements the autoalignment step: pairing codomain axes of $f$ with domain axes of $g$ and merging UIDs (§5.1.1).
- **`align_composed()`** — handles the case where product sizes mismatch: adds identity morphisms on the smaller side to pad dimensions. Implements the insertion of `morphism_object_lift` identity pads when $\text{cod}(f)$ and $\text{dom}(g)$ differ in arity.
- **`excess_product()`** — determines which side has excess axes and where to insert the identity padding.

### [product.py](../construction_helpers/product.py)

**Paper:** §3 (parallel product $\otimes$)

Implements the `*` operator (parallel product):

- **`morphism_product()`** — concatenates domains and codomains of two morphisms. Implements $f \otimes g$ (§3).
- **`datatype_converter()` / `axis_converter()` / `full_converter()`** — type coercion helpers for mixed products.

### [lift.py](../construction_helpers/lift.py)

**Paper:** Defs 10–11 (Reindexing and Batch Lifting)

Implements the `>>` operator (batch lifting):

- **`object_object_lift()`** — $[X, P]$: prepends shape $P$ to every array in object $X$. Implements the object-object lift $[X, P] = \Pi_{i \in I}[a_i, A_i \otimes P]$ (Def 11).
- **`object_morphism_lift()`** — $[X, \eta]$: lifts a stride morphism to a reindexing in **Br**. Implements the identity reindexing $[a, \eta] : [a, Q] \to [a, P]$ (Def 10).
- **`morphism_object_lift()`** — $[f, P]$: batch-lifts morphism $f$ over shape $P$. Implements the batch lift $[f, P] : [X, P] \to [Y, P]$ (Def 11); the defining property $[f,P] ; [Y,p] = [X,p] ; f$ is preserved by construction.
- **`broadcasted_stride_lift()`** — general lift combining the above. Handles the full generality of Defs 10–11 for a `Broadcasted` morphism with existing reindexings.

### [signature.py](../construction_helpers/signature.py)

**Paper:** `Einops` operator / reindexing table in §"Broadcasting"

Parses Einstein-summation style signatures (e.g. `"q h d, x h d -> h q d"`) into `Broadcasted` components:

- Identifies which axes are broadcasted (appear in outputs only → degree $P$), absorbed (contracted → target axes of input weave), or produced (appear in inputs and outputs → target axes of output weave).
- Constructs the weaves and reindexings corresponding to the signature. Mechanically realises the mapping from an einsum string to Def 13 ingredients.

### [einops.py](../construction_helpers/einops.py)

**Paper:** auxiliary to `Einops` operator

Converts einops-style signatures into the bucket/index representation consumed by `signature.py`.

---

## torch_compile/

Translates algebraic morphisms into executable PyTorch `nn.Module`s.

### [torch_compile.py](../torch_compile/torch_compile.py)

**Paper:** §"End-to-End Example" / Def 13 compilation pipeline

- **`ConstructedModule[M]`** — abstract `nn.Module` that holds a morphism and a registry of operator→constructor mappings.
- **`ConstructedComposed`** — sequential module; each sub-morphism becomes a child module. Compiles sequential composition $;$ (`Composed`, §3).
- **`ConstructedProduct`** — parallel module; runs children in parallel and concatenates. Compiles parallel product $\otimes$ (`ProductOfMorphisms`, §3).
- **`ConstructedRearrangement`** — implements axis permutations as tensor transposes/selects. Compiles rearrangements $[\mu]$ (§3).
- **`ConstructedBlock`** — passes through to its body module. Compiles `Block` (§3).
- **`.construct_broadcasted()`** — the critical path: expands a `Broadcasted` into the input-weave → reindexing → operator → output-weave pipeline. Directly executes the four-ingredient structure of Def 13: (1) apply input weaves (permute axes to canonical form), (2) apply reindexings $\eta_i$ (index into tiling axes), (3) run the base operator $f$, (4) apply output weaves.

### [bcast.py](../torch_compile/bcast.py)

**Paper:** Def 12 (Weave) / §"Weaves" GPU tiling

Broadcasting analysis for the compilation pipeline:

- **`unsqueeze_guide()`** — determines where to insert size-1 dimensions to align a tensor with the degree. Implements the $\Omega_w$ permutation step needed to align the canonical split form with PyTorch's implicit broadcasting.
- **`is_semantically_broadcastable()`** — checks whether PyTorch's implicit broadcasting is sufficient, avoiding explicit `vmap`. Corresponds to detecting when the reindexing is an identity or deletion (the two cases where PyTorch broadcasting suffices without `vmap`).
- **`weave_displacement()`** — computes axis offset needed to align weave positions with PyTorch tensor dimensions.

### [torch_utilities.py](../torch_compile/torch_utilities.py)

**Paper:** `Linear` and `Embedding` operators (Concrete Operators)

- **`Weights`** — `nn.Module` with Kaiming-initialised weight and optional bias parameters. The learnable parameter storage for `Linear` (Def 13).
- **`Multilinear`** — multi-axis linear transformation supporting non-flat input/output shapes.

### [operators.py](../torch_compile/operators.py)

**Paper:** Concrete Operators / Def 13

PyTorch `ConstructedModule` implementations for each concrete `Operator` type. Each class here corresponds one-to-one with an `Operator` subclass in `data_structure/Operators.py` and to a row in the paper's operator table.

---

## display/

Renders morphisms as ASCII box diagrams with colour. Corresponds to the paper's *diagrammatic rendering* (Motivation); the full SVG rendering is in the TypeScript companion `tsncd`.

### [Box.py](../display/Box.py)

- **`Box`** — abstract; all display elements implement `.render() -> list[str]`.
- **`Horizontal` / `Vertical`** — composites that arrange children side-by-side or top-to-bottom with alignment.
- **`TextBox`** — wraps a string.
- **`Fill`** — solid rectangle of a single character.
- **`Border`** — adds a box border around content.

### [Color.py](../display/Color.py)

- **`Color`** — abstract base with `.rgb256()`, `.luminance()`, `.contrast()`.
- **`HexadecimalColor`, `RGBColor`, `HSVColor`** — concrete colour types.
- **`colored_output()`** — wraps a string in ANSI escape codes for terminal display; automatically selects black or white foreground based on background luminance.

### [node_category.py](../display/node_category.py)

Low-level primitives that convert specific term types (axes, arrays, weaves, reindexings) into `Box` trees. Renders `Weave` (Def 12) as annotated wire bundles and `Broadcasted` (Def 13) as a box with labelled ports.

### [display_config.py](../display/display_config.py)

Renders a `ConfigLog` as a formatted table showing axis names, types, and assigned sizes.

---

## graphs/

Converts product category terms into hypergraphs for algebraic manipulation (associativity, bifunctoriality, symmetry rewriting). Supports the *algebraic manipulation* use case from the paper's Motivation.

### [UIDHypergraph.py](../graphs/UIDHypergraph.py)

**Paper:** Motivation (algebraic manipulation via category-theoretic rewriting)

- **`HypergraphObject[L]`** — a node in the hypergraph corresponding to a lone object $L$ (an `Axis` or `Array`).
- **`Hypergraph[L, M]`** — abstract base; concrete variants are `Multigraph`, `HypergraphRoot`, `StructuredGraph`.
- **`.from_morphism()`** — converts a `Composed` or `ProductOfMorphisms` term into a graph, tracking nested structure via `Location` paths. Enables the associativity and bifunctoriality rewrites described in §3 to be applied as graph transformations.

---

## websocket_transfer/

### [websockets_transfer.py](../websocket_transfer/websockets_transfer.py)

**Paper:** Motivation (diagrammatic rendering via tsncd)

- **`DataServer`** — async WebSocket server that maintains separate client registries for diagram clients (TypeScript renderer) and data clients (Python).
- **`DataUpdate`** — message type carrying a JSON-serialised term.
- **`DataRequest`** — message type requesting a specific term by name.
- Supports multiple simultaneous connections; pushes updates to all connected diagram clients when data changes.

---

## data_transfer/

### [json.py](../data_transfer/json.py)

**Paper:** no dedicated section (infrastructure)

- **`TermJSONConverter`** — converts terms to JSON and reconstructs them. Maintains a UID repository alongside the term JSON so that shared UIDs across a structure are preserved during round-tripping. Preserves the UID identity semantics of UTerms (§2) across serialisation boundaries.
- **`.export()` / `.load()`** — file-level serialisation.

---

## term_utilities/

### [term_utilities.py](../term_utilities/term_utilities.py)

**Paper:** §2 (term walking) / Def 8/13 (category identification)

- **`deep_pass()` / `deep_iterate()`** — recursively walk a term tree. Implements structural induction over the construction rule grammar (§2).
- **`identify_category()`** — determines whether a morphism belongs to **St** or **Br**. Distinguishes between `StrideMorphism` (Def 8) and `Broadcasted` (Def 13) at the root-morphism level.
- **`is_mappable()` / `get_mapping()`** — checks whether a morphism is a pure rearrangement (no data transformation). Tests for the `Rearrangement` special case (§3).
- **`is_identity()`** — checks for identity morphisms.

### [generate_config.py](../term_utilities/generate_config.py)

**Paper:** Def 8 (axis sizes) / §2 (FreeNumeric)

- **`ConfigLog[T]`** — tracks `FreeNumeric` instances found in an expression, groups them by UID equality class, and exposes `.assign()` to substitute concrete values. Resolves the symbolic axis sizes $|A|$ (introduced as `FreeNumeric` in Def 8) into concrete $\mathbb{N}$ values before PyTorch compilation.
- **`NumericConfig`** — specialisation for axis size configuration; used to set axis sizes before PyTorch compilation.

---

## utilities/

### [utilities.py](../utilities/utilities.py)

`iallequals()`, `yielder()`, `join_with_none()`, `unique_iterable()`, `deconcatenate()`, `concat()`, `intersection()`, `predicate_partition()` — standard functional helpers for iteration and collection manipulation. No direct paper equivalent.

### [justification.py](../utilities/justification.py)

`JustifyMode` enum and `justify()` / `spread()` — text alignment for the box rendering system.

---

## data_structure_kernels/

### [Kernel.py](../data_structure_kernels/Kernel.py)

**Paper:** §"Weaves" (GPU tiling motivation, FlashAttention example)

Extends the type system with kernel-level parallelism metadata. Corresponds to the paper's concrete discussion of tiling vs. target axes (Def 12) and the FlashAttention efficiency argument:

- **`KernelizedAxis`** — axis annotated with a `ChildKernel` (which CUDA kernel handles it) and a `Strategy` (`STREAM` or `TILE`). The `TILE` strategy realises the *tiling axis* concept (Def 12, $w_i = 0$): the axis is partitioned across GPU cores, each loading only its slice from DRAM. The `STREAM` strategy streams a tiling axis through sequentially (e.g. the $x$ axis in FlashAttention) to avoid materialising the full attention matrix.
- **`Tiling`** — axis variant for tiled memory access patterns. The concrete realisation of the tile size $g_q$ mentioned in the paper's FlashAttention example.
- **`kernel_functor()`** — applies kernel transformations recursively through a term. Propagates tiling annotations through a `Composed` or `ProductOfMorphisms` term, mapping the product category structure (§3) onto GPU execution topology.

---

## tests/

### [test_tensor_dsl.py](../tests/test_tensor_dsl.py)

Tests for the `TensorDSL` layer: axis creation, `TL` registry syntax, `IndexedTensor` composition, and declaration kinds.

### [test_tensor_logic.py](../tests/test_tensor_logic.py)

Tests for `TensorLogic`: `NormAxis`, equation retained/contracted axis extraction, topological sort, and `to_morphism()` conversion.

---

## Key Data Flows

### Building a model

```
Operator.template()          →  Broadcasted (placeholder UIDs)   [Def 13]
    @  (compose)             →  Composed                         [§3, §5.1.1]
    *  (product)             →  ProductOfMorphisms               [§3]
    >> (batch lift)          →  Broadcasted with larger degree    [Def 11]
NumericConfig.assign()       →  concrete axis sizes              [Def 8]
```

### Compiling to PyTorch

```
Morphism
  └─ ConstructedModule.construct()
       ├─ Composed       → ConstructedComposed (sequential nn.Module)   [§3]
       ├─ Product        → ConstructedProduct  (parallel nn.Module)     [§3]
       ├─ Rearrangement  → ConstructedRearrangement                     [§3]
       └─ Broadcasted    → input weaves → reindexings → operator → output weaves  [Def 13]
```

### Serialisation and visualisation

```
Morphism
  └─ TermJSONConverter.to_json()   → JSON
       └─ DataServer.send()        → WebSocket → TypeScript renderer → SVG diagram
```

---

## Paper-to-Code Summary

| Paper element | Code element | File |
| --- | --- | --- |
| Construction rule / Term (§2) | `Term` | `data_structure/Term.py` |
| UTerm with UID (§2) | `UTerm` | `data_structure/Term.py` |
| Unique identifier (§2) | `UID[T]` | `data_structure/Term.py` |
| UID equality / Context (§2, §5.1.1) | `EqualityClass`, `Context` | `data_structure/Term.py` |
| Symbolic axis size (§2, Def 8) | `FreeNumeric` | `data_structure/Numeric.py` |
| Concrete size $\lvert A \rvert \in \mathbb{N}$ (Def 8) | `Integer` | `data_structure/Numeric.py` |
| Product object $\Pi_{i\in I} A_i$ (§3) | `ProdObject[L]` | `data_structure/ProductCategory.py` |
| Sequential composition $;$ (§3) | `Composed[L, M]` | `data_structure/ProductCategory.py` |
| Parallel product $\otimes$ (§3) | `ProductOfMorphisms[L, M]` | `data_structure/ProductCategory.py` |
| Rearrangement $[\mu]$ (§3) | `Rearrangement[L]` | `data_structure/ProductCategory.py` |
| Block (§3) | `Block[L, M]` | `data_structure/ProductCategory.py` |
| Axis $A$ with size $\lvert A\rvert$ (Def 8) | `Axis` / `RawAxis` | `data_structure/StrideCategory.py` |
| Finite affine transform $\eta$ (Def 8) | `StrideMorphism` | `data_structure/StrideCategory.py` |
| Category **St** (Def 8) | `StrideCategory[A]` | `data_structure/StrideCategory.py` |
| Datatype $a \in \mathbf{Dt}$ (Def 9) | `Datatype`, `Reals`, `Natural` | `data_structure/BroadcastedCategory.py` |
| Array $[a, A]$ (Def 9) | `Array[B, A]` | `data_structure/BroadcastedCategory.py` |
| Reindexing $[a, \eta]$ (Def 10) | `reindexings` field + `object_morphism_lift` | `data_structure/BroadcastedCategory.py`, `construction_helpers/lift.py` |
| Object-object lift $[X, P]$ (Def 11) | `object_object_lift` | `construction_helpers/lift.py` |
| Batch lift $[f, P]$ (Def 11) | `morphism_object_lift` | `construction_helpers/lift.py` |
| Weave $(w_i)_{i\in I}$ (Def 12) | `Weave[B, A]` | `data_structure/BroadcastedCategory.py` |
| Tiling axis ($w_i=0$, Def 12) | `WeaveMode.TILED` | `data_structure/BroadcastedCategory.py` |
| Target axis ($w_i=1$, Def 12) | concrete `Axis` in `_shape` | `data_structure/BroadcastedCategory.py` |
| Broadcasted operation $F$ (Def 13) | `Broadcasted[B, A, O]` | `data_structure/BroadcastedCategory.py` |
| Base operator $f$ (Def 13) | `Operator` subclass | `data_structure/Operators.py` |
| Degree $P$ (Def 13) | `Broadcasted.degree()` | `data_structure/BroadcastedCategory.py` |
| Einsum operator (Concrete Operators) | `Einops` | `data_structure/Operators.py` |
| Autoalignment via `@` (§5.1.1) | `align_axes`, `align_composed` | `construction_helpers/composition.py` |
| Def 13 pipeline (input weaves→η→f→output weaves) | `construct_broadcasted` | `torch_compile/torch_compile.py` |
| GPU tiling / target split (§"Weaves") | `KernelizedAxis`, `Strategy` | `data_structure_kernels/Kernel.py` |
| Size configuration (Def 8, FreeNumeric) | `NumericConfig`, `ConfigLog` | `term_utilities/generate_config.py` |
