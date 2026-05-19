# Acset × Tensor Logic Integration Section — Documentation Plan

> **This is a documentation plan, not a code implementation plan.** Each task below is a subsection to be written for `papers/acset.md`. Review the plan in full before writing anything. When approved, the content of each subsection can be inserted verbatim (or with light editing) at the end of `acset.md`.

**Goal:** Add a section to `acset.md` that describes how the tensor logic integration (from `tensorLogicNCDIntegration.md`) resolves most of the identified disadvantages of the acset approach, and establishes the dual-view pipeline (TensorProgram → terms + acset instances) as the correct architecture.

**Central argument:** `TensorEquation` is structurally isomorphic to an `SBrInstance` — it already encodes the same information in a slightly different form. Given that tensor logic is the primary user-facing construction interface, the "construction mismatch" dissolves, the operator is no longer absent, and UID-based axis identity already provides the gluing mechanism the acset framework needs. What remains genuinely in the term world — parallel composition and presentation — is precisely what tensor logic deliberately omits.

**Depends on:** The reader has read the preceding sections of `acset.md` (schemas, instances, advantages, disadvantages, mitigations) and §5 of `tensorLogicNCDIntegration.md` (`TensorEquation`, `TensorProgram`, `bc_signature()`).

---

## Section Structure

The new section has five subsections:

```
## Integration with Tensor Logic

### Tensor Logic as the Primary Construction Interface
### TensorEquation as a Proto-Acset
### The Dual-View Pipeline
### Revised Disadvantage Analysis
### Schema Revision: operator_tag
```

---

## Subsection 1: Tensor Logic as the Primary Construction Interface

**Purpose:** Establish the reframing. Terms are a machine-generated IR, not a user-crafted API. Both terms and acset instances derive from the same `TensorProgram` source.

**Content to write:**

> The earlier discussion of disadvantages assumed that the term representation — `StrideMorphism`, `Broadcasted`, `Composed`, `ProductOfMorphisms` — is the primary interface through which morphisms are constructed. `tensorLogicNCDIntegration.md` changes this assumption. Tensor logic is the user-facing construction interface: a user writes tensor equations in the DSL, `TensorProgram.to_morphism()` converts them to a `Composed` of `Broadcasted[B, A, TensorEquation]` morphisms, and the term structure is machine-generated output of a topological sort — not a hand-crafted expression of user intent.
>
> This reframes the term representation as an **internal IR**: a canonical form produced from the tensor logic source and consumed by the compiler, the renderer, and the `Context`-mediated axis unification machinery. Acset instances and terms are now both derived views of the same `TensorProgram` source, not competing representations of the same artifact. The question shifts from "should the acset replace the term?" to "when should each view be computed, and for what purpose?"

**Cross-reference:** `tensorLogicNCDIntegration.md §5.1` (integration boundary), `§5.5` (`TensorProgram.to_morphism()`).

---

## Subsection 2: TensorEquation as a Proto-Acset

**Purpose:** Show the direct, lossless mapping from a `TensorEquation` to the four tables of `SBrInstance`. This is the core technical argument.

**Content to write:**

Intro paragraph:

> `TensorEquation` is a frozen dataclass with named-tensor entities and typed `Axis` fields — structurally identical to what the acset schema $\mathcal{S}_{Br}$ captures in tabular form. The mapping between the two representations is direct and lossless; no information is invented or discarded.

Mapping table:

| `TensorEquation` field | `SBrInstance` table entry |
| --- | --- |
| `lhs_name` | One `Array` row with `is_input = False` |
| Each `(name, indices)` in `rhs` | One `Array` row with `is_input = True` |
| `(tensor, axis)` pair where `axis ∈ lhs_indices` | `ArrayAxis` row with `is_target = False` (degree / TILED) |
| `(tensor, axis)` pair where `axis ∉ lhs_indices` | `ArrayAxis` row with `is_target = True` (contracted) |
| Retained axis `i ∈ lhs_indices` appearing in input `X` | `Sample` row: `src = i`, `tgt = i`, `coeff = 1`, `reindexing_of = X` |
| `operator` field | `operator_tag` attribute on the output `Array` row |

Then a worked example of `Y[i, j] = W[i, k] X[k, j]`:

**Axis table:**

| `Axis` | `size` |
| --- | --- |
| $i$ | FreeNumeric |
| $j$ | FreeNumeric |
| $k$ | FreeNumeric |

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

Explanation paragraph:

> The degree is $(i, j)$ — the retained indices in `lhs_indices`. $W$ is indexed by degree axis $i$ (Sample $s_0$); $X$ is indexed by degree axis $j$ (Sample $s_1$). The contracted axis $k$ appears as a target axis (`is_target = True`) in both $W$ and $X$'s `ArrayAxis` rows and is summed over by the operator. No `Sample` rows reference $k$ — it is not part of any reindexing.

Multi-equation paragraph:

> A `TensorProgram` with multiple equations produces one `SBrInstance` per equation. The instances are linked by shared `Axis` UIDs: when `TensorProgram.to_morphism()` calls `ctx.append_iter` to unify the `lhs_indices` of one equation with the `rhs` input axes of the next, both the term and the acset tables carry the same canonical UIDs. The acset representation of a `TensorProgram` is therefore a sequence of `SBrInstance` values — one per `TensorEquation` — connected by UID-shared `Axis` rows, exactly as `Composed` connects `Broadcasted` morphisms by shared domain/codomain objects.

**Note on strided convolutions:** For non-einsum reindexings (strided convolution, diagonal slice), `coeff ≠ 1` in the `Sample` rows. This is already handled by the `Sample.coeff` attribute — no schema extension is needed.

---

## Subsection 3: The Dual-View Pipeline

**Purpose:** State the architecture clearly. Two views, one source.

**Content to write:**

Opening:

> Given the tensor logic integration, the correct architecture is a **dual-view pipeline**: `TensorProgram` is the source; terms and acset instances are complementary views generated from it, each suited to a different downstream use.

Pipeline diagram (ASCII, matching the style of the rest of the document):

```
               Tensor Logic DSL
                      │
                      ▼
               TensorProgram
              (TensorEquation objects
               with shared Axis UIDs)
               ╱                  ╲
              ▼                    ▼
           Terms               SBrInstances
   (Composed of Broadcasted)  (one per equation,
                               linked by Axis UIDs)
              │                    │
    ┌─────────┴─────────┐   ┌──────┴──────────────┐
    │ compilation        │   │ shape inference (Πφ)│
    │ rendering          │   │ structural matching │
    │ ProductOfMorphisms │   │ data migration      │
    │ Block structure    │   │ serialization       │
    └────────────────────┘   └─────────────────────┘
```

Two-column comparison:

| Terms | Acset instances |
| --- | --- |
| Needed for compilation (operator types, weave structure, code generation) | Needed for shape inference ($\Pi_\phi$, Kan extension) |
| Needed for rendering (`Block` metadata, `ProductOfMorphisms` layout) | Needed for structural pattern matching (kernel selection, fusion) |
| Encode the type-level operator (`Broadcasted[B, A, TensorEquation]`) | Encode the relational structure (queryable tables) |
| Generated by `TensorProgram.to_morphism()` | Generated by `acset.convert.from_tensor_program()` |

Closing:

> The two views are not competing representations; they are projections of `TensorProgram` optimised for different consumers. Generating both from the same source ensures they remain in sync without a round-trip conversion: the same `Axis` UIDs appear in the term's `Weave` objects and in the acset's `ArrayAxis` rows, so any `Context`-mediated unification is automatically reflected in both.

---

## Subsection 4: Revised Disadvantage Analysis

**Purpose:** Show which disadvantages dissolve given the TL integration, which are partially mitigated, and what the genuine residue is.

**Content to write:**

Opening:

> The disadvantages identified in the preceding section were assessed assuming the term is the primary construction interface. Given the tensor logic integration, several dissolve entirely and the remainder shrinks to a well-bounded residue.

Table:

| Disadvantage | Status | Reason |
| --- | --- | --- |
| Construction-oriented API mismatch | **Dissolved** | Tensor logic DSL is the construction interface; terms and acsets are both generated output |
| Operator absent from schema | **Dissolved** | `TensorEquation.operator` → `operator_tag` attribute on output `Array` row (see §below) |
| UID / cross-instance identity absent | **Dissolved** | Tensor logic already uses `Axis` UIDs throughout; sharing them as acset keys requires no new machinery |
| Symbolic sizes do not fit schema | **Dissolved** | DSL axis declarations already use `FreeNumeric`; `Numeric` as attribute type matches exactly |
| Loss of term / compositional structure | **Residual** | `Composed` from `TensorProgram` is a canonical topological sort, not user intent; acset captures the same equations without the incidental ordering. Residue: `ProductOfMorphisms` and `Block` |
| Schema rigidity for new operators | **Largely dissolved** | New operators are `TensorEquation.operator` subtypes; `operator_tag` is an enum attribute, no schema entity types change |
| Eager composition | **Largely dissolved** | `TensorProgram.to_morphism()` is already eager; the acset instance is no more eager than the term |
| Display metadata (`Block`) lost | **Residual** | `Block` lives above `TensorProgram`, is user-facing, and has no acset counterpart — intentionally |

Residue paragraph:

> The genuine residue — `ProductOfMorphisms` (parallel composition) and `Block` (presentation grouping) — is precisely the structure that tensor logic deliberately omits and that `tensorLogicNCDIntegration.md §4.3` catalogues as a gap. `ProductOfMorphisms` will be generated automatically from the dependency DAG analysis described in `§5.6` of that document; until then it is assembled by the caller above `TensorProgram.to_morphism()`. `Block` is a purely presentational annotation that has no bearing on mathematical content. Both belong in the term world; neither belongs in the acset schema.

---

## Self-Review

### Spec coverage

The section addresses all points raised in the conversation:

- ✅ Reframing terms as machine-generated IR
- ✅ Direct mapping TensorEquation → SBrInstance (with worked example)
- ✅ Dual-view pipeline diagram
- ✅ Revised disadvantage table
- ✅ `operator_tag` mapping (`TensorEquation.operator` → `OpTag`, part of baseline $\mathcal{S}_{Br}$ schema)
- ✅ What remains in term world (ProductOfMorphisms, Block)
- ✅ Cross-references to tensorLogicNCDIntegration.md

### Potential gaps

- The multi-equation case (TensorProgram → sequence of SBrInstances) is described but not illustrated with a second example. The prose explanation should be sufficient for the theory document; a full multi-equation table would be long without adding conceptual clarity.
- The generation function is `acset.convert.from_tensor_program()` — a standalone function in a new `acset/` package. **Zero existing files are modified.** The documentation text in the pipeline table has been updated to reflect this.
- The `operator_tag` partial-map notation should be consistent with how `max_value` is described earlier in `acset.md` (already described as a partial map). ✅ Consistent.

### Style consistency with acset.md

- Tables follow the same column ordering and header style. ✅
- Mathematical notation ($\mathcal{S}_{Br}$, $\mathcal{S}_{St}$, `\xrightarrow`) matches. ✅
- Cross-references use backtick filenames. ✅
- No emojis. ✅

---

## Notes for Writing

1. The section title is **"Integration with Tensor Logic"**. It comes after the "Advantages" section (i.e., at the very end of the file). The "Next Steps" section has been removed.

2. Add a horizontal rule `---` before the section heading to match the rest of the file.

3. The generation function is `acset.convert.from_tensor_program()` — a standalone function in the new `acset/` package. Zero existing pyncd files are modified. See the companion implementation plan `2026-05-17-acset-implementation.md`.

4. The pipeline diagram uses ASCII box-drawing that renders in GitHub markdown. Test rendering before final insertion.

5. The worked example axes ($i$, $j$, $k$) should use the same UID-carrying `RawAxis.named()` objects that the codebase uses, consistent with how examples are described in `theory.md`.
