# LeanNCD/Base

## Purpose
Owns: the noncomputable "math tower" — `ColoredPROP` (the shared categorical typeclass), `St` (affine/stride morphisms, mirrors Python `StrideMorphism`), `Br` (broadcast/tensor-op morphisms, mirrors Python's `Broadcasted`/`BroadcastedCategory`, formalized as a free strict symmetric monoidal category), `SizeExpr` (the computable axis-size type), and wiring combinators (`BrWiring`).
Does not own: parsing/compilation (`../DSL/`), evaluation semantics (`../Eval/`), or the acset/CSV bridge (`../Bridge/`, `../Acset/`) — all of those import from here.

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| Shared categorical typeclass (`SmallCategory`, `ColoredPROP`, `Elemental` mixin) | `ColoredPROP.lean` |
| Axis-size symbolic type (`SizeExpr`, `.eval`) | `SizeExpr.lean` |
| Signed reindex-coefficient ring (`Coeff := MvPolynomial String ℤ`) | `Numeric.lean` (12-line stub, post Spike-8c) |
| `StObj`/`Axis`, `StMat` (affine morphism), `St : ColoredPROP StObj` | `St.lean` |
| `BrObj`/`ArrayType`, `Hom`/`Rel`/`BrMorph`, `Br : ColoredPROP BrObj` | `Br.lean` |
| `Br`'s one open sorry (`brCancelPoint`) and its rationale | `Br.lean:252-307` |
| Wiring/fan-out/discard combinators (`pick`, `wiring`) | `BrWiring.lean` |

### Key Relationships
Import order (`LeanNCD.lean:97-113`): `Numeric` → `ColoredPROP` → `St` → `Br` → `SizeExpr`. `Br.lean` imports `St` (each `BrBase` carries St reindexings). `BrWiring.lean` imports only `Br`. Downstream: `Seam/Adapter.lean`, `Acset/SBrInstance.lean`, `Algebra/Target.lean`, `Bridge/*`, `DSL/{Ast,Target}.lean`, `Instances/StBr.lean` all import `Base.*` (verified via `grep -rl "LeanNCD.Base"`).

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `ColoredPROP`, `Elemental` mixin | `St`, `Br`, `Seam/Adapter.lean` | `Elemental` was demoted from a mandatory field to an opt-in mixin (2026-06-22) specifically to keep `Br`'s core instance sorry-free |
| `Coeff` (signed, ℤ not ℕ) | `StMat.coeffs`/`bias` | fixed `21864f7`: ℕ couldn't represent look-back offsets like `X[i-1]` |
| `SizeExpr` | `Axis.size`, DSL layer | the sole axis-size type since Spike 8c — computable/`DecidableEq`, unlike its noncomputable predecessor |
| `StObj`, `StMat`, `St : ColoredPROP StObj` | `Br.lean`, `Instances/StBr.lean` | instance NOT sorry-free — `swap_hexagon_fwd`/`swap_hexagon_rev` are deferred (`St.lean:269-270`); see Pitfalls |
| `BrObj`, `Hom`, `Rel`, `BrMorph`, `Br : ColoredPROP BrObj` | `Bridge/Realize.lean`, `Core/Weave.lean` | core instance (`Br.lean:397-424`) is sorry-free; only the opt-in `Elemental` mixin carries the deferred proof |

### Core Types
- `Axis := { name : Option String, size : SizeExpr }`, `StObj := List Axis` (`St.lean:9-14`).
- `StMat dom cod := { coeffs : Matrix (Fin cod.length) (Fin dom.length) Coeff, bias : Fin cod.length → Coeff }` (`St.lean:28-30`).
- `ArrayType := { dtype, shape : StObj }`, `BrObj := List ArrayType` (`Br.lean:10-14`).
- `Hom`/`Rel`/`BrMorph := Quotient (setoidHom a b)` (`Br.lean:53-141`) — raw syntax (`id`/`gen`/`comp`/`tensor`/`braid`/`copyW`/`delW`) quotiented by the SMC-law congruence.

## Entry Points
| Task | Start Here |
|------|------------|
| Add a new `ColoredPROP` law or field | `ColoredPROP.lean` — then re-prove it for both `St` and `Br` instances |
| Work on `brCancelPoint` | `Br.lean:252-307`'s doc block first, then `spikes/BrNF.lean` for the parked wiring-combinator approach |
| Add a new signed reindex coefficient use | `Numeric.lean`'s `Coeff` |
| Change axis-size representation | `SizeExpr.lean` |

## Contracts
- **`St.elemental` is proved** (`St.lean:363-383`): a stride matrix is fully determined by its action on points — proved via the zero point (bias) + one-hot points (coefficients column-by-column).
- **`Rel.copyW_*` laws are deliberately non-natural** (`Br.lean:121-134`) — no `Rel` constructor makes a general `gen` op commute with `copyW`, keeping `Br` a non-cartesian (Fox-style) gs-monoidal category.
- **`tensorHom_assoc`/unit laws use `HEq`, not `Eq`** (`ColoredPROP.lean:74-81`) — `tensor` is only strictly associative up to `List.append` equality, not defeq; both instances bridge this via dedicated `hext`-style lemmas rather than `simp [cast]` soup.

## Patterns
- **Cast-bridging via dedicated `hext` lemmas** (`St.lean:75-92` `StMat.hext`/`StMatAux.matrix_hext`/`fun_hext`; `Br.lean:313-317` `brHEq_mk_cast`) reduces `HEq` obligations to plain entrywise `Eq` goals — the house style here, not `simp [cast]`.
- **Isolate the hard proof, keep the instance sorry-free (`Br` only)**: `Br`'s core `ColoredPROP` instance is fully proved; its deferred content (`brCancelPoint`) is pushed into the opt-in `Elemental` mixin, never left inside the instance. `St` does NOT follow this pattern — its `swap_hexagon_fwd`/`swap_hexagon_rev` sorries (`St.lean:269-270`) sit directly inside the `St` instance.

## Pitfalls
- **`St` is NOT fully sorry-free — re-verify before assuming otherwise.** `swap_hexagon_fwd`/`swap_hexagon_rev` in the `St : ColoredPROP StObj` instance are `by sorry` (`St.lean:269-270`, tagged "hexagon for StMat swap, deferred"). All other `St` instance fields are proved: `id_comp`/`comp_id`/`comp_assoc`/`assoc` (40-59), `tensor_assoc`/`tensor_unit_l`/`tensor_unit_r` (181-186), `tensorHom_id`/`tensorHom_comp` (203-231), `swap_swap`/`swap_natural` (232-268), `tensorHom_assoc` (275-290), `tensorHom_unit_l`/`tensorHom_unit_r` (291-361), and `St.elemental` (363-383) — only the two hexagon fields are deferred.
- **`Br`'s one remaining sorry is `brCancelPoint`** (`Br.lean:305-307`). It is TRUE (a leading point generator participates in no `Rel` constructor) but not provable by direct induction — the `trans` (congruence-closure) case injects an unconstrained intermediate term that would itself need to be point-prefixed, circularly. Planned route: NbE/initiality (`eval`/`quote`/`sound`/`section_` against a canonical model `N`). A 2026-07 finding showed the prototyped bijective-wiring model (`spikes/BrNF.lean`, parked off the default build) structurally **cannot** represent the `copyW`/`delW` comonoid generators (a bijection `OutPort ≃ InPort` has no room for a 1-in-2-out node) — a non-bijective gs-monoidal/cospan model is needed instead, a larger undertaking than originally scoped. `brCancelPoint`'s only consumer is `weave_unique` (`Core/Weave.lean`), itself a deferred sorry; `weave_unique`'s only consumer is `weave_subsingleton` (`Props/Generic.lean:33-35`), a re-export with no further non-test consumer — nothing load-bearing depends on `brCancelPoint`.
- **`Numeric.lean` is now a 12-line stub** (post Spike-8c, commits `1843a81`/`725e98b`/`7831816`): only `abbrev Coeff := MvPolynomial String ℤ` remains. The old noncomputable `Numeric` size type is gone; `SizeExpr` (relocated from `DSL/`) is the sole axis-size type.
- **Root `LeanNCD.lean`'s doc header is stale on this exact point** (`LeanNCD.lean:10` still describes `Numeric = MvPolynomial String ℕ` for sizes) — despite a docs-fix commit, this line was missed. Don't trust that summary line; read `Numeric.lean` directly.
