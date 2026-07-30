# LeanNCD/Algebra

## Purpose
Owns: the *algebra functor* signature layer (§7.5 of `papers/leanncd.md`) — `Algebra`/`ParaAlgebra` (what a functor `F : C ⥤ V` evaluating a graded PROP into a target category must satisfy) and `TargetActegory` (what the target `V` must be: a right `D`-actegory over a scalar semiring `R`). Signature-first by design: classes and one real theorem exist; concrete instances (e.g. `Br → Mat ℝ`) are **deliberately deferred**, not merely unfinished.
Does not own: any concrete instantiation of these classes — none exists anywhere in the repo yet (verified: `grep -rl TargetActegory` only hits this dir's 3 files + its own test).

## Code Map

### Find It Fast
| Looking for... | Go to |
|---|---|
| `Algebra`/`ParaAlgebra` classes (functor `F`, equivariance laws) | `Algebra.lean:11-124` |
| `TargetActegory` class (`actV`, δ_V/δ0_V/υ_V/α_V coherences) | `Target.lean:14-65` |
| Default target `Mat R := FGModuleCat R` | `Target.lean:68` |
| Why no `Mat ℝ` instance exists (dimension-impossibility) | `Target.lean:70-78` |
| Why no `Bool` instance exists (XOR vs ∨/∧ semantics — read this first) | `Target.lean:80-116` |
| The one proven theorem in this subsystem | `Construct.lean:27-29` (`semiring_choice_split`) |

## Public API

### Key Exports
| Export | Used By | Change Impact |
|---|---|---|
| `class Algebra D C V R` | `ParaAlgebra`, tests | any future `Br → Mat ℝ` instance must fill `F`, `Fbraided`, `equivar*`, `F_ev_p` |
| `class TargetActegory D V R` | `Algebra` (as an instance binder), tests | any concrete `V` (e.g. `Mat ℝ`, or a future Bool/Rel target) must instantiate this |
| `abbrev Mat R := FGModuleCat R` | intended default target for `R = ℝ` | **no `TargetActegory _ (Mat R) R` instance currently exists** |
| `theorem semiring_choice_split` | witnesses the §7.5 R-choice narrative | fully proven, no dependency on any `TargetActegory` instance |

### Core Types
`Algebra`/`ParaAlgebra` generic over `D C : Type`, `V : Type*`, `R [CommSemiring R]`, requiring `[ColoredPROP D] [ColoredPROP C] [MonoidalCategory V] [SymmetricCategory V] [DGradedColoredPROP D C] [TargetActegory D V R]`. `TargetActegory` only requires `CommSemiring R` — deliberately weaker than `CommRing`, to allow non-ring value semirings like the intended `(∨,∧)` boolean semiring. `Mat R` itself requires `CommRing R` (needs additive inverses), which is exactly why a Boolean `Mat` target doesn't give you what you want (see Pitfalls).

## Entry Points
| Task | Start Here |
|------|------------|
| Understand the R=Bool trap before using `Bool` as a target scalar | `Target.lean:80-116` |
| Instantiate a concrete `TargetActegory`/`Algebra` | `Target.lean:70-78` first (why `Mat ℝ` was deleted, not just unfinished) |

## Contracts
- `Algebra` is a `class`, not a `structure`, specifically so `ParaAlgebra` can `extend` it.
- No file anywhere provides a `TargetActegory` instance for any concrete `V`/`R` — this is a deliberate gap, not an oversight; see Pitfalls for why `Mat ℝ` and `Mat Bool` both fail (for different reasons).

## Pitfalls
- **The `R = Bool` trap (the single most important thing to get right here).** Mathlib's `Bool` is a `CommRing` via `BooleanRing.toCommRing`, where `+` is **XOR** and `*` is `∧` — so `true + true = false`. The predicate/relational reading this formalization wants (`∃`-of-`∧` contraction) needs the **`(∨,∧)` semiring** instead — addition = `∨` (idempotent), which is a genuine `CommSemiring` but **not a ring** (no additive inverse for `∨`). Concretely: `Mat Bool = FGModuleCat Bool` **does typecheck** (Bool is a `CommRing`) — the failure is *semantic*, not a typechecking wall. Writing `TargetActegory StObj (Mat Bool) Bool` would silently give you something that computes over **XOR**, not `∨`/`∃` — a wrong-but-compiling formalization. This is exactly the bug fixed in commit `8f86671`: an earlier draft wrongly claimed `Mat Bool` fails to *elaborate* (it doesn't — it typechecks fine and is simply the wrong semantics), and `semiring_choice_split`'s second conjunct was originally stated as `true + true = true` (false under XOR). The fix restated it using `||` directly: `((1:ℝ)+1 ≠ 1) ∧ (true || true = true)`, deliberately bypassing `Bool`'s ring `HAdd` instance. **Never write `+`/`HAdd Bool` here expecting OR-semantics — use `||`/`∨` explicitly.** Building a real Boolean target requires a genuinely different `V` (e.g. `Rel`, or a finite join-semilattice/`Tropical`-style wrapper carrying `(∨,∧)` on `Bool`), not `FGModuleCat Bool`.
- **There are no live `sorry`s in `Construct.lean`/`Target.lean` — do not go hunting for them.** Any grep hit is inside a comment explicitly saying the opposite (e.g. "a genuine theorem (not a `sorry`)"; "NO instance is provided (was: 8 `sorry` fields)"). What actually happened: commit `eb09a6d` ("delete impossible Mat ℝ actegory/algebra instances", Spike 7a) **deleted** 17 sorry'd fields wholesale — the `TargetActegory StObj (Mat ℝ) ℝ` instance (8 sorries) and `Algebra StObj BrObj (Mat ℝ) ℝ` instance (8 sorries) plus `construct_correspondence` (1 sorry). What remains "unproven" is an **absence of an instance**, not a sorry to fill in place — the recorded reason is that a faithful dimension-appending `actV` over `FGModuleCat ℝ` is mathematically impossible given symbolic axis sizes and `δ_V`'s forced dimension-multiplicativity, deferred to a future concrete-`Nat`-sizes (`DenseTensor`) redesign.
- **`SORRY_INVENTORY.md`'s "Milestone H" entry is stale** relative to the current files — it still describes the pre-deletion state (`instAlgebraBrMatR`, `construct_correspondence` as live sorries). Trust the code, not that doc section, for this subsystem's status.
