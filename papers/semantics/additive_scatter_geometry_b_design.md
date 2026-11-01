# Scatter geometry slice B: groups, boxed writers, surface syntax

**Execution update (2026-11-01).** T1-T6 were replayed verbatim on local `main` base `fd922285`;
all 36 stage-specific blob checks and all prescribed builds passed (final graph: 8844 jobs).
The real mutation manifest passed 18/18 with byte-identical restoration. Review and integration
evidence is maintained in [the execution record](additive_scatter_geometry_b_record.md).
The pre-implementation descriptions and probes below remain the approved historical design.

**Scope approved 2026-10-30 (slice A design note, D6: "A then B") and the one new choice, the constant
marker spelling `S[=3]`, approved by the owner on 2026-10-31. Not an implementation plan: the plan exists as
[additive_scatter_geometry_b_plan.md](additive_scatter_geometry_b_plan.md) (this note stays binding; its
section 4 task list became the plan's T1-T5).** Read against
local `main` `eab7dded`. Claims about current code were read from the tree on 2026-10-31; claims marked
**(probe)** are what the prototype dispatch must confirm before the plan ships. Slice A's design note
([additive_scatter_geometry_design.md](additive_scatter_geometry_design.md) section 5, "Slice B") and record
([additive_scatter_geometry_a_record.md](additive_scatter_geometry_a_record.md), "Parked scope") are the
sources; this note adds nothing to their semantics.

## 1. Where slice A left things

| Piece | State on `main` |
| --- | --- |
| Semantics | Reference, legacy and checked backends accept `S[a+b]` and a constant write (rewritten to `n + 1*u` over a synthetic size-1 axis `#const<uid>` by `lowerArith`); extent is the exact reach (M1). |
| Collector admission | `LHSSlot.boundedScatter` (`DSL/Ast.lean`) refuses a multi-axis slot (via `scatterAffineClass`) and refuses the lowered constant through a NAME test (`IdxExpr.isConstUnit`, prefix `constUnitPrefix`). Callers: `boxedSingleGroups` and `checkWriterGroup` (`DSL/Pipeline/Collect.lean`). Groups of these writers fail with `multiWriterScatter`; a boxed single writer keeps the derived shape (B5c D2). |
| Name reservation | `checkReservedAxisNames` (`DSL/Pipeline/Structural.lean`, first phase of both chains in `DSL/Compile.lean`) throws `CompileError.reservedAxisName` (`Exec/Uid.lean`) for a source axis spelled `#const...`. Exists only because the marker is a name. |
| Oracle | `declaredShapeWins` (`Semantics/Source/Differential.lean`) mirrors the boxed-writer rule and excludes constant and multi-axis forms (its `bounded`). |
| Surface | `elabTLLHSSlot` (`DSL/Elab.lean`) parses `x`, `x .`, `n` (scan base case `.iterAt`), `x +1`, `n*x`, `x+n`, `n*x+m`. No multi-axis form, no constant form. |

## 2. Decisions

* **B-D1 Admission (closes B5c D2).** Top-level groups and boxed single writers accept multi-axis and
  lowered-constant slots. After the marker is gone the only slot `boundedScatter` still has a reason to
  refuse is a raw `.affine (.const _)`, which only a hand-built schedule that skipped `lowerArith` can
  carry. It is refused by CONSTRUCTOR, not by name. `checkCollectorShapes`/`CollectorShape.lean` already
  call `outExtent` per slot, so they need no new arithmetic **(probe)**. Whether the predicate keeps the
  name `boundedScatter` is a plan-time call (cost: its four references).
* **B-D2 Delete the marker and its reservation.** Remove `IdxExpr.isConstUnit`, the name-based branch of
  `boundedScatter`, `checkReservedAxisNames`, `CompileError.reservedAxisName` and their pins; the
  synthetic axis keeps a readable name but nothing reads it. This is what the A record promised ("slice B
  deletes the marker, and with it this reservation"). Anti-goal: no behaviour may depend on an axis NAME
  (the A2 defect).
* **B-D3 Shape change, stated.** A single constant or multi-axis writer into a destination declared with
  every axis pinned now publishes the DECLARED shape (and a writer reaching past the box fails with
  `writerExtentExceedsBox`). Today such a program publishes the derived shape. Only hand-built and
  programmatic programs reach it today (the surface cannot say either form), and the D5 idiom exclusion
  (a declared axis that is also one of the writer's source axes keeps the derived shape) is unchanged.
  The prototype measures which existing fixtures move **(probe)**.
* **B-D4 Surface.** Multi-axis: `a + b`, `n*a + m*b`, any number of axis terms (at least two), each
  `ident` or `num * ident`, with an optional trailing numeral bias, elaborated to `.affine bias [(c, axis)…]`.
  Existing single-axis arms keep their current constructors (pinned by `CompileTest` and
  `ScatterCompileTest` S9). Constant: **`S[=3]`** (owner, 2026-10-31), elaborated to `.affine (.const 3)`;
  a lone numeral stays the scan base case. Coefficients and biases stay non-negative numerals. Whether
  `[=3]` tokenizes without a space and parses unambiguously beside `x +1` / `x + n` / `n*x + m` is a
  **(probe)**; fallback spelling `S[= 3]` if not.
* **B-D5 Scan-local stays refused**, with a fixture that a `[=n]` slot inside a scan statement fails loudly
  (no silent overwrite, F3).
* **B-D6 Oracle.** `declaredShapeWins` is updated to the B-D3 rule. Factoring one shared predicate with
  `boxedSingleGroups` (parked at about 0.5 dispatch by slice A) is taken only if it falls out cheaply.

## 3. Non-goals and anti-goals

* Not in scope: scan-local multi-axis/constant (F3), predicate/bool destinations, negative coefficients or
  biases in surface syntax, `route`/JAX scatter capability, the other slice A parked nits.
* Anti-goals: a name-based or otherwise forgeable marker; reinterpreting a lone numeral; a second extent
  formula; a constant or multi-axis write silently skipped or clamped; changing the single-axis
  stride-aligned extent.

## 4. Size and process

Full path (new capability on a soundness surface). Tasks: T1 engine (admission, marker deletion, oracle
mirror, group/boxed fixtures), T2 surface syntax and fixtures, T3 docs. Authoring runs as two prototype
dispatches (engine, then surface on top of it) and then a write-up from their patches. Guess: about 35M
authoring, about one executor dispatch per task.
