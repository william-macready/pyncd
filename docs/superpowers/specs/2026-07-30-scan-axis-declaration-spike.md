# Spike: declared iteration axes + spacing-insensitive recurrence syntax (#5b)

> **Status:** DESIGN SETTLED with the user 2026-07-30; NOT IMPLEMENTED. This is a **breaking
> language change** — write a plan from this spec, then execute subagent-driven. Do not start
> editing without the plan: the four parts below are coupled, and a half-applied grammar change is
> the worst state to leave the repo in.

## The bug being fixed (finding #5b, confirmed by probe)

`ident "+1"` is a **single atom token** in the grammar (`DSL/Syntax.lean:192`), so an LHS slot's
meaning depends on **whitespace**:

```
`l +1`   =>  LHSSlot.iterNext { name := "l", kind := AxisKind.nat  none }   -- scan recurrence
`l + 1`  =>  LHSSlot.affine (IdxExpr.shift { name := "l", kind := .real none } 1)  -- shifted WRITE
```

Confirmed by elaborating both forms (`Elab.lean:245` vs `:252`). It even flips the axis **kind**.
With `l + 1`, `finalizeScans` finds no `iterNext` slot and emits a degenerate `SCAN … axes=[]`,
which `evalScan`'s `axes.isEmpty` guard then rejects with an unrelated message. **The natural
spacing silently means something else rather than failing** — worse than a parse error, and the same
class of defect Spike 3 removed for `Nonlin`.

## The decision (made with the user)

1. **Accept both spacings** — `l +1` and `l + 1` mean the same thing.
2. **Require a declared AND PINNED iteration axis for scans** — an axis used as a recurrence must be
   declared *with an explicit extent*: `axis l : ℕ = N`.

   ⚠️ **The pin is the load-bearing half, and it is NOT implied by declaration.** There is no
   dedicated iteration-axis notation in this language; `axis` gives kind + *optional* size —
   `Syntax.lean:64-65` are two separate productions and `Decl.axis : AxisSpec → Option Nat → Decl`
   has the pin as `Option`. So `axis l : ℕ` alone would disambiguate the slot but would **not** close
   #5: an unsized iteration axis would remain constructible. Requiring `= N` is what closes it.

Clause 2 is what makes clause 1 *safe*: accepting both spacings destroys the only signal currently
distinguishing "iteration advance" from "shift by 1", and a declaration restores it **semantically**
rather than typographically. Clause 2 also closes finding **#5** at the source — *because it requires
the extent pin*, not merely because the axis is declared (an earlier draft of this spec wrongly
asserted "a declared axis is a sized axis"). `evalScan`'s unsized check then becomes defence-in-depth
for programmatically-built ASTs rather than the primary gate.

### How iteration axes are notated TODAY (established 2026-07-30)

There is **no dedicated iteration-axis declaration**. The role is notated **by use, on the LHS slot**:
`G[j, 0]` ⇒ `.iterAt` (base case), `G[j, l+1]` ⇒ `.iterNext` (advance). The only tie between a
declaration and the role is one-way: `iterAxisNotNat` (`Structural.lean:699`) requires an axis used in
`iterAt`/`iterNext` to be ℕ-kinded — necessary, not sufficient, since most ℕ axes are not iteration
axes. `scanAxis` (`Elab.lean:88`) is an internal `AxisSpec` builder, not user syntax.

### Alternatives considered and rejected by the user

- **Disambiguate on the base case** — the machinery already exists (`CompileError.missingBaseCase`
  already rejects a recurrence lacking one). Non-breaking, but leaves iteration axes implicit.
- **A slot-level advance marker** — idiomatic here: `freeNorm` is already marked by a postfix dot at
  the slot (`syntax:max ident "." : tl_lhs_slot`, `Syntax.lean:195`). Needs no reclassification pass,
  no migration, and no language-surface reduction, at the cost of new syntax.

The user preferred the explicit declaration rule over both.

## Implementation shape — four coupled parts

**Part 1 — grammar/elaboration.** `elabTLLHSSlot` is `Syntax → MetaM LHSSlot` and **cannot see
declarations**, so the disambiguation cannot happen there. Elaborate *both* spellings uniformly to
`.affine (.shift x 1)`, then **reclassify after `resolveDecls`**: a slot `.affine (.shift a 1)` whose
axis `a` is a declared `Decl.axis` (nat kind) becomes `.iterNext a`. Precedent: `lowerArith`
(`Structural.lean:803-814`) already reclassifies `.assign` → `.scatter` in a post-resolution pass.
Keep `ident "+1"` working (it is the documented form and is used widely) — the reclassifier makes the
two paths converge.

⚠️ Verify: does anything rely on `.iterNext` existing *before* `resolveDecls`? `finalizeScans` runs
after, which is the phase that consumes `iterInfo`, so this should be safe — but check
`checkDtypes`'s `iterAxisNotNat` / `normAxisNotReal` (`Structural.lean:697-703`), which inspect slot
kinds and may run earlier.

**Part 2 — a new named rejection.** Add `CompileError.scanAxisNotDeclared : String → CompileError`
for a recurrence on an undeclared axis. Follow the Task-0 / #4 precedent: place the check in the
Structural validation phase so it runs in **both** `TLProgram.compile` and `compileToScheduled`.

**Part 3 — migration (~10 recurrences, 6 files).** Add `axis` declarations to the surface-syntax
programs that lack them. Measured 2026-07-30 (surface `tlprog!` programs only):

| File | recurrences | already declared | needs |
|---|---|---|---|
| `Eval/Portfolio/RecurrenceTest.lean` | 10 | 10 | — |
| `Eval/EvalExamplesTest.lean` | 5 | 4 | ~1 |
| `Eval/Portfolio/GenerativeTest.lean` | 5 | 3 | ~2 |
| `Eval/Portfolio/RejectTest.lean` | 4 | 3 | ~1 (**but see RJ6 below**) |
| `Eval/Portfolio/ConvPoolTest.lean` | 3 | 2 | ~1 |
| `Eval/Portfolio/ClassicalMLTest.lean` | 2 | 1 | ~1 |
| `DSL/Pipeline/ScanAffineTest.lean` | 2 | 0 | 2 |
| `DSL/ParseExamplesTest.lean` | 2 | 0 | 2 |
| `Eval/Portfolio/FeedforwardTest.lean` | 1 | 0 | 1 |
| `DSL/ParseProgramTest.lean` | 1 | 0 | 1 |

**`ScanGen`/`ScanUnroll` are NOT affected** — the property oracle's 3,832 programs are built
programmatically (`.assign "S" [.free j1, .iterNext l]`) and already declare
`decls := [.axis j1 (some 2), .axis l (some L), …]`. An earlier estimate wrongly listed them by
grepping for the *surface* `axis … : ℕ` in files that use the AST constructor.

**Part 4 — RJ6's semantics change again.** `RejectTest`'s RJ6 program deliberately has **no** axis
pin; under the new rule it is rejected at **compile** (undeclared axis) rather than at eval. Update
its assertion and its note. Its whole point is the unsized case, so keep it — the rejection just
moves earlier and gets a better name. Also note the program is deliberately written `l + 1` to
exercise #5b; after this change both spacings converge, so the note explaining the spacing must be
rewritten rather than deleted.

## Consequence to decide during planning

Requiring a *pinned* declaration removes **extent inference from an input** for *iteration* axes specifically
(RJ6's note describes "no `axis l` pin **and no input fixing `l`**", implying an input can currently
fix it). Confirm whether any surviving program relies on that, and state the removal explicitly in
the completion report — it is a language-surface reduction, not just a validation addition.

## Verification

`lake build` green (baseline **8610 jobs**; `Eval/Scan.lean` and `Structural.lean` are deep in the
graph, so full rebuilds run minutes, not seconds). No `sorry`/`maxHeartbeats`/`native_decide`. Add a
test asserting **both spacings produce the same `LHSSlot`** — that is the regression guard for #5b
itself, and nothing else would catch a reintroduced divergence.
