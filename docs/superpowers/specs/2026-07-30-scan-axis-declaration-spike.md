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

The user preferred the explicit declaration rule over both. The slot-level family was explored in
full before that choice was confirmed; recorded here so it is not re-derived.

#### Slot-level notation — the four shapes explored (2026-07-30, NOT chosen)

⚠️ **Lexer constraint that eliminates the obvious candidate:** `'` is a legal identifier character
in Lean 4, so `l'` lexes as a *single ident* before any `tl_lhs_slot` production sees it. A postfix
marker must use a character that cannot appear in an ident. `+` and `*` are already claimed by the
affine productions (`Syntax.lean:190-193`), leaving `⁺`, `^`, `@`, `→`.

| # | Shape | Notes |
|---|---|---|
| 1 | `G[j, l⁺]` (ASCII `l^`) | Smallest diff; exact mirror of `freeNorm`'s postfix `.`. Leaves the base case anonymous (finding **G**). |
| 2 | `G[j, l@0]` / `G[j, l@+1]` | Symmetric — **also fixes finding G** by letting the base name its axis, retiring the positional recovery pass at `Structural.lean:849-851`. Cost: every existing base case changes (`G[j,0]` → `G[j,l@0]`), a far larger migration than this spike's. |
| 3 | `G[j, next l]` | Keyword form, using the keyword-category machinery Spike 3b added. Most explicit, most verbose. |
| 4 | *no new syntax* — let `ident "+" num` mean `.iterNext` at `num = 1`, and spell shift-by-1 as `1*l+1` via the **already-existing** `num "*" ident "+" num` production | Zero new tokens, no reclassification pass, and **no declaration requirement** — it fixes #5b outright, with both spacings converging for free. Rejected because `Out[i + 1] := …` in an existing program would *silently* change meaning from shifted-write to iteration-advance — the exact defect class #5b is about. Would need its own guard. |

**If the migration below proves painful, #4 is the documented fallback** — it is the cheapest fix
for #5b considered in isolation, at the cost of leaving iteration axes implicit.

## Proposed syntax for the chosen (declaration) option

**Recommendation: a new `iter` declaration keyword, in the pinned form only.**

```
iter l = 3
```

`iter` is free — grep confirms no `tl` program uses `iter` as an identifier, so introducing the
keyword collides with nothing. It joins `tensor` / `predicate` / `linear` / `axis` as a fifth
`tl_decl` (`Syntax.lean:76-82`).

```lean
-- Syntax.lean, beside the existing `axis` production
syntax "iter" tl_iter_decl_item,+ : tl_decl
syntax ident "=" num              : tl_iter_decl_item   -- ONLY this form. No unpinned variant.

-- Ast.lean
| iter : AxisSpec → Nat → Decl   -- note: `Nat`, NOT `Option Nat`
```

**Why this shape — two whole error classes become ungrammatical rather than validated:**

1. **No unpinned production ⟹ "declared but unpinned" cannot be written.** This collapses Part 2's
   two failure modes into one ("axis used as a recurrence but never declared `iter`"), so
   `CompileError.scanAxisNotPinned` needs to describe only that.
2. **The keyword fixes the kind**, so `iterAxisNotNat` (`Structural.lean:700`) becomes unreachable
   for any declared iteration axis. This is why the kind is *omitted* from the surface form: writing
   `iter l : ℕ = 3` would preserve the visual parallel with `axis` but reintroduce a spelling that
   can be wrong.

⚠️ **Finding H makes the "pinned" test subtle — get this right.** The extent pin and the axis
*kind* are two independent channels, and only one of them is live: `axis l : ℕ[3]` parses into
`AxisKind.nat (some (.lit 3))` and **pins nothing** (probed — it behaves identically to declaring
no axis at all; see audit finding **H**). So the check must test the `Decl` payload, never the kind:

```lean
-- CORRECT                                  -- WRONG: `ℕ[3]` is a decoy that passes this
| .iter _ _ => pinned                       | .axis ax _ => hasSize ax.kind
| .axis _ (some _) => pinned
```

Consider closing H in the same pass — either wire the kind size into `explicitSizes`
(`Lowering.lean:176-178`) or reject the `ℕ[…]`/`ℝ[…]` forms. Leaving a no-op pin in the language
while adding a rule that *requires* a pin is a trap for the next reader.

### Strict vs permissive — decide this before implementing

This is the one open decision, and it is a **migration-cost fork**, not a design fork:

| | Rule | Migration |
|---|---|---|
| **Strict** *(recommended)* | `iter` is the **only** way to declare an iteration axis | **~33 sites.** The ~10 in the table below, **plus the ~23 axes already declared `axis l : ℕ = N`** that must switch keyword. |
| **Permissive** | Require a *pinned* declaration by **either** keyword; `iter` is sugar that also pins the kind | **~10 sites** (the table below only). But iteration-ness stays non-explicit at the declaration site, which was the point of choosing this option. |

Strict is recommended because it delivers the explicitness the option was chosen for, and the extra
~23 edits are a mechanical keyword swap with no semantic change. **The ~23 figure is derived from
the "already declared" column below and has not been re-grepped — confirm it during planning.**

### What this option does NOT fix

Audit finding **G**: a base case still does not name its own axis (`.iterAt (scanAxis "") n`,
`Elab.lean:244`), so `finalizeScans` keeps recovering it **by slot position**
(`Structural.lean:849-851`). A declaration cannot fix a slot-level anonymity — only slot option 2
above would. The single-iteration-axis case *could* be resolved by declaration instead of position;
whether to do that is out of scope here and tracked as finding G.

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

**Part 2 — a new named rejection.** The rule has TWO failure modes, so decide whether they share one
error or get two:
  * the recurrence axis has no `Decl.axis` at all, and
  * it has one but with no pinned extent (`axis l : ℕ` — `Decl.axis a none`).
Suggested: one `CompileError.scanAxisNotPinned : String → CompileError` covering both (the message can
distinguish them), since the *pin* is the actual requirement and "declared but unpinned" must fail too
— an `…NotDeclared` name would under-describe it. Follow the Task-0 / #4 precedent: place the check in
the Structural validation phase so it runs in **both** `TLProgram.compile` and `compileToScheduled`.

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
