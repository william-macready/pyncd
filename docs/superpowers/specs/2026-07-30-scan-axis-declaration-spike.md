# Spike: declared iteration axes + spacing-insensitive recurrence syntax (#5b)

> **Status:** DESIGN SETTLED with the user 2026-07-30; NOT IMPLEMENTED. This is a **breaking
> language change** — write a plan from this spec, then execute subagent-driven. Do not start
> editing without the plan: Parts 1–5 below are coupled, and a half-applied grammar change is
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

### Effect on finding G — it becomes resolvable or loud, though not closed

A base case still does not *name* its own axis (`.iterAt (scanAxis "") n`, `Elab.lean:244`); closing
that needs slot option 2. But `iter` supplies the signal the positional pass lacks, so G stops being
a silent-wrong-answer path. **This is a refinement of an earlier note here that said the declaration
option "does not close G" and stopped there** — true about *closing*, incomplete about the effect.

The mechanism, read precisely (`Stmt.adoptBaseIterAxes`, `Structural.lean:827-835`): each base
`.iterAt _ n` at position `p` adopts `step.stepAxisAt p`, and **on a miss it is "left as-is"** —
keeping the placeholder (`name ""`, `uid 0`), documented at `:824-825`. Grouping is by iteration-axis
UID, so an un-adopted base lands in a uid-0 group, *separate from its own recurrence*: the boundary
never gets initialised and the state is silently zero-filled instead.

**No existing guard covers this.** `outputAxesConsistent` (`Lowering.lean:457-460`) is a different
check — it compares the outputs of one *already-grouped* coupled scan (`G[j,l]` vs `H[l,j]`) on the
routed path, after grouping. Nothing in `finalizeScans` enforces base↔recur slot-order agreement.

See `papers/semantic_payload_audit.md` finding **G**. Fold it in here as **Part 5**:

1. **Single-candidate rule (position-independent).** If the matching step has exactly one `iterNext`
   axis and the base exactly one `iterAt` slot, adopt it **regardless of position**. This removes G's
   failure mode outright for single-axis scans — the common case per Part 3's table — and needs *no*
   declaration, so it could ship independently of this spike.
2. **Positional fallback** for genuinely multi-axis scans, unchanged.
3. **Fail loud on a miss.** Replace the "left as-is" arm with a named rejection, so an un-adopted
   base can no longer flow onward as a uid-0 placeholder:

```lean
| unresolvedBaseIterAxis : String → CompileError
--  "base case of 'G' pins a slot with no corresponding iteration axis in its recurrence"
```

   This means `adoptBaseIterAxes` becomes `Except`-returning. With `iter` available, strengthen the
   check: the adopted axis must also be declared `iter`.

⚠️ **Do not test the placeholder by `uid == 0`** — `uid 0` is a legitimate UID (`scanAxis` merely
*defaults* to it). Detect a miss structurally, at the point adoption fails.

⚠️ **G is UNPROBED.** Verified: the miss arm keeps the placeholder, and no `finalizeScans` check
guards it. NOT verified: a program that triggers it. The routed path may incidentally catch the
resulting base-only group via `stepGuardOk`'s `!outputs.isEmpty` (`Lowering.lean:466-467`); whether
the eval path catches it is unknown. **Write the failing program first** — if it turns out
unreachable, Part 5 reduces to the defensive rejection in step 3 and should be scoped down.

## Implementation shape — Parts 1–4 (Part 5, for finding G, is specified above)

Two of these are **separable and should ship as their own commits, ahead of the rest**: Part 2b
(finding H — a mechanical 70-site type change) and Part 5 step 1 (the single-candidate rule, which
needs no declaration). Neither depends on `iter`.

**Part 1 — grammar/elaboration.** `elabTLLHSSlot` is `Syntax → MetaM LHSSlot` and **cannot see
declarations**, so the disambiguation cannot happen there. Elaborate *both* spellings uniformly to
`.affine (.shift x 1)`, then **reclassify after `resolveDecls`**: a slot `.affine (.shift a 1)` whose
axis `a` is declared `Decl.iter` becomes `.iterNext a`. (Under the *permissive* variant the predicate
widens to `Decl.iter _ _ | Decl.axis _ (some _)`. It must test the `Decl` payload, which is the only
extent channel — and once Part 2b lands, the `AxisKind` decoy that made this worth warning about no
longer exists.) Precedent: `lowerArith`
(`Structural.lean:803-814`) already reclassifies `.assign` → `.scatter` in a post-resolution pass.
Keep `ident "+1"` working (it is the documented form and is used widely) — the reclassifier makes the
two paths converge.

⚠️ Verify: does anything rely on `.iterNext` existing *before* `resolveDecls`? `finalizeScans` runs
after, which is the phase that consumes `iterInfo`, so this should be safe — but check
`checkDtypes`'s `iterAxisNotNat` / `normAxisNotReal` (`Structural.lean:697-703`), which inspect slot
kinds and may run earlier.

**Part 2 — the named rejections (TWO of them).** Place both in the Structural validation phase, per
the Task-0 / #4 precedent, so they run in **both** `TLProgram.compile` and `compileToScheduled`.

*2a — the recurrence rule.* Because the proposed `iter` production is **pinned-only**, "declared but
unpinned" is ungrammatical and the rule has just **one** failure mode: an axis used as a recurrence
that is not declared `iter`. Name it for what it tests:

```lean
| scanAxisNotIter : String → CompileError
--  "axis 'l' is used as a scan recurrence but is not declared; add `iter l = N`"
```

⚠️ Under the *permissive* variant the two modes return (no declaration at all / `axis l : ℕ` with no
pin), and the error should then be named `scanAxisNotPinned` — the *pin* is the requirement, so a
`…NotDeclared` name would under-describe it. **Pick the name after the strict/permissive fork is
settled; the earlier draft of this spec assumed the permissive shape.**

*2b — delete `AxisKind`'s payload; there is no 2b rejection (closes finding **H** at the root).*

**REVISED 2026-07-30 after review.** An earlier draft of this spec proposed keeping the `ℕ[…]`
production and adding `CompileError.unsupportedAxisKindSize`. **That was wrong, and wrong in a way
worth recording:** it contradicted the very argument used for `iter` one section above. There the
reasoning is *make the bad state ungrammatical rather than validated, because that eliminates the
error class*; for H the draft argued the opposite — keep it grammatical so the rejection is testable.
Both cannot be right. Testability of a rejection is instrumental, not terminal: a test protects a
*check* from regressing, and if there is no check because the state is unrepresentable, there is
nothing to protect. Deletion is also strictly stronger — a validation check can be bypassed by a new
entry point (precisely the Task-0 / #4 trap, where a check on one path missed the other), whereas a
deleted production returns only if someone consciously re-adds syntax. "Keep it for the future size
solver" was speculative flexibility of the kind CLAUDE.md §2 forbids.

**Nor is the syntax the root cause** — a programmatically built AST can carry the dead size whatever
the grammar says. The root cause is the payload on the type:

```lean
-- Ast.lean:7-9   BEFORE                        AFTER
inductive AxisKind                              inductive AxisKind
  | real : Option SizeExpr → AxisKind             | real
  | nat  : Option SizeExpr → AxisKind             | nat
```

`AxisKind` is mentioned in **only five places** in `LeanNCD/` — its definition (`Ast.lean:7-9`), the
`AxisSpec.kind` field (`Ast.lean:15`), the elaborator (`Elab.lean:35,63,65`), and `isNat`/`isReal`
(`Structural.lean:688-689`), which **discard the payload with `_`**. Nothing else anywhere, including
no acset/CSV serialization. The payload is therefore *provably* write-only.

**The change:**

1. Drop the `Option SizeExpr` from both `AxisKind` constructors.
2. Delete `syntax "ℝ[" tl_size "]"` / `syntax "ℕ[" tl_size "]"` (`Syntax.lean:55,57`) and their two
   elaborator arms (`Elab.lean:37,39`). `elabTLAxisKind` then has no recursive or `elabTLSize` call
   left, so its `partial` can go too.
3. Mechanically rewrite the construction sites: `.real none` → `.real`, `.nat none` → `.nat`, and
   `.real (some (.lit 2))` → `.real`. Measured 2026-07-30: **70 sites across 20 files** — wide but
   purely mechanical, and a net simplification (`isNat`/`isReal` collapse to a two-constructor match).

**No `CompileError` and no test are needed** — the bad state becomes a *type* error. That is the point:
level 3 removes the rejection and its test rather than adding them.

**Evidence this is a live trap, not a cosmetic one.** The property oracle writes the same size twice,
through both channels — dead and live:

```lean
private def l1 (L : Nat) : AxisSpec := ⟨"l", 202, .nat (some (.lit L))⟩   -- DEAD, never read
  decls := [.axis j1 (some 2), .axis l (some L), …]                       -- LIVE
```

All 15 sites carrying a kind size are of this shape, which is why deleting only the *grammar* (level
2) would be insufficient: those sites would keep writing a size nothing reads.

⚠️ **Consequence to state explicitly, not discover later: `tl_size` becomes orphaned.** Its only
non-self references are the two bracket forms being deleted, so afterwards the whole category
(`Syntax.lean:21,45-51`) and `elabTLSize` (`Elab.lean:23-33`) are reachable **only from
`test/DSL/SizeExprTest.lean`**, which quotes `` `(tl_size| …) `` directly.

**DO NOT delete `tl_size` — H is an unfinished feature, not accidental cruft.** `papers/leanncd.md`
**specifies** it (`:1421-1431`, "Layer 1", with the comment *"bracket holds a `tl_size` term
elaborating to `SizeExpr`, §14.3"*). Deleting it is therefore a **spec deviation needing a paper
update**, not a cleanup. This also explains the 15 oracle sites that write kind sizes: the authors
were following the specified design, and the consumer was simply never built. The paper's own
resolution is the third option — *finish* it by wiring `ℕ[n]` to the affine size solver — which is out
of scope here but should be named as the intended endpoint rather than left implicit.

Deleting it is mechanically safe (the cost is exactly the four `run_cmd` blocks at
`SizeExprTest.lean:40-67`; the 20 `SizeExpr` guards at `:10-38` never touch `tl_size`), so this is a
judgement call, not a constraint. Related: **`SizeExpr.eval` also has zero production callers** —
`Base/SizeExpr.lean:21-27`, self-recursive only. `SizeExpr` is used in production purely as inert
labels (`AxisP.mk (some a.name) (SizeExpr.var a.name)`). It belongs in the same bucket: keep, record.

**Why this is not the argument retracted above.** What made H dangerous was **reachability** —
`axis l : ℕ[3]` was writable in a real program and silently did nothing. Part 2b removes exactly
that. Afterwards `tl_size` cannot mislead anyone, because no program can reach it. The trap was the
bracket form *in an axis declaration*, not the size parser behind it. Keeping a live trap is
speculative flexibility; keeping inert, tested, unreachable machinery that a specified feature will
need is just CLAUDE.md §3 (mention dead code, do not delete it).

⚠️ Do **not** lean on "JAX will want symbolic shapes" as justification — plausible given the terminal
`EvalPlan` goal, but unverified. The paper specification is the load-bearing reason; that intuition
is not.

Note `axis l : ℕ[3] = 5` is grammatical today — two size channels, bracket silently ignored. This
makes it unparseable.

**Separable.** Nothing about `iter` depends on 2b, so it can ship as its own commit *ahead* of the
spike, which shrinks the spike by one error and one test. Recommended, since it also touches 20 files
and is better reviewed on its own.

**Part 3 — migration (~10 recurrences, 6 files, plus 5 AST sites).** Add `iter` declarations to the
surface-syntax programs that lack them. Measured 2026-07-30 (surface `tlprog!` programs only):

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

**`ScanGen`/`ScanUnroll` need no *surface* migration** — the property oracle's 3,832 programs are
built programmatically (`.assign "S" [.free j1, .iterNext l]`) and already declare
`decls := [.axis j1 (some 2), .axis l (some L), …]`. An earlier estimate wrongly listed them by
grepping for the *surface* `axis … : ℕ` in files that use the AST constructor.

⚠️ **But under the strict variant they ARE affected at the AST level** — a prior version of this note
said "NOT affected" without that qualifier. Every programmatic `Decl.axis` for an *iteration* axis
must become `Decl.iter`. Re-measured 2026-07-30: **5 sites**, all declaring `l`, all in
`test/Eval/PropertyOracle/ScanGen.lean` (`:48, :66, :85, :108, :126`). The other pinned AST decls
(`PropertyOracleTest.lean:15,36`, `Gen.lean:21`, `ScanGen.lean:146`) are ordinary axes and stay
`.axis`. So the 3,832-program blast radius costs **5 edits**, not 3,832 — but the count is not zero,
and `ScanGen.lean:146` (`r6`/`c6`, no `l`) is the case to check by hand, since it is a scan-shaped
generator whose axes are *not* named `l`.

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
graph, so full rebuilds run minutes, not seconds). No `sorry`/`maxHeartbeats`/`native_decide`.

**Three** tests, one per behavioural rule. **Each must be mutation-tested** — revert the fix and
confirm the test fails — because three of the bugs in this cluster were "guarded" by a comment
asserting they could not happen, and finding #4 was documented by a test that could never have caught
it (it asserted the op *tag* while the payload was discarded).

1. **Both spacings produce the same `LHSSlot`** (`l +1` vs `l + 1`). The regression guard for #5b
   itself; nothing else would catch a reintroduced divergence.
2. **`scanAxisNotIter`** — a recurrence over an undeclared axis is rejected at compile.
3. **`unresolvedBaseIterAxis`** (finding G) — *write this one first and expect it to be hard.* If no
   program can be constructed that reaches the miss arm, say so explicitly and scope Part 5 down to
   the defensive rejection; do not report a passing suite as evidence that G was closed.

**Finding H gets no test, deliberately** — Part 2b makes the state a *type* error, so there is nothing
runtime to assert. Its verification is that the build still passes after the 70-site rewrite, plus
`#print axioms` unchanged on the touched declarations. If you find yourself writing a test for H, the
change has drifted back to level 1 (validate a still-representable state) — stop and re-read Part 2b.
