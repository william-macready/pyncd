# Spike: declared iteration axes + spacing-insensitive recurrence syntax (#5b)

> **Status:** DONE 2026-07-31. **All parts of this spec are now shipped** — Parts 2b (finding H)
> and 5 (finding G) landed first (2026-07-30, as recorded below), and **Parts 1, 2a, 3, 4 (the
> `iter` keyword + STRICT migration) landed 2026-07-31** across a 9-task implementation/verification
> plan: `iter <ident> = <num>[, <ident> = <num>]*` is now the ONLY way to declare a scan iteration
> axis; `l +1` and `l + 1` elaborate identically; a compile-time `CompileError.scanAxisNotIter`
> replaces the old eval-time rejection path for an undeclared iteration axis (RJ6 in
> `RejectTest.lean` still rejects it, now via the correct mechanism). Full `leanncd/` build green
> (8611 jobs), no new sorries, property-oracle suite unaffected. New test coverage:
> `test/DSL/IterDeclTest.lean`.
>
> The migration touched a different file set than Part 3's table below predicted — corrections
> found during implementation: `ConvPoolTest.lean` and `FeedforwardTest.lean` needed **no** changes
> (zero real scan recurrences in either, contrary to the table); `ParseExamplesTest.lean` and
> `ParseProgramTest.lean` needed **no** changes either (parse-only, never compile, so the new
> mechanism never runs for them); `test/Bridge/AcsetCodecTest.lean` and
> `test/DSL/CompileExamplesTest.lean` **did** need `iter` added despite not appearing in the table
> at all (found via an exhaustive repo-wide grep sweep); `ScanGen.lean`'s 6 programmatic `Decl.axis`
> iteration-axis entries (5× `l`, plus `r6`/`c6`) did **not** need to become `Decl.iter` — their
> `.iterNext`/`.iterAt` slots are built directly in Lean code, never through the ambiguous surface
> grammar `iter` disambiguates (confirmed empirically: the property-oracle suite passes unchanged).
> A gap not named anywhere in this spec: `explicitSizes` (`Lowering.lean`'s `schedule`) needed a new
> `Decl.iter` fold-arm alongside its existing `Decl.axis ax (some n)` arm, or an `iter`-declared
> axis's pinned size would silently never reach shape resolution — found only because the fold is a
> silent-wildcard match with no compiler safety net to flag the missing case.

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

### Strict vs permissive — ✅ DECIDED: STRICT (user, 2026-07-30)

| | Rule | Migration |
|---|---|---|
| **STRICT** ✅ *chosen* | `iter` is the **only** way to declare an iteration axis | ~25 axis swaps + ~10 new + 5 AST sites (measured below) |
| Permissive *(rejected)* | Require a *pinned* declaration by **either** keyword; `iter` is sugar | ~10 new only, no churn |

**Why strict wins, in one line: under permissive, `iter` is a comment; under strict, it is a
guarantee.** If `axis l : ℕ = 3` still counts for a recurrence, Part 1's reclassifier must accept both
spellings, so no code can ever rely on seeing `Decl.iter` — it carries no information the compiler can
use, and the explicitness the option was chosen for never arrives. Under strict, `Decl.iter` becomes a
real invariant (present ⇒ iteration axis, pinned, ℕ-kinded), which is also what collapses Part 2a to a
single failure mode.

⚠️ **The migration is NOT a mechanical keyword swap — an earlier draft of this section said it was,
and that was wrong.** Re-measured 2026-07-30 (the earlier "~23, mechanical" figure was derived from
the table below rather than grepped). Three findings change the character of the work:

1. **`axis X : ℕ = N` does not imply `X` is an iteration axis**, so the swap set requires per-program
   judgement. Confirmed counter-examples that must **stay** `axis`:
   * `RecurrenceTest.lean:77` — `axis i : ℕ = 3, j : ℕ = 3` for `C[i] := X[j] · [j ≤ i]`, a
     triangular-mask contraction with **no recurrence at all**. A non-recurrence program with ℕ axes
     inside the file named `RecurrenceTest` is the trap most likely to catch a bulk edit.
   * `ConvPoolTest.lean` — `p` is a pooling-window axis; the actual iteration axes (`i`, `j`) are
     *undeclared* and belong in the "needs" column instead.
   * `RelationalTest.lean`, `EdgeCaseTest.lean` — ℕ axes, no recurrences.
   * `SyntaxTest.lean:7` — inside a ``#check (`(tl_decl| …) : Lean.MacroM _)`` quotation: a pure
     syntax test, not a program. Leave it: it covers the `axis` production, which survives.
2. **Comma groups of co-iterating axes swap wholesale** — `axis r : ℕ = 2, c : ℕ = 2` for
   `G[r +1, c +1]` becomes `iter r = 2, c = 2`. Most multi-axis scans in `RecurrenceTest` are this
   shape (`:36, :55, :96, :116, :130`), so they are cheap.
3. **Mixed groups must be SPLIT**, which is the genuinely non-mechanical part. Confirmed:
   `EvalExamplesTest.lean:268` — `axis l : ℕ = 3, s : ℕ = 2` where `l` iterates and `s` is a sequence
   axis ⇒ `iter l = 3` **plus** `axis s : ℕ = 2`.

**Measured swap set: ~25 individual axes across ~14 declaration lines in 5 files** —
`RecurrenceTest` ~15 (9 of 10 programs; `:77` excluded), `EvalExamplesTest` ~4, `RejectTest` 3,
`GenerativeTest` 2, `ClassicalMLTest` 1. Higher than the retracted ~23 because multi-axis scans
contribute 2–3 axes per line. **This count is ±2 — the per-program pass belongs in the plan**, and it
is a count of *axes*, not edits; the edit count is nearer 14.

### Effect on finding G — PROBED 2026-07-30: unreachable via surface syntax, Part 5 closed docs-only

A base case still does not *name* its own axis (`.iterAt (scanAxis "") n`, `Elab.lean:244`); that
part of the earlier analysis stands. But the feared consequence — a silent zero-fill when
`adoptBaseIterAxes` misses — does not happen for any program written through `tlprog!`.

The mechanism, read precisely (`Stmt.adoptBaseIterAxes`, `Structural.lean:827-835`): each base
`.iterAt _ n` at position `p` adopts `step.stepAxisAt p`, and on a miss it is "left as-is" — keeping
the placeholder (`name ""`), documented at `:824-825`.

**Three constructions tried, all fail loud, none silent:**

1. Single-axis, iteration axis last-in-base/first-in-step (`G[j,0]` / `G[l+1,j]`) ⇒
   `missingBaseCase "G"`.
2. Multi-axis, one axis adopts correctly and one doesn't (`G[0,k,0]` / `G[r+1,c+1,k]`) ⇒
   `inconsistentScanAxes` — the mismatched slot's placeholder-uid leaks into the stmt's own axis
   set via the correctly-adopted sibling slot, so the component's axis count no longer matches the
   recurrence's advance set.
3. Two independently-mis-ordered scans in one program ⇒ `missingBaseCase` fires on the first,
   unaffected by the second.

**Why it can't be silent — verified by direct inspection**: `assignUIDs` (`Structural.lean:572-578`)
mints exactly one fresh, mutually-distinct, non-zero UID per *distinct axis name* in the whole
program (a de-duplicated name list, `p.axisNames`) via a `memo : HashMap String UID`, then
relabels every occurrence of that name to its minted UID. `""` — the placeholder's name
(`scanAxis ""`, `Elab.lean:244`) — is just one more entry in that name list: it gets minted its
OWN UID like any other name, it does NOT stay at its construction-time default of `0`. Confirmed
by dumping `resolveDecls`'s output on a correctly-adopted program: `l` → uid 1, `j` → uid 2, the
base's placeholder → uid **3**, not 0. (An earlier draft of this section claimed `0` stays
exclusively reserved for the placeholder — that's not the mechanism; the placeholder is relabeled
too, just to a value distinct from every other name's value.) What actually holds: the memo is
name-keyed and injective, so **two axes only ever share a UID if they share a name** — and no
real, surface-declared axis is ever named `""`. So an un-adopted base's axis set is always either
disjoint from its recurrence's real axis set (cases 1/3 — `missingBaseCase`) or a strict superset
of it (case 2 — `inconsistentScanAxes`). It can never be *silently equal*.
`outputAxesConsistent` (`Lowering.lean:457-460`) is unrelated — it compares outputs of an
already-grouped coupled scan post-grouping — and was never the mechanism that closes this.

**The residual risk is programmatic ASTs only**, which bypass `assignUIDs`'s name-based minting
entirely and so *could* deliberately give a real axis the same UID as some placeholder.
`ScanGen.lean` is the one place in the repo doing this, and it already assigns distinct, proper
non-zero UIDs (`202`, `L`, etc.) — no instance of the collision exists in practice. **Still don't
detect a placeholder by `uid == 0` in new code** — that was never the actual invariant (name-based
distinctness is), and a hand-built AST is free to pick any UID for anything.

**Decision: docs-only, per the "write the failing program first, scope down if unreachable"
instruction this section originally carried.** No code change. `papers/semantic_payload_audit.md`
finding G carries the full probe writeup. The single-candidate adoption rule (position-independent
adoption when there's exactly one `iterNext` and one `iterAt`) and the fail-loud
`unresolvedBaseIterAxis` rejection (replacing "left as-is" with an `Except`-returning
`adoptBaseIterAxes`) remain on the table as optional future work — an ergonomic fix and a
defense-in-depth for programmatic ASTs, respectively, neither a safety fix for the surface DSL —
should someone want to revisit them.

## Implementation shape — Parts 1–4 (Part 5, for finding G, is specified above)

Two of these were **separable and shipped ahead of the rest, as planned**: Part 2b (finding H — a
mechanical type change, 72 sites measured, not the estimated 70) is DONE. Part 5 (finding G) turned
out unreachable via surface syntax on probing, so its step 1 (single-candidate rule) was NOT
implemented — see the "Effect on finding G" section above for the full writeup. Neither depended
on `iter`, and Parts 1–4 below are unaffected by either outcome.

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

**DONE, shipped ahead of the spike as its own commit** (72 sites, 20 files — `Ast.lean`, `Syntax.lean`,
`Elab.lean`, `Structural.lean`, and 16 test files). `lake build` green at the same 8610-job baseline
as before the change; no new sorries. `papers/leanncd.md` §14.3 annotated with the deviation.

**Part 3 — migration.** Two halves under STRICT: (a) **add** `iter` declarations where an iteration
axis is undeclared — the table below; (b) **convert** existing `axis … : ℕ = N` declarations of
iteration axes to `iter` — ~25 axes / ~14 lines / 5 files, itemised in the strict-vs-permissive
section above, **including the four files whose ℕ axes must NOT be converted**. Plus 5 AST sites.

⚠️ The "already declared" column below is what produced the retracted "~23, mechanical" estimate —
read it as *"needs conversion, not exempt"*. Measured 2026-07-30 (surface `tlprog!` programs only):

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

**Two** tests, one per behavioural rule. **Each must be mutation-tested** — revert the fix and
confirm the test fails — because three of the bugs in this cluster were "guarded" by a comment
asserting they could not happen, and finding #4 was documented by a test that could never have caught
it (it asserted the op *tag* while the payload was discarded).

1. **Both spacings produce the same `LHSSlot`** (`l +1` vs `l + 1`). The regression guard for #5b
   itself; nothing else would catch a reintroduced divergence.
2. **`scanAxisNotIter`** — a recurrence over an undeclared axis is rejected at compile.

**Finding G needs no test** — probed 2026-07-30 (see `papers/semantic_payload_audit.md`): three
constructions of the base/step mismatch all failed loud via existing guards
(`missingBaseCase`/`inconsistentScanAxes`), and `assignUIDs`' non-zero guarantee shows why no
surface program can reach the silent case. Closed docs-only; no `unresolvedBaseIterAxis`
rejection was added.

**Finding H gets no test, deliberately** — Part 2b makes the state a *type* error, so there is nothing
runtime to assert. Its verification is that the build still passes after the 70-site rewrite, plus
`#print axioms` unchanged on the touched declarations. If you find yourself writing a test for H, the
change has drifted back to level 1 (validate a still-representable state) — stop and re-read Part 2b.
