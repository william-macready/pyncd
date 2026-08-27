# Close the fourth class-6 door (`.freeNorm` diagonal write bypasses `slotsBecomeScatter`)

**Origin.** The just-merged tests-only slice (`docs/superpowers/plans/2026-08-26-nonlinearity-t2-route-corpus.md`,
merged to `main` at `6758e8f`) built a 145-case corpus over the route-fragment boundary and its
whole-branch review found a real, pre-existing production soundness bug — not introduced by that
slice, just found by it. This slice fixes it. Production code changes, plus regression tests and
doc updates; not tests-only.

---

## §0 Verified baseline

Everything below was re-run against `main` @ `6758e8f` (this worktree's base) during planning, not
transcribed from the prior slice's write-up. Commands used `.claude/skills/slice-plan/check-snippet.sh`,
which compiles a snippet against the real `leanncd` environment in gitignored `spikes/` and cleans
up after itself — no production file was edited during this planning pass.

### 0.1 The bug, reproduced independently

```lean
import Eval.Portfolio.Harness
namespace LeanNCD.Eval
open Std Lean Elab Command

run_cmd do
  match TLProgram.compile (tlprog!{ Y[i, i.] := softmax(X[i]) }) |>.run 0 with
  | .error e _ => logInfo s!"REPRO bug case: REJECTED with {repr e}"
  | .ok tc _   => logInfo s!"REPRO bug case: ACCEPTED, steps = {repr tc.steps}"

run_cmd do
  match TLProgram.compile (tlprog!{ Y[i, i] := softmax(X[i]) }) |>.run 0 with
  | .error e _ => logInfo s!"REPRO control case: REJECTED with {repr e}"
  | .ok tc _   => logInfo s!"REPRO control case: ACCEPTED, steps = {repr tc.steps}"

end LeanNCD.Eval
```

Observed output:

```
REPRO bug case: ACCEPTED, steps = [{ op := LeanNCD.BrOp.contract, ... },
 { op := LeanNCD.BrOp.softmax, ...
   reindexings := [{ domLen := 1, codLen := 2, coeffs := [[1], [1]], bias := [0, 0] }] }]
REPRO control case: REJECTED with LeanNCD.CompileError.unsupportedNonlinScatter "Y"
```

Confirmed exactly as documented: `Y[i, i.] := softmax(X[i])` compiles to a two-step
`[contract, softmax]` program whose `softmax` step reindexes from `domLen 1` to `codLen 2` — a real
producer/consumer rank disagreement, silently accepted. The control `Y[i, i] := softmax(X[i])`
(both slots plain `.free`, no `.freeNorm`) is correctly rejected with
`CompileError.unsupportedNonlinScatter "Y"`. Not a stale claim — this is `main`'s current behavior.

### 0.2 `.freeNorm` semantics — investigated, not assumed

Central design question: does `[.free a, .freeNorm a]` on the *same* axis carry legitimate,
non-diagonal semantics (in which case the fix would be to route it correctly), or is it just
another spelling of the diagonal write `Y[i,i]` (in which case the fix is to reject it, extending
the existing detector)?

Traced every use of `.freeNorm` (`Ast.lean`, `Elab.lean`, `Structural.lean`, `Eval/Plan/Compile.lean`):

- `LHSSlot.freeNorm : AxisSpec → LHSSlot` is documented at its declaration (`Ast.lean`) as "a free
  output axis marked (`m.`) as the softmax/normalize reduction axis" — a `.freeNorm` slot **is** a
  free output-placement axis, just one additionally marked as the axis an `AxiswiseFn`
  (softmax/normalize/l2normalize) reduces over.
- `LHSSlot.outIdx` maps **both** `.free a` and `.freeNorm a` to the identical `IdxExpr.axis a` —
  the write-coordinate arithmetic does not distinguish them at all. The marker carries no placement
  information; it is purely a "which slot position is the reduction axis" pointer for
  `resolveNonlinAxis` (`Eval/Plan/Compile.lean`) to consume.
- `AxiswiseFn`s (`softmax`/`normalize`/`l2normalize`) are rank-*preserving*: they normalize values
  along one axis, they do not reduce rank. So the marked axis still occupies a real output
  position — there is no sense in which `.freeNorm` "hides" an axis or turns two slots into one.

Given both of those: two LHS slots naming the **same UID** — one `.free`, one `.freeNorm` — place
the output at the same coordinate twice, i.e. write only the diagonal `Y[i,i]`. There is no
well-defined non-diagonal reading: a `.freeNorm` axis paired with a `.free` axis on two *different*
UIDs is the ordinary, well-supported case (`freeNormAxiswiseProg` in `RouteWeaveTest.lean`:
`Y[q, s.] := normalize(W[q,d]·X[d,s])`, `q ≠ s`); pairing it with the *same* UID collapses to
exactly the shape `checkScatterNonlin` already rejects for the plain-`.free` spelling.

**Conclusion: `[.free a, .freeNorm a]` (same axis) must be REJECTED, matching the `Y[i,i]` control.**
The correct fix is narrow — extend the existing diagonal-write detector to also count `.freeNorm`
UIDs — not a physicalization/routing change. This also matches what `RouteFragments.lean`'s own
header docstring already concluded when it recorded the bug: "closing this needs
`slotsBecomeScatter` — or an equivalent duplicate-UID check — to also count `.freeNorm` UIDs."

### 0.3 The fix, verified in isolation

`LHSSlot.freeUID?` (`Ast.lean`) is `slotsBecomeScatter`'s ONLY caller (grepped; single call site,
`Ast.lean` itself). Its current definition:

```lean
def LHSSlot.freeUID? : LHSSlot → Option UID
  | .free a => some a.uid
  | _       => none
```

Verified via a standalone snippet (imports `LeanNCD.DSL.Ast`, no production edit) that broadening
it to also match `.freeNorm` produces the correct truth table on every case that matters:

```lean
import LeanNCD.DSL.Ast
namespace LeanNCD

def i : AxisSpec := { name := "i", uid := 1, kind := .real }
def j : AxisSpec := { name := "j", uid := 2, kind := .real }
def k : AxisSpec := { name := "k", uid := 3, kind := .real }

def fixedFreeUID? : LHSSlot → Option UID
  | .free a     => some a.uid
  | .freeNorm a => some a.uid
  | _           => none

def fixedSlotsBecomeScatter (slots : List LHSSlot) : Bool :=
  slots.any (fun sl => match sl with | .affine _ => true | _ => false)
  || (let us := slots.filterMap fixedFreeUID?
      us.length ≠ us.eraseDups.length)

-- 1. CONFIRM THE BUG: production `slotsBecomeScatter` does NOT flag the same-axis pair today.
#guard slotsBecomeScatter [.free i, .freeNorm i] == false

-- 2. CONFIRM THE FIX: the patched detector DOES flag it — same verdict as the plain-diagonal
--    control, which production already rejects correctly.
#guard fixedSlotsBecomeScatter [.free i, .freeNorm i] == true
#guard fixedSlotsBecomeScatter [.free i, .free i] == true          -- control, unaffected
#guard slotsBecomeScatter      [.free i, .free i] == true          -- production already agrees

-- 3. CONFIRM NO REGRESSION: `.freeNorm` on a DIFFERENT axis from every `.free` slot (the shape
--    `freeNormProgram`/`freeNormAxiswiseProg` actually exercise) must NOT be flagged, before or
--    after the fix.
#guard slotsBecomeScatter      [.freeNorm i, .free j, .free k] == false
#guard fixedSlotsBecomeScatter [.freeNorm i, .free j, .free k] == false
#guard slotsBecomeScatter      [.free i, .freeNorm j, .free k] == false
#guard fixedSlotsBecomeScatter [.free i, .freeNorm j, .free k] == false

-- 4. CONFIRM: an affine slot is still flagged regardless (unrelated disjunct, untouched by the fix).
#guard slotsBecomeScatter      [.free i, .affine (.scale 2 j)] == true
#guard fixedSlotsBecomeScatter [.free i, .affine (.scale 2 j)] == true

end LeanNCD
```

`check-snippet.sh` result: **COMPILES** — all eight `#guard`s hold. This is the strongest
verification available without editing production `Ast.lean` (out of scope for a planning-only
pass): it proves the exact patched pattern-match, byte-for-byte what Task 1 will ship, produces the
correct Boolean on the bug case, the plain-diagonal control, both existing distinct-axis fixtures'
shapes, and the affine trigger. `checkScatterNonlin`'s and `physicalizeOne`'s own logic
(read directly, §0.3.1 below) is unconditional on that Boolean and unchanged by this fix, so the
Boolean fix alone determines the outcome at both call sites.

#### 0.3.1 The two call sites that consume the fixed Boolean, read directly

`checkScatterNonlin` (`Structural.lean`):
```lean
| .assign nm ls rhs =>
    if slotsBecomeScatter ls && rhs.nonlin ≠ Nonlin.identity then
      throw (.unsupportedNonlinScatter nm)
```
For `Y[i, i.] := softmax(X[i])`: `ls = [.free i, .freeNorm i]`, `rhs.nonlin = .axiswise .softmax none
≠ .identity`. Once `slotsBecomeScatter ls = true` (§0.3, case 2), this throws
`.unsupportedNonlinScatter "Y"` — the same constructor and payload as the control, unconditionally.

`physicalizeOne` (`RouteFragments.lean`), the hand-built-schedule entry point (bypasses
`checkScatterNonlin`, which only runs inside `TLProgram.compile`/`compileToScheduled`):
```lean
| .pointwise _ | .axiswise _ _ =>
  if slotsBecomeScatter slots then throw (.unsupportedNonlinScatter nm)
  else ...
```
Same reasoning: fixing the shared Boolean closes this path too, with no separate code change.

### 0.4 Regression fixtures — verified RED against current code

Two fixtures, one per entry point named in §0.3.1, each a one-field clone of an existing donor.

**RSN5** (donor: `RSN4` in `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` — clone, swap the
diagonal trigger `Y[i, i] := relu(X[i])` for the freeNorm-diagonal trigger and `softmax`):
```lean
run_cmd do
  match TLProgram.compile (tlprog!{ Y[i, i.] := softmax(X[i]) }) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => pure ()
  | .error e _ => throwError s!"RSN5: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "RSN5: expected unsupportedNonlinScatter, compile succeeded"
```
`check-snippet.sh` on this exact block today: **DOES NOT COMPILE** —
`error: RSN5: expected unsupportedNonlinScatter, compile succeeded`. Confirmed RED.

**Fixture 15** (donor: `f14DiagSlots`/`f14RouteRejects` in `test/DSL/Pipeline/RouteWeaveTest.lean`
— clone `f14AffineAssign`'s shape, swap the trigger `[.free i, .free i]` for `[.free i, .freeNorm i]`):
```lean
private def f15Axis : AxisSpec := { name := "i", uid := 1, kind := .real }
/-- FreeNorm-diagonal trigger: `Y[i, i.]` — the SAME axis, once plain once norm-marked. -/
private def f15FreeNormDiagSlots : List LHSSlot := [.free f15Axis, .freeNorm f15Axis]

private def f15FreeNormDiagAssign (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" f15FreeNormDiagSlots
      { body := { terms := [{ factors := [.read "X" [.axis f15Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f15RouteRejects (nl : Nonlin) : Bool :=
  match route (f15FreeNormDiagAssign nl) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => true
  | _ => false

#guard f15RouteRejects (.pointwise .relu)
#guard f15RouteRejects (.axiswise .softmax none)
```
`check-snippet.sh` on this exact block today (both `#guard`s together): **DOES NOT COMPILE** —
```
error: Expression f15RouteRejects (Nonlin.pointwise PointwiseFn.relu) did not evaluate to `true`
error: Expression f15RouteRejects (Nonlin.axiswise AxiswiseFn.softmax none) did not evaluate to `true`
```
Confirmed RED on both nonlinearity kinds — the bug is independent of which `Nonlin` triggers the
split arm, purely a property of `slotsBecomeScatter`'s blindness to `.freeNorm`.

Both fixtures are exactly what Task 1 ships. Task 1's own acceptance check is: apply the `Ast.lean`
fix, re-run both, confirm they flip to GREEN (this plan cannot do that step itself without editing
production code, which is out of scope for planning — §0.3's isolated-function proof plus this §0.4
RED confirmation is the evidence a green flip is expected; Task 1's implementer performs and
records the actual flip).

### 0.5 Third door — verified out of scope, independently

`RouteFragments.lean`'s header names a third open class-6 door: `LHSSlot.toReadIdx` collapses
`.iterAt a n`/`.iterNext a` to `.axis a`, discarding the pinned literal/shift. Read `toReadIdx`
directly (`Ast.lean`):
```lean
def LHSSlot.toReadIdx : LHSSlot → Option IdxExpr
  | .free a     => some (.axis a)
  | .freeNorm a => some (.axis a)
  | .iterAt a _ => some (.axis a)
  | .iterNext a => some (.axis a)
  | .affine _   => none
```
This is a **different function** from `freeUID?`, with a different caller (`physicalizeOne`'s
consumer-read-coordinate build, not the `slotsBecomeScatter` diagonal check) and a different
defect shape (collapsing distinct constructors to the same `IdxExpr`, not undercounting a
duplicate-UID scan). The two share no helper. Fixing `freeUID?` (§0.3) touches nothing `toReadIdx`
reads or calls, and vice versa. **Confirmed: no shared root cause. Third door stays out of scope**,
per the default in this slice's brief — deferred to its own later slice.

### 0.6 Recurring-defect sibling sweep

`freeUID?`/`slotsBecomeScatter` is the diagonal-write (duplicate-placement-UID) detector for
`.plain` statements. The only other duplicate-axis-UID check in the codebase is
`firstDuplicateUID` (`Eval/Plan/Compile.lean`), called from `compileScan` on
`slots.mapM (scanSlotAxisOrFail ...) |>.map (·.uid)` for scan base/recurrence blocks. Two reasons
this is NOT a sibling instance of the same bug:
- it is built from `scanSlotAxisOrFail`, which uses `LHSSlot.axisSpec?` — already total over
  `free`/`freeNorm`/`iterAt`/`iterNext` (all four map to `some`), not the selective `freeUID?`;
- `.freeNorm` cannot even reach it: `checkScanLHSSlot` (`Eval/Plan/Compile.lean`) throws
  `.unsupportedLhsSlot` on any `.freeNorm` slot inside a scan block, at preflight, strictly before
  `compileScan` runs.

No other function in `Ast.lean`/`Structural.lean`/`Eval/Plan/Compile.lean` computes "is this UID
repeated across LHS slots" from a *selective* per-constructor accessor the way `freeUID?` does —
every other slot-list traversal found (`axisSpec?`, `axisUID?`, `outIdx`, the `Stmt.uids_eq`
UID-collector family, `checkLHSSlot`/`checkScanLHSSlot`/`freeUidOrFail`) is either fully total over
the constructor surface or `normUID?`, which is deliberately `.freeNorm`-only for a different
purpose (locating the one reduction-axis position, not duplicate detection). No second instance
found.

### 0.7 Doc-location accuracy check

All four locations the fix must update currently describe the bug as **open**, matching `main`'s
real behavior (§0.1): `RouteFragments.lean`'s header (the "FOURTH door" paragraph),
`LeanNCD/DSL/AGENTS.md`'s case-table row 6, `papers/nonlinearity_split_pair_direct_lowering.md`'s
§2.4 table (same row), and `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`'s `G24` comment (the
`!slotsBecomeScatter producer` stopgap conjunct's explanation, which currently reads "None of the 9
corpus cases hit this shape today ... so this conjunct is free here"). All four paths verified with
`ls`/`grep` to exist at the stated locations, current as of `main` @ `6758e8f`.

---

## §1 Global constraints

- **Current behavior (exact).** `TLProgram.compile (tlprog!{ Y[i, i.] := softmax(X[i]) })` returns
  `.ok` with a two-step `[contract, softmax]` program whose second step's `reindexings` has
  `domLen 1, codLen 2` — a real shape mismatch, silently accepted. The identical shape spelled
  `Y[i, i] := softmax(X[i])` (no `.freeNorm`) already correctly returns
  `.error (CompileError.unsupportedNonlinScatter "Y")`.
- **Target behavior (exact).** `TLProgram.compile (tlprog!{ Y[i, i.] := softmax(X[i]) })` must
  return `.error (CompileError.unsupportedNonlinScatter "Y")` — byte-identical constructor and
  payload to the control. Same for the hand-built-schedule `route`/`physicalizeForRoute` entry
  point (fixture 15, §0.4).
- **The fix is exactly one function's pattern match** — `LHSSlot.freeUID?` (`Ast.lean`) gains a
  `.freeNorm a => some a.uid` arm. No other function changes. `slotsBecomeScatter`,
  `checkScatterNonlin`, `fragmentClass`, `physicalizeOne`, and `stmtLhsRank` are all unconditional
  consumers of `slotsBecomeScatter`'s Boolean and need no code change (§0.3.1).
- **No regression on the legitimate distinct-axis `.freeNorm` case.** `[.freeNorm a, .free b, .free
  c]` (distinct UIDs) — the shape `freeNormProgram` (9 corpus cases) and `freeNormAxiswiseProg` (F6,
  G25) already exercise — must remain unflagged, unchanged, verified in §0.3.
- **Out of scope, deliberately:**
  - the third class-6 door (`toReadIdx` collapsing `iterAt`/`iterNext`) — verified separate root
    cause, §0.5, deferred to its own slice;
  - any change to `producerSlots`, `toReadIdx`, `outIdx`, or any physicalization/routing logic —
    the conclusion in §0.2 is that this shape must be *rejected*, not routed, so nothing downstream
    of `checkScatterNonlin`/`physicalizeOne`'s existing reject arms needs to change;
  - `stmtLhsRank`'s own behavior for scatter-shaped LHS is pre-existing and already exercised by
    the `.affine`/plain-diagonal doors (RSN1/RSN4) — this fix reaches that same branch via a fourth
    trigger, not new code, so no dedicated fixture is added for it.
- **No `sorry`/`admit`/`axiom` introduced.**

---

## §2 Task breakdown

**Two tasks.** Boundary chosen by the reviewer test: a reviewer could accept the code fix and its
regression tests while rejecting a doc edit's prose accuracy (or vice versa) — they are not the
same failure mode. Both are small; splitting further would not survive the "could a reviewer reject
one while approving its neighbour" test (e.g. RSN5 and fixture 15 have no independent failure mode
from the one-line `Ast.lean` fix — they exist to prove it, so they stay in the same task as the fix).

| Task | Deliverable | Fixtures | Mutation cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | the fix (`LHSSlot.freeUID?`) + two regression fixtures | 2 (RSN5, fixture 15) | 1 | the fix is one pattern-match arm on a function with exactly one caller — the risk is entirely in confirming no unintended fixture elsewhere flips (full `lake build Tests`), not in the fix's own logic (already verified, §0.3) |
| 2 | doc updates across the 4 locations that documented this as open | 0 | 0 | pure prose-accuracy risk — each location must state the fix truthfully and consistently with the others, not code risk |

### Task 1 — the fix + regression tests

**Outcome.** `LHSSlot.freeUID?` (`LeanNCD/DSL/Ast.lean`) also matches `.freeNorm a`. Two new
fixtures pin the target behavior at both entry points named in §0.3.1.

**Files:**
- `LeanNCD/DSL/Ast.lean` — the fix.
- `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` — new fixture `RSN5` (donor: `RSN4`, same file).
- `test/DSL/Pipeline/RouteWeaveTest.lean` — new fixture 15 (donor: `f14DiagSlots`/`f14RouteRejects`,
  same file).

**The fix**, verified compiling in §0.3 (the block below is the exact production edit; only the
name `fixedFreeUID?` there becomes `freeUID?` here — same pattern, same types):

```lean
/-- The UID of a `free` or `freeNorm` slot — the axes that place an output coordinate directly
    (as opposed to `iterAt`/`iterNext`, which place a *scan* coordinate, or `affine`, which is
    itself the scatter trigger). `.free` and `.freeNorm` are both "free placement" axes per
    `.freeNorm`'s own doc comment above — differing only by the reduction marker, not by where
    they place the output — so a repeated UID across either is the same diagonal LHS (`Y[i,i]`
    and `Y[i, i.]` name the same mathematical shape). Intentionally selective: a repeated
    `freeUID?` across a stmt's slots is how a diagonal LHS is detected and routed to `scatter`.
    NOT `axisUID?` (which also counts `iterAt`/`iterNext`, whose repeats mean something else —
    see the third class-6 door, still open, `RouteFragments.lean`'s header).

    ⚠️ Fixed 2026-08-27 (found in whole-branch review, the "fourth class-6 door"): this used to
    match only `.free`, so `[.free a, .freeNorm a]` (the same axis) counted as ONE free UID and
    slipped past `slotsBecomeScatter`'s duplicate check. See `RouteFragments.lean`'s header for the
    full account and `ScatterNonlinRejectTest.lean`'s `RSN5` / `RouteWeaveTest.lean`'s fixture 15
    for the regression. -/
def LHSSlot.freeUID? : LHSSlot → Option UID
  | .free a     => some a.uid
  | .freeNorm a => some a.uid
  | _           => none
```

**Regression fixtures** — exact text, both verified RED in §0.4:

`RSN5`, appended to `ScatterNonlinRejectTest.lean` after `RSN4`:
```lean
-- RSN5  freeNorm-diagonal trigger: `Y[i, i.]` — the SAME axis, once plain once norm-marked. The
--   fourth class-6 door (whole-branch review, 2026-08-27, fixed here): `slotsBecomeScatter`'s
--   `freeUID?` used to count only `.free`, so this slipped past undetected while `producerSlots`
--   degraded it to a genuine `[.free i, .free i]` diagonal producer downstream. Same rejection as
--   the plain-diagonal control (RSN4).
run_cmd do
  match TLProgram.compile (tlprog!{ Y[i, i.] := softmax(X[i]) }) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => pure ()
  | .error e _ => throwError s!"RSN5: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "RSN5: expected unsupportedNonlinScatter, compile succeeded"
```

Fixture 15, appended to `RouteWeaveTest.lean` after fixture 14 (same section style):
```lean
/-! ### Fixture 15 — §2.4 class 6, the fourth door: a nonlinear `.plain (.assign …)` whose LHS
combines `.free a` and `.freeNorm a` on the SAME axis. Fixture 14 covers the plain-diagonal and
affine triggers of `slotsBecomeScatter`; this covers the `.freeNorm` trigger found in whole-branch
review (2026-08-27) and fixed here — `slotsBecomeScatter`'s `freeUID?` now counts `.freeNorm` too.
Asserted at public `route`, mirroring fixture 14 exactly. -/

private def f15Axis : AxisSpec := { name := "i", uid := 1, kind := .real }
/-- FreeNorm-diagonal trigger: `Y[i, i.]` — the SAME axis, once plain once norm-marked. -/
private def f15FreeNormDiagSlots : List LHSSlot := [.free f15Axis, .freeNorm f15Axis]

private def f15FreeNormDiagAssign (nl : Nonlin) : ScheduledProgram :=
  { decls := []
  , stmts := [.plain (.assign "Y" f15FreeNormDiagSlots
      { body := { terms := [{ factors := [.read "X" [.axis f15Axis]] }] }, nonlin := nl, agg := .sum })]
  , env := {}
  , extNames := insert "X" (∅ : Finset String)
  , explicitSizes := ∅ }

private def f15RouteRejects (nl : Nonlin) : Bool :=
  match route (f15FreeNormDiagAssign nl) |>.run 0 with
  | .error (.unsupportedNonlinScatter "Y") _ => true
  | _ => false

#guard f15RouteRejects (.pointwise .relu)
#guard f15RouteRejects (.axiswise .softmax none)
```
(The extra `.pointwise .relu` case is free coverage in the same shape as fixture 14's own two
nonlinearity variants per trigger — not a separate mutation cycle, same fixture.)

**Gate (mutation cycle 1, to be recorded in the SDD ledger by the implementer):**
1. Confirm `RSN5` and fixture 15 fail to compile against unfixed `main` (already done in this plan,
   §0.4 — implementer re-confirms by checking out the fixtures alone first, OR trusts this plan's
   recorded RED and proceeds directly to the fix, recording that choice).
2. Apply the `Ast.lean` fix.
3. `lake build Tests` (or targeted: `ScatterNonlinRejectTest`, `RouteWeaveTest`,
   `RouteFragmentCorpusTest`, `LoweringTest`) — full green, including `RSN5`/fixture 15 now passing
   and every pre-existing fixture (`RSN1`–`RSN4`, `F6`, `G20`–`G26`, the `PRODUCERSLOTS` fixture in
   `LoweringTest.lean`) unchanged.
4. Record the observed RED→GREEN flip for `RSN5` and fixture 15 in the ledger — this task's mutation
   cycle.

### Task 2 — doc updates (the door is now closed)

**Outcome.** The four locations that currently document this as an open, unfixed door are updated
to state it is closed, consistently, each pointing at the fix (`LHSSlot.freeUID?`) and the
regression fixtures (`RSN5`, fixture 15).

**Files and exact edits:**

1. **`LeanNCD/DSL/Pipeline/RouteFragments.lean`** — replace the paragraph beginning "⚠️ **A FOURTH
   door is open and NOT closed here**" (in the module header docstring, immediately after the third
   door's paragraph) with:
   ```
   ✅ **A fourth door was found (whole-branch review, 2026-08-27) and is now CLOSED.**
   `slotsBecomeScatter`'s diagonal-write detector (`Ast.lean`) went through `LHSSlot.freeUID?`,
   which used to return `some` only for `.free` — never `.freeNorm`. So an LHS like `[.free a,
   .freeNorm a]` (the SAME axis, once plain and once norm-marked) had exactly one free UID by that
   count, was NOT classified scatter-shaped, and took the ordinary split arm — but `producerSlots`
   then degraded `.freeNorm a → .free a` on the producer, turning it into `[.free a, .free a]`: a
   genuine diagonal LHS that no gate had checked. It was reachable from **surface `tlprog!` syntax
   through public `TLProgram.compile`**, not only from a hand-built schedule — more severe than the
   doors above. Root cause: `checkScatterNonlin` (`Structural.lean`) and
   `fragmentClass`/`physicalizeOne` both consult the SAME `slotsBecomeScatter`, so both gates were
   blind to this shape at once.

   Fixed by broadening `LHSSlot.freeUID?` to also return `some a.uid` for `.freeNorm a` — `.free`
   and `.freeNorm` are both "free placement" axes per `.freeNorm`'s own doc comment, differing only
   by the reduction marker, so both belong in the diagonal-UID count. `slotsBecomeScatter` now
   flags `[.free a, .freeNorm a]` exactly like the plain-diagonal control `[.free a, .free a]`, and
   `checkScatterNonlin` rejects it with the same `unsupportedNonlinScatter` diagnostic before
   physicalization ever runs. Regression: `test/Eval/Portfolio/ScatterNonlinRejectTest.lean`'s
   `RSN5` (the `TLProgram.compile` entry point) and `test/DSL/Pipeline/RouteWeaveTest.lean`'s
   fixture 15 (the hand-built-schedule / `route` entry point, mirroring fixture 14's `.assign`
   door).
   ```
   Leave the third-door paragraph immediately above this one unchanged (still open, still
   out of scope, per §0.5).

2. **`LeanNCD/DSL/AGENTS.md`** — in the case-table row for class 6, replace the sentence beginning
   "⚠️ A FOURTH door is open, not yet closed, and MORE SEVERE" through "the SDD ledger for the
   reproduction and planned fix." with:
   ```
   ✅ A FOURTH door was found (whole-branch review, 2026-08-27) and is now CLOSED — it was
   reachable from surface `tlprog!` syntax through public `compile`, not only a hand-built
   schedule: `slotsBecomeScatter`'s diagonal detector (`freeUID?`) used to count only
   `.free`-marked axes, so `[.free a, .freeNorm a]` (same axis) was not flagged, yet
   `producerSlots` degrading `.freeNorm a → .free a` on the producer turned it into a genuine
   diagonal `[.free a, .free a]` no gate checked. Fixed by broadening `freeUID?` to also count
   `.freeNorm` UIDs, so `slotsBecomeScatter`/`checkScatterNonlin` reject
   `tlprog!{ Y[i, i.] := softmax(X[i]) }` exactly like the control `Y[i, i] := softmax(X[i])`. See
   `RouteFragments.lean`'s header, and regression fixtures `RSN5`
   (`ScatterNonlinRejectTest.lean`) / fixture 15 (`RouteWeaveTest.lean`).
   ```
   Leave the third-door sentence immediately before it unchanged.

3. **`papers/nonlinearity_split_pair_direct_lowering.md`** — in §2.4's class-6 table row, replace
   the sentence beginning "**A fourth door, MORE SEVERE, found in the Task-2-slice whole-branch
   review" through "the reproduction and planned fix." with the same closed-door text as location 2
   above. **Checked, not assumed:** the AGENTS.md and papers-doc class-6 cells are NOT verbatim
   identical today (confirmed by direct comparison — 1853 vs 1612 characters, differing wording
   throughout, not just this sentence) — there is no pre-existing "keep them byte-identical"
   convention to preserve. Using the same closed-door text for both here is this task's own choice
   for consistency of the new claim, not a restoration of prior verbatim equality.

4. **`test/DSL/Pipeline/RouteFragmentCorpusTest.lean`** — in `freeNormStructural`'s `G24` comment,
   replace the whole parenthetical comment (from "the degraded producer is not ITSELF scatter-shaped"
   through "silently mis-routing) …", i.e. every `--` line between `producer == producerSlots
   slots && !slotsHaveFreeNorm producer` and `!slotsBecomeScatter producer &&`) with, verbatim
   (given as a complete replacement, not a splice, to avoid stitching a broken sentence across the
   edit boundary):
   ```
            -- … the degraded producer is not ITSELF scatter-shaped (the fourth class-6 door,
            -- found in whole-branch review 2026-08-27 and CLOSED by broadening `freeUID?`
            -- (`Ast.lean`) to also count `.freeNorm` UIDs — see `RouteFragments.lean`'s header.
            -- A `[.free a, .freeNorm a]` logical LHS is now rejected by `checkScatterNonlin`
            -- before physicalization ever runs, so this conjunct is unreachable-false by
            -- construction rather than merely untested; kept as defense-in-depth, so a future
            -- case that does hit the shape fails the build instead of silently mis-routing) …
   ```
   (Not part of the four locations named in the brief, but found during §0.7's accuracy check —
   folded into this task since it is the same kind of edit to a file this task is already touching
   conceptually, and leaving it stale would misdescribe the fix's own regression coverage.)

**Gate:** re-read each edited location once, side by side with the fix's actual behavior (§0.3.1),
confirming no location claims the door is open, no location's fix description contradicts another's,
and every location's cross-reference (`RSN5`, fixture 15) actually exists post-Task-1. No `lake
build` needed for prose-only files, but `RouteFragmentCorpusTest.lean`'s edit is inside a doc
comment only (not code) — confirm the comment boundaries don't spill into or truncate the
surrounding executable `freeNormStructural` definition.

---

## §3 Review plan

**One review pass**, covering both tasks together, not a per-task review plus a separate
whole-branch tier. Justification: this slice is a single pattern-match arm added to a function with
exactly one caller, whose two consuming call sites were read directly and confirmed unconditional on
the fixed Boolean (§0.3.1); the recurring-defect sibling sweep (§0.6) already ran at planning time
and found no second instance; and the only two "could a reviewer reject one part while approving
the other" seams (fix-vs-tests, code-vs-docs) both live inside one diff small enough for one
reviewer to hold in full context. This does not contradict the skill's "don't skimp on the final
whole-branch review" guidance — that guidance is about not *replacing* the final pass with several
cheaper per-task passes on a slice large enough that a per-task reviewer cannot see cross-file
interactions (as happened with `stepWriteRowsOk` in Wave F F4). Here there is no second task whose
own diff could hide a cross-file interaction from a single reviewer; splitting the review would add
dispatch overhead without adding coverage.

The review must independently check:
- the `Ast.lean` diff is exactly the one arm shown in §2 Task 1, with no other function touched;
- `RSN5` and fixture 15 actually exercise the freeNorm-same-axis shape (not a copy-paste that
  silently reverted to the plain-diagonal trigger — compare against `f14DiagSlots`/`RSN4` textually);
- the full test suite (`lake build`) is green, specifically including every fixture named in Task
  1's gate;
- all four doc locations agree with each other and with the actual fixed behavior (re-run §0.1's
  repro one more time post-fix and compare its output against what the docs now claim).

If this single pass surfaces anything unexpected (a fixture failing for a reason other than the
targeted shape, or a doc location this plan did not anticipate), escalate to a second independent
reviewer before merging — per the standing "scale process to task risk" practice — rather than
patching around it in the same pass.

---

## §4 Stop conditions

- Any existing fixture (RSN1–RSN4, F6–F11, F13–F14, G1–G26, the `LoweringTest.lean` `PRODUCERSLOTS`
  fixture, or anything else touched by `lake build Tests`) regresses after the fix — stop, do not
  paper over it with a scope change to those fixtures; the fix is expected to be behavior-preserving
  everywhere except the exact bug shape.
- `RSN5` or fixture 15 fails to flip to GREEN after applying exactly the `Ast.lean` edit in §2 —
  stop; this plan's §0.3/§0.3.1 reasoning has a gap that needs to be found before proceeding, not
  worked around with a different code change.
- Any doc location's post-fix text is found to still describe behavior that doesn't match a fresh
  re-run of §0.1's repro — stop and correct the text; do not merge a doc claim that hasn't been
  checked against the actual post-fix behavior.

## §5 Definition of done

- `LHSSlot.freeUID?` matches `.freeNorm`, matching §2 Task 1's exact block.
- `RSN5` (`ScatterNonlinRejectTest.lean`) and fixture 15 (`RouteWeaveTest.lean`) exist, pass, and
  were observed to fail before the fix and pass after (recorded in the SDD ledger).
- `lake build Tests` (or the full `lake build`) is green.
- All four locations in §2 Task 2 read as closed, consistently, and were re-checked against a
  post-fix re-run of §0.1's repro.
- No `sorry`/`admit`/`axiom` introduced; no production file touched other than `Ast.lean`.
- Per Rule 13 (standing decisions): once both tasks are green and this plan's final review pass
  (§3) is clean or its findings adjudicated, merge to local `main`, delete the branch, and remove
  the worktree — no menu, no confirmation needed.
