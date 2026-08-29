# Brief: extend the independent scan-unrolling oracle to accept `.freeNorm`

**Audience:** an external coding agent (GPT / Copilot), working in this repository.
**Written:** 2026-08-28. **Against:** `main` at `41f5eea`.

This is step 10 of Task 4 in `papers/nonlinearity_split_pair_direct_lowering.md` §3.6, delegated so
it can run in parallel with the rest of that task being planned. It is a **small, additive change to
two functions**, plus a verification that the change actually works against a program with a known
value.

---

## Base, branch, and where output is saved

Repository `main` at **`41f5eea`**.

Create and work on branch **`agents/task4-oracle-freenorm`** — this exact name, so it can be found
without searching.

**All output is committed to that branch as files. Nothing counts as delivered if it exists only in
a chat reply.** Two paths change:

| Path | What goes there |
|---|---|
| `leanncd/test/Eval/PropertyOracle/ScanUnroll.lean` | **edited** — the two new `.freeNorm` alternatives, and nothing else |
| `papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/README.md` | **appended** — a `## Oracle `.freeNorm` extension` section with the record described below |

Touch no other file.

---

## What the oracle is, and why the change is needed

`test/Eval/PropertyOracle/ScanUnroll.lean` is an **independent** re-implementation of scan semantics:
it unrolls a scan into an equivalent scan-free program. `ScanOracle.lean`'s `checkScanLaw` then
requires that the legacy evaluator and this unrolling publish identical histories. That two-way
agreement is what makes the differential meaningful.

The unroller currently **rejects** any `.freeNorm` slot. Both rejections are single match arms:

- `buildGeom` (around line 151): the `| some sl => .error s!"...dimension {p} is neither advancing
  nor a plain free axis ({repr sl}) — outside the oracle's fragment"` arm.
- `baseFreeSlots` (around line 254): the `| _ => .error s!"base write for {st.name}: dimension {p}
  must be a plain free axis"` arm.

Task 4 admits axiswise nonlinear scans, which carry `.freeNorm`. §3.6 step 10 says to extend the
unroller by adding **only** `.freeNorm` preservation alternatives to those two functions.

`.freeNorm` and `.free` denote the same axis for geometry purposes — the marker records that the
axis is the one an axiswise nonlinearity normalizes over. The unroller's geometry handling should
treat them identically; it must not drop or rewrite the marker.

---

## The hard boundary — this is a soundness rule, not style

**`ScanUnroll.lean` must not import `Eval.Plan.*`, `DSL.Pipeline.*`, or any route helper.** It
currently imports exactly `Eval.PropertyOracle.Compare` and `Eval.PropertyOracle.ScanGen`, and that
must not change.

The oracle exists to be an *independent* check on the Plan path. If it reaches into the thing it is
checking, the differential becomes circular and the three-way guarantee in §2.8 collapses. A change
that works but adds such an import is worse than no change, and will be rejected on that basis
alone. If you believe you need one, **stop and report** rather than adding it.

---

## Verification target — a program with a known value

Fixture 2 in
[`nonlinear_scan_admission/OracleFixtureSeed.lean`](../../../../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean)
is an interleaved-axiswise scan that carries `.freeNorm`. Its legacy value is already observed and
independently hand-checked:

```
S shape [3, 2, 3], nonzero only on the advancing diagonal:
  S[0,:,0] = [1, 3]
  S[1,:,1] = [0.25, 0.75]
  S[2,:,2] = [0.25, 0.75]
```

Recurrence LHS slots are `[0: .iterNext, 1: .freeNorm, 2: .iterNext]`, inputs `X = [1, 3]`, both
iteration extents 3.

**Your change is correct exactly when the independent unrolling of that program agrees with legacy
on it.** Verify by writing a scratch file in `leanncd/spikes/` (gitignored) that calls
`evalScheduled` and `independentRun` on fixture 2's program and inputs and compares the published
state — the same comparison `ScanOracle.checkScanLaw` performs, but on a supplied program rather
than a generated `ScanCase`. Delete the scratch file when done; commit only the two paths above.

Before your change, that comparison fails with the unroller's "outside the oracle's fragment"
error. **Record both observations** — the before-error and the after-agreement. A change whose
"before" state already passes means you are not testing what you think you are.

---

## Gates

From `leanncd/`:

```bash
"$HOME/.elan/bin/lake" build Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

`Tests` must be **8,657** and `LeanNCD` **8,543** — unchanged. Your change adds no module.

`PropertyOracleScanTest.lean` runs `runAllScans`, the existing law over all 17 generated cases. It
must stay green: your change is purely additive (it widens what the unroller accepts and rejects
nothing new), so **no existing case may change behaviour**. If any does, stop and report — that
means the change is not additive.

---

## Hard boundaries

1. **Edit only the two match arms.** No refactoring, no reformatting, no "while I'm here"
   improvements to adjacent code. The diff should be small enough to read in one screen.
2. **No new imports in `ScanUnroll.lean`.** See the soundness rule above.
3. **Do not touch `ScanOracle.lean`, `ScanGen.lean`, `PropertyOracleScanTest.lean`,** or anything
   under `LeanNCD/`.
4. **Do not modify `OracleFixtureSeed.lean`** — it is your verification input, not your workspace.
5. No `sorry`, `admit`, or `axiom`.

---

## What to return

**The report is the appended README section, committed.** Your chat reply should be a short summary
plus the commit SHA — not the report itself.

The `## Oracle `.freeNorm` extension` section must contain:

1. The complete diff of `ScanUnroll.lean`, verbatim.
2. The **before** observation: the exact error the unrolling produced on fixture 2 prior to the
   change.
3. The **after** observation: the unrolled result and the legacy result, and that they agree.
4. The three gate job counts, verbatim.
5. Confirmation that `ScanUnroll.lean`'s import list is unchanged, with the list quoted.
6. Anything you had to decide that this brief did not specify.

**Paste raw output into the README. Do not summarize it, do not retype a value from memory, and never
record a result you did not observe.**

### Before you declare done, run this and paste its output in your reply

```bash
cd /Users/williammacready/code/python/pyncd
git log --oneline main..agents/task4-oracle-freenorm
git status --porcelain
git show --stat --format="%H" agents/task4-oracle-freenorm
```

The first must list at least one commit, the second must be **empty**, and the third gives the SHA to
report. If the first is empty, your work is not saved — commit it before replying.

---

## Stop and report rather than improvise if

- the change appears to require an import outside `Compare`/`ScanGen`;
- it appears to require touching any function other than `buildGeom` and `baseFreeSlots`;
- any of the 17 existing generated cases changes behaviour;
- the pre-change comparison on fixture 2 **passes** (it should fail — if it does not, the fixture is
  not exercising the path you are changing);
- the post-change unrolling disagrees with legacy on fixture 2 — report the disagreement rather than
  adjusting anything to make it agree. A mismatch here is a real finding about scan semantics, and
  bending the oracle to match legacy would destroy the independence that makes it worth having;
- your gate job counts differ from 8,657 / 8,543.
