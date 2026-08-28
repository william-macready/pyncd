# Brief: author six oracle fixtures for Task 4, and record their observed values

**Audience:** an external coding agent (GPT / Copilot), working in this repository.
**Written:** 2026-08-28. **Against:** `main` at `760ee22`.

You are producing an **implementation seed**: six small scan programs, each exercising one required
shape, each executed through the legacy evaluator with its observed value recorded. You are **not**
implementing Task 4, modifying production code, or touching any file under `leanncd/test/`.

---

## Base, branch, and where output is saved

Repository `main` at **`760ee22`**.

Create and work on branch **`agents/task4-oracle-fixtures`** — this exact name, so it can be found
without searching.

**All output is committed to that branch as files. Nothing counts as delivered if it exists only in
a chat reply.** Exactly two paths change:

| Path | What goes there |
|---|---|
| `papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean` | **new** — the six fixtures, their inputs, their structural assertions, and the code that prints each observed value |
| `papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/README.md` | **appended** — a new `## Oracle fixture authoring` section holding the full report described below |

Do not modify `NonlinearScanAdmissionSeed.lean` in that same directory (the earlier stop report), and
do not touch any other file anywhere.

---

## Background — why you are authoring rather than recovering

`papers/nonlinearity_split_pair_direct_lowering.md` §3.6 records six "oracle group" values from an
early spike. **Those values are unrecoverable** — no source program or input set survives, confirmed
by an exhaustive forensic search (all reachable refs, every Git blob including unreachable objects,
the retained session store), independently re-verified. See §3.6's opening blockquote and this
directory's existing `README.md`.

That question is **closed**. **Do not search for, or construct a program to reproduce, any recorded
float.** Fitting a program to a remembered answer is forbidden by §1.3.1's donor boundaries: it pins
nothing and converts a differential guarantee into a tautology.

The six *shapes* are sound and remain the coverage Task 4 needs. Your job is to author fresh programs
of those shapes and record whatever legacy produces. **The value is an output, never a target.**

A structural survey already ran; its results are below and you should use them rather than repeat it.

---

## Two shapes are ADOPTED, not authored

These already exist with verified values. Reference them in your file (import and re-run to confirm
the value still holds), but do not rewrite them.

| Shape | Program | Where | Value |
|---|---|---|---|
| 3 — leading persistent nonlinear | `S[j,0]:=X[j]; S[j,l+1] := relu(S[j,l]·A[j])`, `X=[1]`, `A=[-1]`, `L=2` | `test/Eval/ScanTest.lean`, the ReLU-scan `run_cmd` | `S = [1, 0]` |
| 6 — coupled states | `G[j,l+1] := relu(G·W_G + H·U)`, `H[j,l+1] := relu(H·W_H + G·V)` | `test/Eval/EvalExamplesTest.lean`, example 5 | `G = [1,3,6]`, `H = [2,3,6]` |

Confirm both reproduce. If either does not, **stop and report** — that means the tree moved.

---

## Four shapes to author

**The group 1 / group 3 distinction is settled as follows and is not yours to revisit:** group 1 is a
pointwise nonlinearity on a **block-local scratch** (a destination with a recurrence write and *no*
base write); group 3 is a pointwise nonlinearity on a **persistent state's own recurrence** (base
*and* recurrence writes). This keeps "persistent" in group 3's name meaningful and gives the groups
distinct coverage.

For each fixture below: write the program, supply inputs, run it through legacy, and record BOTH the
observed value AND the structural facts listed. Keep programs minimal — small axis sizes, small
integer inputs, no more structure than the shape requires.

### Fixture 1 — leading pointwise (scratch)

A scan in which a **scratch** destination is produced by a pointwise nonlinearity, with its local
axis at slot position 0. Scratch means: written in the recurrence, never given a base write, and
consumed by a state.

- Model the scratch mechanics on `test/Eval/Plan/ScanCompileTest.lean`'s `scratchSched` (an existing
  one-scratch scan) — but make the scratch's producing statement nonlinear, which `scratchSched`'s
  is not.
- **Structural facts to record:** the scratch's LHS slot list, showing its local axis at index 0 and
  no `.iterAt` slot anywhere in it; and that the scratch name has exactly one writing statement.

### Fixture 2 — interleaved axiswise

An **axiswise** nonlinearity (`normalize`, `softmax`, or `l2normalize` — unmasked) in a recurrence,
where the normalized local axis sits **strictly between** two iteration axes in the LHS slot order.

- This is the only shape with no existing candidate, but its **geometry** exists: the survey found
  `ScanCompileTest.coupledSched` already has interleaved geometry and lacks only a nonlinear
  recurrence, and `RouteFragmentCorpusTest.multiAxisProgram` uses an `[i, l, m]` layout. Take the
  geometry from one of those and put an axiswise recurrence on it.
- **Structural facts to record:** the LHS slot list with indices, showing the `.freeNorm` slot at an
  index strictly greater than one iteration-axis slot and strictly less than another.
- **The nonlinearity must be unmasked.** A `where`-predicate makes this a masked axiswise, which
  §3.1 does not admit and which Task 4 pins as a *rejection* fixture. If you find yourself needing a
  mask, stop and report.

### Fixture 4 — nonlinear base

A scan whose **base** statement carries the nonlinearity, with a linear recurrence.

- Structural donor: `RouteFragmentCorpusTest.nonlinearBaseProgram` (base is `.pointwise .relu`,
  recurrence `.identity`) — it has no inputs, so you supply them.
  `ScanCompileTest.multiBaseSched` is a base-geometry donor.
- **Structural facts to record:** that the base statement's `nonlin` is pointwise and the
  recurrence's is `.identity` — the opposite of fixtures 1 and 3.

### Fixture 5 — scratch → scratch → state

A **nonlinear** scratch consumed by a **second** scratch, which then writes a state.

- The real precedent is `EvalExamplesTest.lean` example 13, whose body contains exactly this chain —
  **but do not adopt it**: it is the scan-form of the causal-attention example and carries a masked
  softmax, which is outside the admitted capability. Model the chain, not the program.
- **Structural facts to record:** the three destination names in dependency order, and that the two
  scratches have no base write while the state has one.

---

## Hard boundaries

1. **Modify no production file and no file under `leanncd/test/`.** Your output is one new seed file
   plus a README section.
2. **Never import from `papers/`**, and nothing in `papers/` may be imported by production.
3. **Do not construct a program to hit a recorded float.** Values are observed, never targeted.
4. **Unmasked pointwise/axiswise `f64` only.** No masks, no Iverson predicates, no programmatic
   max/min, no scatter. If a shape seems to need one, stop and report.
5. **Do not reuse `ScanGen.template2`** or any private template as a donor — §3.6 forbids it. Shape
   precedent only.
6. No `sorry`, `admit`, or `axiom`.

---

## Gates

From `leanncd/`, before and after:

```bash
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

Expected **8,657 / 8,543**, unchanged — your seed is outside both target graphs. Run your own file
directly:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/nonlinear_scan_admission/OracleFixtureSeed.lean
```

---

## What to return

**The report is the appended README section, committed.** Your chat reply should be a short summary
plus the commit SHA — not the report itself.

The `## Oracle fixture authoring` section must contain:

1. A table per fixture: the program source verbatim, its inputs, the **observed** legacy value, and
   the structural facts this brief lists for that shape.
2. Confirmation that the two adopted fixtures still reproduce their recorded values.
3. The two gate job counts, verbatim.
4. Your seed file's raw stdout, verbatim.
5. Anything you had to decide that this brief did not specify.

**Paste raw output into the README. Do not summarize it, do not retype a value from memory, and never
record a result you did not observe.** If a program will not elaborate, paste the full error rather
than quietly changing the shape to something that compiles — a fixture that compiles but has the
wrong shape is worse than one that does not compile, because it passes while covering nothing.

### Before you declare done, run this and paste its output in your reply

```bash
cd /Users/williammacready/code/python/pyncd
git log --oneline main..agents/task4-oracle-fixtures
git status --porcelain
git show --stat --format="%H" agents/task4-oracle-fixtures
```

The first must list at least one commit, the second must be **empty** (nothing uncommitted or
untracked left behind), and the third gives the SHA to report. If the first is empty, your work is
not saved — commit it before replying.

---

## Stop and report rather than improvise if

- either adopted fixture no longer reproduces its value;
- a shape appears to require a mask, predicate, or any capability outside unmasked pointwise/axiswise
  `f64`;
- the interleaved geometry for fixture 2 cannot be built without two genuine iteration axes;
- you cannot write a structural assertion that distinguishes the shape from its neighbours — say so,
  because that means the shape as specified is not pinned by anything;
- your gate job counts differ from 8,657 / 8,543.
