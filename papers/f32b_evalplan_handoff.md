# F32-B execution plan — implementation handoff

This is the companion to [`f32b_evalplan.md`](f32b_evalplan.md), and it is written for a fresh
agent session with no prior context that will execute that plan. Read this file first, then the
plan. The format follows [`f32_evalplan_handoff.md`](f32_evalplan_handoff.md), the F32-A handoff,
which is now a completed record.

## 1. Checkpoint — exact state at handoff

| Item | Value |
|---|---|
| Plan document | `papers/f32b_evalplan.md` (1820 lines) |
| Plan content SHA-256 at handoff | `1a00bf31a64767f7b32a849939839f202d7a474370481c280fdbbb52fdc7675d` |
| Plan committed on | `main`, in the same commit as this file (`git log -1 -- papers/f32b_evalplan.md`) |
| Base it was measured against | `main` at `6a53ce7`, where F32-A is complete and merged |
| Authoring status | Complete. It had one self-review pass against `.claude/skills/slice-plan/SKILL.md`'s checklist, then two independent adversarial review rounds (2026-09-23). The second was aimed at the first round's own edits. Both are recorded at the end of the plan's §8. |
| Implementation status | **Not started.** No Lean source file has been modified. |
| Open questions | **None.** The draft's Q1–Q3 are closed decisions D1–D3 in the plan's §9: native libm transcendentals, no `f64` keyword, witness fixtures in the default `Tests` target. |
| `main` vs `origin/main` | `main` is ahead. **Not pushed.** |

Verify you have the right plan before doing anything:

```bash
shasum -a 256 papers/f32b_evalplan.md
# must print 1a00bf31a64767f7b32a849939839f202d7a474370481c280fdbbb52fdc7675d
```

If the hash differs, someone has edited the plan since handoff. Read
`git log -- papers/f32b_evalplan.md` and reconcile before proceeding.

Also re-check that the plan's six Lean blocks still compile against your tree:

```bash
awk '/^```lean$/{f=1;next} /^```$/{f=0} f' papers/f32b_evalplan.md \
  | bash .claude/skills/slice-plan/check-snippet.sh -
```

At handoff this printed `COMPILES.` The blocks include live `#guard`s against today's
`Eval/Nonlin.lean`, which are the golden binary64 table, and five libm witness checks. If the check
now fails, either the tree moved or the platform libm changed. Both are stop conditions (§5).

## 2. What the plan contains

It has five tasks, and each is an independently rejectable boundary. Tasks 2 and 3 depend only on
Task 1 and may run in either order.

| Task | Deliverable | Fixture groups | Mutation cycles |
|---|---|---:|---:|
| 1 | Binary32 math core. One formula per function over a private `NonlinScalarOps` record; `UnaryOp.applyChecked32`; the binary64 golden gate | 8 | 16 |
| 2 | Checked binary32 inline unary factors end to end, with the `unaryDomain32` payload | 11 | 6 |
| 3 | Checked binary32 pointwise/axiswise: storage-kind evidence, guarded workers, `checkPlan`/`runDensePlan32` dispatch | 11 | 11 |
| 4 | Compiler emission: the hard-coded binary64 nonlinear arms fixed; named end-to-end (causal attention, sigmoid, normalize) | 7 | 7 |
| 5 | Capability docs, final audit of tables A/B, close-out | 0 | 0 |
| | **Total** | **37** | **40** |

Section map of the plan:

- **§1** — the semantic decision, the admitted fragment, and what stays deferred. Read §1.1 in
  full: the platform libm is not correctly rounded, and that fact decides the shape of every
  numerical fixture.
- **§2** — the current boundary, re-derived from `main` at `6a53ce7`. §2.6 carries every observed
  discriminating bit pattern.
- **§3** — the architecture. Its Lean blocks form one compiled probe file. §3.5 contains the two
  sibling-audit tables that Tasks 3–5 must complete.
- **§4** — the tasks. Each has its Files, Implementation, numbered fixtures with donors, and
  mutation cycles.
- **§5** — dependencies and risk sizing.
- **§6** — cadence, per-task build targets, regression gates, the documentation sweep, and the two
  final reviews.
- **§7** — the definition of done, with exact bits, and the stop conditions.
- **§8** — the authoring verification record. It says what was measured and what was not.
- **§9** — the three closed design decisions (D1–D3) and their rationale.

## 3. Setup

`EnterWorktree` must run first. Then:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh
```

Do **not** pass `--plan`, because this plan is tracked in `papers/`. Read the script's six numbered
steps, and do not proceed past a failure. It fast-forwards the stale base and syncs a built `.lake`,
which prevents a multi-hour Mathlib cold build. Then refresh the project's own oleans:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD
```

`lake` is not on `PATH`, so always use `cd leanncd && "$HOME/.elan/bin/lake" build <targets>`. If a
build looks like it is compiling Mathlib, stop: the sync is broken.

The approved scripts are listed in `leanncd/AGENTS.md`:

- `leanncd/scripts/mutation-cycle.sh`, for every mutation cycle, invoked by the controlling session
  directly;
- `leanncd/scripts/lake-build.sh`;
- `leanncd/scripts/lean-file.sh`;
- `.claude/skills/slice-plan/check-snippet.sh`.

A snippet may `import` a test module such as `Eval.Plan.CompileTest` to reuse its donors. That was
verified at authoring time.

## 4. Execution discipline — the non-negotiables

1. **Fixture 1.1 is written and built green on the unmodified tree before `Eval/Nonlin.lean` is
   touched.** It is the only independent evidence that the binary64 refactor changed nothing. The
   legacy evaluator, the checked backend, and the scan-unroll oracle all call the functions being
   rewritten.
2. **Every one of the 40 mutation cycles is run and recorded**, with its fail and restored-pass
   observations. Nine already have observed wrong values from authoring: the eight named in plan
   Task 1's list, plus Task 3's M1 on `runDensePointwise`. The rest are predictions to confirm.
   There is one partial exception, from review round 2: Task 4's M1–M7 failure payloads were
   observed on hand-built raw plans, but not through the mutated compiler. Their old-strings must
   be multi-line (plan Task 4, "Old-string uniqueness").
3. **Guards before admission (Task 3).** The four worker guards and their order fixtures come before
   `checkPointwiseF32`/`checkAxiswiseF32` can produce evidence, in the same commit.
4. **The audit tables are deliverables.** Table A's worker/checker columns belong to Task 3, table B
   to Task 4, and the cell-by-cell re-verification to Task 5. A (c) cell is not a pass. It names the
   guard it relies on and the slice that inherits it.
5. **Use the §6.0 review cadence between tasks.** Tasks 1 and 3 get a strong reviewer.
6. **Done is §7**, not "it compiles".

## 5. Traps

- **Native libm transcendentals are decided (plan §9, D1).** Do not substitute correctly rounded
  binary64-then-narrow for `expf`/`logf`/…, even though it looks more accurate. That substitution
  is exactly what the witness fixtures and Task 1's M12/M13 cycles exist to reject.
- **Witness fixtures are platform-specific by design** (plan §3.6). If one fails with "no lane
  separates native binary32 from binary64-then-narrow", the libm changed. Re-run the plan's §8
  witness search for new lanes. Do not weaken the precondition.
- **Do not assert NaN bit patterns.** Use `isNaN`. IEEE-754 does not fix libm NaN payloads.
- **Do not assert a lone transcendental's hardcoded bits** except at the portable lanes of §2.6.
  Those were chosen with margins of at most 0.041 ulp.
- **`#check_failure` privacy fixtures only work across modules** (fixture 3.3). Inside the defining
  file the private constructor is visible.
- **Three existing passages are false and are Task 2's to fix.** `AdapterTest.lean` (twice) and
  `Adapter32Test.lean` (once) say `PlanRunCause.execution` is unreachable after a successful pack. A
  runtime unary domain violation reaches it, which was observed in binary64.
- **Deferred means deferred.** No f32 scan, scatter, JAX, conversion, or `f64` keyword work belongs
  here. `compileScan`'s literal `.f64` result slots are named as an F32-C obligation, not fixed.
- **Do not delete retired constructors.** This covers `unaryNotAdmittedForDtype`,
  `unaryNotAdmittedForStorage`, and the `unsupportedDtype`/`f32UnsupportedStep` payload kinds.

## 6. How to behave when the plan is wrong

It has had one self-review pass and two independent adversarial reviews. Expect findings anyway:
the reviews re-measured claims, but neither executed any task.

- **Verify against source, never against prose.** That covers the plan's prose, this document's,
  and any reviewer's.
- **A correction is not safer than the text it corrects.** F32-A's handoff §6 records that three
  consecutive review rounds each introduced a defect while fixing one. Verify any amendment
  first-hand. The session that writes a fix must not be the only one that certifies it.
- **When a fixture exists to distinguish reading A from reading B, check that its values actually
  differ.** Plan §2.6 records one case where they did not: `softmax [0, 0, 2.5]` gives the same
  bits under both fold orders, so a different row pins fold order.
- **If you hit a genuinely blocked task, stop and report.** Do not improvise.

## 7. Repo conventions you inherit

- Commit freely as work lands, in the `type(scope): imperative` style.
- Merging a completed branch to local `main` is pre-authorized once the full build is green and the
  final reviews are clean or adjudicated.
- **Pushing is not pre-authorized.**
- Anything destructive beyond the branch's own work needs explicit approval.
