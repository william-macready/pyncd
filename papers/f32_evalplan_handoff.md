# f32 execution plan — implementation handoff

> **✅ THE HANDOFF WAS TAKEN — all five tasks are implemented.** This document is now a completed
> record of the moment work started, not live instructions. **Its entire "Checkpoint — exact state at
> handoff" table is a snapshot and is retained verbatim**: "Implementation status: Not started",
> the plan's line count, and its content SHA-256 were all true at handoff and are all false now
> (`papers/f32_evalplan.md` has since been closed out as a completed record, so the `shasum`
> verification below will deliberately not match). Do not run this document's setup steps or treat
> its status table as current. Its review-history table and the standing lesson in the paragraph
> after it remain accurate and are the reason it is kept. For what the slice actually delivered,
> read `papers/f32_evalplan.md` §6.5.

Companion to `papers/f32_evalplan.md`. Written for a fresh agent session with no prior context that
will execute that plan. Read this file first, then the plan itself.

## 1. Checkpoint — exact state at handoff

| Item | Value |
|---|---|
| Plan document | `papers/f32_evalplan.md` (1793 lines) |
| Plan committed on | `main`, commit `7ff2fdd` |
| Plan content SHA-256 | `08e87529055e7073250158b6f7407b8812b78266201f98ea6977eab3c46d9893` |
| Authoring status | **Complete.** Seven review rounds closed. |
| Implementation status | **Not started.** Zero Lean source files have been modified. |
| Branch/worktree for implementation | **None yet.** Create one (Section 3 below). |
| `main` vs `origin/main` | `main` is 8 commits ahead; **not pushed** |

Verify you have the right plan before doing anything:

```bash
shasum -a 256 papers/f32_evalplan.md
# must print 08e87529055e7073250158b6f7407b8812b78266201f98ea6977eab3c46d9893
```

If it differs, someone has edited the plan since handoff — read `git log -- papers/f32_evalplan.md`
and reconcile before proceeding.

### Review history (why the plan is in the state it is)

Seven rounds, each two independent lenses against a frozen revision:

| Round | Scope | Findings |
|---|---|---|
| 1 | architecture/evidence | 19 (2 blocking) — resolved |
| 2 | donor, regression-gate, execution-table, historical status | 11 — resolved |
| 3 | identifiers, donors, paths, file lists; coverage completeness, sibling doors | **0** |
| 4 | a risk-reweighting change: arithmetic + engineering judgment | 3 blocking — resolved |
| 5 | confirmatory, on round 4's correction | 1 real gap + 1 miscount — resolved |
| 6 | general: does every fixture claim have a mutation cycle that can fail? | 16 candidates → 9 fixed, 7 judged already covered |
| 7 | text rounds 4–6 *added*, never source-verified; cross-section consistency | 12 (4 blocking) — all resolved |

**Round 7's finding matters to you:** every one of its twelve defects was introduced by rounds 4–6's
own corrections, not by the original authoring — each time because a fix was written from a
reviewer's prose instead of from the source the reviewer had read. Section 8 of the plan records this
as a standing lesson. It applies to implementation exactly as it applied to authoring.

## 2. What the plan contains

Five sequential tasks, each an independently rejectable boundary. Task N+1 depends on Task N.

| Task | Deliverable | Fixture groups | Mutation cycles |
|---|---|---:|---:|
| 1 | Explicit source f32 (`Decl.typedTensor`), close the legacy evaluator boundary | 16 | 18 |
| 2 | Checked binary32 evidence + compiler specialization | 25 | 33 + 1 sweep |
| 3 | Native binary32 local and graph execution | 16 | 15 |
| 4 | Named f32 boundary, guard the legacy adapter | 15 | 19 |
| 5 | JAX truthfulness, capability documentation | 2 | 1 |
| | **Total** | **74** | **86 + 1 sweep** |

Section map of the plan:

- **§1** — the decision, the exact admitted fragment, and explicitly deferred slices. Read §1.3
  before assuming any f32 operation is in scope; most are not.
- **§2** — the current boundary, re-derived from the tree at authoring time.
- **§3** — architecture: source dtype authority (§3.1), checked evidence and algebra (§3.2), the
  native worker (§3.3), named adapter (§3.4), and the execution-door audit table (§3.5).
- **§4** — the five tasks: Files, Implementation steps, numbered fixtures, mutation cycles.
- **§5** — dependency graph and per-task risk sizing.
- **§6** — validation: review cadence (6.0), per-task build commands (6.1), regression gates (6.2),
  documentation sweep (6.3), full gate and two final reviews (6.4).
- **§7** — success criteria and stop conditions. This is the definition of done.
- **§8** — authoring verification record, including why several decisions are what they are. Read the
  relevant entry before proposing to change anything; most obvious "improvements" were already tried
  and reverted for a recorded reason.

## 3. Setup

`EnterWorktree` must run first (it changes the session working directory; a script cannot). Then:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh
```

Do **not** pass `--plan` — that option copies a gitignored plan from `docs/superpowers/plans/`. This
plan lives in `papers/` and is tracked, so it is already present in the worktree.

The script prints six numbered steps and exits non-zero on any problem. **Read its output; do not
proceed past a failure.** It exists because two of those steps are traps that silently cost hours:

- **Stale base.** `EnterWorktree` branches from `origin/<default>`, not local `main`, and local
  `main` runs well ahead. The script fast-forwards.
- **Cold Mathlib build.** A worktree with an empty `.lake/build` compiles Mathlib from source —
  hours. The script rsyncs a built `.lake` from a donor checkout and verifies ≥95% completeness
  before declaring the worktree ready.

After it succeeds, refresh project-owned oleans against this worktree's source (the donor's `LeanNCD`
oleans may be from another branch):

```bash
cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD
```

### Building

`lake` is not on `PATH`. The invocation shape is always:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build [targets...]
```

A prepared worktree builds the full suite in well under a minute. **If a build looks like it is
compiling Mathlib from scratch, stop** — the `.lake` sync is broken. Do not wait it out.

`leanncd/AGENTS.md` is the single source of truth for build invocation and the Mathlib warning.

### Approved scripts

These exist so that permission rules have one stable command shape. Prefer them over ad hoc chains:

| Script | Purpose |
|---|---|
| `leanncd/scripts/lake-build.sh <leanncd-dir> [targets...]` | Build targets using the checkout's pinned toolchain |
| `leanncd/scripts/mutation-cycle.sh [--cd <dir>] [--hashes <manifest>] <label> <leanncd-dir> <file> <old> <new> <targets...>` | One full auditable mutation record: baseline pass / exact mutation / intended failure / restored pass |
| `leanncd/scripts/mutate-and-build.sh` | The mutate+build primitive `mutation-cycle.sh` builds on |
| `leanncd/scripts/lean-file.sh` | Single-file elaboration |
| `.claude/skills/slice-plan/check-snippet.sh <file.lean>` | Compile a standalone snippet against the real environment |

## 4. Execution discipline — the non-negotiables

1. **Tasks run in order, 1 → 5.** Each depends on its predecessor. Do not start Task N+1 before Task
   N's review is clean.

2. **Every one of the 86 mutation cycles must actually be run.** A mutation cycle is: apply the exact
   source change the plan names → observe the named fixture fail → restore → observe it pass. Both
   observations get recorded. These are completion gates, not documentation. `mutation-cycle.sh`
   produces the auditable record in one command. A plan that says "fixture X would fail" is a claim;
   your job is to turn each into an observation.

3. **The door-guard completeness sweep is Task 2 implementation item 7** — a recorded per-door
   deliverable of the task, not a reviewer courtesy. It is the *only* verification standing in for
   fixture 23 and the existence halves of 22/25, which carry no mutation cycle. Open each of the
   eight named plan-level entries and record, per door, that its guard is present.

4. **Run the per-task review cadence in §6.0 between tasks:** commit the task as one reviewable unit,
   run an independent review against its requirements/fixtures/mutations/targeted commands, inspect
   unchanged sibling entry points named by the execution-door audit, then resolve or explicitly
   adjudicate every finding and get a clean re-review before starting the next task.

5. **Run the gates:** §6.1 per-task targeted builds, §6.2 existing regression gates (including the
   3,832-case scan-free and 17-case scan differential corpora), §6.3 the documentation and
   stale-value sweep, §6.4 the full `lake build` plus `JaxExperiment` and **two** independent
   whole-branch reviews with different lenses.

6. **Task 5 step 5 closes the loop:** change the plan's status from implementation plan to completed
   record and append the observed mutation results, build results, and both final-review
   adjudications. The plan is the record; leave it truthful.

7. **Done is §7**, not "the code compiles." Fourteen criteria, including specific bit patterns.

## 5. Traps

- **Mathlib cold build** — see Section 3. The single most expensive mistake available here.
- **Task 1 installs a temporary stop that Task 2 removes.** Task 1 makes `prepareEvalPlan` reject
  every homogeneous f32 schedule with `CapabilityError.unsupportedDtype "f32 execution not yet
  admitted"`. That is deliberate: it keeps the tree safe between tasks. Task 2 removes it *only after*
  checked evidence and the Float-worker guards exist. Do not remove it early, and do not "fix" Task
  1's fixtures that assert it.
- **Do not delete any error constructor.** The plan extends producer-less families rather than
  pruning them; several documentation counts depend on the exact constructor inventory.
- **Deferred means deferred.** §1.3 lists F32-B (unary/nonlinear), F32-C (scans), F32-D (top-level
  scatter), F32-E (conversions), F32-JAX, and Complex-A/B. Every one of those appears in this slice
  only as a *rejection* fixture. If you find yourself implementing execution for one, you have left
  the slice.
- **The counting convention for mutation cycles** (recorded in §8): one mutation observed across
  several fixtures is one cycle; only an explicit "N cycles" annotation, or "independently" applied
  to an enumerated list, counts as N. Use it if you need to re-derive a total.

## 6. How to behave when the plan is wrong

It may be. Seven rounds reduced that probability; they did not eliminate it.

- **Verify against source, never against prose** — not the plan's, not this document's, not a
  reviewer's. Round 7 exists entirely because that rule was broken three times in a row.
- **A correction is not safer than the text it corrects.** Rounds 4, 5, and 6 each fixed a real
  defect and each introduced a new one doing so. If you amend the plan mid-implementation, verify the
  amendment first-hand, and do not let the session that writes a fix be the only one that certifies
  it.
- **When a fixture's stated purpose is to distinguish reading A from reading B, build it so it
  actually can.** Check the concrete values/shapes make the two readings differ; a fixture where both
  readings coincide pins nothing, however many you write.
- **If you hit a genuinely blocked task** — a plan defect that invalidates later tasks, or a review
  finding that is real, load-bearing, and unfixable within the plan — **stop and report.** Do not
  improvise around it. This is a standing repo rule, not a preference.
- **Read the relevant §8 entry before proposing a design change.** Several plausible-looking
  improvements were tried and reverted with recorded reasons.

## 7. Repo conventions you inherit

- Commit freely as work lands, following the repo's message style (`type(scope): imperative`).
- Merging a completed branch to local `main` is pre-authorized once the full build is green and the
  final reviews are clean or adjudicated.
- **Pushing to a remote is not pre-authorized.** Leave `main` ahead of `origin/main` and say so.
- Anything destructive beyond the current branch's own work (force-push, history rewrite, deleting
  others' branches or worktrees) requires explicit approval.
- `papers/` holds design/plan documents; `leanncd/` is the Lean subproject with its own AGENTS.md
  and build pitfalls; `.claude/skills/` holds the slice tooling.
