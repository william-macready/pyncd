---
name: new-slice
description: Set up an isolated leanncd worktree for slice work (or any leanncd branch work) — creates the worktree, fixes the stale-base trap, syncs the built .lake so Mathlib never cold-builds, copies the gitignored plan, and scaffolds the SDD ledger; also gives the subagent-brief preamble and the finish/merge sequence. Use whenever starting implementation work on a leanncd slice/plan in a fresh worktree.
---

# Starting a leanncd slice

Six setup steps used to be done by hand at the start of every slice, and two of
them are traps that silently cost hours if missed. `prepare-worktree.sh` does
all six and fails loudly instead of silently.

> Before any of this, pick the process weight: `.claude/skills/slice-plan/`
> section 0 decides whether a change needs the full plan-and-worktree pipeline
> or a direct test-first implementer. Writing the plan you are about to execute
> is a separate, earlier step with its own disciplines (task right-sizing,
> compiling plan code before it ships): see that skill.

## Why this exists

- **Stale base.** `EnterWorktree` branches from `origin/<default>`, not local
  `main`. Local `main` routinely runs ahead of `origin/main`, so a new worktree
  starts on stale code. This has been hit repeatedly and was always caught by
  eyeballing `git log`, never by tooling.
- **Cold Mathlib build.** A worktree with an empty `.lake/build` compiles
  Mathlib from source — hours. `leanncd/AGENTS.md` documents the manual
  rsync-a-donor procedure; this script performs it and then *verifies* the
  result is ≥95% complete before declaring the worktree ready.
- **Donor project oleans.** The whole `.lake` sync also copies the donor's
  `LeanNCD` oleans, which may have been built from a different branch even when
  Mathlib itself is compatible. Refresh `LeanNCD` before any `lake env lean` or
  `check-snippet.sh` call, or stale fields can appear as ghost compile errors.

## Usage

`EnterWorktree` must run first — it changes the session's working directory,
which a script cannot do. Then run the script from inside the new worktree:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh \
  --plan docs/superpowers/plans/<YYYY-MM-DD-slice-name>.md
```

Options: `--base <branch>` (default `main`), `--plan <repo-relative path>`
(optional; skip it for non-plan branch work — steps 5 and 6 are then no-ops).

It prints numbered steps and exits non-zero on any problem. Read the
output; do not proceed past a failure. In particular it refuses to run in the
primary checkout, refuses to auto-merge diverged branches, and refuses to call
a worktree ready when Mathlib is under 95% built.

Re-running is safe: the fast-forward, rsync, and ledger creation are all
idempotent, and an existing ledger is left untouched (resume, don't restart).

## After it succeeds

1. Refresh project-owned oleans against this worktree's source with the build
   wrapper (next section), target `LeanNCD`. The synced Mathlib cache keeps
   this fast.
2. Do the pre-flight conflict scan over the plan (per
   `superpowers:subagent-driven-development`) before dispatching Task 1.
3. Dispatch tasks. **Open every subagent brief with the preamble below.**

## Building leanncd

`lake` is not on `PATH`, and a hand-rolled invocation is a trap. Always:

```bash
bash leanncd/scripts/lake-build.sh /path/to/worktree/leanncd [target...]
```

The wrapper runs from inside `leanncd/` so the checkout's pinned toolchain is
used. Do NOT run `lake` from the worktree root: it resolves the Elan default
toolchain and can clobber `.lake` package oleans. See `leanncd/AGENTS.md`
("Invoking Lake") for the full rule, and for the single-file and mutation
wrappers (`lean-file.sh`, `mutation-cycle.sh`, `mutation-manifest.sh` — all
run as `bash <script>`; they are not meant to be executable).

A prepared worktree builds the full suite in well under a minute (minutes
after a large merge). If a build looks like it is compiling Mathlib from
scratch, something is wrong with the `.lake` sync — stop rather than waiting
it out. Run long builds in the background and wait for completion; do not
poll them turn by turn, since waiting burns the turn budget.

## Subagent brief preamble (copy verbatim into every brief)

The agent shell harness rejects compound shell and runtime-computed values, and
every agent has relearned this the hard way:

> Plain, separate shell commands only: no `cd x && y`, no `$VAR` in a command,
> no pipelines into git. Use absolute paths and `/usr/bin/git -C <worktree>`.
> Build only with `bash <worktree>/leanncd/scripts/lake-build.sh <worktree>/leanncd [target]`;
> never run `lake` from the worktree root. Use the Read tool for file windows
> and `rg -n` for search. Stage files by explicit path; never commit
> `.claude/settings.json`. Stay within the stated turn and context budget and
> say so in the report if you breach it.

When you launch several agents at once, write each launch's returned agent id
next to its label immediately, before sending any message to one of them.

## Finishing the slice

After the whole-branch review is clean and the full build is green:
`ExitWorktree` with `keep`, then merge from the primary checkout
(`/usr/bin/git -C <primary> merge --no-ff <branch>`), confirm
`git diff --stat main <branch>` is empty, then
`git worktree remove --force <worktree>` and `git branch -d <branch>`. Look at
`git status` in the worktree first: only discard files you have identified.
Do not push unless asked.
