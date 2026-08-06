---
name: new-slice
description: Set up an isolated leanncd worktree for a Wave C slice (or any leanncd branch work) — creates the worktree, fixes the stale-base trap, syncs the built .lake so Mathlib never cold-builds, copies the gitignored plan, and scaffolds the SDD ledger. Use whenever starting implementation work on a leanncd slice/plan in a fresh worktree.
---

# Starting a leanncd slice

Six setup steps used to be done by hand at the start of every slice, and two of
them are traps that silently cost hours if missed. `prepare-worktree.sh` does
all six and fails loudly instead of silently.

> Writing the plan you are about to execute is a separate, earlier step with
> its own disciplines (task right-sizing, compiling plan code before it ships):
> see `.claude/skills/slice-plan/`.

## Why this exists

- **Stale base.** `EnterWorktree` branches from `origin/<default>`, not local
  `main`. On this repo local `main` runs far ahead (21 commits at the time of
  writing), so a new worktree starts on stale code. This has been hit
  repeatedly and was always caught by eyeballing `git log`, never by tooling.
- **Cold Mathlib build.** A worktree with an empty `.lake/build` compiles
  Mathlib from source — hours. `leanncd/AGENTS.md` documents the manual
  rsync-a-donor procedure; this script performs it and then *verifies* the
  result is ≥95% complete before declaring the worktree ready.

## Usage

`EnterWorktree` must run first — it changes the session's working directory,
which a script cannot do. Then run the script from inside the new worktree:

```bash
bash .claude/skills/new-slice/prepare-worktree.sh \
  --plan docs/superpowers/plans/<YYYY-MM-DD-slice-name>.md
```

Options: `--base <branch>` (default `main`), `--plan <repo-relative path>`
(optional; skip it for non-plan branch work — steps 5 and 6 are then no-ops).

It prints six numbered steps and exits non-zero on any problem. Read the
output; do not proceed past a failure. In particular it refuses to run in the
primary checkout, refuses to auto-merge diverged branches, and refuses to call
a worktree ready when Mathlib is under 95% built.

Re-running is safe: the fast-forward, rsync, and ledger creation are all
idempotent, and an existing ledger is left untouched (resume, don't restart).

## After it succeeds

1. Do the pre-flight conflict scan over the plan (per
   `superpowers:subagent-driven-development`) before dispatching Task 1.
2. Dispatch tasks. Subagent prompts do **not** need to restate the lake
   invocation or the Mathlib warning — point them at `leanncd/AGENTS.md`
   instead, which is the single source for both.

## Building leanncd

`lake` is not on `PATH`. Always:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

A prepared worktree builds the full suite in well under a minute. If a build
looks like it is compiling Mathlib from scratch, something is wrong with the
`.lake` sync — stop rather than waiting it out.
