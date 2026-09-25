# Phase-2 handoff: <Task N> — fixtures and mutation cycles

Fill in and paste as the second implementer's prompt (see SKILL.md §5, "Split long implementer
dispatches"). Everything below comes from command output or the plan, never retyped from memory.

## State you inherit
- Worktree: `<absolute path>`; branch `<branch>`.
- Phase-1 commit: `<sha>` (`git show --stat <sha>` lists what changed). It builds green:
  `<exact lake-build.sh command>` → `Build completed successfully`.
- Phase 1 changed only production code. Do not modify it except to fix a defect a fixture exposes;
  if you do, say so in your report as a separate item.

## Where things are (identifier @ file — `rg -n <identifier>`, then read a ~40-line window)
- `<identifier>` @ `<file>` — <one line: what it is / why you need it>
- …

Do not read any file over ~20k characters whole.

## What to do
1. Fixtures: plan §<ref>, fixtures <list>. Each names its donor (`clone <fixture>, change <field>`).
2. Mutation cycles:
   `bash leanncd/scripts/mutation-manifest.sh --task <N> --out <table.md> <leanncd-dir> papers/<plan>_mutations.json`.
   Every row must PASS. A FAIL with "expected text not in mutated build log" means the fixture
   does not catch the mutation for the stated reason — fix the fixture, not the manifest.
3. Commit, then report: the commit SHA, the results table verbatim, and any deviation from the plan.

## Phase-1 notes (≤10 lines, from the phase-1 implementer's report)
- <non-obvious thing phase 1 learned that phase 2 needs, e.g. a helper's actual name>
