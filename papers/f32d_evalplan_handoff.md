# F32-D execution plan — implementation handoff

Companion to [`f32d_evalplan.md`](f32d_evalplan.md), for a fresh session with no prior context that
will execute it. Read this file, then the plan. You do not need `f32d_record.md` (the authoring
record) unless a value disagrees.

## 1. Checkpoint — exact state at handoff

| Item | Value |
|---|---|
| Plan | `papers/f32d_evalplan.md`, 860 lines |
| Plan SHA-256 at handoff | `42b30db2ff8d213915d976250d97a21014771cbe80cd4662b635aadb91d51005` |
| Base | `main` at `6303e9f`; F32-A and F32-B complete and merged |
| Manifests | `papers/f32d_mutations.json` (7 cycles on code that exists today, `--check` OK); `papers/f32d_mutations_post.json` (11 cycles on code each task adds, validated against post-edit copies) |
| Files to copy, not retype | `papers/f32d_files/ScatterDense32Test.lean`, `papers/f32d_files/Scatter32OracleTest.lean` |
| Authoring | Drafted, then two independent adversarial reviews (source truth; test strength), a fix pass, and a verification round aimed at the fixes. 1 Critical found and fixed (no fixture for the binary32 fill-refusal direction). |
| Verified how | Every plan edit applied to full copies of the REAL modules (real namespace and module split) and compiled, all changed tests green: `papers/f32d_files/rv_build.py` → `ALL COMPILED`. Every value observed, never hand-derived. |
| NOT verified | A real `lake build` with the edits; the post-manifest cycles through the real `mutation-manifest.sh` (run with an equivalent scratch runner); the prose edits (specified, not performed). |
| Open questions | None. |
| `main` vs `origin/main` | ahead; **not pushed** |

```bash
shasum -a 256 papers/f32d_evalplan.md   # must print the SHA above; if not, read git log -- papers/f32d_evalplan.md
```

## 2. Setup

`EnterWorktree`, then `bash .claude/skills/new-slice/prepare-worktree.sh` (no `--plan`: the plan is
tracked). Then `bash leanncd/scripts/lake-build.sh <worktree>/leanncd` — baseline ends
`Build completed successfully` (8670 jobs at `6303e9f`). If it compiles Mathlib, stop: the sync
broke.

## 3. Dispatch shape (token budget: CLAUDE.md Rule 6)

| Task | Implementer | Reviewer | Why |
|---|---|---|---|
| 1 | Sonnet, one dispatch | Opus | the storage-kind guards and carrier split are the soundness surface |
| 2 | Sonnet, one dispatch | Sonnet | two arms and re-points; code pre-verified |
| 3 | Sonnet, **two dispatches** (phase 1: production + fixtures green; phase 2: cycles + scripted docs) via `.claude/skills/slice-plan/split-handoff-template.md` | Opus, after phase 2, over both commits | the compiler admission and the oracle |
| Final | — | **two** Opus whole-branch reviewers, different lenses (soundness of every f32 scatter door; docs/value-grep truth) | skill §4: the tier that finds what diffs cannot show |

Every brief pastes the task's `identifier @ file` list from the plan; implementers `rg -n` and read
windows, never a whole file over ~20k characters. Mutation cycles are never hand-written:
`bash leanncd/scripts/mutation-manifest.sh --task N --out <table.md> <leanncd-dir> <manifest>` on
both manifests, pasting the table into the report. After each dispatch, run
`python3 .claude/skills/slice-plan/token-report.py <session-id>` and ledger it; a dispatch past a
~250k context peak or ~60 turns says so in its report.

## 4. Non-negotiables

1. **Task 1's gate G64 is green on the unmodified tree first**, and again after the edit, with no
   edit to the binary64 scatter tests. It is the only evidence the carrier split changed nothing.
2. **A value that differs from the plan is a STOP** (plan §8), not an expectation to edit.
3. **Guard first at every scatter door** (plan §2); fixtures pin the ORDER, not just existence.
4. **The oracle runs early in Task 3 phase 1 and must be observed RED on the unmodified compiler**
   before Step 0c is lifted.
5. **Done is plan §7**, including the value-grep sweep printing nothing.

## 5. Traps

- `Float32.ofInt (-(2^128))` IS `-∞`: the binary32 fill arm's `isFinite` conjunct is load-bearing
  (fixture `f32ScatterOverflowFillProg`, cycle P3-4). The binary64 arm's analogous `2^1024`
  overflow is a pre-existing gap and is deliberately left alone.
- Under some post-manifest cycles an upstream test module fails first and the named module never
  builds (P1-4 is caught by the binary64 `ScatterDenseTest`; P2-1/P2-2 by `GraphCheckTest`). That is
  expected; the manifest's `expect` strings already reflect it.
- Scan-local scatter does NOT reuse this slice's path (plan §1.3) — do not touch `runDenseScan`.
- Deferred means deferred: no scan, JAX, legacy-evaluator, collision-policy, or nonlinear-scatter
  work belongs here.

## 6. When the plan is wrong

Verify against source, never against prose (the plan's, this file's, or a reviewer's). A correction
is not safer than the text it corrects: the session that writes a fix must not be the only one that
certifies it. A genuinely blocked task is a stop-and-report, not an improvisation.
