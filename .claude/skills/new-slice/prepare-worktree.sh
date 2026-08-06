#!/usr/bin/env bash
# Prepare a freshly-created leanncd worktree for slice work.
#
# Run this from INSIDE a linked worktree, immediately after EnterWorktree
# (which is the one step a script cannot do — it changes the session's cwd).
#
# Does, in order:
#   1. refuse to run outside a linked worktree
#   2. fast-forward the worktree branch to the LOCAL base branch
#      (EnterWorktree branches from origin/<default>, which is routinely
#      behind local main — this trap has bitten repeatedly)
#   3. rsync a fully-built .lake from the fullest donor checkout
#      (a cold Mathlib build is multi-hour; this makes it seconds)
#   4. verify the synced Mathlib is actually complete, and fail loudly if not
#   5. copy the (gitignored) plan file in, so subagents can read it
#   6. scaffold the subagent-driven-development ledger
#
# Usage:
#   prepare-worktree.sh [--base <branch>] [--plan <path-relative-to-repo-root>]
#
# Defaults: --base main, no plan copy.

set -euo pipefail

BASE_BRANCH="main"
PLAN_PATH=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) BASE_BRANCH="$2"; shift 2 ;;
    --plan) PLAN_PATH="$2"; shift 2 ;;
    -h|--help) sed -n '2,24p' "$0"; exit 0 ;;
    *) echo "prepare-worktree: unknown argument: $1" >&2; exit 2 ;;
  esac
done

say() { printf '  %s\n' "$*"; }
step() { printf '\n[%s] %s\n' "$1" "$2"; }

# ---------------------------------------------------------------- 1. guard ---
step 1/6 "Verifying this is a linked worktree"

GIT_DIR_ABS=$(cd "$(git rev-parse --git-dir)" && pwd -P)
GIT_COMMON_ABS=$(cd "$(git rev-parse --git-common-dir)" && pwd -P)

if [[ "$GIT_DIR_ABS" == "$GIT_COMMON_ABS" ]]; then
  echo "prepare-worktree: refusing to run — this is the primary checkout, not a linked worktree." >&2
  echo "  Call EnterWorktree first, then re-run this from inside the new worktree." >&2
  exit 1
fi

WORKTREE_ROOT=$(git rev-parse --show-toplevel)
MAIN_ROOT=$(cd "$GIT_COMMON_ABS/.." && pwd -P)
BRANCH=$(git branch --show-current)
say "worktree : $WORKTREE_ROOT"
say "branch   : ${BRANCH:-<detached>}"
say "primary  : $MAIN_ROOT"

# ------------------------------------------------------- 2. stale-base fix ---
step 2/6 "Fast-forwarding to local '$BASE_BRANCH'"

if ! git rev-parse --verify --quiet "$BASE_BRANCH" >/dev/null; then
  echo "prepare-worktree: base branch '$BASE_BRANCH' does not exist locally." >&2
  exit 1
fi

BEFORE=$(git rev-parse --short HEAD)
if git merge-base --is-ancestor HEAD "$BASE_BRANCH"; then
  git merge --ff-only "$BASE_BRANCH" >/dev/null
  AFTER=$(git rev-parse --short HEAD)
  if [[ "$BEFORE" == "$AFTER" ]]; then
    say "already at $BASE_BRANCH ($AFTER) — nothing to do"
  else
    say "fast-forwarded $BEFORE -> $AFTER (this is the stale-base trap, now handled)"
  fi
else
  echo "prepare-worktree: HEAD is not an ancestor of '$BASE_BRANCH' — branches have diverged." >&2
  echo "  Refusing to auto-merge. Resolve manually before starting slice work." >&2
  exit 1
fi

# --------------------------------------------------------- 3+4. .lake sync ---
step 3/6 "Locating the fullest .lake donor"

# Count built mathlib oleans in a checkout. Must tolerate a missing directory:
# most candidate worktrees have no .lake at all, and under `set -eo pipefail`
# a failing `find` inside a pipeline would otherwise abort the whole script.
count_oleans() {  # $1 = checkout root
  local dir="$1/leanncd/.lake/packages/mathlib/.lake/build/lib"
  [[ -d "$dir" ]] || { echo 0; return 0; }
  find "$dir" -name '*.olean' 2>/dev/null | wc -l | tr -d ' '
}

# Same tolerance for counting mathlib sources.
count_sources() {  # $1 = checkout root
  local dir="$1/leanncd/.lake/packages/mathlib/Mathlib"
  [[ -d "$dir" ]] || { echo 0; return 0; }
  find "$dir" -name '*.lean' 2>/dev/null | wc -l | tr -d ' '
}

BEST_DONOR=""
BEST_COUNT=0
while read -r candidate; do
  [[ -z "$candidate" || "$candidate" == "$WORKTREE_ROOT" ]] && continue
  c=$(count_oleans "$candidate")
  if (( c > BEST_COUNT )); then BEST_COUNT=$c; BEST_DONOR=$candidate; fi
done < <(git worktree list --porcelain | awk '/^worktree /{print $2}')

if [[ -z "$BEST_DONOR" ]]; then
  echo "prepare-worktree: no checkout with a built .lake found. A build here would cold-compile" >&2
  echo "  Mathlib (hours). Build one checkout fully first, then re-run." >&2
  exit 1
fi
say "donor    : $BEST_DONOR ($BEST_COUNT mathlib oleans)"

step 4/6 "Syncing .lake and verifying completeness"

MINE=$(count_oleans "$WORKTREE_ROOT")
if (( MINE >= BEST_COUNT )); then
  say "already have $MINE oleans — skipping rsync"
else
  rsync -a "$BEST_DONOR/leanncd/.lake/" "$WORKTREE_ROOT/leanncd/.lake/"
  say "rsynced $BEST_COUNT oleans"
fi

# A build is only safe if the synced Mathlib is essentially complete. Compare
# built oleans against Mathlib's own source count in the SYNCED tree.
SRC=$(count_sources "$WORKTREE_ROOT")
BUILT=$(count_oleans "$WORKTREE_ROOT")
if (( SRC == 0 )); then
  echo "prepare-worktree: mathlib sources not found after sync — cannot verify." >&2
  exit 1
fi
PCT=$(( BUILT * 100 / SRC ))
say "mathlib  : $BUILT built / $SRC sources (${PCT}%)"
if (( PCT < 95 )); then
  echo "prepare-worktree: Mathlib build is only ${PCT}% complete — 'lake build' would cold-compile" >&2
  echo "  the remainder (potentially hours). Refusing to declare this worktree ready." >&2
  exit 1
fi

# ------------------------------------------------------------ 5. plan copy ---
step 5/6 "Copying the plan file"

LEDGER_DIR=""
if [[ -n "$PLAN_PATH" ]]; then
  SRC_PLAN="$MAIN_ROOT/$PLAN_PATH"
  if [[ ! -f "$SRC_PLAN" ]]; then
    echo "prepare-worktree: plan not found at $SRC_PLAN" >&2
    exit 1
  fi
  mkdir -p "$WORKTREE_ROOT/$(dirname "$PLAN_PATH")"
  cp "$SRC_PLAN" "$WORKTREE_ROOT/$PLAN_PATH"
  say "copied $PLAN_PATH (gitignored — does not arrive with the branch)"
  LEDGER_DIR="$WORKTREE_ROOT/.superpowers/sdd/$(basename "${PLAN_PATH%.md}")"
else
  say "no --plan given; skipping"
fi

# ---------------------------------------------------------- 6. ledger init ---
step 6/6 "Scaffolding the SDD ledger"

if [[ -n "$LEDGER_DIR" ]]; then
  mkdir -p "$LEDGER_DIR"
  LEDGER="$LEDGER_DIR/progress.md"
  if [[ -f "$LEDGER" ]]; then
    say "ledger already exists — left untouched (resume, do not restart)"
  else
    cat > "$LEDGER" <<LEDGER_EOF
# SDD ledger — plan: $PLAN_PATH

Worktree: $WORKTREE_ROOT
Branch: $BRANCH (fast-forwarded to local $BASE_BRANCH @ $(git rev-parse --short HEAD))
.lake synced from $BEST_DONOR ($BUILT/$SRC mathlib oleans, no cold build needed)
Prepared by: .claude/skills/new-slice/prepare-worktree.sh
LEDGER_EOF
    say "created $LEDGER"
  fi
else
  say "no plan given; skipping"
fi

printf '\nWorktree ready. Next: pre-flight conflict scan, then Task 1.\n'
