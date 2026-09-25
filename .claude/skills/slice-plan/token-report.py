#!/usr/bin/env python3
"""Report a Claude Code session's token cost, per subagent, from its local transcripts.

Usage: python3 .claude/skills/slice-plan/token-report.py <session-id> [<session-id>...]

"ctx" is cumulative input tokens: every turn's full context (input + cache read + cache write),
summed over turns. That is the number CLAUDE.md Rule 6 budgets and slice-plan §5 measures.
"peak" is the largest single-turn context, the thing a dispatch split reduces.
"""
import glob, json, os, sys

ROOT = os.path.expanduser("~/.claude/projects")


def usage(path):
    seen, ctx, out = set(), [], 0
    for line in open(path, errors="ignore"):
        try:
            m = json.loads(line).get("message") or {}
        except ValueError:
            continue
        u = m.get("usage") if isinstance(m, dict) else None
        if not u or m.get("id") in seen:
            continue
        seen.add(m.get("id"))
        ctx.append(sum(u.get(k, 0) or 0 for k in
                       ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")))
        out += u.get("output_tokens", 0) or 0
    return ctx, out


def row(label, ctx, out):
    return (f"{sum(ctx) / 1e6:8.1f}M ctx  peak {max(ctx, default=0) // 1000:4}k  "
            f"turns {len(ctx):4}  out {out // 1000:4}k  {label}")


if len(sys.argv) < 2:
    sys.exit(__doc__)
for sess in sys.argv[1:]:
    mains = glob.glob(f"{ROOT}/*/{sess}.jsonl")
    if not mains:
        print(f"no transcript for session {sess}", file=sys.stderr)
        continue
    ctx, out = usage(mains[0])
    total = sum(ctx)
    print(f"## session {sess}")
    print(row("(controller)", ctx, out))
    for sub in sorted(glob.glob(f"{os.path.dirname(mains[0])}/{sess}/subagents/*.jsonl")):
        meta = sub[:-len(".jsonl")] + ".meta.json"
        label = json.load(open(meta)).get("description", "?") if os.path.exists(meta) else "?"
        c, o = usage(sub)
        total += sum(c)
        print(row(label, c, o))
    print(f"{total / 1e6:8.1f}M ctx  TOTAL")
