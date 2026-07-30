# Archived drafts

Superseded documents, kept for reference only. **Do not treat anything here as current.**
The live versions live in `papers/` proper.

## Naperian typing drafts (archived 2026-07-30)

Four files, salvaged from two branches (`agents/gpt55-summary-dgraded-prop-combination`,
`agents/gpt-5-5-naperian-typing-background`) before those branches were deleted.

They are **not older revisions** of the live docs — they are *independently written* documents that
happened to share the same filenames. Compared against `papers/NaperianTypingIntegrationPlan.md`,
the 2026-06-29 draft shares **exactly one section heading**: the diff is +748/−686, i.e. a fork, not
a superset.

| Archived file | Lines | Live counterpart |
|---|---|---|
| `NaperianTypingIntegrationPlan-2026-06-29-draft.md` | 926 | `papers/NaperianTypingIntegrationPlan.md` (864) |
| `NaperianTypingIntegrationPlan-2026-07-01-draft.md` | 450 | ″ |
| `NaperianTyping-2026-06-29-draft.md` | 708 | `papers/NaperianTyping.md` (990) |
| `NaperianTyping-2026-07-01-draft.md` | 856 | ″ |

**Why the live version won despite one draft being longer.** The live
`NaperianTypingIntegrationPlan.md` carries `## 0. Code audit findings (2026-07-01) — read this
first` and `## 8. Track A — final status (2026-07-03)` — both *later* than the drafts, and both
absent from them. More decisively, the drafts are organised entirely around introducing a Naperian
**typeclass** (`Core/Naperian.lean`, `Instances/StNaperian.lean`, a concrete `NaperianAxis StObj`
instance). That plan was **superseded**: what actually shipped was Track A — the routing-layer
`StMatP` reindexing invariants — merged as `b0bc15a`, explicitly *not* the typeclass. So adopting a
draft on length alone would have replaced a live plan-with-status by a dead proposal.

Read these only for ideas that the superseded typeclass framing may still contain; the sequencing,
file lists, and status claims in them are wrong relative to the code as it now stands.
