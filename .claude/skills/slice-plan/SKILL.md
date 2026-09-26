---
name: slice-plan
description: Authoring discipline for leanncd slice implementation plans (Wave C/F slices, or any subagent-driven-development plan in this repo) — verifying plan code, paths, and prose claims before they ship; covering the recurring-defect siblings a diff review structurally cannot see; right-sizing tasks by fixture count; budgeting implementer AND authoring context (reading windows, mutation manifests, per-task patches, a live plan kept apart from its record); and where review budget actually pays. Use when writing or revising an implementation plan for leanncd, before executing it.
---

# Writing a leanncd slice plan

Rules learned from measured failures in Waves C and F and the F32 slices. Apply them while authoring;
after a plan ships they are too late. Each rule's measured example and full reasoning is in
`REFERENCE.md` under the same section number — read it only when a rule leaves you unsure. Setting
up a worktree to *execute* a plan is `.claude/skills/new-slice/`.

## 1. Verify everything the plan asserts (REFERENCE §1)

- **Compile every Lean block** with `bash .claude/skills/slice-plan/check-snippet.sh <file|->`,
  fragments concatenated with their dependencies. Re-check any block edited after its drafter
  verified it, including "cosmetic" reformatting during assembly.
- **Observe every asserted value** from a real run; never hand-derive.
- **Mutation-test every regression/parity fixture**: break the code, see the fixture fail, restore.
- **Index, locator, order, and payload requirements** need a fixture whose construction makes the
  candidate readings DIFFER; an order claim needs a fixture violating both conditions at once.
- **Prose claims about code** ("X reuses Y", "no second Z") are diffed or grepped, not asserted.
- **Re-measure every inherited claim** before restating it, including carried-forward gap lists;
  after moving a capability boundary, value-grep the whole repo for the numbers that moved.
- **`ls` every path**; derive each task's Files list from where its deliverable must live.
- **No `File.lean:NNN`** in any text a task ships; cite identifiers.

## 2. Cover what a diff cannot show (REFERENCE §2)

A review package is a diff, and unchanged sibling code is invisible to it. When a task fixes
instance N of a known defect family, the plan names the sibling functions and makes a case × class
table (required / forbidden / **silently ignored**) a deliverable of that task; every
silently-ignored cell is a candidate instance N+1. Write-path predicates are the usual culprits, and
audit call-site preconditions, not only predicate text.

## 3. Right-size tasks (REFERENCE §3)

Split only where a reviewer could reject one task while approving its neighbor. Merge small,
purely additive tasks that share a test cycle. Size by fixtures and mutation cycles, not production
lines, and state both counts in the risk table. Name the donor for every fixture
(`clone <fixture>, change <field>`). Flag a task that bundles housekeeping with claims needing
verification.

## 4. What not to trim (REFERENCE §4)

The final whole-branch review finds what no per-task diff shows; for a soundness surface, use two
final reviewers with different lenses, paid for by mid-tier per-task review of clean tasks. Schedule
independent verification (oracles, extra differential legs) early, while the code is still in flux.

## 5. Budget the implementer's context (REFERENCE §5)

Cost is turns × context per turn; reviews are cheap, implementers are not.
- Briefs list every symbol as `identifier @ file`; implementers `rg -n` and read ~40–60-line windows,
  never a whole file over ~20k characters.
- Trim any AGENTS.md node whose hook-injected sections (Pitfalls/Checks/Patterns/Context) exceed
  ~3k characters before the slice edits under it.
- Mutation cycles ship as `papers/<plan>_mutations.json` (code that exists) and
  `papers/<plan>_mutations_post.json` (code a task adds), with `expect` strings copied from observed
  failures, run by `leanncd/scripts/mutation-manifest.sh`; nobody hand-writes a cycle during execution.
- The live plan holds only what execution needs (~800 lines); records go in `papers/<plan>_record.md`.
- Documentation sweeps are written as commands; they don't get a heavyweight dispatch.
- A task expected past ~60 implementer turns runs as two dispatches (production commit, then
  fixtures + cycles) using `split-handoff-template.md`.

## 6. Budget the authoring itself

F32-D's authoring cost ~73M against F32-B's ~77M because §5 only covered implementers. Its drafter ran
145 turns to a 441k context: exploring took it to 206k (6.4M), prototyping to 334k (16.2M), and
writing the plan, manifest, record and verify script (turns 109–127) and re-running the checks cost
another 16.0M at 335–441k, carrying every exploration read and build log it no longer needed.
- **Two authoring dispatches, not one.** (a) Explore and prototype: apply the slice to real-split
  copies (or a scratch branch), compile, run every fixture and cycle, record observed values. (b) A
  fresh dispatch writes the plan from those artifacts only. Estimated saving: ~30% of the drafter.
- **Ship the prototype as per-task patches** (`git apply` in task order), generated mechanically from
  the text that compiled — F32-D's `papers/f32d_files/rv_build.py --emit-patches` is the pattern.
  The plan then holds rationale, decisions, the §2 audit, fixtures, and prose edits, not transcribed
  code; the "does this paste into the real module" review lens mostly disappears.
- **Prototype on the real module split and namespace**, not renamed concatenated copies, so no
  fidelity check is needed.
- **Brief with numbers**: window size in lines, the functions to open, the facts already measured.
  "Keep reads small" was ignored; 190–290-line windows were used.
- **Reviewers append findings to a file as they go**, and check usage headroom before a parallel
  launch: two reviewers stopped at a session-limit pause lost 7.6M with nothing kept.
- **One fix dispatch per finding group**, each given only its plan sections, not one dispatch with
  sub-commits: F32-D's fixer ran 99 turns re-reading the whole plan for 14 groups.
- What worked, keep it: a controller brief carrying measured facts (draft 38M vs 50M), two parallel
  review lenses (3–6M each, one found the Critical), and a small verification round aimed only at
  the fixes (2M).
- `python3 .claude/skills/slice-plan/token-report.py <session-id>` measures all of this; CLAUDE.md
  Rule 6's dispatch budget applies to authoring dispatches too.

## Authoring checklist

- [ ] Every Lean block compiled via `check-snippet.sh` (fragments concatenated
      with their dependencies).
- [ ] Every Lean block that was reformatted, inlined, or otherwise edited
      *after* its drafting agent's own verification — including during final
      assembly into one document — re-verified in its post-edit form, not
      assumed safe because the pre-edit version compiled.
- [ ] Every asserted fixture value observed from a real run, not hand-derived.
- [ ] Every regression/parity fixture mutation-tested, with both observations
      recorded in the plan.
- [ ] For every requirement about an index, locator, check order, or diagnostic
      payload: the plan names a fixture that could FAIL if it were violated, and
      that fixture's construction actually distinguishes the two readings (the
      common trap is a fixture in which both readings coincide, so it pins
      nothing). Order claims need a fixture violating both conditions at once.
- [ ] Every claim in the plan's prose or a completion-record template it produces
      — "X reuses Y," "no second Z was added," "both are reachable from W" —
      checked against the actual functions/files, not asserted from the plan's
      own design intent.
- [ ] Every file path the plan names verified with `ls`, and each task's Files
      list derived from where its deliverable must live rather than from memory.
- [ ] Every "known gap" inherited from a previous slice's completion record
      re-derived against the tree before being restated. A gap list reads as
      settled fact and is aimed at by none of the usual safeguards, so an entry
      the previous slice closed will otherwise propagate indefinitely.
- [ ] For any slice that moves a capability boundary: before its documentation
      sweep is declared complete, value-grep the whole repo for the numbers that
      moved (`9 accepted`, `accepted == 9`, …) — the stale values, not the
      surrounding vocabulary — so a stale claim in a document not in the edit set
      is caught. A re-read covers only documents already opened and a marker-`rg`
      audit only vocabulary you thought to list; both miss a document nobody reopened.
- [ ] No `File.lean:NNN` line numbers in any text the plan tells a task to ship
      (completion records, AGENTS.md rows, design-doc edits) — identifiers only,
      since a later code commit in the same slice invalidates line numbers.
- [ ] For any task fixing instance _N_ of a known recurring defect family: the
      plan names the sibling functions a diff review cannot see, and requires the
      case × class table (required / forbidden / **silently ignored**) as a
      deliverable of that task. Every silently-ignored cell is a candidate
      instance _N+1_.
- [ ] Every required fixture names its donor — `clone <existing fixture>, change
      <one field>` — rather than leaving the implementer to rediscover it.
- [ ] Task boundaries pass the reviewer test above; tiny pure-addition tasks
      merged into neighbours.
- [ ] Each task's risk entry states its fixture and mutation-cycle count, not
      just its production-line count — that count, not the diff size, is what
      the task will actually cost.
- [ ] Global Constraints state exact values, and name anything the plan
      deliberately does *not* do (and which later slice owns it).
- [ ] If this slice introduces a new subsystem or file tree, the plan makes it
      *discoverable*, not just correct: reachable from a plain top-level import
      a new reader would already use, and mentioned in the AGENTS.md a reader
      would already open. Wave C's C0-C4 shipped 10 files and a working
      compiler that `import LeanNCD` couldn't reach and neither AGENTS.md
      mentioned — invisible until a later audit slice (C6) fixed it. Don't
      defer this to "someone will notice eventually."
- [ ] Every task's brief lists the symbols it touches as `identifier @ file` (plus a
      "window-read, don't whole-file-read" instruction) so the implementer doesn't re-grep for
      what the author already found.
- [ ] Every AGENTS.md node covering files the slice edits injects ≤ ~3k characters of
      Pitfalls/Checks/Patterns/Context per edit; trim it before execution if not (§5).
- [ ] Mutation cycles are in `papers/<plan>_mutations.json` with `expect` strings copied from
      observed failures, and `mutation-manifest.sh --check` passes on it.
- [ ] Close-out and authoring-verification records go in `papers/<plan>_record.md`, not the live
      plan; the live plan is ≤ ~800 lines.
- [ ] Documentation-sweep steps are written as commands (value-grep, counts, `--out` results
      table), and the docs work is not a heavyweight dispatch of its own.
- [ ] Any task expected to exceed ~60 implementer turns is marked for a two-dispatch split
      (production commit, then fixtures + cycles via `split-handoff-template.md`), with its
      phase-2 `identifier @ file` list written out.

- [ ] Authoring ran as two dispatches (prototype/verify, then write-up from artifacts), and the
      verified code ships as per-task patches that `git apply` cleanly in order onto the base.
- [ ] Reviewer and fixer briefs give window sizes and the exact functions/sections to open;
      reviewers write findings to a file incrementally; fixes are one dispatch per group.
