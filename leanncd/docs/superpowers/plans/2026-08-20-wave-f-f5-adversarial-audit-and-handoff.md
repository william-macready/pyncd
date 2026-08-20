# Wave F — F5 Adversarial Audit and Handoff Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** F5 is not new architecture — it is an audit-and-consolidate pass over F0-F4's already-shipped
checked-scan work (`papers/wave_f_scanplan_proposal.md` §13's F5 entry), closing the gaps a real audit
finds, and publishing one concise reference (a capability manifest, the Wave F analogue of C6's
`papers/wave_c_capability_manifest.md`) so Wave G can build on the checked-scan API without re-deriving
what it supports from source. This is the last slice of Wave F and the last step of thread 3 in
`papers/jax_evalplan_architecture.md`'s Part III table. Nothing here is speculative: every fix in
Task 1/2 closes a specific, cited gap F4's own completion record already named as a deliberate,
unfixed follow-up (`papers/wave_f_scanplan_proposal.md` lines 1843-1914); nothing is added "for
completeness" beyond what that record and this plan's own audit found.

**Architecture:** F5 of `papers/wave_f_scanplan_proposal.md` §13, the final slice of Wave F — F0-F4 are
landed (F4 completion record, same file, 2026-08-19). Its own Gate ("Laws 1, 2, 4, and the general
side of Law 5 hold; Wave G can consume checked scan APIs without importing source compilation or
legacy execution") should be read against what this plan's own audit found about that second clause:
**`import LeanNCD` already transitively imports the source scan compiler** (`Compile.lean`, hence
`ScanCompileError`, the DSL pipeline, `DSL.Pipeline.Lowering`), so the Gate can only be satisfied by a
consumer importing a narrow `Eval.Plan.*` leaf directly (e.g. `Eval.Plan.EvalPlan`/`Eval.Plan.Scan`),
exactly as Wave C's C6 gate was satisfied by `Plan.Check`/`Plan.Dense` rather than `import LeanNCD`
(`papers/wave_c_capability_manifest.md` §6, "Which import to use"). This plan's capability manifest
(Task 4) states this explicitly rather than letting Wave G rediscover it. Specialized PyTorch/JAX scan
lowerings remain a later wave (§13's F5 entry says so directly) — out of scope here.

## 0. Session verification record (2026-08-20)

This plan's Task 1 fixes and Task 2's new fixture were verified by actually applying them to the real
tree, running the affected builds, and reverting (via `git stash`, not `git checkout`, since this
worktree's guardrail hook blocks destructive checkout) before writing this document — not asserted
from reading the code alone:

- **The three payload fixes in Task 1** (`ScanPlanError.causalityFailure` gains the discarded loop
  index; `ScanCompileError.duplicateAxisInLhs` gains `isBase`; `ScanCompileError.blockReadNotAvailable`
  gains a `ReadUnavailableCause` discriminant) were applied together with every existing call site and
  fixture they touch, and `cd leanncd && lake build` ran **green at 8,652 jobs** — identical to the F4
  baseline, confirming these are pure signature refinements that add no new module and no new
  compilation unit.
- **The `blockReadNotAvailable` cause assignment was traced through the real control flow, not
  guessed:** `scratchOf` (`Compile.lean`'s recurrence-classification loop) is populated in one full
  pass over **all** of `recurParts` before the read-availability loop runs, so by the time a step
  statement `ri` checks a read, `scratchOf[rn]` already holds the producer index for every scratch
  name in the block — including names produced at or after `ri`. The existing `unless producer < ri`
  guard therefore already conflates two distinct causes (`producer == ri`, a genuine self-read, and
  `producer > ri`, a forward reference to a not-yet-computed value) in addition to the separately
  reachable "name resolves to nothing at all" case. All three are real and already reachable — this
  plan's fix classifies them, not invents new rejections.
- **The two existing step-block fixtures already exercise the two distinct step-side causes**: the
  "forward scratch read" fixture (statement 0 reads `T`, produced by statement 1) and the "reads
  ITSELF" fixture (statement 0's own RHS reads `T`) were, before this fix, asserted to the same
  `blockReadNotAvailable "sc" false 0 "T"` value — exactly the F4 record's complaint. After the fix
  they assert `.forwardReference` and `.selfRead` respectively, verified against the real build, not
  hand-derived.
- **The `partialAdvancingResult` degenerate sub-case fixture in Task 2** (a state result advancing the
  right NUMBER of context axes but the wrong SET) was constructed against the existing two-axis
  playground (`rej2Sched`/`okBase2`, `test/Eval/Plan/ScanCompileTest.lean`), built, and run for real:
  `causeOf (prepareEvalPlan partialSetSched rej2Sig) == some (.scan (.partialAdvancingResult "sc2" "dp"
  0 2 2))`, confirmed by a green `lake build Eval.Plan.ScanCompileTest`, then reverted.
- **Not independently re-verified this session:** the `scanFeatures` "extent one" tightening, the
  `advScratch` coverage assertion, and the `scanCorpusSplit` double-computation cleanup (Task 2) are
  specified precisely below (exact donor code, exact predicate) but were not round-tripped through a
  real build by this plan's author, since they are small, low-risk, test-file-only edits with an
  existing green baseline either side. Per this repo's own `verify-before-claiming-code-state`
  discipline, Task 2's implementer must still run `check-snippet.sh` or a real build before committing
  them, per the `slice-plan` skill's own rule — this note does not exempt that step.
- **The `DSL/AGENTS.md` import-direction finding (Task 3)** was confirmed by reading
  `LeanNCD/Eval/Plan/Compile.lean`'s import list directly (`import LeanNCD.DSL.Pipeline.Lowering`) and
  its real use (`idxToRow`, called inside `compileScan`) — not inferred from the doc's own claim.
- **The version-tag removal (Task 4)** was confirmed already complete: `RawEvalPlan`
  (`Graph.lean`) has no `version` field, `PlanError` has no `versionNotAdmitted` constructor, both
  removed in F3 per that slice's own plan. The one stale reference is
  `experiments/jax_bridge/EvalPlanCodegen.lean`'s non-default `JaxExperiment` target, already known
  broken (F4 record) and out of scope here.
- **8,652 is the current full-build baseline** (this session's own `lake build`, matching F4's
  recorded count), used below as the pre-F5 reference job count.

## Global Constraints

- **This slice adds one new file** (`papers/wave_f_capability_manifest.md`, Task 4) and otherwise only
  extends already-registered test modules and documentation. No new `lakefile.toml` entry, no new
  production `.lean` file.
- **Job count should not change from the 8,652 baseline**, per the same reasoning as C6's Global
  Constraints: Task 1's signature changes and Task 2's new fixtures extend already-compiled modules;
  nothing here adds a module to the `Tests` library's globs. If the observed count differs, explain
  why rather than asserting the expected number blindly.
- **Every new/changed `ScanPlanError`/`ScanCompileError` constructor payload must be re-asserted at
  every existing call site**, not just the one this plan names — Task 1's own audit already found and
  fixed every site for its three targets (verified above); the "Instructions" checklist below is the
  mechanism for any that later fixes (Task 2) might touch.
- **No new `String`/`unsupported` escape hatch** on either error family — every new field is a closed
  inductive (`ReadUnavailableCause`) or an existing `Bool`/`Nat`/`UID`, matching this repo's own
  discipline (`papers/wave_f_scanplan_proposal.md` §7.5's "no `unsupportedScan : String` escape
  hatch").
- **`ReadUnavailableCause` lives in `Error.lean`, immediately before `ScanCompileError`** — Lean 4 doc
  comments (`/-- ... -/`) attach to the very next command; inserting one declaration's doc comment
  between another declaration's own doc comment and that declaration is a parse error (`unexpected
  token '/--'`), confirmed by this plan's own authoring (see §0). Declare `ReadUnavailableCause` and
  its doc comment as a whole new declaration BEFORE `ScanCompileError`'s existing doc comment begins,
  never between it and `inductive ScanCompileError`.
- Invoke lake via Elan, from `leanncd/`: `cd leanncd && "$HOME/.elan/bin/lake" build`. Not on `PATH`.
- No `sorry`.

## Verified facts (established by this plan's own audit — do not re-litigate)

| Claim | How it was verified |
|---|---|
| `causalityFailure`'s `factorIndex` discards its enclosing loop's assignment index (`ai`, `Scan.lean`'s causality loop over `raw.stepBlock.assignments`) — a real, already-reachable gap, now fixed in Task 1 | read the loop directly; confirmed the sibling `ScanCompileError.stateReadNotCausal` already carries the analogous `stmtIndex` and `causalityFailure` alone lacked it |
| `duplicateAxisInLhs` lacks the `isBase` flag every sibling two-block constructor carries (`advancingAxisNotInLhs` has it) — two ScanCompileTest.lean fixtures (one base, one step) already assert byte-identical payloads as a result | read `Error.lean`'s full `ScanCompileError` declaration and both call sites in `Compile.lean` |
| `blockReadNotAvailable` collapses three distinct causes (`unknownName`, `forwardReference`, `selfRead`) into one payload discriminated only by `isBase` — confirmed reachable via the existing "forward scratch read" and "reads ITSELF" fixtures, which assert identical values today | traced `scratchOf`'s population order against its one read site; both existing fixtures rebuilt with the fix and produced the two distinct values expected |
| The `partialAdvancingResult` degenerate sub-case (right count, wrong set) has **zero existing fixture** and is real and reachable via the two-axis playground | built and ran `partialSetSched` against `rej2Sig`; got `.partialAdvancingResult "sc2" "dp" 0 2 2`, not a rejection at an earlier phase |
| The wrong-arity-read gap F4's own record described (`invalidPlan` instead of a source diagnostic) is confirmed **unreachable from real source** — `checkReadRanks` runs pre-grouping, before `finalizeScans` ever splits a scan's statements out — so it needs no fix here, only the record's own "unreachable, not a live gap" conclusion carried into the capability manifest | re-read `DSL/Compile.lean:37`'s phase order and `DSL/Pipeline/Structural.lean`'s `checkReadRanks`, confirmed against the F4 record's own re-derivation |
| `checkScanPlan` never validates a state destination slot's dtype — confirmed cosmetic/contained (a non-`f64` source is separately rejected by `checkAssign`, and a captured state's dtype is separately checked by `captureSignatureMismatch`) per F4's own record; **not fixed here**, recorded in the capability manifest as a named, deliberately-not-closed gap, not re-litigated | re-read the F4 record's own reasoning; not independently re-derived this session beyond confirming the record's citations still match the current file |
| `import LeanNCD` already transitively imports the source scan compiler (`Compile.lean`, hence `ScanCompileError`, `DSL.Pipeline.Lowering`) via `Adapter.lean` → `Compile.lean` — a plain `import LeanNCD` consumer cannot get checked-scan-only access without importing a narrower leaf directly | read `LeanNCD.lean`'s full import list and `Adapter.lean`/`Compile.lean`'s own import lines |
| `LeanNCD/DSL/AGENTS.md`'s "Key Relationships" paragraph states "`Eval/*` ... never `Pipeline.Structural`/`Lowering` directly" — **false** as of F4: `Eval/Plan/Compile.lean` imports `Pipeline.Lowering` directly and uses `idxToRow` inside `compileScan`, a real, undocumented cross-layer exception | read `Compile.lean`'s import list and confirmed the real call site of `idxToRow` inside `compileScan` |
| `LeanNCD/Eval/AGENTS.md`'s `Plan/` discoverability documentation (file table, parity matrix, independent-oracle row) is already current as of F4 — this is NOT a gap F5 must close, only re-confirm | read the file directly; its `Plan/` file table already lists all 16 files including `Block`/`RawStep`/`Scan`/`EvalPlan`, and the parity matrix already has 8 points plus the independent-oracle row F4's own record claims to have added |
| `RawEvalPlan.version`/`admittedVersion`/`PlanError.versionNotAdmitted` are already removed (F3) — `papers/wave_c_capability_manifest.md` §1 is the one stale reference left, since it still describes the now-deleted mechanism | read `Graph.lean`'s `RawEvalPlan` fields and `PlanError`'s full constructor list directly; grepped for `versionNotAdmitted`/`admittedVersion` outside the non-default `experiments/jax_bridge/` tree — zero matches |
| The full default `lake build` is green at **8,652 jobs** on this branch today, unchanged since F4 | this session's own full build (§0) |

---

## File Structure

- **Modify:** `leanncd/LeanNCD/Eval/Plan/Scan.lean` — `causalityFailure` signature + throw site (Task 1).
- **Modify:** `leanncd/LeanNCD/Eval/Plan/Error.lean` — `duplicateAxisInLhs`/`blockReadNotAvailable`
  signatures, new `ReadUnavailableCause` (Task 1).
- **Modify:** `leanncd/LeanNCD/Eval/Plan/Compile.lean` — the three call sites the above touch (Task 1).
- **Modify:** `leanncd/test/Eval/Plan/ScanTest.lean` — two `causalityFailure` assertions (Task 1).
- **Modify:** `leanncd/test/Eval/Plan/ScanCompileTest.lean` — six existing assertions (two
  `duplicateAxisInLhs`, four `blockReadNotAvailable`) plus one new fixture (`partialAdvancingResult`
  degenerate case) (Task 1, Task 2).
- **Modify:** `leanncd/test/Eval/Plan/DifferentialTest.lean` — `scanFeatures`'s "extent one" tightening,
  `scanCorpusSplit`'s double-computation cleanup (Task 2).
- **Modify:** `leanncd/test/Eval/PropertyOracle/ScanOracle.lean` (or wherever the two-way sweep over
  generated cases lives — confirm exact file before editing) — an `advScratch` coverage assertion
  (Task 2).
- **Modify:** `leanncd/LeanNCD/DSL/AGENTS.md` — correct the stale import-direction sentence (Task 3).
- **Create:** `papers/wave_f_capability_manifest.md` (Task 4).
- **Modify:** `papers/wave_c_capability_manifest.md` — correct the stale version-tag section, add a
  cross-reference to the new Wave F manifest (Task 4).
- **Modify:** `leanncd/LeanNCD/Eval/AGENTS.md` — one-line pointer update to the new manifest (Task 4).
- **Modify:** `papers/wave_f_scanplan_proposal.md` — append an F5 completion record under §13 (Task 4).

**Task count note:** four tasks. Task 1 (production payload fixes) and Task 2 (test-only mutation-
matrix closures) are split because Task 1 touches shared error types with call sites outside test
files — a real blast radius a reviewer could reject independently of Task 2's test-file-only additions,
per the `slice-plan` skill's reviewer test. Task 3 (import audit + discoverability) is small and
mechanical but a different kind of scrutiny (doc-accuracy, not code-behavior) than either. Task 4
(capability manifest, generator-coverage write-up, final gate, completion record) is the whole-branch
audit and publication step this plan's own final review belongs to — do not skip or merge it away.

---

### Task 1: Sharpen three under-specified error payloads

**Files:**
- Modify: `leanncd/LeanNCD/Eval/Plan/Scan.lean`
- Modify: `leanncd/LeanNCD/Eval/Plan/Error.lean`
- Modify: `leanncd/LeanNCD/Eval/Plan/Compile.lean`
- Modify: `leanncd/test/Eval/Plan/ScanTest.lean`
- Modify: `leanncd/test/Eval/Plan/ScanCompileTest.lean`

**Interfaces:** none new beyond the three signature changes below — every call site of the three
touched constructors is enumerated here and must be updated; there are no others (confirmed by a
repo-wide grep in §0).

Every snippet below was compiled against the real tree this session (§0) — transcribe verbatim.

- [ ] **Step 1: `ScanPlanError.causalityFailure` — carry the discarded loop index**

In `Scan.lean`, change:

```lean
  | causalityFailure              (stateIndex termIndex factorIndex : Nat)  -- Task 2
```

to:

```lean
  | causalityFailure              (stateIndex stmtIndex termIndex factorIndex : Nat)  -- Task 2
```

(the trailing `-- Task 2` comment is pre-existing, referring to Wave F's own F3 Task 2 — leave it
unchanged.) And its one throw site — inside the causality loop that iterates `ai` over
`raw.stepBlock.assignments`:

```lean
            unless stateReadCausal st.advancingDims t.contextPos f do
              throw (.causalityFailure si ai ti fi)
```

(previously `.causalityFailure si ti fi`, dropping `ai`).

In `test/Eval/Plan/ScanTest.lean`, both existing causality-rejection fixtures (the constant-read and
look-ahead-read cases, each a single-assignment step block, so `ai = 0`) change from:

```lean
  | .error e => unless e == .causalityFailure 0 0 0 do
```

to:

```lean
  | .error e => unless e == .causalityFailure 0 0 0 0 do
```

(verified against a real run — both fixtures still fail with `stateIndex = 0`, and the new leading
zero is the assignment index of the block's own single step assignment).

- [ ] **Step 2: `ScanCompileError.duplicateAxisInLhs` — carry `isBase`**

In `Error.lean`, change:

```lean
  | duplicateAxisInLhs       (scan name : String) (stmtIndex : Nat) (uid : UID)
```

to:

```lean
  | duplicateAxisInLhs       (scan name : String) (isBase : Bool) (stmtIndex : Nat) (uid : UID)
```

(matching `advancingAxisNotInLhs`'s existing field order exactly.) In `Compile.lean`, its two call
sites — one in the base-statement loop, one in the recurrence-statement loop:

```lean
    match firstDuplicateUID (slotAxes.map (·.uid)) with
    | some u => throw (scanErr warnings (.duplicateAxisInLhs scanName nm true bi u))
```

(base block, was `.duplicateAxisInLhs scanName nm bi u`) and:

```lean
    match firstDuplicateUID (slotAxes.map (·.uid)) with
    | some u => throw (scanErr warnings (.duplicateAxisInLhs scanName nm false ri u))
```

(recurrence/step block, same prior text).

In `test/Eval/Plan/ScanCompileTest.lean`, the two existing fixtures — a base statement pinning and
freeing the same axis, and a step result advancing the same axis twice — change from:

```lean
  == some (.scan (.duplicateAxisInLhs "sc" "S" 0 axL.uid))
```
```lean
  == some (.scan (.duplicateAxisInLhs "sc" "S" 0 axL.uid))
```

to:

```lean
  == some (.scan (.duplicateAxisInLhs "sc" "S" true 0 axL.uid))
```
```lean
  == some (.scan (.duplicateAxisInLhs "sc" "S" false 0 axL.uid))
```

respectively (first fixture is the base-block one, second is the step-block one — confirmed by which
`rej [..] [..]` argument position each's mutated statement sits in).

- [ ] **Step 3: `ScanCompileError.blockReadNotAvailable` — discriminate the real cause**

In `Error.lean`, declare a new closed cause type **immediately before `ScanCompileError`'s own doc
comment begins** (see Global Constraints — do not place it between that doc comment and
`inductive ScanCompileError`):

```lean
/-- Why `blockReadNotAvailable` rejected a name: it never resolves to a state, a block-local
    scratch producer, or an outer/external tensor at all (`unknownName`); it resolves to a scratch
    name whose one producing statement comes strictly LATER in source order (`forwardReference`);
    or it resolves to the very statement that is itself about to produce it (`selfRead`, the
    `producer == stmtIndex` edge of the same check). Base blocks have no block-local scratch
    (§4.2/§8.4), so every base-side `blockReadNotAvailable` is `unknownName`. -/
inductive ReadUnavailableCause
  | unknownName
  | forwardReference
  | selfRead
  deriving DecidableEq, BEq, Repr, Inhabited
```

Then change `blockReadNotAvailable`'s own line:

```lean
  | blockReadNotAvailable    (scan : String) (isBase : Bool) (stmtIndex : Nat) (name : String)
                             (cause : ReadUnavailableCause)
```

(previously ending at `(name : String)`, no trailing field). In `Compile.lean`, its three call sites:

the base-block unknown-name site (base blocks have no scratch, so this is always `.unknownName`):

```lean
      | none => throw (scanErr warnings (.blockReadNotAvailable scanName true bi rn .unknownName))
```

the step-block "producer not yet available" site — split by whether the producer IS the current
statement (`selfRead`) or comes strictly later (`forwardReference`):

```lean
          | some producer =>
              unless producer < ri do
                throw (scanErr warnings (.blockReadNotAvailable scanName false ri rn
                  (if producer == ri then .selfRead else .forwardReference)))
```

and the step-block genuinely-unknown-name site:

```lean
          | none =>
              match slotOf[rn]? with
              | none => throw (scanErr warnings (.blockReadNotAvailable scanName false ri rn .unknownName))
```

In `test/Eval/Plan/ScanCompileTest.lean`, four existing fixtures change. The "forward scratch read"
fixture (statement 0 reads `T`, produced by statement 1 — a genuine forward reference):

```lean
  == some (.scan (.blockReadNotAvailable "sc" false 0 "T" .forwardReference))
```

the base-block unknown-name fixture:

```lean
  == some (.scan (.blockReadNotAvailable "sc" true 0 "NOPE" .unknownName))
```

the "reads ITSELF" fixture (statement 0's own RHS reads the name it itself produces — a genuine
self-read):

```lean
  == some (.scan (.blockReadNotAvailable "sc" false 0 "T" .selfRead))
```

and the step-block unknown-name fixture:

```lean
  == some (.scan (.blockReadNotAvailable "sc" false 0 "NOPE" .unknownName))
```

(each replacing its prior four-argument form, in the same order the fixtures already appear in the
file — do not reorder them; only append the new final argument to each).

- [ ] **Step 4: Verify and commit**

```bash
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.ScanTest Eval.Plan.ScanCompileTest
```

Expected: both build green (verified this session — see §0). Then a full build:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Expected: `Build completed successfully (8652 jobs)` — unchanged from the pre-F5 baseline (§0). If the
count differs, explain why rather than asserting the expected number blindly.

```bash
git add leanncd/LeanNCD/Eval/Plan/Scan.lean leanncd/LeanNCD/Eval/Plan/Error.lean \
        leanncd/LeanNCD/Eval/Plan/Compile.lean leanncd/test/Eval/Plan/ScanTest.lean \
        leanncd/test/Eval/Plan/ScanCompileTest.lean
git commit -m "fix(leanncd): sharpen three under-specified scan error payloads (Wave F F5, part 1)

- causalityFailure now carries the step-block assignment index it was
  silently discarding, matching stateReadNotCausal's sibling shape
- duplicateAxisInLhs now carries isBase, matching advancingAxisNotInLhs;
  two existing fixtures that asserted byte-identical payloads for a base-
  block vs a step-block defect now assert distinct values
- blockReadNotAvailable now carries a ReadUnavailableCause discriminant
  (unknownName / forwardReference / selfRead); scratchOf's population
  order confirms forwardReference and selfRead are both genuinely
  reachable, not merely theoretical
"
```

---

### Task 2: Close the remaining named mutation-matrix gaps

**Files:**
- Modify: `leanncd/test/Eval/Plan/ScanCompileTest.lean`
- Modify: `leanncd/test/Eval/Plan/DifferentialTest.lean`
- Modify: `leanncd/test/Eval/PropertyOracle/ScanOracle.lean` (confirm exact file before editing — see
  Step 3)

**Interfaces:** none new — every addition below tests an existing predicate/function or tightens an
existing test-support predicate. Independently rejectable from Task 1: these are test-file-only edits
with no shared-type call-site ripple.

- [ ] **Step 1: `partialAdvancingResult`'s degenerate sub-case — add the missing fixture**

In `test/Eval/Plan/ScanCompileTest.lean`, alongside the existing two-axis playground
(`rej2Sched`/`rej2Sig`/`okBase2`/`okRecur2`), donor: clone `rej2Sched`'s shape, add `axJ` (already
declared in the file, uid 13, used elsewhere as a size-2 `.axis`) to `decls`/`explicitSizes`, and
replace `okRecur2`'s second `.iterNext axC` with `.iterNext axJ` — a result that advances the RIGHT
NUMBER of axes (2, matching `numAxes = 2`) but the WRONG SET (`{axR, axJ}` instead of `{axR, axC}`):

```lean
def partialSetSched : ScheduledProgram :=
  { decls := [.iter axR 3, .iter axC 3, .axis axJ (some 2)]
  , stmts := [.scan "sc2" [axR, axC]
      [okBase2]
      [.assign "dp" [.iterNext axR, .iterNext axJ]
        { body := { terms := [{ factors := [.read "dp" [.axis axR, .axis axC]] }] }
        , nonlin := .identity }] false]
  , env := {}, extNames := insert "ROW" (∅ : Finset String)
  , explicitSizes :=
      (((({} : HashMap UID Nat).insert axR.uid 3).insert axC.uid 3).insert axJ.uid 2) }

#guard causeOf (prepareEvalPlan partialSetSched rej2Sig)
  == some (.scan (.partialAdvancingResult "sc2" "dp" 0 2 2))
```

Verified this session (§0): compiles and the `#guard` passes against the real compiler — `declared =
2` and `expected = 2` are equal (both counts agree; only the SET disagrees), which is exactly the
degenerate sub-case F4's own record named as uncovered. Add this fixture inside the existing `### 2.1`
partial-advancing-result section (after the file's existing `partialAdvancingResult "sc" "S" 0 2 1`
fixture), not as a new top-level section.

```bash
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.ScanCompileTest
```

Expected: PASS.

- [ ] **Step 2: `scanFeatures`'s "extent one" predicate — require the extent-one axis to be a scan
      axis, not merely declared**

In `test/Eval/Plan/DifferentialTest.lean`, the current predicate (`scanFeatures`'s `"extent one"`
entry) only checks that the schedule declares SOME `.iter _ 1` anywhere, not that the axis so declared
is one the scan itself advances over:

```lean
  , ("extent one", fun s => s.decls.any (fun d => match d with
        | .iter _ 1 => true
        | _ => false))
```

Tighten it to require the extent-one axis to be a member of some scan node's own `axes` list (using
the file's existing `scanNodesOf` helper, already used by every other row in this table):

```lean
  , ("extent one", fun s => (scanNodesOf s).any (fun (axes, _, _) =>
        s.decls.any (fun d => match d with
          | .iter a 1 => axes.any (fun x => x.uid == a.uid)
          | _ => false)))
```

The existing `extentOneSched` fixture (per F4's own record, "declares exactly one iter axis, of extent
1") must still satisfy this — that axis IS the scan's own advancing axis, so no regression is expected,
but confirm with a real build rather than assuming it (this predicate change was specified, not
round-tripped through a build, this session — see §0).

```bash
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest
```

Expected: PASS, in particular the file's own `run_cmd` coverage-gap guard over `scanFeatures` (which
fails loudly if no gated fixture exhibits a feature) must still pass for "extent one" specifically —
if it does not, `extentOneSched`'s extent-one axis is not actually one of its own scan's advancing
axes, which would itself be a second, more interesting finding to report rather than paper over.

- [ ] **Step 3: `advScratch` coverage — add an explicit assertion**

Locate the exact file and structure of the two-way sweep over `enumScanCases`/`ScanGen.lean`'s
generated corpus (the F4 record names `ScanOracle.lean` as running "the two-way law ... over all
seventeen generated cases, including the eight F4 rejects" — confirm this is still the right file
before editing, since this plan's author did not independently re-verify its exact structure this
session). Per the F4 record, `advScratch` (`test/Eval/PropertyOracle/ScanUnroll.lean`'s `ScanGeom`
field, "the `%nl` shape `splitNonlins` manufactures for a nonlinear recurrence") is populated only by
the four `relu`-template generated cases, and nothing asserts its presence the way `scanFeatures`
asserts coverage of every OTHER named shape.

Add a coverage assertion in the same spirit as `DifferentialTest.lean`'s existing `scanFeatures`
loop (`run_cmd`, fails loudly if the corpus stops producing the shape): assert that at least one of
the generated/gated scan cases actually produces a non-empty `ScanGeom.advScratch` list after
unrolling. The exact predicate depends on `ScanOracle.lean`'s real API surface (whether the built
`ScanGeom` values are directly inspectable at the point the two-way sweep runs, or need a small
accessor) — read the file first, then add the narrowest assertion that fails if no case in the swept
corpus ever populates `advScratch`, mirroring `scanFeatures`'s "THREE-WAY GATE COVERAGE GAP"-style
`throwError` message so a future template change that silently drops `relu` cases is caught here
instead of discovered by a later audit.

```bash
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.PropertyOracle.ScanOracle
```

(module name may differ from this guess — use whatever `lakefile.toml` actually registers; confirm
before running.) Expected: PASS.

- [ ] **Step 4: `scanCorpusSplit`'s double computation — dedup**

In `test/Eval/Plan/DifferentialTest.lean`, `scanCorpusSplit` (the full 17-case execution matrix) is
currently computed twice — once for a `dbg_trace` diagnostic, once for the pinned `#guard` — re-running
every case's `scanParityCheck` a second time for no functional benefit (a cheap, purely mechanical
cleanup the F4 record names as a known follow-up, not a defect). Merge the two call sites into the one
existing `run_cmd` block, replacing the separate trailing `#guard`:

```lean
run_cmd do
  match scanCorpusSplit with
  | .error msg => throwError s!"SCAN CORPUS GATE FAILED:\n{msg}"
  | .ok (total, accepted, nonlin, agg) =>
      dbg_trace s!"DifferentialTest scan corpus: total={total} accepted={accepted} \
unsupportedNonlin={nonlin} unsupportedAgg={agg}"
      unless total == 17 && accepted == 9 && nonlin == 4 && agg == 4 do
        throwError s!"scan corpus split counts changed: total={total} accepted={accepted} \
nonlin={nonlin} agg={agg}"
```

removing the separate trailing `#guard match scanCorpusSplit with ...` block entirely (both the
`dbg_trace` diagnostic and the exact-count pin now share the one computed result). This is behaviorally
identical for CI purposes (`throwError` inside `run_cmd` fails the build exactly as a failing `#guard`
does) — not independently re-verified via a real build this session (see §0); the implementer must
build this file before committing.

```bash
cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.DifferentialTest
```

Expected: PASS, with the `dbg_trace` line still appearing exactly once in the build log (confirming
the computation now runs once, not twice).

- [ ] **Step 5: Verify and commit**

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Expected: `Build completed successfully (8652 jobs)` — unchanged (Steps 1-4 add fixtures/tighten
predicates in already-registered modules, no new module).

```bash
git add leanncd/test/Eval/Plan/ScanCompileTest.lean leanncd/test/Eval/Plan/DifferentialTest.lean \
        leanncd/test/Eval/PropertyOracle/ScanOracle.lean
git commit -m "test(leanncd): close Wave F F5's remaining named mutation-matrix gaps (part 2)

- Add a fixture for partialAdvancingResult's degenerate sub-case (right
  count, wrong set), previously untested anywhere
- Tighten scanFeatures' extent-one predicate to require the declared
  extent-one axis be one the scan itself advances over
- Add an explicit advScratch coverage assertion, previously implicit in
  which generated templates happen to exist
- Dedup scanCorpusSplit's double computation (diagnostic + guard now
  share one result)
"
```

---

### Task 3: Import-direction audit fix and discoverability re-confirmation

**Files:**
- Modify: `leanncd/LeanNCD/DSL/AGENTS.md`

**Interfaces:** none — documentation only.

- [ ] **Step 1: Correct the stale import-direction claim**

In `leanncd/LeanNCD/DSL/AGENTS.md`'s "Key Relationships" paragraph (under `## Code Map`), the closing
sentence currently reads:

> `Eval/*` imports `DSL.Ast`/`DSL.Compile`/`Pipeline.Types`/`TraverseAxes` but never
> `Pipeline.Structural`/`Lowering` directly.

This is false as of Wave F F4: `Eval/Plan/Compile.lean` imports `Pipeline.Lowering` directly and calls
its `idxToRow` inside `compileScan`, to lower a scan's affine reads the same way `Lowering.lean` itself
does. Replace that sentence with (matching the same paragraph's existing "one deliberate cross-layer
exception" style used for `Structural.lean`'s own reverse import a few sentences earlier):

```
`Eval/*` imports `DSL.Ast`/`DSL.Compile`/`Pipeline.Types`/`TraverseAxes` — with one exception:
`Eval/Plan/Compile.lean` (Wave F F4) also imports `Pipeline.Lowering` directly, reusing `idxToRow` to
lower a scan's affine reads exactly as `Lowering.lean` itself does. Every other `Eval/*` file still
never imports `Pipeline.Structural`/`Lowering`.
```

Do not otherwise edit this paragraph — the rest of its claims (the `Structural.lean:15` exception, the
`Bridge/*` import lines) were not challenged by this plan's audit and are out of scope.

- [ ] **Step 2: Re-confirm — do not re-author — `Eval/AGENTS.md`'s discoverability content**

Per this plan's own audit (§0's Verified facts), `leanncd/LeanNCD/Eval/AGENTS.md`'s `Plan/` file table,
parity matrix, and independent-oracle row are already current as of F4. Re-read the file and confirm
this is still true (no drift since F4's own doc commit); if it is, make NO edit here — Task 4 adds the
one new pointer line this plan actually needs (to the new capability manifest). If re-reading finds it
is NOT current (a real regression since F4), stop and report rather than silently patching scope this
plan did not budget for.

- [ ] **Step 3: Verify and commit**

```bash
cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD
```

Expected: green, unchanged job count (doc-only change).

```bash
git add leanncd/LeanNCD/DSL/AGENTS.md
git commit -m "docs(leanncd): correct DSL/AGENTS.md's stale Eval/* import-direction claim (Wave F F5, part 3)"
```

---

### Task 4: Capability manifest, final gate, and Wave F completion record

**Files:**
- Create: `papers/wave_f_capability_manifest.md`
- Modify: `papers/wave_c_capability_manifest.md`
- Modify: `leanncd/LeanNCD/Eval/AGENTS.md`
- Modify: `papers/wave_f_scanplan_proposal.md`

**Interfaces:** none — this task publishes documentation and runs the final build. This is the
whole-branch review the `slice-plan` skill calls "the one earning its keep" (per its own §4, every
prior Wave's most valuable finding came from exactly this tier) — do not skip or merge it away.

- [ ] **Step 1: Write `papers/wave_f_capability_manifest.md`**

A concise, standalone reference mirroring `papers/wave_c_capability_manifest.md`'s exact section
shape — not a design narrative (that's what `wave_f_scanplan_proposal.md` is for):

1. **Semantic and wire versions.** State that the in-memory version tag (`RawEvalPlan.version`,
   `admittedVersion`, `PlanError.versionNotAdmitted`) was removed in F3, not merely deferred — cite
   `wave_f_scanplan_proposal.md` §2.3's argument (adding `PlanStep.scan` changes the plan language's
   Lean type directly, which motivates removing the field rather than bumping it). Wire: still N/A,
   unchanged from Wave C (C5's canonical codec remains deferred).
2. **Accepted scan source constructs.** Restate proposal §5.1's admitted fragment as what is actually
   shipped and confirmed by the three-way differential gate: rectangular uniform n-dimensional scans,
   advancing dimensions in arbitrary tensor positions, coupled recurrences, external per-step reads,
   contractions inside a recurrence, deep constant look-back, block-local scratch, more than one scan
   axis, more than one scan per schedule, a plain statement consuming a published history — every base
   /step operation restricted to the checked Wave C local kernel (`f64`, real sum-product, identity
   nonlinearity, plain/affine reads, zero padding).
3. **Rejected scan source constructs.** All 24 `ScanCompileError` constructors plus the 2
   `CapabilityError` additions Wave F owns (`scanNode` has no producer left; `noAdvancingAxis` is new),
   organized by the same six categories `Error.lean`'s own doc comment already groups them into (state/
   base/result pairing; block dependency order; context axes and per-state geometry; base write
   placement; causality). Name the constructors this plan's own audit found under-specified before
   Task 1/2 (now closed) and the ones deliberately left as named, non-blocking gaps: the dtype check
   `checkScanPlan` never performs on a state destination slot (contained downstream — a non-`f64`
   source is separately rejected by `checkAssign`); the wrong-arity-read gap (confirmed unreachable
   from real source, per this plan's own audit); the independent oracle's `rewriteRead` performing no
   causality check of its own (not live — `compileScan`/F3 both reject a non-causal read first).
4. **Law 1 corpus coverage for scans.** The real, counted three-way differential gate result: 17
   generated cases (9 accepted / 4 `unsupportedNonlin` / 4 `unsupportedAgg`), 21 total programs
   (generated + hand-written) agreeing bit-for-bit across the compiled checked path, `evalScheduled`,
   and the independent scan-free unrolling — cite `DifferentialTest.lean`'s pinned counts and the F4
   completion record's structurally-derived feature table (deep look-back, coupled states, scratch,
   external reads, contraction, extent one, more than one scan axis, several base writes, a
   non-trailing advancing dimension, more than one scan, a plain consumer of a published history).
5. **Extension points**, stated as what's NOT yet supported and why, not as a roadmap commitment:
   reproduce proposal §1's "Functionality still missing after Wave F" table verbatim (pointwise/
   axiswise nonlinearities; masks/predicates/Boolean factors; unary factors; max/min aggregation;
   scatter/affine-LHS writes; non-`f64` dtypes and dynamic shapes; `.scanPre`/callbacks/nonlinear scan
   bodies; general n-dimensional recurrence geometry beyond the rectangular uniform fragment;
   multi-face full-boundary writes and genuinely overlapping writes; PyTorch/JAX execution and
   optimized `lax.scan`/compact-carry/wavefront/parallel-prefix lowering) so this backlog survives the
   handoff rather than disappearing once the proposal doc stops being the first thing a Wave G reader
   opens. State explicitly that the next semantic-expansion work is the named checked local-kernel
   capability wave proposal §1 describes, not chosen or ordered by Wave F.
6. **Audit findings confirmed clean**, mirroring C6's own closing section: the module import graph
   (state that `import LeanNCD` reaches the source scan compiler transitively, and that a checked-
   scan-only consumer must import a narrower `Eval.Plan.*` leaf directly — this is the concrete
   resolution of the Gate's "without importing source compilation" clause); the `DSL/AGENTS.md`
   correction from Task 3; a one-paragraph summary of the checker/error mutation-matrix work (Task 1/2
   closed three real gaps; the wrong-arity and dtype gaps are named, not fixed, for the reasons in
   point 3 above). End with a "Which import to use" paragraph exactly like C6's: `Eval.Plan.EvalPlan`/
   `Eval.Plan.Scan` for checked-scan execution with no source compilation; `Eval.Plan.Adapter` for the
   named source-to-plan boundary (pulls in `Compile.lean`); `import LeanNCD` pulls in everything,
   including the legacy evaluator and the full DSL pipeline.

- [ ] **Step 2: Correct `papers/wave_c_capability_manifest.md`'s stale version section**

In its `## 1. Semantic and wire versions` section, replace the now-false claim ("`checkPlan` rejects
any `RawEvalPlan.version` other than `1` with `PlanError.versionNotAdmitted`") with a note that this
mechanism was removed in Wave F F3 (`wave_f_scanplan_proposal.md` §2.3) once a stateful `PlanStep.scan`
constructor made bumping the field the wrong fix, and point to the new
`papers/wave_f_capability_manifest.md` for what replaced it (nothing — there is no version tag today).
Also add `papers/wave_f_capability_manifest.md` to the `Plan/` subtree's pointer sentence in
`leanncd/LeanNCD/Eval/AGENTS.md` (the sentence already reading "see `papers/wave_c_capability_manifest.md`
... and `papers/wave_f_scanplan_proposal.md` ... for the full designs" — add the new manifest
alongside them).

- [ ] **Step 3: Run the full build gate**

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Expected: `Build completed successfully (8652 jobs)` — unchanged from the pre-F5 baseline (§0), since
this slice adds no new module. Verify the arithmetic against what you actually observe.

- [ ] **Step 4: Whole-branch review**

Before committing, re-read every file this plan touched together against
`papers/wave_f_scanplan_proposal.md` §13's F5 entry and this plan's Global Constraints, specifically
checking:
- Every call site of `causalityFailure`/`duplicateAxisInLhs`/`blockReadNotAvailable` was updated — no
  stale four/three-argument construction survives anywhere (`grep -rn` for each constructor name
  across `leanncd/`, confirm every hit matches its new arity).
- No existing file outside this plan's own File Structure list was touched.
- The capability manifest's every numeric claim was counted from an actual run this task performed,
  not copied from this plan's own prose.

- [ ] **Step 5: Append an F5 completion record**

In `papers/wave_f_scanplan_proposal.md`, under the F5 entry in §13 (immediately after the existing F4
completion record), add a completion record matching the F0-F4 convention: concrete constructors
fixed, the exact fixture counts added, the exact `lake build` job count from Step 3, and Wave F's own
closing status against §14.1's Definition of Done (state which of its 11 items hold and cite the
manifest for the ones that hold only for the admitted fragment, not for the missing-capability table's
contents).

- [ ] **Step 6: Commit**

```bash
git add papers/wave_f_capability_manifest.md
git commit -m "docs(leanncd): publish the Wave F capability manifest (F5)"
git add papers/wave_c_capability_manifest.md leanncd/LeanNCD/Eval/AGENTS.md
git commit -m "docs(leanncd): cross-reference the Wave F capability manifest, correct the stale version-tag note"
git add papers/wave_f_scanplan_proposal.md
git commit -m "docs(leanncd): close Wave F F5 — Wave F complete"
```

**Gate:** Laws 1, 2, 4, and the general side of Law 5 hold for the admitted scan fragment (unchanged
by this slice — F5 audits, it does not alter checked semantics); Wave G can consume checked scan APIs
without importing source compilation or legacy execution, **by importing `Eval.Plan.EvalPlan`/
`Eval.Plan.Scan` directly rather than `import LeanNCD`** — the concrete resolution this plan's own
audit found necessary and the capability manifest now states explicitly.
