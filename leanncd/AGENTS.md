# AGENTS.md — leanncd

## Doing slice work here: two skills

Implementation slices (Wave C's C0/C1/C2…, and any other plan executed via
subagent-driven-development) have two mechanized steps. Use them rather than
redoing the setup by hand:

| When | Skill | What it covers |
|---|---|---|
| Writing the plan | `.claude/skills/slice-plan/` | task right-sizing; compiling plan code before it ships (`check-snippet.sh`) |
| Executing the plan | `.claude/skills/new-slice/` | worktree creation, stale-base fix, `.lake` sync, plan copy, ledger scaffold |

## Invoking Lake

From the repository root, invoke Lake through Elan from inside the Lean subproject:

```bash
cd leanncd && "$HOME/.elan/bin/lake" build
```

Do not assume `lake` is on `PATH`, and do not run it from the repository root: the Lake
configuration lives under `leanncd/`. Replace `build` with the desired target or Lake command.

**`lake env lean <file>` does not rebuild the file's dependencies — it only typechecks that one
file against whatever `.olean`s already exist.** If you edit module `A.lean` and then run
`lake env lean` on a file `B.lean` that imports `A`, `B` is checked against `A`'s STALE `.olean`
from before your edit — you can get a clean pass, or a failure that references A's old behavior,
either way silently wrong. Real incident: editing `Check.lean` to wrap an error constructor with
extra context, then running `lake env lean test/…/GraphCheckTest.lean` (which imports `Check.lean`)
showed the *old*, unwrapped error value on the first attempt — not because the test was wrong, but
because `Check.lean`'s `.olean` hadn't been refreshed yet. Fix: `lake build <TheModuleYouEdited>`
(e.g. `lake build LeanNCD.Eval.Plan.Check`) before `lake env lean`-checking anything that imports
it. When in doubt, `lake build` the whole project — the cost is proportional to what actually
changed, not a full rebuild, once `.lake` is already warm (see the cold-build note below).

## New worktree / fresh checkout: don't cold-build Mathlib

This project depends on Mathlib (thousands of files). A `lake build` from a
checkout that has never been built compiles Mathlib from source, which can
take several hours — even though `.lake/packages` (the source fetch) may
already be present, `.lake/build` (the compiled `.olean`s) starts empty.

**Do not do this by hand — run the script.** From inside a newly-created
worktree (after `EnterWorktree`, which the script cannot do for you):

```bash
bash .claude/skills/new-slice/prepare-worktree.sh --plan <plan-path>
```

It finds the fullest donor checkout, rsyncs its `.lake`, and then *verifies*
the result is ≥95% built before declaring the worktree ready — plus it
fast-forwards the branch to local `main` (see the stale-base trap below) and
scaffolds the SDD ledger. See `.claude/skills/new-slice/SKILL.md`.

If you ever do need to sync manually, the counts to compare are:

```bash
git worktree list   # candidate checkouts
find <candidate>/leanncd/.lake/packages/mathlib/.lake/build/lib -name "*.olean" | wc -l
find <candidate>/leanncd/.lake/packages/mathlib/Mathlib -name "*.lean" | wc -l  # total to compare against
rsync -a "<candidate>/leanncd/.lake/" "./leanncd/.lake/"
```

Note the source path is `.lake/packages/mathlib/Mathlib`, **not**
`leanncd/Mathlib` — the latter does not exist and silently counts 0, which
makes a completely unbuilt checkout look "complete" by comparison.

**Use plain `rsync -a`, not `--info=progress2` or other GNU-rsync-only flags.**
macOS ships `openrsync` (protocol 29) by default, not GNU rsync — passing a
flag it doesn't recognize causes it to print usage and silently copy nothing,
while still exiting 0. Check `rsync --version` if unsure; don't trust a
"completed, exit 0" report alone — verify the `.olean` count in the
destination afterward.

After syncing, run `cd leanncd && "$HOME/.elan/bin/lake" build` — it will only need to compile the
handful of `LeanNCD`-specific modules (and whatever the new worktree's edits
touch), typically well under a minute instead of hours.

## New worktree: the stale-base trap

`EnterWorktree` branches from `origin/<default-branch>`, **not** from local
`main`. This repo's local `main` routinely runs far ahead of `origin/main`
(21 commits at the time of writing), so a new worktree silently starts on
stale code — and every edit you make is against the wrong base.

This has been hit repeatedly and was always caught by eyeballing `git log`,
never by tooling. `prepare-worktree.sh` (above) now fast-forwards for you and
refuses to proceed if the branches have genuinely diverged. If you set a
worktree up by hand instead, check `git status -sb` / `git log --oneline -3`
against local `main` **before** making any edits.

## Intent Layer

> TL;DR: LeanNCD formalizes the category-theoretic core of pyncd (a "math tower": `St`/`Br` in
> `Base/`, meeting a computable pipeline: `DSL/` parses+routes, `Eval/` gives reference semantics,
> `Bridge/` proves the two agree, `Acset/` mirrors Python's CSV schema). Start at Entry Points,
> check Subsystems for deep dives.

## Purpose
Owns: the Lean 4 formal verification of pyncd's category-theoretic model (a separate lakefile/toolchain subproject within the pyncd repo, not a standalone git repo).
Does not own: the Python implementation (`../data_structure/`, `../acset/`, etc. at the pyncd root) — leanncd mirrors that design in Lean to prove properties about it, it does not execute or replace it.

## Code Map (subsystem-level — see each child AGENTS.md for file-level maps)

### Subsystems

| Area | Location | Description |
|------|----------|-------------|
| Math tower | `LeanNCD/Base/AGENTS.md` | `ColoredPROP`, `St` (affine morphisms), `Br` (free strict SMC), `SizeExpr` |
| DSL + routing | `LeanNCD/DSL/AGENTS.md` | `tl!{...}` parse/elaborate/compile/route pipeline (largest, most active subsystem) |
| Bridge | `LeanNCD/Bridge/AGENTS.md` | `realize`, acset codec + round-trip proofs, DSL/CSV agreement — highest-churn subsystem |
| Evaluation | `LeanNCD/Eval/AGENTS.md` | reference-semantics interpreter + the Portfolio test suite |
| Acset schema | `LeanNCD/Acset/AGENTS.md` | row-table schema + CSV text mechanics (mirrors Python `acset/`) |
| Algebra | `LeanNCD/Algebra/AGENTS.md` | algebra-functor signatures (`Algebra`/`TargetActegory`); deliberately no concrete instance yet |

Small subsystems (no dedicated node — each <170 lines, single-file or near it): `Core/` (`Graded.lean` — `sh_act`/DGraded machinery consumed by `Algebra`; `Weave.lean` — `weave_unique`, itself a deferred sorry), `Mixins/`, `Props/` (`Generic.lean`), `Seam/` (`Adapter.lean` — strictifies `ColoredPROP` onto Mathlib's `MonoidalCategory`/`SymmetricCategory`, fully sorry-free), `Grothendieck/`, `Exec/` (`Uid.lean` — `CompileError` variants), `Instances/` (`StBr.lean`).

### Downlinks

| Area | Node | What's There |
|------|------|--------------|
| Base | `LeanNCD/Base/AGENTS.md` | `brCancelPoint`/BrNF situation, St hexagon gap |
| DSL | `LeanNCD/DSL/AGENTS.md` | 8-phase pipeline, Track A routing proofs, `readArityOk` gap |
| Bridge | `LeanNCD/Bridge/AGENTS.md` | round-trip Task A-E staging, `wf_topo` history |
| Eval | `LeanNCD/Eval/AGENTS.md` | scatterOutDim/scatterOutShape sync contract, Portfolio test patterns |
| Acset | `LeanNCD/Acset/AGENTS.md` | schema/CSV split from Bridge's round-trip proofs |
| Algebra | `LeanNCD/Algebra/AGENTS.md` | the R=Bool XOR-ring trap |

### Entry Points

| Task | Start Here |
|------|------------|
| Understand overall architecture (two tracks + bridge) | `LeanNCD.lean`'s header doc comment (note: has some stale spots, cross-check against code — see Base/AGENTS.md Pitfalls) |
| Check current sorry/proof status authoritatively | `SORRY_INVENTORY.md` (more current than scattered doc comments) |
| Understand the `realize` bridge problem in depth | `realize.md` (companion to `SORRY_INVENTORY.md`) |
| Design history / past decisions | `docs/superpowers/plans/`, `docs/superpowers/specs/` |
| Build the project | `cd leanncd && "$HOME/.elan/bin/lake" build` (see Mathlib cold-build pitfall above) |
| Run the test suite | `cd leanncd && "$HOME/.elan/bin/lake" build` (Tests is a default target — `lakefile.toml`'s `globs` list elaborates every test module, firing all `#guard`/example/`#print axioms` checks) |
| Experimental/scratch work | `spikes/` — gitignored except `spikes/BrNF.lean` (kept in-tree, off the default build, for its wiring-combinator technique) |

### Global Invariants (Contracts)

- **Fail loud, never silently drop semantics** — the intended convention across `DSL/` and `Eval/`: cyclic dataflow, non-injective scatters, nonlinear scatters, inconsistent scan axis orders, unsized axes are all explicit errors, not silent miscompiles or wrong answers. ⚠️ **Read this as "enforced where audited, aspirational where not."** This line previously stated the convention as achieved; the 2026-07-30 audit (`papers/semantic_payload_audit.md`) found **five live violations of it** — `evalScan` panicked on an unsized iteration axis instead of erroring, `brOpOfIdx` mapped any unknown tag to `.contract`, `writeSBr` swallowed CSV encode errors, `checkScatterNonlin` accepted `.recurMorphism` then discarded it, and `splitNonlins` dropped `rhs.agg`. Wave A closed six findings; **finding #6 (the boundary *decoder* defaults — `realizeStMat` zero-fill, `realizeBrBaseP`, `AcsetCodec`, `realizeSBr`) is still UNAUDITED.** Treat the convention as a goal to verify, not a guarantee to rely on.
- **Isolate hard proofs, keep load-bearing instances sorry-free (`Br` only)** — `Br`'s core `ColoredPROP` instance is fully proved; its deferred content (`brCancelPoint`) is pushed into the opt-in `Elemental` mixin, never left inside the instance. `St` does NOT follow this pattern — `swap_hexagon_fwd`/`swap_hexagon_rev` (`St.lean:269-270`) are `by sorry` directly inside the `St` instance; see `Base/AGENTS.md`.
- **Doc comments and status docs drift out of date faster than code** — `SORRY_INVENTORY.md` is the closest thing to authoritative, but even it has stale entries (see Algebra/AGENTS.md). Always verify a "sorry-free" or "X sorries remain" claim by reading the actual file, not by trusting a comment or a memory of one.

### Patterns

- **When the same logic is genuinely duplicated across two or more call sites, unify it into one
  general routine — don't leave parallel near-copies to drift.** The trigger is an actual second
  occurrence, not an anticipated one: this does not license speculative generalization (building a
  general routine for a hypothetical future second caller is exactly what the root `CLAUDE.md`'s
  "no abstractions for single-use code" rule forbids). Duplicated logic across real call sites is
  also where correctness bugs hide, precisely because nothing forces the copies to stay in sync —
  treat "these two blocks look alike" as a prompt to check whether they've already diverged, not
  just an opportunity to tidy up.
  Concrete precedent: `docs/superpowers/plans/2026-07-31-wave-b-eval-unification.md` (Eval
  contraction/nonlinearity unification) is built entirely around this — `evalAssignWith`/
  `evalAssignSeeded` unify into one `evalAssignSeeded` (`evalAssignWith` becomes its empty-seed
  wrapper); `evalPlain`'s and `Scan.evalStmtSliceSeeded`'s duplicated norm-axis-lookup blocks
  unify into one `resolveNonlin`; their duplicated dtype dispatch unifies into one
  `evalAssignDtypedSeeded`. In each case the two copies had already silently diverged (a real
  defect, not a style nit) — the strongest evidence a unification is overdue, not premature.

### Global Pitfalls

- **`lake env lean <file>` checks against stale `.olean`s for anything that file imports** — see
  "Invoking Lake" above. `lake build <edited-module>` first, or you may verify a fix against the
  pre-edit behavior without realizing it.
- **`grep sorry` produces false positives constantly in this codebase** — many files have prose doc comments that mention the word "sorry" (e.g. "fully executable, zero `sorry`") without containing one. Always read the surrounding line, don't just count grep hits.
- **The R=Bool XOR-ring trap** (`Algebra/AGENTS.md`) — Mathlib's `Bool` ring instance is XOR, not `(∨,∧)`; `Mat Bool` typechecks but computes the wrong thing.
- **`scatterOutDim`/`scatterOutShape` must stay in sync with no import enforcing it** (`Eval/AGENTS.md`) — a real, previously-shipped soundness bug (fixed, but structurally re-introducible).
- **`brCancelPoint` (`Base/`) is a known-hard, well-scoped open sorry**, not a mystery — it needs a non-bijective gs-monoidal/cospan model; the bijective-wiring approach (`spikes/BrNF.lean`) is proven inadequate. Nothing load-bearing (Bridge/Eval/DSL) depends on it.

### Boundaries

#### Never
- Treat `spikes/*.lean` (other than `BrNF.lean`) as stable or reviewed — the directory is gitignored precisely because it's scratch work.
- Trust a top-of-file doc comment's sorry/status claims without cross-checking `SORRY_INVENTORY.md` and the actual `sorry` occurrences in the file.

#### Ask First
- Attempting to close `brCancelPoint` via the bijective `BrNF` route — this was tried and found structurally inadequate (see `Base/AGENTS.md`); a cospan/gs-monoidal model is the documented next step, a large undertaking.
- Instantiating `TargetActegory _ (Mat Bool) Bool` for boolean/predicate semantics — read `Algebra/AGENTS.md`'s XOR pitfall first.
