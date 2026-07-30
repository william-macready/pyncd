# AGENTS.md — leanncd

## New worktree / fresh checkout: don't cold-build Mathlib

This project depends on Mathlib (thousands of files). A `lake build` from a
checkout that has never been built compiles Mathlib from source, which can
take several hours — even though `.lake/packages` (the source fetch) may
already be present, `.lake/build` (the compiled `.olean`s) starts empty.

Before running `lake build` in a new worktree or fresh clone, check whether
another checkout of this repo already has a fully-built `.lake` directory,
and copy it over instead of rebuilding:

```bash
# 1. Find candidate checkouts (main repo, other worktrees)
git worktree list

# 2. Check if a candidate is actually fully built (compare to the target's
#    lakefile.toml / lake-manifest.json — a build from a different mathlib
#    rev won't help and lake will partially recompile it anyway, which is
#    still much faster than a full cold build):
find <candidate>/leanncd/.lake/packages/mathlib/.lake/build/lib -name "*.olean" | wc -l
find <candidate>/leanncd/Mathlib -name "*.lean" | wc -l   # rough total to compare against

# 3. If the candidate's count is at or near the total, sync its .lake into
#    the new worktree before building:
rsync -a "<candidate>/leanncd/.lake/" "./leanncd/.lake/"
```

**Use plain `rsync -a`, not `--info=progress2` or other GNU-rsync-only flags.**
macOS ships `openrsync` (protocol 29) by default, not GNU rsync — passing a
flag it doesn't recognize causes it to print usage and silently copy nothing,
while still exiting 0. Check `rsync --version` if unsure; don't trust a
"completed, exit 0" report alone — verify the `.olean` count in the
destination afterward.

After syncing, run `lake build` normally — it will only need to compile the
handful of `LeanNCD`-specific modules (and whatever the new worktree's edits
touch), typically well under a minute instead of hours.

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
| Build the project | `lake build` (see Mathlib cold-build pitfall above) |
| Run the test suite | `lake build` (Tests is a default target — `lakefile.toml`'s `globs` list elaborates every test module, firing all `#guard`/example/`#print axioms` checks) |
| Experimental/scratch work | `spikes/` — gitignored except `spikes/BrNF.lean` (kept in-tree, off the default build, for its wiring-combinator technique) |

### Global Invariants (Contracts)

- **Fail loud, never silently drop semantics** — the dominant convention across `DSL/` and `Eval/`: cyclic dataflow, non-injective scatters, nonlinear scatters, inconsistent scan axis orders, unsized axes are all explicit errors, not silent miscompiles or wrong answers.
- **Isolate hard proofs, keep load-bearing instances sorry-free** — both `St`/`Br`'s core `ColoredPROP` instances are fully proved; deferred content is pushed into standalone lemmas (`brCancelPoint`) or opt-in mixins (`Elemental`), never left inside a core instance.
- **Doc comments and status docs drift out of date faster than code** — `SORRY_INVENTORY.md` is the closest thing to authoritative, but even it has stale entries (see Algebra/AGENTS.md). Always verify a "sorry-free" or "X sorries remain" claim by reading the actual file, not by trusting a comment or a memory of one.

### Global Pitfalls

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
