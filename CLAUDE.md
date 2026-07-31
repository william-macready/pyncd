# CLAUDE.md

Behavioral guidelines to reduce common LLM coding mistakes. Merge with project-specific instructions as needed.

**Tradeoff:** These guidelines bias toward caution over speed. For trivial tasks, use judgment.

## 1. Think Before Coding

**Don't assume. Don't hide confusion. Surface tradeoffs.**

Before implementing:
- State your assumptions explicitly. If uncertain, ask.
- If multiple interpretations exist, present them - don't pick silently.
- If a simpler approach exists, say so. Push back when warranted.
- If something is unclear, stop. Name what's confusing. Ask.

## 2. Simplicity First

**Minimum code that solves the problem. Nothing speculative.**

- No features beyond what was asked.
- No abstractions for single-use code.
- No "flexibility" or "configurability" that wasn't requested.
- No error handling for impossible scenarios.
- If you write 200 lines and it could be 50, rewrite it.

Ask yourself: "Would a senior engineer say this is overcomplicated?" If yes, simplify.

## 3. Surgical Changes

**Touch only what you must. Clean up only your own mess.**

When editing existing code:
- Don't "improve" adjacent code, comments, or formatting.
- Don't refactor things that aren't broken.
- Match existing style, even if you'd do it differently.
- If you notice unrelated dead code, mention it - don't delete it.

When your changes create orphans:
- Remove imports/variables/functions that YOUR changes made unused.
- Don't remove pre-existing dead code unless asked.

The test: Every changed line should trace directly to the user's request.

## 4. Goal-Driven Execution

**Define success criteria. Loop until verified.**

Transform tasks into verifiable goals:
- "Add validation" → "Write tests for invalid inputs, then make them pass"
- "Fix the bug" → "Write a test that reproduces it, then make it pass"
- "Refactor X" → "Ensure tests pass before and after"

For multi-step tasks, state a brief plan:
```
1. [Step] → verify: [check]
2. [Step] → verify: [check]
3. [Step] → verify: [check]
```

Strong success criteria let you loop independently. Weak criteria ("make it work") require constant clarification.

## Rule 5 — Use the model only for judgment calls
Use me for: classification, drafting, summarization, extraction.
Do NOT use me for: routing, retries, deterministic transforms.
If code can answer, code answers.

## Rule 6 — Token budgets are not advisory
Per-task: 4,000 tokens. Per-session: 30,000 tokens.
If approaching budget, summarize and start fresh.
Surface the breach. Do not silently overrun.

## Rule 7 — Surface conflicts, don't average them
If two patterns contradict, pick one (more recent / more tested).
Explain why. Flag the other for cleanup.
Don't blend conflicting patterns.

## Rule 8 — Read before you write
Before adding code, read exports, immediate callers, shared utilities.
"Looks orthogonal" is dangerous. If unsure why code is structured a way, ask.

## Rule 9 — Tests verify intent, not just behavior
Tests must encode WHY behavior matters, not just WHAT it does.
A test that can't fail when business logic changes is wrong.

## Rule 10 — Checkpoint after every significant step
Summarize what was done, what's verified, what's left.
Don't continue from a state you can't describe back.
If you lose track, stop and restate.

## Rule 11 — Match the codebase's conventions, even if you disagree
Conformance > taste inside the codebase.
If you genuinely think a convention is harmful, surface it. Don't fork silently.

## Rule 12 — Fail loud
"Completed" is wrong if anything was skipped silently.
"Tests pass" is wrong if any were skipped.
Default to surfacing uncertainty, not hiding it.

---

**These guidelines are working if:** fewer unnecessary changes in diffs, fewer rewrites due to overcomplication, and clarifying questions come before implementation rather than after mistakes.

## Intent Layer

> TL;DR: pyncd formally expresses deep learning models as morphisms in a category (`data_structure/`), built via operator overloading (`construction_helpers/`), compiled to PyTorch (`torch_compile/`), rendered as text (`display/`) or serialized to ACSet/CSV (`acset/`). Start at Entry Points, check Subsystems for deep dives.

### Subsystems

| Area | Location | Description |
|------|----------|-------------|
| Core data structure | `data_structure/AGENTS.md` | `Term`/`UID` identity, `BroadcastedCategory`, `StrideCategory`, operators, `TensorLogic`/`TensorDSL` |
| Operator overloading | `construction_helpers/AGENTS.md` | `@`/`*`/`>>` — composition, product, batch lifting |
| PyTorch codegen | `torch_compile/AGENTS.md` | compiles morphism trees to `nn.Module` trees |
| Textual rendering | `display/AGENTS.md` | box-layout engine + Category-variant renderer |
| ACSet/CSV serialization | `acset/AGENTS.md` | flattens morphisms to tables, round-trips via CSV |
| Test conventions | `tests/AGENTS.md` | pipeline-layered test organization, golden-file regeneration |
| Lean formalization | `leanncd/AGENTS.md` | separate Lean 4 subproject; **has its own build pitfalls (Mathlib cold-build) — read before touching `leanncd/`** |

Small utility dirs (no dedicated node — see README for their one-line purpose): `data_transfer/` + `websocket_transfer/` (JSON encoding + WebSocket transport to the [`tsncd`](https://github.com/mit-zardini-lab/tsncd) TypeScript diagram viewer), `graphs/` (morphism→hypergraph conversion, prototype-stage), `term_utilities/`, `data_structure_kernels/` (kernelized/tiled axis variants), `utilities/` (generic helpers, no pyncd-specific logic).

### Downlinks

| Area | Node | What's There |
|------|------|--------------|
| Core | `data_structure/AGENTS.md` | Category theory core — read this first if unfamiliar with the codebase |
| Construction | `construction_helpers/AGENTS.md` | Operator overloading semantics + axis-alignment contracts |
| Codegen | `torch_compile/AGENTS.md` | Morphism → `nn.Module` compilation, `.normalize()` semantics trap |
| Rendering | `display/AGENTS.md` | Box-layout text renderer |
| Serialization | `acset/AGENTS.md` | ACSet/CSV round-trip contracts |
| Tests | `tests/AGENTS.md` | Golden-fixture regeneration workflow |

### Entry Points

| Task | Start Here |
|------|------------|
| Author a model with the TL DSL | `data_structure/TensorDSL.py` (`TL`, `axes`, `relu`, `softmax`), example in `minimum_working_example_tl.py` (`README.md`'s example uses the older `construction_helpers`/`Operators` API directly, not the TL DSL) |
| Compose models with `@`/`*`/`>>` | `construction_helpers/AGENTS.md` — import the relevant submodule to activate operators |
| Compile a model to PyTorch | `torch_compile/torch_compile.py::ConstructedModule.construct` |
| Visualize a model (browser diagram) | `make diagram-server` + `make diagram-frontend` (clones/runs the companion `tsncd` repo), or `make diagram-example` for CLI; see `README_DIAGRAMS.md` |
| Export a standalone HTML diagram | `make diagram-html` |
| Run the test suite | `uv run pytest` from repo root (regenerate golden fixtures first — see `tests/AGENTS.md`) |

### Global Invariants

- **Axis identity is by `UID`, never by name.** Two axes are "the same axis" iff they share a UID; string-based axis matching is a bug wherever it appears (see `data_structure/AGENTS.md` Contracts).
- **`data_structure/` is a one-way dependency root, with one known exception.** `construction_helpers/`, `torch_compile/`, `display/`, `acset/`, `graphs/`, `term_utilities/` all import from it. But `data_structure/Operators.py` imports `construction_helpers.product` directly (`object_product`, `morphism_product`, `datatype_converter`, `axis_converter`) to build operator templates — this is a deliberate, narrow reverse dependency, not a violation to "fix." See `construction_helpers/AGENTS.md` Key Relationships for the exact scope.

### Global Pitfalls

- **`.normalize()` is sum-normalization, not `LayerNorm`** — a documented, easy-to-assume-wrong trap in `torch_compile/`.
- **No `causal_softmax` operator exists** — attempted and reverted (one episode, touching both `data_structure/` and `torch_compile/`). Causal masking goes through `softmax(..., where=predicate)`. Check git history (`e29fdac`) before re-adding dedicated causal-attention support.
- **Golden-file test fixtures under `tests/cset_serialization/` are gitignored, generated artifacts** — a fresh clone fails `test_cset_roundtrip.py` until `python tests/generate_cset_serialization.py` is run once.
- **In `leanncd/`'s TL surface syntax, whitespace is SEMANTIC in an LHS slot** — `G[j, l +1]` is a scan recurrence but `G[j, l + 1]` is a shifted *write* (`ident "+1"` is a single atom token), and the more natural spacing silently means the other thing rather than failing. Same class of trap as `.normalize()` above and reachable from ordinary surface syntax. A breaking fix is specced but NOT implemented — see `leanncd/LeanNCD/DSL/AGENTS.md` and `docs/superpowers/specs/2026-07-30-scan-axis-declaration-spike.md`.

### Boundaries

#### Never
- Hash a `FreeNumeric`/`Numeric` value by anything other than `uid._id` — breaks round-trip equality after acset serialization (fix `d146fb6`). Plain `UID` equality (`ax.uid == other.uid`) for axis identity is unaffected and is the normal, correct pattern throughout `data_structure/`.
- Hand-edit a CSV fixture under `tests/cset_serialization/` — regenerate via `tests/generate_cset_serialization.py` instead.

#### Ask First
- Reintroducing a dedicated causal-softmax-style operator — this was tried and reverted; understand why (see `torch_compile/AGENTS.md` Pitfalls) before proposing it again.
