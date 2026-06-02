# TL → Br Compilation: Pragmatic Improvements

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the Scan short-circuit that forces a plain `Composed` fallback, add dead-code elimination before routing-table construction, and add a normalization simplification pre-pass — all while keeping `bc_signature()` errors at the point of equation registration.

**Architecture:** Three independent improvements to `data_structure/TensorDSL.py` and `data_structure/torch_compile.py`. Phase 1 (DCE) and Phase 3 (normalization simplification) are purely additive passes that operate on existing data structures before routing. Phase 2 (Scan integration) removes the `input_names=()` sentinel that bypasses the live-pool threading mechanism by teaching `_finalize_iter()` to populate external input names for uncoupled Scans, then relaxes the short-circuit guard in `to_morphism()`. Each phase is independently testable and releasable.

**Tech Stack:** Python 3.12+, PyTorch, pytest. All changes are in `data_structure/` and `tests/`.

---

## Background: the two compilation paths

`TL.to_morphism()` currently has two code paths:

**Non-Scan path (ThreadedComposed):** Each equation stored in `self._equations` is compiled by `TensorEquation.bc_signature()` into a `Broadcasted` morphism. `to_morphism()` then builds a routing table over `_entries` (a list of `(lhs_name, morphism, output_axes, input_names)` tuples) and returns a `ThreadedComposed` that runs the live-pool threading at forward time.

**Scan path (Composed fallback):** Recurrence equations are accumulated in `self._pending_iter` rather than `self._equations`. `_finalize_iter()` builds `Scan` objects and appends them to `self._entries` with `input_names=()`. `to_morphism()` detects the empty tuple and falls back to a plain `Composed`, bypassing the live pool entirely. This is the source of the ad hoc feeling and the split that these improvements address.

**Key invariant throughout all phases:** `ConstructedScan.forward(*xs)` already receives its inputs as positional arguments. The split `xs[:self.n_base]` goes to the base morphism; `xs[self.n_base:]` goes to the step morphism. This is already correct — the only missing piece is that `_entries` does not record what names to route into those positions.

---

## File map

| File | Role | Changes |
|---|---|---|
| `data_structure/TensorDSL.py` | TL class, `_finalize_iter`, `to_morphism` | DCE helper, Scan input-name extraction, normalization pre-pass |
| `data_structure/TensorLogic.py` | `TensorEquation`, `NormAxis` | Read only |
| `data_structure/torch_compile.py` | `ConstructedScan`, `ConstructedModule` | Regression check only — no changes expected |
| `tests/test_tensor_dsl.py` | Unit tests for TL | New DCE and normalization tests |
| `tests/test_torch_compile.py` | End-to-end forward-pass tests | New Scan-in-ThreadedComposed tests |

---

## Phase 1: Dead Code Elimination

### Task 1.1 — Write the failing DCE test

**Files:**
- Modify: `tests/test_tensor_dsl.py`

- [ ] **Step 1: Add the failing test**

```python
# tests/test_tensor_dsl.py  — add after test_ffn_to_morphism

def test_dead_equation_excluded_from_routing():
    """An equation whose output is never consumed must not appear in the
    compiled morphism.  ThreadedComposed.content length is the signal."""
    from data_structure.ProductCategory import ThreadedComposed
    q = real_axis('q', 3)
    m = real_axis('m', 4)
    k = real_axis('k', 4)
    tl = TL()
    # Dead: Unused is defined but never referenced downstream.
    tl.Unused[q, m] = tl.W_dead[m, k] * tl.X_dead[q, k]
    # Live: the actual output.
    tl.Out[q, m] = tl.W[m, k] * tl.X[q, k]
    morph = tl.to_morphism()
    assert isinstance(morph, ThreadedComposed)
    # Only one step in the chain — the dead equation must be gone.
    assert len(morph.content) == 1


def test_live_equation_retained():
    """An equation whose output feeds downstream must survive DCE."""
    from data_structure.ProductCategory import ThreadedComposed
    q = real_axis('q', 3)
    m = real_axis('m', 4)
    k = real_axis('k', 4)
    tl = TL()
    tl.Hidden[q, k] = relu(tl.W1[m, k] * tl.X[q, m])
    tl.Out[q, m]    = tl.W2[m, k] * tl.Hidden[q, k]
    morph = tl.to_morphism()
    assert isinstance(morph, ThreadedComposed)
    assert len(morph.content) == 2
```

- [ ] **Step 2: Run to confirm both tests fail**

```bash
cd /Users/williammacready/code/python/pyncd
python -m pytest tests/test_tensor_dsl.py::test_dead_equation_excluded_from_routing tests/test_tensor_dsl.py::test_live_equation_retained -v
```

Expected: `test_dead_equation_excluded_from_routing` FAILS (currently returns 2 steps, not 1). `test_live_equation_retained` may PASS or FAIL depending on whether ThreadedComposed is currently produced; confirm status.

---

### Task 1.2 — Implement `_live_entries()` and wire it into `to_morphism()`

**Files:**
- Modify: `data_structure/TensorDSL.py`

- [ ] **Step 1: Add the `_live_entries` helper**

Locate the block near the top of `TL.to_morphism()` where `internal_names` is built (around line 807). Add this private function *just above* `to_morphism()`:

```python
def _live_entries(
    entries: list[tuple],
) -> list[tuple]:
    """Return only entries reachable from the last output, preserving order.

    Unreachable entries — those whose lhs_name is never referenced by any
    downstream input_names — are silently dropped.  Entries with lhs_name=None
    (side-effect nodes) are always kept.
    """
    if not entries:
        return entries

    # Map each produced name to the index of the entry that produces it.
    name_to_idx: dict = {}
    for i, (lhs, _, _, _) in enumerate(entries):
        if lhs is not None:
            name_to_idx[lhs] = i

    # BFS backward from the final entry.
    reachable: set[int] = set()
    queue: list[int] = [len(entries) - 1]
    while queue:
        idx = queue.pop()
        if idx in reachable:
            continue
        reachable.add(idx)
        _, _, _, input_names = entries[idx]
        for name in input_names:
            if name is not None and name in name_to_idx:
                queue.append(name_to_idx[name])

    # Entries with lhs_name=None are always live (cannot be proven dead).
    for i, (lhs, _, _, _) in enumerate(entries):
        if lhs is None:
            reachable.add(i)

    # Return in original declaration order.
    return [e for i, e in enumerate(entries) if i in reachable]
```

- [ ] **Step 2: Call `_live_entries` at the top of `to_morphism()`**

In `TL.to_morphism()`, find the line that reads:

```python
internal_names = {lhs for lhs, _, _, _ in self._entries if lhs is not None}
```

Add the DCE call immediately before it:

```python
entries = _live_entries(self._entries)
internal_names = {lhs for lhs, _, _, _ in entries if lhs is not None}
```

Then replace every subsequent reference to `self._entries` in `to_morphism()` with `entries`. There are typically four such references: the Scan short-circuit check, the external-order loop, the routing loop, and the morphism compilation loop.

- [ ] **Step 3: Run the DCE tests**

```bash
python -m pytest tests/test_tensor_dsl.py::test_dead_equation_excluded_from_routing tests/test_tensor_dsl.py::test_live_equation_retained -v
```

Expected: both PASS.

- [ ] **Step 4: Run the full test suite to check for regressions**

```bash
python -m pytest tests/ -v
```

Expected: all pre-existing tests pass.

- [ ] **Step 5: Commit**

```bash
git add data_structure/TensorDSL.py tests/test_tensor_dsl.py
git commit -m "feat: dead code elimination pre-pass in TL.to_morphism()

Equations whose output is never consumed are dropped before the routing
table is built.  Uses a backward BFS from the final entry over input_names.
"
```

---

## Phase 2: Uncoupled Scan → Live Pool Integration

**Scope note:** This phase handles single-state (`n_states=1`) recurrences only. Coupled (`n_states>1`) recurrences continue to use the `Composed` fallback until Phase 4 (separate plan). The guard in `to_morphism()` is tightened rather than removed so coupled Scans keep working unchanged.

### Task 2.1 — Write the failing Scan integration tests

**Files:**
- Modify: `tests/test_torch_compile.py`

- [ ] **Step 1: Add the failing tests**

```python
# tests/test_torch_compile.py  — add in the ThreadedComposed section

def test_uncoupled_scan_returns_threaded_composed():
    """An uncoupled recurrence must produce ThreadedComposed, not Composed."""
    from data_structure.ProductCategory import ThreadedComposed, Composed
    i = real_axis('i', 3)
    l = real_axis('l', 4)
    tl = TL()
    tl.H[i, 0]     = tl.X[i]
    tl.H[i, l + 1] = tl.H[i, l] + tl.Delta[i, l]
    morph = tl.to_morphism()
    assert isinstance(morph, ThreadedComposed), (
        f"Expected ThreadedComposed, got {type(morph).__name__}"
    )


def test_uncoupled_scan_in_threaded_matches_composed_numerics():
    """Numerical output of ThreadedComposed path must match Composed fallback.

    We build two identical programs: one with the fix applied (ThreadedComposed)
    and one forced through the old Composed path.  Their outputs must agree.
    """
    import torch
    i = real_axis('i', 3)
    l = real_axis('l', 4)

    def build_module():
        tl = TL()
        tl.H[i, 0]     = tl.X[i]
        tl.H[i, l + 1] = tl.H[i, l] + tl.Delta[i, l]
        return ConstructedModule.construct(tl.to_morphism())

    mod = build_module()
    X     = torch.tensor([1.0, 2.0, 3.0])
    Delta = torch.zeros(3, 4)  # shape (i, l)
    Delta[0, :] = 1.0

    result = mod(X, Delta)
    H_out = result[0] if isinstance(result, tuple) else result

    # Reference: H[i, 0]=X[i], H[i, l+1]=H[i,l]+Delta[i,l]
    H = X.clone()
    H_hist = [H.clone()]
    for step in range(4):
        H = H + Delta[:, step]
        H_hist.append(H.clone())
    expected = torch.stack(H_hist, dim=-1)   # shape (3, 5)

    assert torch.allclose(H_out, expected), (
        f"Mismatch:\n{H_out}\nvs\n{expected}"
    )


def test_uncoupled_scan_mixed_with_non_scan_equations():
    """A program with both plain equations and an uncoupled Scan must compile
    to a single ThreadedComposed where earlier plain equations feed the Scan."""
    import torch
    q = real_axis('q', 2)
    m = real_axis('m', 3)
    l = real_axis('l', 3)
    tl = TL()
    # Plain equation: embed input
    tl.E[q, m] = tl.Emb[m, q] * tl.Tok[q]          # Tok:(q,), Emb:(m,q) -> E:(q,m)
    # Recurrence over E
    tl.H[q, m, 0]     = tl.E[q, m]
    tl.H[q, m, l + 1] = tl.H[q, m, l] + tl.Step[q, m, l]
    from data_structure.ProductCategory import ThreadedComposed
    assert isinstance(tl.to_morphism(), ThreadedComposed)
```

- [ ] **Step 2: Run to confirm tests fail**

```bash
python -m pytest tests/test_torch_compile.py::test_uncoupled_scan_returns_threaded_composed tests/test_torch_compile.py::test_uncoupled_scan_in_threaded_matches_composed_numerics tests/test_torch_compile.py::test_uncoupled_scan_mixed_with_non_scan_equations -v
```

Expected: all FAIL (currently returns `Composed`).

---

### Task 2.2 — Add `_external_names_from_value()` helper

**Files:**
- Modify: `data_structure/TensorDSL.py`

- [ ] **Step 1: Add the helper**

Add this function immediately above `_live_entries` in `TensorDSL.py`:

```python
def _external_names_from_value(
    value,   # RHSExpression | SumExpr
    exclude: set,  # set of DynamicName to skip (state proxies)
) -> tuple:
    """Return unique tensor names from a stripped RHS value, excluding states.

    'value' is the result of _strip_iter_axis_from_value: state factors appear
    first in canonical (sorted) order, non-state factors follow in expression
    order.  We collect non-excluded names in their order of first appearance.
    """
    seen: set = set()
    result: list = []
    # Flatten SumExpr into a single factor list preserving expression order.
    if hasattr(value, 'terms'):   # SumExpr
        factors = [f for term in value.terms for f in term.factors]
    else:                          # RHSExpression
        factors = value.factors
    for f in factors:
        # IndexedTensor check: has a .name attribute that is a DynamicName.
        if hasattr(f, 'name') and hasattr(f, 'indices'):
            if f.name not in exclude and f.name not in seen:
                seen.add(f.name)
                result.append(f.name)
    return tuple(result)
```

- [ ] **Step 2: Write a unit test for the helper**

```python
# tests/test_tensor_dsl.py

def test_external_names_from_value_excludes_state():
    """_external_names_from_value must skip state proxy names."""
    from data_structure.TensorDSL import _external_names_from_value
    import data_structure.Term as fd
    i, k = axes('i k')
    tl = TL()
    # Build a stripped RHSExpression that looks like: W[i,k] * H_state[i,k]
    # (state proxy H_state should be excluded, W should be included)
    h_proxy = fd.DynamicName('H_state')
    expr = tl.W[i, k] * tl.H_state[i, k]   # RHSExpression
    names = _external_names_from_value(expr, exclude={h_proxy})
    assert fd.DynamicName('W') in names
    assert h_proxy not in names
    assert names.index(fd.DynamicName('W')) == 0
```

- [ ] **Step 3: Run the helper test**

```bash
python -m pytest tests/test_tensor_dsl.py::test_external_names_from_value_excludes_state -v
```

Expected: PASS.

---

### Task 2.3 — Populate `input_names` in `_finalize_iter()` for uncoupled Scans

**Files:**
- Modify: `data_structure/TensorDSL.py`

- [ ] **Step 1: Locate the uncoupled-Scan branch in `_finalize_iter()`**

Find the block in `_finalize_iter()` that handles `n_states == 1`. It ends with a line that appends to `self._entries`:

```python
self._entries.append((lhs_name, scan, step_out + (l,), ()))
```

- [ ] **Step 2: Replace the empty `input_names` with computed names**

Replace that single append line with:

```python
# Collect external input names for the live-pool routing table.
# state_proxies maps original state name → proxy DynamicName; exclude both.
_proxy_names = set(state_proxies.values()) | set(state_proxies.keys())
_base_external = _external_names_from_value(base_value, _proxy_names)
_step_external = _external_names_from_value(step_value, _proxy_names)
_input_names = _base_external + _step_external
self._entries.append((lhs_name, scan, step_out + (l,), _input_names))
```

`state_proxies` is a `dict[DynamicName, DynamicName]` already in scope at this point in `_finalize_iter()` (it maps each original state name to its proxy name used inside the step morphism). `base_value` is the stripped base-case expression; `step_value` is the stripped recurrence expression (both are in scope immediately above the append line).

- [ ] **Step 3: Tighten the Scan guard in `to_morphism()` without removing it**

Find the guard block:

```python
if any(not input_names for _, _, _, input_names in self._entries):
    morphisms = tuple(_compiled(morph) for _, morph, _, _ in self._entries)
    if len(morphisms) == 1:
        return morphisms[0]
    return pc.Composed(content=morphisms)
```

Change it to only trigger for coupled Scans (those that still have `input_names=()`):

```python
# Coupled Scans (n_states > 1) still produce input_names=() until Phase 4.
# Uncoupled Scans now have proper input_names and go through ThreadedComposed.
_has_unresolved_scan = any(
    not input_names and isinstance(morph, Scan)
    for _, morph, _, input_names in entries
)
if _has_unresolved_scan:
    morphisms = tuple(_compiled(morph) for _, morph, _, _ in entries)
    if len(morphisms) == 1:
        return morphisms[0]
    return pc.Composed(content=morphisms)
```

(`entries` is the DCE-filtered list from Phase 1. `Scan` is already imported at the top of `TensorDSL.py`.)

- [ ] **Step 4: Run the Scan integration tests**

```bash
python -m pytest tests/test_torch_compile.py::test_uncoupled_scan_returns_threaded_composed tests/test_torch_compile.py::test_uncoupled_scan_in_threaded_matches_composed_numerics tests/test_torch_compile.py::test_uncoupled_scan_mixed_with_non_scan_equations -v
```

Expected: all PASS.

- [ ] **Step 5: Run the full suite — coupled Scans must not regress**

```bash
python -m pytest tests/ -v
```

Expected: all tests pass, including `test_coupled_jacobi_correctness`, `test_coupled_ordering_invariance`, `test_coupled_with_per_step_inputs`.

- [ ] **Step 6: Commit**

```bash
git add data_structure/TensorDSL.py tests/test_tensor_dsl.py tests/test_torch_compile.py
git commit -m "feat: uncoupled Scan participates in live-pool (ThreadedComposed)

_finalize_iter() now populates input_names for n_states=1 Scans by
extracting base and step external tensor names via _external_names_from_value.
The Composed fallback in to_morphism() is tightened to only trigger for
coupled Scans (n_states > 1) that still have input_names=().
"
```

---

## Phase 3: Normalization Simplification Pre-Pass

**Background:** `norm_axis('x')` produces a `NormAxis` instance. When used in a TL LHS — `tl.Comp[h, q, x] = softmax(...)` — the resulting `TensorEquation.lhs_indices` contains a `NormAxis` at that slot. Any additive term in the RHS whose factors all have indices disjoint from the `NormAxis` UID is constant along the normalization axis and can be dropped by the identity `softmax(f + c) = softmax(f)`.

This pass operates on the `TensorEquation` objects in `self._equations` before `bc_signature()` is called, so error attribution is not disturbed.

### Task 3.1 — Write the failing normalization test

**Files:**
- Modify: `tests/test_tensor_dsl.py`

- [ ] **Step 1: Add the test**

```python
# tests/test_tensor_dsl.py

def test_normalization_simplification_drops_constant_bias():
    """A bias that does not depend on the norm axis must be dropped before
    bc_signature() is called.

    tl.Comp[h, q, x] = softmax(tl.Q[q,h,k] * tl.K[x,h,k] + tl.bias[h])

    tl.bias[h] has free indices {h}; the norm axis is x (a NormAxis).
    Since x is not in {h}, the bias term is constant along x and must be
    removed.  The resulting Broadcasted must have 2 input weaves (Q, K),
    not 3 (Q, K, bias).
    """
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl = TL()
    tl.Comp[h, q, x] = softmax(tl.Q[q, h, k] * tl.K[x, h, k] + tl.bias[h])
    sig = tl.bc_signature()    # single-equation program
    assert len(sig.input_weaves) == 2, (
        f"Expected 2 input weaves (Q, K); got {len(sig.input_weaves)}"
    )


def test_normalization_simplification_keeps_axis_dependent_term():
    """A term that depends on the norm axis must NOT be dropped."""
    q, h, k = axes('q h k')
    x = norm_axis('x')
    tl = TL()
    # tl.scale[x] depends on x → must be kept
    tl.Comp[h, q, x] = softmax(tl.Q[q, h, k] * tl.K[x, h, k] + tl.scale[x])
    sig = tl.bc_signature()
    assert len(sig.input_weaves) == 3, (
        f"Expected 3 input weaves (Q, K, scale); got {len(sig.input_weaves)}"
    )
```

- [ ] **Step 2: Run to confirm the first test fails**

```bash
python -m pytest tests/test_tensor_dsl.py::test_normalization_simplification_drops_constant_bias tests/test_tensor_dsl.py::test_normalization_simplification_keeps_axis_dependent_term -v
```

Expected: `test_normalization_simplification_drops_constant_bias` FAILS (3 weaves, not 2). `test_normalization_simplification_keeps_axis_dependent_term` should already PASS.

---

### Task 3.2 — Implement the simplification pre-pass

**Files:**
- Modify: `data_structure/TensorDSL.py`

- [ ] **Step 1: Add the helper `_drop_norm_invariant_terms()`**

Add this function above `_live_entries` in `TensorDSL.py`:

```python
def _drop_norm_invariant_terms(equation):
    """Remove additive terms that are constant along the normalization axis.

    If the LHS contains a NormAxis, any SumExpr term whose factors' index
    UIDs are all disjoint from the NormAxis UID can be dropped.

    Returns the equation unchanged if no NormAxis is present or if the RHS
    is not a SumExpr.
    """
    from data_structure.TensorDSL import NormAxis   # avoid circular at top

    # Find the NormAxis UID in the LHS (if any).
    norm_uid = None
    for ax in equation.lhs_indices:
        if isinstance(ax, NormAxis):
            norm_uid = ax.uid
            break
    if norm_uid is None:
        return equation

    # Only SumExpr RHS has multiple additive terms worth filtering.
    if not hasattr(equation, 'rhs_sum') or equation.rhs_sum is None:
        return equation

    def term_depends_on_norm(term) -> bool:
        """True if any factor index in the term has the norm_uid."""
        for f in term.factors:
            if hasattr(f, 'indices'):
                for ax in f.indices:
                    if hasattr(ax, 'uid') and ax.uid == norm_uid:
                        return True
        return False

    kept = [t for t in equation.rhs_sum.terms if term_depends_on_norm(t)]
    if len(kept) == len(equation.rhs_sum.terms):
        return equation   # nothing to drop

    # Rebuild the equation with the filtered terms.
    # If only one term remains, collapse SumExpr → RHSExpression.
    if len(kept) == 1:
        new_rhs_sum = None
        new_rhs = kept[0]
    else:
        import copy
        new_rhs_sum = copy.replace(equation.rhs_sum, terms=tuple(kept))
        new_rhs = equation.rhs

    return equation._replace(rhs=new_rhs, rhs_sum=new_rhs_sum)
```

**Note:** The exact field names (`rhs_sum`, `_replace`) depend on whether `TensorEquation` is a `dataclass` or `NamedTuple`. Inspect the class definition and adjust accordingly. If `TensorEquation` is a frozen dataclass use `dataclasses.replace(equation, ...)` instead of `equation._replace(...)`.

- [ ] **Step 2: Wire the pass into `TL.__setitem__`**

Locate the point in `TL.__setitem__` where a `TensorEquation` is constructed and appended to `self._equations`. Immediately before the append, call:

```python
eq = _drop_norm_invariant_terms(eq)
self._equations.append(eq)
```

- [ ] **Step 3: Run the normalization tests**

```bash
python -m pytest tests/test_tensor_dsl.py::test_normalization_simplification_drops_constant_bias tests/test_tensor_dsl.py::test_normalization_simplification_keeps_axis_dependent_term -v
```

Expected: both PASS.

- [ ] **Step 4: Run the full suite**

```bash
python -m pytest tests/ -v
```

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add data_structure/TensorDSL.py tests/test_tensor_dsl.py
git commit -m "feat: drop norm-axis-invariant additive terms before bc_signature()

For softmax/normalize equations, any RHS term whose factor indices are
disjoint from the NormAxis is constant along the normalisation axis and
can be dropped by the identity softmax(f + c) = softmax(f).  The pass runs
at __setitem__ time on TensorEquation objects, before bc_signature() is
called, so error attribution is preserved.
"
```

---

## Phase 4: Coupled Scan → Live Pool (deferred)

Coupled recurrences (`n_states > 1`) use `input_names=()` and still fall back to `Composed`. The remaining guard in `to_morphism()` protects them. The fix follows the same pattern as Phase 2 but with additional complexity:

1. `_finalize_iter()` must collect external names for every state's base and step value separately, then combine them in canonical (sorted-by-state-name) order, matching the order `ConstructedScan.forward()` expects for coupled scans.
2. The guard in `to_morphism()` can be removed entirely once this is done.
3. `produced_idx` in the routing table must handle the multi-output case — a coupled Scan produces a *tuple* of tensors, but routing tracks a single `lhs_name`. The routing table may need to be extended to support tuple outputs, or the coupled Scan entry may need to be split into one entry per state.

This warrants a separate plan. The existing coupled-Scan tests (`test_coupled_jacobi_correctness`, `test_coupled_ordering_invariance`, `test_coupled_with_per_step_inputs`) serve as the acceptance criteria.

---

## Known risks and mitigations

**`_external_names_from_value` field detection:** The helper uses `hasattr(f, 'name')` and `hasattr(f, 'indices')` to detect `IndexedTensor` instances. If `TensorRef` (the factor type stored in `TensorEquation.rhs`) has different attribute names, the helper will silently return an empty tuple and the Scan entry will have `input_names=()`, falling through to the Composed fallback (safe degradation, not a crash). Add an assertion `assert _input_names, "no external inputs found"` during development to catch this.

**`_drop_norm_invariant_terms` field names:** `TensorEquation`'s internal structure (`rhs_sum` field, `_replace` or `dataclasses.replace`) must be confirmed against the class definition before step 3.2.2. If the field names differ, the helper returns the equation unchanged (safe no-op) until corrected.

**Scan affine positions after Phase 2:** `ScanAffine.a_positions` and `b_positions` index into the non-state step inputs. The ordering of step inputs in `_input_names` must match the ordering `_recognize_affine` assumed when it computed those positions. Both use `_strip_iter_axis_from_value`'s canonical factor ordering (state first, non-state in expression order), so they should agree. Verify with `test_uncoupled_scan_in_threaded_matches_composed_numerics` against a program that triggers the affine fast path.

**DCE and Scan interaction:** After Phase 2, Scan entries have non-empty `input_names` and participate in the BFS. A Scan that produces a state tensor used by a downstream plain equation will be correctly retained. A Scan whose output is the final entry (the common case) will always be retained.
