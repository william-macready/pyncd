# Tensor Logic Integration — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `NormAxis`, `TensorEquation(Operator)`, and `TensorProgram(Term)` as described in §5 of `papers/tensorLogicNCDIntegration.md`.

**Architecture:** All three classes live in a new `data_structure/TensorLogic.py`. `TensorEquation.bc_signature()` reads `lhs_indices` and `rhs` to build `Broadcasted` weaves and reindexings from UID identity — no string parsing. `TensorProgram.to_morphism()` topologically sorts equations by tensor name, then uses `Context.append_iter` to unify axes across equation boundaries, converting tensor logic's implicit name-sharing into pyncd's explicit UID identity.

**Tech stack:** Python 3.14, pyncd (`Term`, `UTerm`, `Axis`, `Operator`, `Broadcasted`, `Rearrangement`, `Weave`, `WeaveMode`, `Composed`, `Context`), pytest for tests.

---

## File Structure

**Create:**
- `data_structure/TensorLogic.py` — `NormAxis`, `TensorEquation`, `TensorProgram`, `_topological_sort`
- `tests/__init__.py` — empty
- `tests/test_tensor_logic.py` — pytest tests

**Modify:**
- `data_structure/Category.py` — add exports for `NormAxis`, `TensorEquation`, `TensorProgram`

---

## Background: Key pyncd Interfaces

Before tasks, a quick reference so implementation details are unambiguous.

**`Operator`** (`data_structure/BroadcastedCategory.py:151`): abstract frozen dataclass with one field `name: DynamicName | None = None`. Has `bc_signature(signature='', datatype=Reals(), give_names=True) -> Broadcasted[B, RawAxis]` which raises `NotImplementedError` (monkey-patched in `Operators.py` with `broadcast` for the default implementation; `TensorEquation` overrides it).

**`Broadcasted`** (`BroadcastedCategory.py:163`): frozen dataclass with fields `operator`, `input_weaves`, `output_weaves`, `reindexings`. `degree()` returns `iallequals(m.dom() for m in reindexings)` — so all reindexings must share the same `_dom`. `dom()` reconstructs input arrays by calling `weave.imprint_to_degree(reindexing.cod())` per input. `cod()` builds output arrays with `weave.imprint_to_degree(self.degree())`.

**`Weave`** (`BroadcastedCategory.py:92`): shape template. Each position is either `WeaveMode.TILED` (filled at runtime from the degree) or a concrete `Axis` (a contracted or private axis). `imprint_to_degree(other)` replaces TILED positions with successive elements of `other`, leaving concrete axes in place.

**`Rearrangement`** (`ProductCategory.py:165`): `mapping: Prod[int]`, `_dom: Prod[L]`. `cod() = tuple(dom[i] for i in mapping)`. So `mapping[j] = i` means `cod[j] = dom[i]`. Used as a reindexing: `dom` = full degree, `cod` = the subset of degree axes this input participates in.

**`Context.apply`** (`Term.py:270`): calls `deep_reconstruct` recursively, substituting any `UTerm` whose `uid` is in an equality class with its canonical representative. Because `TensorEquation` is a `Term`, `deep_reconstruct` walks into all its fields including `lhs_indices` (a tuple of `Axis` objects) and `rhs` (a tuple of tuples containing `Axis` objects) — so axis substitutions propagate into the equation automatically.

**Python dataclass constraint:** Since `Operator` has `name: DynamicName | None = None` (a field with a default), all fields added in `TensorEquation` must also have defaults to satisfy the dataclass inheritance rule. Use `None` as the default for all new fields.

---

## Task 1: Test infrastructure and `NormAxis`

**Files:**
- Create: `data_structure/TensorLogic.py`
- Create: `tests/__init__.py`
- Create: `tests/test_tensor_logic.py`

- [ ] **Step 1: Add pytest dev dependency**

```bash
cd /Users/williammacready/code/python/pyncd
uv add --dev pytest
```
Expected: `uv.lock` updated, `pyproject.toml` gains `[dependency-groups]` section.

- [ ] **Step 2: Write failing tests**

```python
# tests/test_tensor_logic.py
import sys
sys.path.insert(0, '.')

from data_structure.TensorLogic import NormAxis
from data_structure.StrideCategory import RawAxis, Axis


def test_norm_axis_is_rawaxis_subclass():
    ax = NormAxis()
    assert isinstance(ax, RawAxis)


def test_norm_axis_named_returns_norm_axis():
    ax = NormAxis.named('t')
    assert isinstance(ax, NormAxis)


def test_norm_axis_distinct_from_raw_axis():
    assert NormAxis is not RawAxis
    assert not isinstance(RawAxis(), NormAxis)
```

- [ ] **Step 3: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py -v
```
Expected: `ModuleNotFoundError: No module named 'data_structure.TensorLogic'`

- [ ] **Step 4: Create `tests/__init__.py` (empty)**

```python
# tests/__init__.py
```

- [ ] **Step 5: Create `data_structure/TensorLogic.py` with `NormAxis`**

```python
# data_structure/TensorLogic.py
from __future__ import annotations
from dataclasses import dataclass

import data_structure.StrideCategory as sc


@dataclass(frozen=True)
class NormAxis(sc.RawAxis):
    """Axis subclass marking the normalisation dimension in a TensorEquation."""
    ...
```

- [ ] **Step 6: Run tests to verify pass**

```bash
uv run python -m pytest tests/test_tensor_logic.py -v
```
Expected: 3 PASSED

- [ ] **Step 7: Commit**

```bash
git add data_structure/TensorLogic.py tests/__init__.py tests/test_tensor_logic.py pyproject.toml uv.lock
git commit -m "feat: add NormAxis and test infrastructure"
```

---

## Task 2: `TensorEquation` dataclass and helper methods

**Files:**
- Modify: `data_structure/TensorLogic.py`
- Modify: `tests/test_tensor_logic.py`

- [ ] **Step 1: Write failing tests**

```python
# Append to tests/test_tensor_logic.py

import data_structure.Term as fd
from data_structure.TensorLogic import NormAxis, TensorEquation
from data_structure.StrideCategory import RawAxis
from data_structure.Operators import Identity, SoftMax


def _matmul_eq():
    """Y[i,j] = W[i,k] X[k,j]"""
    i = RawAxis.named('i')
    j = RawAxis.named('j')
    k = RawAxis.named('k')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    return eq, i, j, k


def test_tensor_equation_construction():
    eq, i, j, k = _matmul_eq()
    assert eq.lhs_name == fd.DynamicName('Y')
    assert len(eq.lhs_indices) == 2
    assert len(eq.rhs) == 2


def test_retained_uids_contains_lhs_indices():
    eq, i, j, k = _matmul_eq()
    retained = eq.retained_uids()
    assert i.uid in retained
    assert j.uid in retained
    assert k.uid not in retained


def test_contracted_axes_are_rhs_only():
    eq, i, j, k = _matmul_eq()
    contracted = eq.contracted_axes()
    assert len(contracted) == 1
    assert contracted[0].uid == k.uid


def test_tensor_equation_with_norm_axis():
    b = RawAxis.named('b')
    p = RawAxis.named('p')
    d = RawAxis.named('d')
    t = NormAxis.named('t')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(b, p, t),
        rhs=(
            (fd.DynamicName('W_O'), (t, d)),
            (fd.DynamicName('Stream'), (b, p, d)),
        ),
        operator=SoftMax(),
    )
    retained = eq.retained_uids()
    assert t.uid in retained
    assert d.uid not in retained
    contracted = eq.contracted_axes()
    assert any(ax.uid == d.uid for ax in contracted)
```

- [ ] **Step 2: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "tensor_equation" -v
```
Expected: `ImportError` (TensorEquation not defined yet)

- [ ] **Step 3: Implement `TensorEquation` dataclass with helpers**

```python
# Append to data_structure/TensorLogic.py

import data_structure.Term as fd
import data_structure.BroadcastedCategory as bc


@dataclass(frozen=True)
class TensorEquation(bc.Operator):
    # Inherits name: DynamicName | None = None from Operator.
    # All new fields must have defaults (dataclass inheritance constraint).
    name: fd.DynamicName | None = None
    lhs_name: fd.DynamicName | None = None
    lhs_indices: fd.Prod[sc.Axis] = ()
    rhs: fd.Prod[tuple[fd.DynamicName, fd.Prod[sc.Axis]]] = ()
    operator: bc.Operator | None = None  # nonlinearity; None means Identity

    def retained_uids(self) -> set[fd.UID]:
        return {ax.uid for ax in self.lhs_indices}

    def contracted_axes(self) -> tuple[sc.Axis, ...]:
        retained = self.retained_uids()
        seen: set[fd.UID] = set()
        result = []
        for _, input_axes in self.rhs:
            for ax in input_axes:
                if ax.uid not in retained and ax.uid not in seen:
                    seen.add(ax.uid)
                    result.append(ax)
        return tuple(result)
```

- [ ] **Step 4: Run tests to verify pass**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "tensor_equation or norm_axis" -v
```
Expected: 7 PASSED

- [ ] **Step 5: Commit**

```bash
git add data_structure/TensorLogic.py tests/test_tensor_logic.py
git commit -m "feat: add TensorEquation dataclass with retained_uids and contracted_axes"
```

---

## Task 3: `TensorEquation.bc_signature()`

**Files:**
- Modify: `data_structure/TensorLogic.py`
- Modify: `tests/test_tensor_logic.py`

The method builds a `Broadcasted[B, Axis, TensorEquation]` from the equation's UID structure:
- **degree** = `self.lhs_indices` (the retained axes, in LHS order)
- For each input `(tensor_name, input_axes)`:
  - **weave shape**: `WeaveMode.TILED` where the axis UID is retained; the concrete `Axis` object where it is contracted
  - **reindexing mapping**: for each axis in `input_axes` that is retained, record its position in `degree`; `Rearrangement(mapping, _dom=degree).cod()` then equals the subset of degree axes this input contributes
- **output weave**: all `WeaveMode.TILED` positions (output shape = degree)
- `operator=self` — the `Broadcasted.operator` IS the `TensorEquation`

- [ ] **Step 1: Write failing tests**

```python
# Append to tests/test_tensor_logic.py

import data_structure.BroadcastedCategory as bc
import data_structure.ProductCategory as pc


def test_bc_signature_matrix_multiply_degree():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.degree() == pc.ProdObject((i, j))


def test_bc_signature_matrix_multiply_input_count():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert len(br.input_weaves) == 2
    assert len(br.output_weaves) == 1


def test_bc_signature_w_weave_shape():
    # W[i, k]: i is retained (TILED), k is contracted (concrete)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.input_weaves[0]._shape == (bc.WeaveMode.TILED, k)


def test_bc_signature_x_weave_shape():
    # X[k, j]: k is contracted (concrete), j is retained (TILED)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.input_weaves[1]._shape == (k, bc.WeaveMode.TILED)


def test_bc_signature_output_weave_all_tiled():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert all(p is bc.WeaveMode.TILED for p in br.output_weaves[0]._shape)
    assert len(br.output_weaves[0]._shape) == 2  # i, j


def test_bc_signature_operator_is_equation():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.operator is eq


def test_bc_signature_w_reindexing_cod():
    # W contributes degree axis i (pos 0) → cod = (i,)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.reindexings[0].cod() == pc.ProdObject((i,))


def test_bc_signature_x_reindexing_cod():
    # X contributes degree axis j (pos 1) → cod = (j,)
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    assert br.reindexings[1].cod() == pc.ProdObject((j,))


def test_bc_signature_dom_reconstructs_input_shapes():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    dom = br.dom()
    # W shape: (i, k); X shape: (k, j)
    assert dom[0] == bc.Array(bc.Reals(), (i, k))
    assert dom[1] == bc.Array(bc.Reals(), (k, j))


def test_bc_signature_cod_is_output_shape():
    eq, i, j, k = _matmul_eq()
    br = eq.bc_signature()
    cod = br.cod()
    assert cod[0] == bc.Array(bc.Reals(), (i, j))
```

- [ ] **Step 2: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "bc_signature" -v
```
Expected: `NotImplementedError` from the base `Operator.bc_signature`

- [ ] **Step 3: Implement `bc_signature()` on `TensorEquation`**

Add this method inside the `TensorEquation` class body in `data_structure/TensorLogic.py`:

```python
    def bc_signature[B: bc.Datatype](
        self,
        signature: str = '',
        datatype: B = bc.Reals(),
        give_names: bool = True,
    ) -> bc.Broadcasted:
        import data_structure.ProductCategory as pc
        degree = self.lhs_indices
        retained_uid_to_pos = {ax.uid: i for i, ax in enumerate(degree)}

        input_weaves = tuple(
            bc.Weave(
                datatype,
                tuple(
                    bc.WeaveMode.TILED if ax.uid in retained_uid_to_pos else ax
                    for ax in input_axes
                ),
            )
            for _, input_axes in self.rhs
        )
        output_weave = bc.Weave(
            datatype,
            tuple(bc.WeaveMode.TILED for _ in degree),
        )
        reindexings = tuple(
            pc.Rearrangement(
                mapping=tuple(
                    retained_uid_to_pos[ax.uid]
                    for ax in input_axes
                    if ax.uid in retained_uid_to_pos
                ),
                _dom=degree,
            )
            for _, input_axes in self.rhs
        )
        return bc.Broadcasted(
            operator=self,
            input_weaves=input_weaves,
            output_weaves=(output_weave,),
            reindexings=reindexings,
        )
```

- [ ] **Step 4: Run tests to verify pass**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "bc_signature" -v
```
Expected: 10 PASSED

- [ ] **Step 5: Run full suite to check no regressions**

```bash
uv run python -m pytest tests/ -v
```
Expected: all PASSED

- [ ] **Step 6: Commit**

```bash
git add data_structure/TensorLogic.py tests/test_tensor_logic.py
git commit -m "feat: implement TensorEquation.bc_signature() via UID-based weave construction"
```

---

## Task 4: `_topological_sort` helper

**Files:**
- Modify: `data_structure/TensorLogic.py`
- Modify: `tests/test_tensor_logic.py`

Kahn's algorithm over `TensorEquation` objects. An equation B depends on equation A if `A.lhs_name` appears among B's rhs tensor names. `DynamicName` is a frozen dataclass so dict keys and set membership work by field equality.

- [ ] **Step 1: Write failing tests**

```python
# Append to tests/test_tensor_logic.py

from data_structure.TensorLogic import NormAxis, TensorEquation, _topological_sort


def _chain_equations():
    """Hidden[i] = W1[i,k] X[k,i]; Y[i] = W2[i,k] Hidden[k,i]"""
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i,),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, i)),
        ),
        operator=Identity(),
    )
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=(
            (fd.DynamicName('W2'), (i, k)),
            (fd.DynamicName('Hidden'), (k, i)),
        ),
        operator=Identity(),
    )
    return eq1, eq2, i, k


def test_topological_sort_already_ordered():
    eq1, eq2, i, k = _chain_equations()
    result = _topological_sort((eq1, eq2))
    assert result[0] is eq1
    assert result[1] is eq2


def test_topological_sort_reversed_input():
    eq1, eq2, i, k = _chain_equations()
    result = _topological_sort((eq2, eq1))
    assert result[0] is eq1
    assert result[1] is eq2


def test_topological_sort_independent_equations():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    eq_a = TensorEquation(
        lhs_name=fd.DynamicName('A'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i, k)),),
        operator=Identity(),
    )
    eq_b = TensorEquation(
        lhs_name=fd.DynamicName('B'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('Y'), (i, k)),),
        operator=Identity(),
    )
    result = _topological_sort((eq_a, eq_b))
    assert set(r.lhs_name for r in result) == {fd.DynamicName('A'), fd.DynamicName('B')}
    assert len(result) == 2
```

- [ ] **Step 2: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "topological_sort" -v
```
Expected: `ImportError` (_topological_sort not defined)

- [ ] **Step 3: Implement `_topological_sort`**

Add this function to `data_structure/TensorLogic.py` (module level, before `TensorProgram`):

```python
def _topological_sort(
    equations: fd.Prod['TensorEquation'],
) -> list['TensorEquation']:
    name_to_eq: dict[fd.DynamicName, TensorEquation] = {
        eq.lhs_name: eq for eq in equations
    }
    deps: dict[fd.DynamicName, set[fd.DynamicName]] = {
        eq.lhs_name: {
            name for name, _ in eq.rhs
            if name in name_to_eq
        }
        for eq in equations
    }
    result: list[TensorEquation] = []
    ready: list[TensorEquation] = [
        eq for eq in equations if not deps[eq.lhs_name]
    ]
    while ready:
        eq = ready.pop(0)
        result.append(eq)
        for other in equations:
            if other.lhs_name not in (e.lhs_name for e in result):
                deps[other.lhs_name].discard(eq.lhs_name)
                if not deps[other.lhs_name]:
                    ready.append(other)
    return result
```

- [ ] **Step 4: Run tests to verify pass**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "topological_sort" -v
```
Expected: 3 PASSED

- [ ] **Step 5: Commit**

```bash
git add data_structure/TensorLogic.py tests/test_tensor_logic.py
git commit -m "feat: add _topological_sort for TensorProgram equation ordering"
```

---

## Task 5: `TensorProgram` and `to_morphism()`

**Files:**
- Modify: `data_structure/TensorLogic.py`
- Modify: `tests/test_tensor_logic.py`

`to_morphism()` iterates equations in topological order. For each equation, it unifies its rhs tensor axes with the `lhs_indices` of whichever prior equation produced that tensor (via `ctx.append_iter`). Then `ctx.apply(eq)` substitutes canonical UIDs into the equation (and its internal `Axis` objects), and `bc_signature()` builds the `Broadcasted`. The result is `Composed(tuple(morphisms))`.

- [ ] **Step 1: Write failing tests**

```python
# Append to tests/test_tensor_logic.py

from data_structure.TensorLogic import NormAxis, TensorEquation, TensorProgram, _topological_sort
from data_structure.ProductCategory import Composed


def test_tensor_program_two_equation_chain():
    """Two equations in sequence; to_morphism() produces a Composed of length 2."""
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')

    # Hidden[i, j] = W1[i, k] X[k, j]
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )

    # New axes for eq2 that will be unified with eq1's lhs_indices
    i2 = RawAxis.named('i')
    j2 = RawAxis.named('j')
    m = RawAxis.named('m')
    # Y[i, m] = W2[i, j] Hidden[j, m]   (j2 and m are eq2-local; j2 will unify with j)
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i2, m),
        rhs=(
            (fd.DynamicName('W2'), (i2, j2)),
            (fd.DynamicName('Hidden'), (j2, m)),
        ),
        operator=Identity(),
    )

    prog = TensorProgram(equations=(eq1, eq2))
    morphism = prog.to_morphism()

    assert isinstance(morphism, Composed)
    assert len(morphism.content) == 2


def test_tensor_program_composed_cod_matches_second_equation():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('Hidden'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W1'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    i2 = RawAxis.named('i')
    j2 = RawAxis.named('j')
    m = RawAxis.named('m')
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i2, m),
        rhs=(
            (fd.DynamicName('W2'), (i2, j2)),
            (fd.DynamicName('Hidden'), (j2, m)),
        ),
        operator=Identity(),
    )
    prog = TensorProgram(equations=(eq1, eq2))
    morphism = prog.to_morphism()
    # The final codomain should be one Array with 2 axes (i2 and m, after unification)
    cod = morphism.cod()
    assert len(cod) == 1
    assert len(cod[0]._shape) == 2


def test_tensor_program_single_equation():
    i = RawAxis.named('i')
    k = RawAxis.named('k')
    j = RawAxis.named('j')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, j),
        rhs=(
            (fd.DynamicName('W'), (i, k)),
            (fd.DynamicName('X'), (k, j)),
        ),
        operator=Identity(),
    )
    prog = TensorProgram(equations=(eq,))
    morphism = prog.to_morphism()
    assert isinstance(morphism, Composed)
    assert len(morphism.content) == 1
```

- [ ] **Step 2: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "tensor_program" -v
```
Expected: `ImportError` (TensorProgram not defined)

- [ ] **Step 3: Implement `TensorProgram`**

Append to `data_structure/TensorLogic.py`:

```python
import data_structure.ProductCategory as pc


@dataclass(frozen=True)
class TensorProgram(fd.Term):
    equations: fd.Prod[TensorEquation] = ()

    def to_morphism(self) -> pc.Composed:
        ctx = fd.Context()
        morphisms = []
        name_to_axes: dict[fd.DynamicName, fd.Prod[sc.Axis]] = {}

        for eq in _topological_sort(self.equations):
            for tensor_name, input_axes in eq.rhs:
                if tensor_name in name_to_axes:
                    prior_axes = name_to_axes[tensor_name]
                    ctx.append_iter(
                        axis
                        for pair in zip(prior_axes, input_axes)
                        for axis in pair
                    )
            br = ctx.apply(eq).bc_signature()
            morphisms.append(br)
            applied_eq = ctx.apply(eq)
            name_to_axes[eq.lhs_name] = applied_eq.lhs_indices

        return pc.Composed(content=tuple(morphisms))
```

Note: `ctx.append_iter` unifies pairs by treating them as one iterable; since `EqualityClass.from_iter` picks a canonical from the whole set, we need to unify each pair separately. Replace the inner loop with:

```python
            for tensor_name, input_axes in eq.rhs:
                if tensor_name in name_to_axes:
                    prior_axes = name_to_axes[tensor_name]
                    for prior_ax, eq_ax in zip(prior_axes, input_axes):
                        ctx.append_iter((prior_ax, eq_ax))
```

Final `to_morphism()` implementation:

```python
    def to_morphism(self) -> pc.Composed:
        ctx = fd.Context()
        morphisms = []
        name_to_axes: dict[fd.DynamicName, fd.Prod[sc.Axis]] = {}

        for eq in _topological_sort(self.equations):
            for tensor_name, input_axes in eq.rhs:
                if tensor_name in name_to_axes:
                    for prior_ax, eq_ax in zip(name_to_axes[tensor_name], input_axes):
                        ctx.append_iter((prior_ax, eq_ax))
            applied_eq = ctx.apply(eq)
            br = applied_eq.bc_signature()
            morphisms.append(br)
            name_to_axes[eq.lhs_name] = applied_eq.lhs_indices

        return pc.Composed(content=tuple(morphisms))
```

- [ ] **Step 4: Run tests to verify pass**

```bash
uv run python -m pytest tests/test_tensor_logic.py -k "tensor_program" -v
```
Expected: 3 PASSED

- [ ] **Step 5: Run full suite**

```bash
uv run python -m pytest tests/ -v
```
Expected: all PASSED

- [ ] **Step 6: Commit**

```bash
git add data_structure/TensorLogic.py tests/test_tensor_logic.py
git commit -m "feat: implement TensorProgram.to_morphism() with Context-mediated axis unification"
```

---

## Task 6: Export from `Category.py`

**Files:**
- Modify: `data_structure/Category.py`
- Modify: `tests/test_tensor_logic.py`

- [ ] **Step 1: Write failing test**

```python
# Append to tests/test_tensor_logic.py

def test_exports_from_category():
    from data_structure.Category import NormAxis, TensorEquation, TensorProgram
    assert NormAxis is not None
    assert TensorEquation is not None
    assert TensorProgram is not None
```

- [ ] **Step 2: Run to verify failure**

```bash
uv run python -m pytest tests/test_tensor_logic.py::test_exports_from_category -v
```
Expected: `ImportError`

- [ ] **Step 3: Add exports to `data_structure/Category.py`**

Add at the top of `data_structure/Category.py` (after existing imports):

```python
from data_structure.TensorLogic import (
    NormAxis,
    TensorEquation,
    TensorProgram,
)
```

Add to `__all__`:

```python
    'NormAxis',
    'TensorEquation',
    'TensorProgram',
```

- [ ] **Step 4: Run full test suite**

```bash
uv run python -m pytest tests/ -v
```
Expected: all PASSED

- [ ] **Step 5: Commit**

```bash
git add data_structure/Category.py tests/test_tensor_logic.py
git commit -m "feat: export NormAxis, TensorEquation, TensorProgram from Category"
```

---

## Self-Review

**Spec coverage:**
- §5.2 `TensorEquation(Operator)` with `lhs_name`, `lhs_indices`, `rhs`, `operator` fields → Task 2 ✓
- §5.2 `NormAxis` subclass for normalization axis marking → Task 1 ✓
- §5.3 `bc_signature()` reads UID graph to build degree/weaves/reindexings → Task 3 ✓
- §5.3 `operator=self` in returned `Broadcasted` → Task 3 ✓
- §5.4 Round-trip: `Context.apply` traverses `TensorEquation` fields via `deep_reconstruct` (this is free — no code needed, follows from `TensorEquation` being a `Term`) ✓
- §5.5 `TensorProgram(Term)` with `to_morphism()` and topological sort → Tasks 4–5 ✓
- §5.5 `Context`-mediated axis unification via `name_to_axes` → Task 5 ✓

**Gaps not addressed (intentionally, per §5.6):** parallel product extraction, symbolic shape propagation, embedding datatype extension, predicate/Boolean tensors. These are above `TensorProgram.to_morphism()` and are the caller's responsibility.

**Placeholder scan:** No TBDs, no "similar to Task N" references, no steps without code.

**Type consistency:**
- `_topological_sort` takes `Prod[TensorEquation]`, returns `list[TensorEquation]` — matches Task 5 usage ✓
- `TensorEquation.bc_signature()` returns `bc.Broadcasted` — matches `TensorProgram.to_morphism()` usage (appended to `morphisms`) ✓
- `TensorProgram.to_morphism()` returns `pc.Composed` — matches test assertions ✓
- `NormAxis` is a subclass of `sc.RawAxis` — satisfies `sc.Axis` type bound used in `TensorEquation.lhs_indices: Prod[sc.Axis]` ✓
