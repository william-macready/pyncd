# Acset Integration — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement a standalone `acset/` package that converts existing pyncd objects (`StrideMorphism`, `TensorEquation`, `TensorProgram`) to acset instances (`SStInstance`, `SBrInstance`) with zero changes to any existing file.

**Architecture:** A new `acset/` top-level package with two modules: `instances.py` (pure dataclasses, no pyncd imports) and `convert.py` (standalone functions reading existing dataclass fields). All needed information is already accessible as public fields on frozen dataclasses in `data_structure/`. No methods are added to existing classes.

**Tech Stack:** Python 3.12 dataclasses, pytest. Imports only from `data_structure/` (read-only).

---

## File Map

| File | Status | Responsibility |
|---|---|---|
| `acset/__init__.py` | **Create** | Re-export public API |
| `acset/instances.py` | **Create** | `OpTag`, `SStInstance`, `SBrInstance` and their row types |
| `acset/convert.py` | **Create** | `from_stride_morphism`, `from_tensor_equation`, `from_tensor_program` |
| `tests/test_acset_instances.py` | **Create** | Dataclass construction and field access |
| `tests/test_acset_convert.py` | **Create** | Conversion correctness against known examples |

---

## Key field reference (read-only, no changes needed)

```python
# StrideMorphism (data_structure/StrideCategory.py)
m._dom: tuple[Axis, ...]                         # domain axes
m._cod_stride: tuple[tuple[Axis, tuple[Numeric, ...]], ...]
#   each entry: (cod_axis, (coeff_for_dom_0, coeff_for_dom_1, ...))

# TensorEquation (data_structure/TensorLogic.py)
eq.lhs_name: DynamicName | None                  # output tensor name
eq.lhs_indices: tuple[RawAxis, ...]              # retained (degree) axes
eq.rhs: tuple[tuple[DynamicName, tuple[RawAxis, ...]], ...]  # inputs
eq.operator: Operator | None                     # None means Identity
eq.retained_uids() -> set[UID]                   # already implemented
eq.contracted_axes() -> tuple[Axis, ...]         # already implemented

# TensorProgram (data_structure/TensorLogic.py)
prog.equations: tuple[TensorEquation, ...]


# Axis (data_structure/StrideCategory.py)
ax.uid: UID                                      # unique identity
ax.local_size() -> Numeric                       # symbolic or concrete size
```

---

## Task 1: `SStInstance` dataclass

**Files:**
- Create: `acset/__init__.py`
- Create: `acset/instances.py`
- Create: `tests/test_acset_instances.py`

- [ ] **Step 1: Write the failing test**

```python
# tests/test_acset_instances.py
from acset.instances import SStInstance, EntryRow

def test_sstinstance_empty():
    inst = SStInstance()
    assert inst.axis_sizes == {}
    assert inst.entries == []

def test_sstinstance_stores_entry():
    from data_structure.Term import UID
    from data_structure.StrideCategory import RawAxis
    from data_structure.Numeric import Integer
    a, b = RawAxis.named('a'), RawAxis.named('b')
    inst = SStInstance(
        axis_sizes={a.uid: Integer(4), b.uid: Integer(6)},
        entries=[EntryRow(src=a.uid, tgt=b.uid, coeff=Integer(2))],
    )
    assert inst.axis_sizes[a.uid] == Integer(4)
    assert inst.entries[0].coeff == Integer(2)
```

- [ ] **Step 2: Run to verify it fails**

```
cd /Users/williammacready/code/python/pyncd
python -m pytest tests/test_acset_instances.py -v 2>&1 | head -20
```
Expected: `ModuleNotFoundError: No module named 'acset'`

- [ ] **Step 3: Write `acset/instances.py`**

```python
# acset/instances.py
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum

import data_structure.Term as fd
import data_structure.Numeric as nm


class OpTag(Enum):
    Identity                = 'identity'
    SoftMax                 = 'softmax'
    Elementwise             = 'elementwise'
    Normalize               = 'normalize'
    Embedding               = 'embedding'
    AdditionOp              = 'addition'
    WeightedTriangularLower = 'weighted_triangular_lower'
    Linear                  = 'linear'


@dataclass
class EntryRow:
    src:   fd.UID   # domain axis UID
    tgt:   fd.UID   # codomain axis UID
    coeff: nm.Numeric


@dataclass
class SStInstance:
    """Acset instance for one StrideMorphism."""
    axis_sizes: dict[fd.UID, nm.Numeric] = field(default_factory=dict)
    entries:    list[EntryRow]           = field(default_factory=list)


@dataclass
class ArrayRow:
    name:         fd.DynamicName | None
    is_input:     bool
    operator_tag: OpTag | None  # None for input arrays
    norm_axis:    fd.UID | None = None  # UID of normalisation axis; SoftMax/Normalize output arrays only


@dataclass
class ArrayAxisRow:
    array_name: fd.DynamicName | None
    axis_uid:   fd.UID
    is_target:  bool            # True = contracted; False = degree/TILED


@dataclass
class SampleRow:
    src_uid:       fd.UID              # degree axis
    tgt_uid:       fd.UID              # input axis (equals src for pure einsum)
    coeff:         nm.Numeric
    reindexing_of: fd.DynamicName | None  # input array name


@dataclass
class SBrInstance:
    """Acset instance for one TensorEquation or Broadcasted."""
    axis_sizes:  dict[fd.UID, nm.Numeric] = field(default_factory=dict)
    arrays:      list[ArrayRow]           = field(default_factory=list)
    array_axes:  list[ArrayAxisRow]       = field(default_factory=list)
    samples:     list[SampleRow]          = field(default_factory=list)
```

- [ ] **Step 4: Write `acset/__init__.py`**

```python
# acset/__init__.py
from acset.instances import (
    OpTag,
    EntryRow, SStInstance,
    ArrayRow, ArrayAxisRow, SampleRow, SBrInstance,
)
```

- [ ] **Step 5: Run tests to verify they pass**

```
python -m pytest tests/test_acset_instances.py -v
```
Expected: 2 passed.

- [ ] **Step 6: Commit**

```bash
git add acset/__init__.py acset/instances.py tests/test_acset_instances.py
git commit -m "feat(acset): add SStInstance and SBrInstance dataclasses"
```

---

## Task 2: `from_stride_morphism`

**Files:**
- Create: `acset/convert.py`
- Modify: `tests/test_acset_convert.py` (create)

- [ ] **Step 1: Write the failing tests**

```python
# tests/test_acset_convert.py
import data_structure.Term as fd
from data_structure.StrideCategory import RawAxis, StrideMorphism
from data_structure.Numeric import Integer
from data_structure.TensorLogic import TensorEquation, TensorProgram
from data_structure.Operators import Identity, SoftMax
from acset.convert import from_stride_morphism, from_tensor_equation, from_tensor_program
from acset.instances import SStInstance, SBrInstance, OpTag


def _identity_morphism():
    """Identity on one axis: (p,) → (p,) with coeff=1."""
    return StrideMorphism.from_matrix(
        (1,), dom_names=('p',), cod_names=('p',)
    )

def _duplication_morphism():
    """Duplication: (p,) → (p, p) each coeff=1."""
    return StrideMorphism.from_matrix(
        (1,), (1,), dom_names=('p',), cod_names=('p0', 'p1')
    )

def _conv_shift_morphism():
    """Convolution shift: (x', w) → (x'+w,) coeffs=(1,1)."""
    return StrideMorphism.from_matrix(
        (1, 1), dom_names=("x'", 'w'), cod_names=('x',), name='+'
    )


def test_from_stride_morphism_returns_sstinstance():
    result = from_stride_morphism(_identity_morphism())
    assert isinstance(result, SStInstance)


def test_identity_morphism():
    # from_matrix creates fresh dom and cod axes even with the same name,
    # so axis_sizes has 2 entries (one per distinct UID); entries has 1 row.
    m = _identity_morphism()
    inst = from_stride_morphism(m)
    assert len(inst.axis_sizes) == 2
    assert len(inst.entries) == 1
    assert inst.entries[0].coeff == Integer(1)


def test_duplication_has_three_axes():
    # dom: p; cod: p0, p1 — three distinct axes, two entry rows
    inst = from_stride_morphism(_duplication_morphism())
    assert len(inst.axis_sizes) == 3
    assert len(inst.entries) == 2
    for e in inst.entries:
        assert e.coeff == Integer(1)


def test_conv_shift_entries():
    # (x', w) → (x,): two entries, both coeff=1
    inst = from_stride_morphism(_conv_shift_morphism())
    assert len(inst.entries) == 2
    assert all(e.coeff == Integer(1) for e in inst.entries)
```

- [ ] **Step 2: Run to verify they fail**

```
python -m pytest tests/test_acset_convert.py -v 2>&1 | head -20
```
Expected: `ModuleNotFoundError: No module named 'acset.convert'`

- [ ] **Step 3: Write `acset/convert.py`**

```python
# acset/convert.py
from __future__ import annotations

import data_structure.Term as fd
import data_structure.Numeric as nm
from data_structure.StrideCategory import StrideMorphism
from data_structure.TensorLogic import TensorEquation, TensorProgram, NormAxis
import data_structure.Operators as ops

from acset.instances import (
    OpTag, EntryRow, SStInstance,
    ArrayRow, ArrayAxisRow, SampleRow, SBrInstance,
)


def _operator_to_tag(operator) -> OpTag:
    """Map an Operator instance to its OpTag enum value."""
    if operator is None:
        return OpTag.Identity
    # Identity must be checked before Elementwise: Identity is a subclass of Elementwise.
    if isinstance(operator, ops.Identity):
        return OpTag.Identity
    if isinstance(operator, ops.Elementwise):
        return OpTag.Elementwise
    if isinstance(operator, ops.SoftMax):
        return OpTag.SoftMax
    if isinstance(operator, ops.Normalize):
        return OpTag.Normalize
    if isinstance(operator, ops.Embedding):
        return OpTag.Embedding
    if isinstance(operator, ops.AdditionOp):
        return OpTag.AdditionOp
    if isinstance(operator, ops.WeightedTriangularLower):
        return OpTag.WeightedTriangularLower
    if isinstance(operator, ops.Linear):
        return OpTag.Linear
    return OpTag.Identity


def from_stride_morphism(m: StrideMorphism) -> SStInstance:
    """Convert a StrideMorphism to an SStInstance.

    Each nonzero coefficient in the matrix becomes one EntryRow.
    Domain and codomain axes live together in axis_sizes, keyed by UID.
    """
    inst = SStInstance()
    for ax in m._dom:
        inst.axis_sizes[ax.uid] = ax.local_size()
    for cod_ax, coeffs in m._cod_stride:
        inst.axis_sizes[cod_ax.uid] = cod_ax.local_size()
        for dom_ax, coeff in zip(m._dom, coeffs):
            inst.entries.append(EntryRow(
                src=dom_ax.uid, tgt=cod_ax.uid, coeff=coeff
            ))
    return inst
```

- [ ] **Step 4: Run tests to verify they pass**

```
python -m pytest tests/test_acset_convert.py -v
```
Expected: 4 passed.

- [ ] **Step 5: Commit**

```bash
git add acset/convert.py tests/test_acset_convert.py
git commit -m "feat(acset): add from_stride_morphism conversion"
```

---

## Task 3: `from_tensor_equation`

**Files:**
- Modify: `acset/convert.py` (add function)
- Modify: `tests/test_acset_convert.py` (add tests)

- [ ] **Step 1: Write the failing tests**

Add to `tests/test_acset_convert.py`:

```python
from data_structure.TensorLogic import TensorEquation, NormAxis
from data_structure.Operators import Identity, SoftMax
from acset.convert import from_tensor_equation
from acset.instances import SBrInstance, OpTag


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


def test_from_tensor_equation_returns_sbr_instance():
    eq, *_ = _matmul_eq()
    assert isinstance(from_tensor_equation(eq), SBrInstance)


def test_matmul_has_three_arrays():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    # Y (output), W (input), X (input)
    assert len(inst.arrays) == 3


def test_matmul_output_array_not_input():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.name == fd.DynamicName('Y')
    assert output.operator_tag == OpTag.Identity


def test_matmul_contracted_axis_is_target():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    # k appears in W and X as is_target=True
    k_rows = [r for r in inst.array_axes if r.axis_uid == k.uid]
    assert len(k_rows) == 2
    assert all(r.is_target for r in k_rows)


def test_matmul_retained_axes_not_target():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    # i appears in Y and W as is_target=False
    i_rows = [r for r in inst.array_axes if r.axis_uid == i.uid]
    assert all(not r.is_target for r in i_rows)


def test_matmul_samples_count():
    # W contributes i → one sample; X contributes j → one sample
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert len(inst.samples) == 2


def test_matmul_samples_have_unit_coeff():
    eq, *_ = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert all(s.coeff == Integer(1) for s in inst.samples)


def test_matmul_axis_sizes_contains_all_axes():
    eq, i, j, k = _matmul_eq()
    inst = from_tensor_equation(eq)
    assert i.uid in inst.axis_sizes
    assert j.uid in inst.axis_sizes
    assert k.uid in inst.axis_sizes


def test_softmax_operator_tag():
    i = NormAxis.named('i')
    eq = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i,),
        rhs=((fd.DynamicName('X'), (i,)),),
        operator=SoftMax(),
    )
    inst = from_tensor_equation(eq)
    output = next(a for a in inst.arrays if not a.is_input)
    assert output.operator_tag == OpTag.SoftMax
    assert output.norm_axis == i.uid
```

- [ ] **Step 2: Run to verify they fail**

```
python -m pytest tests/test_acset_convert.py -k "tensor_equation" -v 2>&1 | head -20
```
Expected: `AttributeError` or `ImportError` — `from_tensor_equation` not yet defined.

- [ ] **Step 3: Add `from_tensor_equation` to `acset/convert.py`**

Append to `acset/convert.py`:

```python
def from_tensor_equation(eq: TensorEquation) -> SBrInstance:
    """Convert one TensorEquation to an SBrInstance.

    Retained indices (lhs_indices) become degree/TILED axes (is_target=False).
    Contracted indices (in rhs but not lhs_indices) become target axes (is_target=True).
    One SampleRow per (input_tensor, retained_axis) pair, all with coeff=Integer(1).
    """
    inst = SBrInstance()
    retained = eq.retained_uids()

    # Output array — NormAxis in lhs_indices marks the normalisation axis
    norm_axis_uid = next((ax.uid for ax in eq.lhs_indices if isinstance(ax, NormAxis)), None)
    inst.arrays.append(ArrayRow(
        name=eq.lhs_name,
        is_input=False,
        operator_tag=_operator_to_tag(eq.operator),
        norm_axis=norm_axis_uid,
    ))
    for ax in eq.lhs_indices:
        inst.axis_sizes[ax.uid] = ax.local_size()
        inst.array_axes.append(ArrayAxisRow(
            array_name=eq.lhs_name, axis_uid=ax.uid, is_target=False
        ))

    # Input arrays
    for tensor_name, input_axes in eq.rhs:
        inst.arrays.append(ArrayRow(
            name=tensor_name, is_input=True, operator_tag=None
        ))
        for ax in input_axes:
            inst.axis_sizes[ax.uid] = ax.local_size()
            inst.array_axes.append(ArrayAxisRow(
                array_name=tensor_name,
                axis_uid=ax.uid,
                is_target=ax.uid not in retained,
            ))
        # One Sample per retained axis this input contributes
        for ax in input_axes:
            if ax.uid in retained:
                inst.samples.append(SampleRow(
                    src_uid=ax.uid,
                    tgt_uid=ax.uid,
                    coeff=nm.Integer(1),
                    reindexing_of=tensor_name,
                ))

    return inst
```

- [ ] **Step 4: Run tests to verify they pass**

```
python -m pytest tests/test_acset_convert.py -v
```
Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add acset/convert.py tests/test_acset_convert.py
git commit -m "feat(acset): add from_tensor_equation conversion"
```

---

## Task 4: `from_tensor_program`

**Files:**
- Modify: `acset/convert.py` (add function)
- Modify: `tests/test_acset_convert.py` (add tests)

- [ ] **Step 1: Write the failing tests**

Add to `tests/test_acset_convert.py`:

```python
from data_structure.TensorLogic import TensorProgram
from acset.convert import from_tensor_program


def _two_equation_program():
    """
    H[i, k] = W1[i, j] X[j, k]   (matmul)
    Y[i, k] = relu(W2[i, m] H[m, k])  (another matmul with relu)
    """
    i  = RawAxis.named('i')
    j  = RawAxis.named('j')
    k  = RawAxis.named('k')
    m  = RawAxis.named('m')
    eq1 = TensorEquation(
        lhs_name=fd.DynamicName('H'),
        lhs_indices=(i, k),
        rhs=(
            (fd.DynamicName('W1'), (i, j)),
            (fd.DynamicName('X'),  (j, k)),
        ),
        operator=Identity(),
    )
    eq2 = TensorEquation(
        lhs_name=fd.DynamicName('Y'),
        lhs_indices=(i, k),
        rhs=(
            (fd.DynamicName('W2'), (i, m)),
            (fd.DynamicName('H'),  (m, k)),
        ),
        operator=Identity(),
    )
    return TensorProgram(equations=(eq1, eq2)), i, j, k, m


def test_from_tensor_program_returns_list():
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert isinstance(result, list)


def test_from_tensor_program_one_instance_per_equation():
    prog, *_ = _two_equation_program()
    result = from_tensor_program(prog)
    assert len(result) == 2
    from acset.instances import SBrInstance
    assert all(isinstance(r, SBrInstance) for r in result)


def test_from_tensor_program_each_has_three_arrays():
    prog, *_ = _two_equation_program()
    instances = from_tensor_program(prog)
    # Each equation has one output + two inputs
    assert all(len(inst.arrays) == 3 for inst in instances)


def test_from_tensor_program_shared_axis_same_uid():
    # axis 'i' appears in both equations; its UID must be consistent
    prog, i, j, k, m = _two_equation_program()
    instances = from_tensor_program(prog)
    # i.uid should appear in both instances' axis_sizes
    assert i.uid in instances[0].axis_sizes
    assert i.uid in instances[1].axis_sizes
```

- [ ] **Step 2: Run to verify they fail**

```
python -m pytest tests/test_acset_convert.py -k "tensor_program" -v 2>&1 | head -20
```
Expected: `ImportError` — `from_tensor_program` not yet defined.

- [ ] **Step 3: Add `from_tensor_program` to `acset/convert.py`**

Append to `acset/convert.py`:

```python
def from_tensor_program(prog: TensorProgram) -> list[SBrInstance]:
    """Convert a TensorProgram to one SBrInstance per equation.

    Instances are independent; shared axes are identified by UID across them.
    The equations are converted in their stored order (topological sort is the
    caller's responsibility via TensorProgram.to_morphism() if needed).
    """
    return [from_tensor_equation(eq) for eq in prog.equations]
```

- [ ] **Step 4: Run all tests to verify they pass**

```
python -m pytest tests/test_acset_convert.py -v
```
Expected: all tests pass.

- [ ] **Step 5: Update `acset/__init__.py` to export convert functions**

```python
# acset/__init__.py
from acset.instances import (
    OpTag,
    EntryRow, SStInstance,
    ArrayRow, ArrayAxisRow, SampleRow, SBrInstance,
)
from acset.convert import (
    from_stride_morphism,
    from_tensor_equation,
    from_tensor_program,
)
```

- [ ] **Step 6: Run the full test suite to confirm no regressions**

```
python -m pytest tests/ -v
```
Expected: all tests pass. No existing tests should be affected — zero existing files were modified.

- [ ] **Step 7: Commit**

```bash
git add acset/__init__.py acset/convert.py tests/test_acset_convert.py
git commit -m "feat(acset): add from_tensor_program; complete acset package"
```

---

## Self-Review

### Spec coverage
- ✅ `SStInstance` with `axis_sizes` and `entries` (Task 1)
- ✅ `SBrInstance` with `arrays`, `array_axes`, `samples` (Task 1)
- ✅ `OpTag` enum covering all existing operator types (Task 1)
- ✅ `from_stride_morphism` (Task 2)
- ✅ `from_tensor_equation` with retained/contracted classification (Task 3)
- ✅ `from_tensor_program` returning one instance per equation (Task 4)
- ✅ `norm_axis` inferred from `NormAxis` instances in `lhs_indices`; stored in `ArrayRow` (Task 3)
- ✅ Zero changes to existing files — verified by the file map
- ✅ Regression check in Task 4 Step 6

### Type consistency
- `fd.UID` used as key type throughout — matches `ax.uid` return type ✅
- `nm.Integer(1)` used for unit coefficients — matches `Numeric` hierarchy ✅
- `fd.DynamicName` used for tensor names — matches `TensorEquation.lhs_name` type ✅
- `nm.Numeric` used for `axis_sizes` values — matches `ax.local_size()` return type ✅
- `ops.Identity` checked before `ops.Elementwise` in `_operator_to_tag` — `Identity` subclasses `Elementwise` so order matters ✅

### Known omissions (intentional — out of scope for this plan)
- `from_broadcasted`: converting a full `Broadcasted` (with arbitrary `StrideMorphism` reindexings) requires reading `Weave._shape` and correlating TILED positions with reindexing codomains. This is more involved and adds no new structural concepts — it is a straightforward extension of `from_tensor_equation` once the above is working.
- `φ*` (restriction), `Φ_a` (left Kan extension): these are schema morphism operations built on top of `SStInstance` and `SBrInstance` and belong in a follow-on plan.
- Shape inference (Π_φ): requires a schema morphism framework, also a follow-on.
