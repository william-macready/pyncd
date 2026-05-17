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
    src:   fd.UID
    tgt:   fd.UID
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
    operator_tag: OpTag | None


@dataclass
class ArrayAxisRow:
    array_name: fd.DynamicName | None
    axis_uid:   fd.UID
    is_target:  bool


@dataclass
class SampleRow:
    src_uid:       fd.UID
    tgt_uid:       fd.UID
    coeff:         nm.Numeric
    reindexing_of: fd.DynamicName | None


@dataclass
class SBrInstance:
    """Acset instance for one TensorEquation."""
    axis_sizes:  dict[fd.UID, nm.Numeric] = field(default_factory=dict)
    arrays:      list[ArrayRow]           = field(default_factory=list)
    array_axes:  list[ArrayAxisRow]       = field(default_factory=list)
    samples:     list[SampleRow]          = field(default_factory=list)
