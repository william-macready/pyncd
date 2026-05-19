"""Acset instance dataclasses for St (stride) and Br (broadcasted) morphisms."""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum

import data_structure.Term as fd
import data_structure.Numeric as nm


class OpTag(Enum):
    """Base operation type for an output Array."""
    IDENTITY                  = 'identity'
    SOFTMAX                   = 'softmax'
    ELEMENTWISE               = 'elementwise'
    NORMALIZE                 = 'normalize'
    EMBEDDING                 = 'embedding'
    ADDITION_OP               = 'addition'
    WEIGHTED_TRIANGULAR_LOWER = 'weighted_triangular_lower'
    LINEAR                    = 'linear'


class DataTag(Enum):
    """Scalar datatype of an Array: continuous reals or discrete naturals."""
    REALS   = 'reals'
    NATURAL = 'natural'


@dataclass
class EntryRow:
    """One nonzero coefficient in a stride morphism's coefficient matrix."""
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
    """One tensor (input or output) in a Broadcasted morphism."""
    name:            fd.DynamicName | None
    is_input:        bool
    operator_tag:    OpTag | None
    norm_axis:       fd.UID | None     = None
    datatype_tag:    DataTag           = DataTag.REALS
    max_value:       nm.Numeric | None = None
    bias:            bool | None       = None
    elementwise_fn:  str | None        = None


@dataclass
class ArrayAxisRow:
    """One axis belonging to one Array, with its role and physical position."""
    array_name: fd.DynamicName | None
    axis_uid:   fd.UID
    is_target:  bool
    position:   int = 0


@dataclass
class SampleRow:
    """One component of the reindexing rule for one input Array."""
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
