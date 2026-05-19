"""Semantic axis-type annotations for downstream tooling (acset conversion, renderers, etc.).

These classes are treated identically to RawAxis by bc_signature() and to_morphism();
the distinction is available for isinstance checks in convert.py and rendering code.
"""
from __future__ import annotations
from dataclasses import dataclass

import data_structure.StrideCategory as sc


@dataclass(frozen=True)
class NormAxis(sc.RawAxis):
    """Marks the normalisation dimension (e.g. softmax axis)."""


@dataclass(frozen=True)
class NatAxis(sc.RawAxis):
    """Marks a natural-number (ℕ) index dimension."""


@dataclass(frozen=True)
class PredAxis(sc.RawAxis):
    """Marks a predicate (Boolean-filter) index dimension."""
