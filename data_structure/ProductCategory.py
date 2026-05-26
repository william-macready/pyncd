from __future__ import annotations
from dataclasses import dataclass, field
from typing import (
    Any,
    Self,
    Type,
    TypeVar,
    Callable,
    Iterable,
    Iterator,
    overload,
    Sequence,
    Iterable,
)
import random
import math
from abc import ABC
from enum import Enum
import data_structure.Numeric as nm

import data_structure.Term as fd # for 'foundations'
import utilities.utilities as util

L = TypeVar('L', covariant=True)

type ProdCategory[L, M:Morphism] = \
    (M | Rearrangement[L]
     | Composed[L, ProdCategory[L, M]]
     | ProductOfMorphisms[L, ProdCategory[L, M]]
     | Block[L, ProdCategory[L, M]]
    )

@dataclass(frozen=True)
class ProdObject[L](fd.Term):
    content: fd.Prod[L] = ()

    def identity(self) -> Rearrangement[L]:
        return Rearrangement(
            mapping=tuple(range(len(self.content))), 
            _dom=self.content
        )

    # Conveniances
    @classmethod
    def from_iter(cls, xs: Iterable[L]) -> ProdObject[L]:
        return cls(content=tuple(xs))

    def __iter__(self) -> Iterator[L]:
        return iter(self.content)
    def __len__(self) -> int:
        return len(self.content)
    @overload
    def __getitem__(self, index: slice) -> fd.Prod[L]: ...
    @overload
    def __getitem__(self, index: int) -> L: ...
    def __getitem__(self, index: int | slice) -> L | fd.Prod[L]:
        return self.content[index]
    
@dataclass(frozen=True)
class Morphism[L](fd.Term, ABC):
    def dom(self) -> ProdObject[L]:
        raise NotImplementedError()
    def cod(self) -> ProdObject[L]:
        raise NotImplementedError()
    
    # Conveniances
    def __matmul__[M:Morphism](self,
            other: ProdCategory[L, M] | fd.Prod[int]) -> ProdCategory[L, M]:
        raise NotImplementedError()
    def __rmatmul__[M:Morphism](self, 
            other: ProdCategory[L, M] | fd.Prod[int]) -> ProdCategory[L, M]:
        raise NotImplementedError()
    def __mul__[M:Morphism](self, other: M | ProdObject[L] | L) -> ProdCategory[L, M]:
        raise NotImplementedError()
    def __rrshift__(self, other) -> Self:
        raise NotImplementedError()
    
@dataclass(frozen=True)
class BlockAesthetics(fd.Term):
    title:       str | None = None
    description: str | None = None
    fill_color:  str | None = None

@dataclass(frozen=True)
class BlockTag(fd.UTerm):
    repetition: nm.Numeric = nm.Integer(1)
    aesthetics: BlockAesthetics | None = None

@dataclass(frozen=True)
class Block[L, M: Morphism](Morphism[L]):
    body: M
    block_tag: BlockTag = BlockTag()
    def dom(self) -> ProdObject[L]:
        return self.body.dom()
    def cod(self) -> ProdObject[L]:
        return self.body.cod()
    @classmethod
    def template(cls, 
                 target: M,
                 title: str | None = None,
                 description: str | None = None,
                 fill_color: str | None = None,
                 repetition: int | nm.Numeric = 1) -> Block[L, M]:
        return Block(
            body=target,
            block_tag=BlockTag(
                repetition=nm.Integer(repetition) if isinstance(repetition, int) else repetition,
                aesthetics=BlockAesthetics(
                    title=title,
                    description=description,
                    fill_color=fill_color
                )
            )
        )
    @property
    def aesthetics(self) -> BlockAesthetics | None:
        return self.block_tag.aesthetics
    @property
    def repetition(self) -> nm.Numeric:
        return self.block_tag.repetition

@dataclass(frozen=True)
class Composed[L, M: Morphism](Morphism[L]):
    content: fd.Prod[M] = ()
    def dom(self) -> ProdObject[L]:
        return self.content[0].dom()
    def cod(self) -> ProdObject[L]:
        return self.content[-1].cod()
    
    # Conveniances
    @classmethod
    def from_iter(cls, xs: Iterable[M]) -> Composed[L, M]:
        return cls(content=tuple(xs))

@dataclass(frozen=True)
class ThreadedComposed[L, M: Morphism](Morphism[L]):
    """Composed morphism with explicit per-step input routing.

    Produced by TensorProgram.to_morphism() / TL.to_morphism() when external
    tensors are shared across multiple equations. routing[i][j] is the
    live-pool index for input slot j of step i.

    Live pool: indices 0..n_external-1 are initial caller inputs; index
    n_external+i is the output of step i.
    """
    content: fd.Prod[M] = ()
    routing: fd.Prod[fd.Prod[int]] = ()
    n_external: int = 0

    def dom(self) -> ProdObject[L]:
        external_types: list = [None] * self.n_external
        for step_morph, route in zip(self.content, self.routing):
            dom = step_morph.dom()
            for slot, live_idx in enumerate(route):
                if live_idx < self.n_external and external_types[live_idx] is None:
                    external_types[live_idx] = dom[slot]
        return ProdObject(tuple(external_types))

    def cod(self) -> ProdObject[L]:
        return self.content[-1].cod()


@dataclass(frozen=True)
class ProductOfMorphisms[L, M: Morphism](Morphism[L]):
    content: fd.Prod[M] = ()
    def dom(self) -> ProdObject[L]:
        return ProdObject.from_iter(segment for m in self.content for segment in m.dom())
    def cod(self) -> ProdObject[L]:
        return ProdObject.from_iter(segment for m in self.content for segment in m.cod())
    
    def partition[T](self, target: fd.Prod[T]) -> Iterable[tuple[M, fd.Prod[T]]]:
        start = 0
        for m in self.content:
            end = start + len(m.dom())
            yield (m, target[start:end])
            start = end

    def partition_codomain[T](self, target: fd.Prod[T]) -> Iterable[tuple[M, fd.Prod[T]]]:
        start = 0
        for m in self.content:
            end = start + len(m.cod())
            yield (m, target[start:end])
            start = end

    # Conveniances
    @classmethod
    def from_iter(cls, xs: Iterable[M]) -> ProductOfMorphisms[L, M]:
        return cls(content=tuple(xs))
    def __iter__(self) -> Iterator[M]:
        return iter(self.content)
    
@dataclass(frozen=True)
class Rearrangement[L](Morphism[L]):
    mapping: fd.Prod[int] = ()
    _dom: fd.Prod[L] = ()

    def dom(self) -> ProdObject[L]:
        return ProdObject(self._dom)
    def cod(self) -> ProdObject[L]:
        return ProdObject(self.apply(self._dom))
    # from domain to codomain
    def apply[S](self, target: fd.Prod[S]) -> fd.Prod[S]:
        return tuple(target[i] for i in self.mapping)
    # from codomain to domain
    def invert[S](self, target: fd.Prod[S]) -> fd.Prod[S]:
        return tuple(
            util.iallequals(
                segment 
                for segment, muj in 
                zip(target, self.mapping) if i == muj)
            for i in range(len(self._dom))
        )
    