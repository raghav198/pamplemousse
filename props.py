from __future__ import annotations
from dataclasses import dataclass
from typing import Literal, Union


@dataclass(eq=True, frozen=True)
class BaseProp:
    name: str

    def __repr__(self) -> str:
        return self.name


# variable
@dataclass(eq=True, frozen=True)
class PropHole:
    name: str

    def __repr__(self) -> str:
        return f"?{self.name}"


@dataclass(eq=True, frozen=True)
class And:
    p: Prop
    q: Prop

    def __repr__(self) -> str:
        return rf"({self.p} /\ {self.q})"


@dataclass(eq=True, frozen=True)
class Or:
    p: Prop
    q: Prop

    def __repr__(self) -> str:
        return rf"({self.p} \/ {self.q})"


@dataclass(eq=True, frozen=True)
class Imp:
    p: Prop
    q: Prop

    def __repr__(self) -> str:
        if self.q == False:
            return f"~{self.p}"
        return f"({self.p} -> {self.q})"


# these go to predicates
@dataclass(eq=True, frozen=True)
class ModelRef:
    name: str

    def __repr__(self):
        return self.name


# these go to predicates
@dataclass(eq=True, frozen=True)
class ModelRefHole:
    name: str

    def __repr__(self) -> str:
        return f"?{self.name}"


@dataclass(eq=True, frozen=True)
class Predicate:
    name: BaseProp
    args: tuple[ModelRef]

    def __repr__(self) -> str:
        return f'{self.name}({", ".join(map(repr, self.args))})'


@dataclass(eq=True, frozen=True)
class ForAll:
    var: Union[ModelRef, ModelRefHole]
    formula: Prop

    def __repr__(self) -> str:
        return f"(forall {self.var}, {self.formula})"


@dataclass(eq=True, frozen=True)
class Exists:
    var: Union[ModelRef, ModelRefHole]
    formula: Prop

    def __repr__(self) -> str:
        return f"(exists {self.var}, {self.formula})"


def Not(p: Prop) -> Prop:
    return Imp(p, False)


Prop = Union[
    BaseProp,
    PropHole,
    ModelRef,
    ModelRefHole,
    And,
    Or,
    Imp,
    ForAll,
    Exists,
    Literal[True],
    Literal[False],
]


# A -> B
def apply(f: Prop, x: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert f.p == x, f"Implication expects {f.p}, got {x}!"
    return f.q


def compose(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.q == g.p, f"Cannot compose {f} and {g}, since {f.q} != {g.p}!"
    return Imp(f.p, g.q)


# example a or b |- a
def proj_L(p: Prop) -> Prop:
    assert isinstance(p, And), f"{p} is not a conjunction!"
    return p.p


def proj_R(p: Prop) -> Prop:
    assert isinstance(p, And), f"{p} is not a conjunction!"
    return p.q


def inj_L(p: Prop, q: Prop) -> Prop:
    return Or(p, q)


def inj_R(p: Prop, q: Prop) -> Prop:
    return Or(q, p)


def diag(p: Prop) -> Prop:
    return And(p, p)


def codiag(p: Prop) -> Prop:
    assert isinstance(p, Or), f"{p} is not a sum type!"
    assert p.p == p.q, f"No codiagonal out of {p}!"
    return p.p


def univ_prod(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.p == g.p, f"Domains of {f} and {g} do not match!"
    return Imp(f.p, And(f.q, g.q))


def univ_coprod(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.q == g.q, f"Codomains of {f} and {g} do not match!"
    return Imp(Or(f.p, g.p), f.q)


def inspect_not(p: Prop) -> Prop:
    assert isinstance(p, Imp) and p.q is False, f"{p} is not a negation!"
    return p.p
