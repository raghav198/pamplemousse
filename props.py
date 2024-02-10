# This file defines the core logical proposition types and operations for use in logical proofs.

from __future__ import annotations
from dataclasses import dataclass
from typing import Literal, Union


### These form the type tree ###

# Base proposition class with a simple name attribute.
@dataclass(eq=True, frozen=True)
class BaseProp:
    name: str

    def __repr__(self) -> str:
        return self.name


# Represents a variable or placeholder within propositions.
@dataclass(eq=True, frozen=True)
class PropHole:
    name: str

    def __repr__(self) -> str:
        return f"?{self.name}"

# Logical AND connective, combining two propositions.
@dataclass(eq=True, frozen=True)
class And:
    p: Prop # Left proposition
    q: Prop # Right proposition

    def __repr__(self) -> str:
        return rf"({self.p} /\ {self.q})"


# Logical OR connective, combining two propositions.
@dataclass(eq=True, frozen=True)
class Or:
    p: Prop
    q: Prop

    def __repr__(self) -> str:
        return rf"({self.p} \/ {self.q})"

# Logical implication, representing "if p then q".
@dataclass(eq=True, frozen=True)
class Imp:
    p: Prop # Antecedent proposition
    q: Prop # Consequent proposition

    def __repr__(self) -> str:
        if self.q == False:
            return f"~{self.p}"
        return f"({self.p} -> {self.q})"


# Predicate base type
@dataclass(eq=True, frozen=True)
class ModelRef:
    name: str

    def __repr__(self):
        return self.name


# Predicate variable or placeholder 
@dataclass(eq=True, frozen=True)
class ModelRefHole:
    name: str

    def __repr__(self) -> str:
        return f"?{self.name}"

# Represents a predicate with a name and a tuple of arguments.
@dataclass(eq=True, frozen=True)
class Predicate:
    name: BaseProp          # Name of the predicate
    args: tuple[ModelRef]   # Arguments of the predicate

    def __repr__(self) -> str:
        return f'{self.name}({", ".join(map(repr, self.args))})'


# Universal quantifier, representing "for all".
@dataclass(eq=True, frozen=True)
class ForAll:
    var: Union[ModelRef, ModelRefHole] # The variable being quantified
    formula: Prop # The proposition under quantification

    def __repr__(self) -> str:
        return f"(forall {self.var}, {self.formula})"


# Existential quantifier, representing "there exists".
@dataclass(eq=True, frozen=True)
class Exists:
    var: Union[ModelRef, ModelRefHole] # The variable being quantified
    formula: Prop                      # The proposition under quantification

    def __repr__(self) -> str:
        return f"(exists {self.var}, {self.formula})"


# Defines a NOT operation as an implication towards False.
def Not(p: Prop) -> Prop:
    return Imp(p, False)

# Union type for all proposition types, facilitating type checking.
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

### These are type check actions on the type system ###
# The latter part of the props.py file defines a series of functions for
# logical operations and type checking within the logical proof system. These
# functions are designed to:

# - Apply and compose implications: Determine how one logical statement can
# lead to another, either directly or through composition.  
# 
# - Project: Extract specific components of a compound logical statement.  
#
# - Inject: Create new logical statements by combining existing ones.  
#
# - Handle diagonals and codiagonals: Work with propositions that are repeated
# in logical structures or need simplification.  
#
# - Combine and differentiate implications: Based on shared antecedents or
# consequents, showing the system's ability to manipulate and reason about
# complex logical relationships.

# These operations are essential for the manipulation and analysis of logical
# propositions, allowing the system to verify, simplify, and derive logical
# conclusions from given premises. They provide the foundational logic needed
# to support a wide range of reasoning tasks within the proof system.

# Apply function: Attempts to apply an implication.
def apply(f: Prop, x: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert f.p == x, f"Implication expects {f.p}, got {x}!"
    return f.q

# Compose function: Composes two implications.
def compose(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.q == g.p, f"Cannot compose {f} and {g}, since {f.q} != {g.p}!"

    # Returns a new implication from the antecedent of f to the consequent of g.
    return Imp(f.p, g.q)


# a or b |- a ?
# Project Left function: Extracts the left part of a conjunction.
def proj_L(p: Prop) -> Prop:
    assert isinstance(p, And), f"{p} is not a conjunction!"
    return p.p


# a or b |- b ?
# Project Right function: Extracts the right part of a conjunction.
def proj_R(p: Prop) -> Prop:
    assert isinstance(p, And), f"{p} is not a conjunction!"
    return p.q

# Inject Left function: Creates a disjunction with the proposition on the left.
def inj_L(p: Prop, q: Prop) -> Prop:
    return Or(p, q)


# Inject Right function: Creates a disjunction with the proposition on the right.
def inj_R(p: Prop, q: Prop) -> Prop:
    return Or(q, p)

# Diagonal function: Creates a conjunction of a proposition with itself.
def diag(p: Prop) -> Prop:
    return And(p, p)


# Co-diagonal function: Simplifies a disjunction where both parts are the same.
def codiag(p: Prop) -> Prop:
    assert isinstance(p, Or), f"{p} is not a sum type!"
    assert p.p == p.q, f"No codiagonal out of {p}!"
    return p.p

# Universal Product function: Combines two implications sharing the same antecedent.
def univ_prod(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.p == g.p, f"Domains of {f} and {g} do not match!"
    return Imp(f.p, And(f.q, g.q))


# Universal Coproduct function: Creates an implication from a disjunction of antecedents to a common consequent.
def univ_coprod(f: Prop, g: Prop) -> Prop:
    assert isinstance(f, Imp), f"{f} is not an implication!"
    assert isinstance(g, Imp), f"{g} is not an implication!"
    assert f.q == g.q, f"Codomains of {f} and {g} do not match!"
    return Imp(Or(f.p, g.p), f.q)


# Inspect Not function: Identifies the proposition negated by an implication to False.
def inspect_not(p: Prop) -> Prop:
    assert isinstance(p, Imp) and p.q is False, f"{p} is not a negation!"
    return p.p
