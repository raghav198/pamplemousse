from __future__ import annotations

from typing import TYPE_CHECKING, Callable
from arguments import Argument
from props import *

if TYPE_CHECKING:
    from proof import Line


def unify(p: Prop, q: Prop, subst: dict[str, Prop]) -> bool:
    if PropVar in (type(p), type(q)):
        if type(p) is PropVar:
            var, exp = p.name, q
        else:
            assert type(q) is PropVar # mypy
            var, exp = q.name, p
            
        if var in subst:
            return subst[var] == exp
        
        subst[var] = exp
        return True
    
    match p, q:
        case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
            return unify(a, c, subst) and unify(b, d, subst)
        case PropVar(a), PropVar(b):
            assert False, 'Whoops! I need to implement this :)'
        case (True, True) | (False, False):
            return True
        case BaseProp(a), BaseProp(b):
            return a == b
        case _:
            return False
        
def diff_tree(p: Prop, q: Prop) -> tuple[Prop, Prop]:
    match p, q:
        case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
            if a != c and b != d:
                return p, q
            if a == c:
                return diff_tree(b, d)
            if b == d:
                return diff_tree(a, c)
            assert False, f'{p} == {q}!'
        case _:
            return p, q
        
def try_rewrite(transformation, rule):
    if transformation[0] == transformation[1]:
        return {}
    old_t, new_t = diff_tree(*transformation)
    old_r, new_r = rule
    
    def rewrite():
        subst = {}
        assert unify(old_t, old_r, subst) and unify(new_t, new_r, subst), f'Failed to apply rule {old_r} <=> {new_r} to {transformation[0]} => {transformation[1]}!'
        return subst
    
    try:
        return rewrite()
    except AssertionError:
        old_r, new_r = new_r, old_r
        return rewrite()

    
def make_argument(rule: tuple[Prop, Prop], name: str) -> Callable[[Line], Argument]:
    class RW(Argument):
        def __init__(self, old: Line) -> None:
            self.old = old
            
        def typecheck(self, new: Prop) -> bool:
            try_rewrite((self.old.typ, new), rule)
            return True
        
        def __repr__(self) -> str:
            return f'{name} {self.old.num}'
            
    return RW

a, b, c = PropVar('a'), PropVar('b'), PropVar('c')

# comm
or_comm = Or(a, b), Or(b, a)
and_comm = And(a, b), And(b, a)

# assoc
or_assoc = Or(Or(a, b), c), Or(a, Or(b, c))
and_assoc = And(And(a, b), c), And(a, And(b, c))

double_neg = a, Imp(Imp(a, False), False)

OrComm = make_argument(or_comm, 'comm')
AndComm = make_argument(and_comm, 'comm')
OrAssoc = make_argument(or_assoc, 'assoc')
AndAssoc = make_argument(and_assoc, 'assoc')
DoubleNeg = make_argument(double_neg, 'dn')

# A, B, C, D = BaseProp('A'), BaseProp('B'), BaseProp('C'), BaseProp('D')

# old = Imp(And(A, And(B, C)), D)
# new = Imp(And(And(A, B), C), D)

# try:
#     print(try_rewrite((old, new), or_assoc))
# except AssertionError as e:
#     print(e)