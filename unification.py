from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Dict, Set

from props import *

if TYPE_CHECKING:
    from proof import Line

# The unification function attempts to determine if two propositions (p and q) can be made identical
# through substitution. It takes two propositions and two dictionaries:
# subst, which maps variable names in propositions to propositions, and
# var_subst, which is intended for model-specific substitutions.
# Returns True if the propositions can be unified under the given substitutions, False otherwise.
def unify(
    p: Prop, q: Prop, subst: Dict[str, Prop] = {}, var_subst: Dict[str, ModelRef] = {}
) -> bool:

    # Handle the case where either p or q is a PropHole (a placeholder for a proposition)
    if PropHole in (type(p), type(q)):

        # Determine which of p or q is the PropHole and set the other as the expression to substitute
        if type(p) is PropHole:
            hole, exp = p.name, q   # if p is the placeholder, q is the expression
        else:
            assert type(q) is PropHole  
            hole, exp = q.name, p   # if q is the placeholder, p is the expression

        # If the placeholder already has a substitution, check if it matches the current expression
        if hole in subst:
            return subst[hole] == exp # True if the substitution is consistent, False otherwise

        # Assign the expression to the placeholder in subst and return True
        subst[hole] = exp
        return True

    # Similar case as before, but for predicates
    if ModelRefHole in (type(p), type(q)):
        if type(p) is ModelRefHole:
            hole, exp = p.name, q
        else:
            assert type(q) is ModelRefHole
            hole, exp = q.name, p

        if not (type(exp) is ModelRef):
            return False

        if hole in var_subst:
            return var_subst[hole] == exp

        var_subst[hole] = exp
        return True

    ### After variables are resolved, case match recursively.
    #
    # match p, q:
    #     case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
    #         return unify(a, c, subst) and unify(b, d, subst)
    #     case PropVar(a), PropVar(b):
    #         assert False, 'Whoops! I need to implement this :)'
    #     case (True, True) | (False, False):
    #         return True
    #     case BaseProp(a), BaseProp(b):
    #         return a == b
    #     case _:
    #         return False

    ### This code follows the above pseudocode 
    if (
        (isinstance(p, And) and isinstance(q, And))
        or ((isinstance(p, Or) and isinstance(q, Or)))
        or ((isinstance(p, Imp) and isinstance(q, Imp)))
    ):
        return unify(p.p, q.p, subst, var_subst) and unify(p.q, q.q, subst, var_subst)
    elif isinstance(p, PropHole) and isinstance(q, PropHole):
        assert False, "Whoops! I need to implement this :)"
    elif isinstance(p, bool) and isinstance(q, bool):
        return p == q
    elif (isinstance(p, BaseProp) and isinstance(q, BaseProp)) or (
        isinstance(p, ModelRef) and isinstance(q, ModelRef)
    ):
        return p.name == q.name
    elif (isinstance(p, ForAll) and isinstance(q, ForAll)) or (
        isinstance(p, Exists) and isinstance(q, Exists)
    ):
        return unify(p.var, q.var, subst, var_subst) and unify(
            p.formula, q.formula, subst, var_subst
        )
    elif isinstance(p, Predicate) and isinstance(q, Predicate):
        return (
            p.name == q.name
            and len(p.args) == len(q.args)
            and all(unify(xp, xq) for xp, xq, in zip(p.args, q.args))
        )
    else:
        assert type(p) != type(q)
        return False


def diff_tree(p: Prop, q: Prop) -> tuple[Prop, Prop]:
    # Compares two propositions and identifies their differences.
    # Returns a tuple of the differing parts of the propositions.

    # Handles compound logical expressions (And, Or, Imp) by checking if both propositions
    # are of the same type and then recursively identifying differences in their components.
    if (
        (isinstance(p, And) and isinstance(q, And))
        or ((isinstance(p, Or) and isinstance(q, Or)))
        or ((isinstance(p, Imp) and isinstance(q, Imp)))
    ):
        # If both components of the propositions are different, return the propositions as is.
        if p.p != q.p and p.q != q.q:
            return p, q
        # If the left components are equal, recurse on the right components.
        if p.p == q.p:
            return diff_tree(p.q, q.q)
        # If the right components are equal, recurse on the left components.
        if p.q == q.q:
            return diff_tree(p.p, q.p)
        # Assert failure if propositions are considered equal but shouldn't be; likely a logic error.
        assert False, f"{p} == {q}"

    # Handles quantified expressions (ForAll, Exists) by comparing the bound variable
    # and recursively comparing the formula if the variables are the same.
    elif (isinstance(p, ForAll) and isinstance(q, ForAll)) or (
        isinstance(p, Exists) and isinstance(q, Exists)
    ):
        if p.var == q.var:
            return diff_tree(p.formula, q.formula)
        return p, q

    # Handles predicates by directly asserting they are not equal if they are of the same type.
    # Returns the propositions as differing if the assertion doesn't fail.
    elif isinstance(p, Predicate) and isinstance(q, Predicate):
        assert p != q, f"{p} == {q}"
        return p, q

    # For all other cases, return the propositions as is, indicating they differ.
    else:
        return p, q

    ### simplified match case pseudocode
    # match p, q:
    #     case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
    #         if a != c and b != d:
    #             return p, q
    #         if a == c:
    #             return diff_tree(b, d)
    #         if b == d:
    #             return diff_tree(a, c)
    #         assert False, f'{p} == {q}!'
    #     case _:
    #         return p, q


def try_rewrite(transformation, rule):
    # Attempts to apply a transformation rule to a given transformation of propositions.
    # transformation: A tuple of two propositions indicating the original and the intended transformation.
    # rule: A tuple of two propositions representing the rule for rewriting.
    
    # Check if the transformation is trivial (no change), returning an empty substitution if so.
    if transformation[0] == transformation[1]:
        return {}

    # Use diff_tree to identify the specific components of the transformation and rule that differ.
    old_t, new_t = diff_tree(*transformation)
    old_r, new_r = rule

    def rewrite():

        # Initialize dictionaries for substitutions.
        subst = {}
        var_subst = {}

        # Assert that the old and new components of both the transformation and rule can be unified.
        # If unification fails, it indicates the rule cannot be applied, raising an AssertionError.
        assert unify(old_t, old_r, subst, var_subst) and unify(
            new_t, new_r, subst, var_subst
        ), f"Failed to apply rule {old_r} <=> {new_r} to {transformation[0]} => {transformation[1]}!"
        return subst, var_subst

    try:
        # Attempt the rewrite. Return the substitution results if successful.
        return rewrite()
    except AssertionError:

        # If the initial rewrite attempt fails, swap the rule components and try again.
        old_r, new_r = new_r, old_r
        return rewrite()


def alpha_renaming(
    orig: Prop, new: Prop, orig_var: ModelRef, subst: Dict[ModelRef, ModelRef] = {}
):
    # Performs alpha renaming on propositions to ensure variable names are consistent.
    # orig: The original proposition.
    # new: The proposition after some transformation.
    # orig_var: The original variable to be renamed.
    # subst: A dictionary for tracking substitutions made during the renaming process.
    
    # Assert that the original and new propositions are of the same type, which is a prerequisite for renaming.
    assert type(orig) == type(
        new
    ), "Statements differ in more than just variable names!"
    if (
        (isinstance(orig, And) and isinstance(new, And))
        or (isinstance(orig, Or) and isinstance(new, Or))
        or (isinstance(orig, Imp) and isinstance(new, Imp))
    ):
        alpha_renaming(orig.p, new.p, orig_var, subst)
        alpha_renaming(orig.q, new.q, orig_var, subst)
    elif (isinstance(orig, ForAll) and isinstance(new, ForAll)) or (
        isinstance(orig, Exists) and isinstance(new, Exists)
    ):
        assert (
            orig.var == new.var
        ), "Statements differ in more than just variable names!"
        if orig_var in subst:
            assert (
                subst[orig_var] != new.var
            ), "Cannot instantiate into a quantified variable!"
        alpha_renaming(orig.formula, new.formula, orig_var, subst)
    elif isinstance(orig, Predicate) and isinstance(new, Predicate):
        assert (
            orig.name == new.name
        ), "Statements differ in more than just variable names!"
        assert len(orig.args) == len(
            new.args
        ), "Statements differ in more than just variable names!"
        for orig_arg, new_arg in zip(orig.args, new.args):
            if orig_arg == orig_var:
                if orig_var not in subst:
                    subst[orig_var] = new_arg
                assert (
                    subst[orig_var] == new_arg
                ), f"Ambiguous substitution: [{orig_var} -> {subst[orig_var]}, {new_arg}]"


def formula_uses(formula: Prop, var_name: ModelRef):
    # Determines if a given variable (var_name) is used within a logical formula.
    # This function recursively traverses the formula to check for the presence of the variable.

    # For compound logical expressions (And, Or, Imp), recursively check both sides of the expression.
    if isinstance(formula, And) or isinstance(formula, Or) or isinstance(formula, Imp):
        return formula_uses(formula.p, var_name) or formula_uses(formula.q, var_name)

    # For quantified expressions (ForAll, Exists), check if the variable is the bound variable
    # or if it is used within the quantified formula.
    elif isinstance(formula, ForAll) or isinstance(formula, Exists):
        return formula.var == var_name or formula_uses(formula.formula, var_name)

    # For predicates, check if the variable is among the predicate's arguments.
    elif isinstance(formula, Predicate):
        return var_name in formula.args

    # If none of the above cases apply, return False indicating the variable is not used in the formula.
    return False


def get_symbols(formula: Prop) -> tuple[Set[ModelRef], Set[ModelRef]]:
    # Extracts and returns two sets of symbols from a logical formula: one for proposition symbols
    # and another for variable symbols. This can be useful for identifying all the unique elements
    # within a formula.

    # Handles compound logical expressions by recursively gathering symbols from both sides.
    if isinstance(formula, And) or isinstance(formula, Or) or isinstance(formula, Imp):

        # Recursively get symbols for left and right sides of the compound expression.
        # This accounts for complex nested structures within the logical formula.
        lsym, lvar = get_symbols(formula.p) # Left side symbols
        rsym, rvar = get_symbols(formula.q) # Right side symbols

        return lsym | rsym, lvar | rvar     # Union of left and right side symbols

    # For quantified expressions (ForAll, Exists), the bound variable is explicitly included in both sets.
    # This acknowledges the variable's presence in the formula, important for both sets' completeness.
    elif isinstance(formula, ForAll) or isinstance(formula, Exists):
        assert isinstance(formula.var, ModelRef)
        sym, var = get_symbols(formula.formula)  # Recursively extract symbols from the quantified formula.
        return sym | {formula.var}, var | {formula.var} # Include the bound variable
    
    # For predicates, arguments are directly treated as symbols, but only added to the first set.
    elif isinstance(formula, Predicate):
        return set(formula.args), set()

    # If the formula doesn't match any of the above types, empty sets are returned.
    # This case handles simple propositions or other forms not requiring symbol extraction.
    return set(), set()


class Argument:
    # The Argument class serves as a base class for various logical arguments within the system.
    # Its primary role is to provide a common interface for verifying arguments based on a line of proof and a set of constants.

    def verify(self, line: Line, constants: Set[ModelRef]):
        # Calls typecheck with the type of the line as an argument.
        # This method is intended to be overridden in subclasses where specific verification logic is implemented.
        return self.typecheck(line.typ)

    def typecheck(self, _: Prop) -> bool:
        # Placeholder method for type checking, to be implemented by subclasses.
        # Raises NotImplemented error indicating it needs to be overridden.
        raise NotImplemented


def make_argument(rule: tuple[Prop, Prop], name: str) -> Callable[[Line], Argument]:
    # Factory function to create argument instances based on a rewriting rule.
    # This allows for dynamic creation of argument types based on logical rules defined elsewhere in the system.

    class RW(Argument):
        # Nested class within make_argument, represents a rewrite argument derived from the Argument base class.
        # This class is specific to implementing a type of logical argument that involves rewriting propositions.

        def __init__(self, old: Line) -> None:
            # Initializes the RW argument with a reference to an existing line of proof (old).
            self.old = old

        def typecheck(self, new: Prop) -> bool:
            # Implements the typecheck method to verify the new proposition against the old one using the provided rule.
            # The try_rewrite function is called with the old and new propositions alongside the rule, determining if the rewrite is valid.
            try_rewrite((self.old.typ, new), rule)
            return True

        def __repr__(self) -> str:
            return f"{name} {self.old.num}"

    return RW


a, b, c = PropHole("a"), PropHole("b"), PropHole("c")

# comm
or_comm = Or(a, b), Or(b, a)
and_comm = And(a, b), And(b, a)

# assoc
or_assoc = Or(Or(a, b), c), Or(a, Or(b, c))
and_assoc = And(And(a, b), c), And(a, And(b, c))

# double negation
double_neg = a, Imp(Imp(a, False), False)

# contrapositive
cp = Imp(a, b), Imp(Not(b), Not(a))

# implication equivalence
impl_equiv = Imp(a, b), Or(Not(a), b)

# distributivity
distr_and_or = And(a, Or(b, c)), Or(And(a, b), And(a, c))
distr_or_and = Or(a, And(b, c)), And(Or(a, b), Or(a, c))

# demorgan's laws
demorgan_and_or = Not(And(a, b)), Or(Not(a), Not(b))
demorgan_or_and = Not(Or(a, b)), And(Not(a), Not(b))

# self
self_or = a, Or(a, a)
self_and = a, And(a, a)

# exportation
exp = Imp(a, Imp(b, c)), Imp(And(a, b), c)

# quantified demorgan's laws
x, y, z = ModelRefHole("x"), ModelRefHole("y"), ModelRefHole("z")
demorgan_forall_exists = Not(ForAll(x, a)), Exists(x, Not(a))
demorgan_exists_forall = Not(Exists(x, a)), ForAll(x, Not(a))

# alpha equivalence


# turn these all into arguments
OrComm = make_argument(or_comm, "comm")
AndComm = make_argument(and_comm, "comm")
OrAssoc = make_argument(or_assoc, "assoc")
AndAssoc = make_argument(and_assoc, "assoc")
DoubleNeg = make_argument(double_neg, "dn")
ImplEquiv = make_argument(impl_equiv, "impl")
DistribAndOr = make_argument(distr_and_or, "dist")
DistribOrAnd = make_argument(distr_or_and, "dist")
DemorganAndOr = make_argument(demorgan_and_or, "dm")
DemorganOrAnd = make_argument(demorgan_or_and, "dm")
DemorganForallExists = make_argument(demorgan_forall_exists, "dm")
DemorganExistsForall = make_argument(demorgan_exists_forall, "dm")
Exportation = make_argument(exp, "exp")
Contrapositive = make_argument(cp, "cp")
SelfOr = make_argument(self_or, "self_or")
SelfAnd = make_argument(self_and, "self_and")

__all__ = [
    "Argument",
    "OrComm",
    "AndComm",
    "OrAssoc",
    "AndAssoc",
    "DoubleNeg",
    "ImplEquiv",
    "DistribAndOr",
    "DistribOrAnd",
    "DemorganAndOr",
    "DemorganOrAnd",
    "DemorganForallExists",
    "DemorganExistsForall",
    "Exportation",
    "Contrapositive",
    "SelfOr",
    "SelfAnd",
]


# A, B, C, D = BaseProp('A'), BaseProp('B'), BaseProp('C'), BaseProp('D')

# old = Imp(And(A, And(B, C)), D)
# new = Imp(And(And(A, B), C), D)

# try:
#     print(try_rewrite((old, new), or_assoc))
# except AssertionError as e:
#     print(e)
