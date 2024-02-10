# An abstraction layer above props.py and unification.py

from __future__ import annotations
from collections import defaultdict

from typing import TYPE_CHECKING, Callable, Set, Dict, List
from props import *
from unification import *
from unification import alpha_renaming
from unification import formula_uses
from unification import get_symbols

# Conditional imports for type checking, avoiding circular dependencies.
if TYPE_CHECKING:
    from proof import Line, Context

# Implements the Modus Ponens argument: If "P implies Q" and "P" then "Q".
class ModusPonens(Argument):
    def __init__(self, imp: Line, ante: Line) -> None:
        self.imp = imp # The line stating "P implies Q"
        self.ante = ante # The line stating "P"

    def typecheck(self, expected: Prop) -> bool:
        # Verifies that applying the argument to the antecedent yields the expected proposition.
        return apply(self.imp.typ, self.ante.typ) == expected

    def __repr__(self) -> str:
        return f"mp {self.imp.num}, {self.ante.num}"


# Implements the Modus Tollens argument: If "P implies Q" and "not Q" then "not P".
class ModusTollens(Argument):
    def __init__(self, imp: Line, cont: Line) -> None:
        self.imp = imp      # "P implies Q"
        self.cont = cont    # "not Q"

    def typecheck(self, expected: Prop) -> bool:
        # Checks if the contrapositive application is logically valid.
        assert (
            isinstance(self.cont.typ, Imp) and self.cont.typ.q is False
        ), f"{self.cont.num}: {self.cont.typ} is not a negation!"
        return compose(self.imp.typ, self.cont.typ) == expected

    def __repr__(self) -> str:
        return f"{self.imp.num}, {self.cont.num}"


class Simplify(Argument):
    def __init__(self, conj: Line) -> None:
        self.conj = conj

    def typecheck(self, expected: Prop) -> bool:
        return expected in (proj_L(self.conj.typ), proj_R(self.conj.typ))

    def __repr__(self) -> str:
        return f"simp {self.conj.num}"


class Addition(Argument):
    def __init__(self, disj: Line) -> None:
        self.disj = disj

    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(expected, Or), f"{expected} is not a disjunction!"
        return self.disj.typ in (expected.p, expected.q)

    def __repr__(self) -> str:
        return f"add {self.disj.num}"


class HypotheticalSyllogism(Argument):
    def __init__(self, imp1: Line, imp2: Line) -> None:
        self.imp1 = imp1
        self.imp2 = imp2

    def typecheck(self, expected: Prop) -> bool:
        return compose(self.imp1.typ, self.imp2.typ) == expected

    def __repr__(self) -> str:
        return f"hs {self.imp1.num}, {self.imp2.num}"


class DisjunctiveSyllogism(Argument):
    def __init__(self, disj: Line, neg: Line) -> None:
        self.disj = disj
        self.neg = neg

    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(
            self.disj.typ, Or
        ), f"{self.disj.num}: {self.disj.typ} is not a disjunction!"
        assert inspect_not(self.neg.typ) in (self.disj.typ.p, self.disj.typ.q)
        return expected in (self.disj.typ.p, self.disj.typ.q)

    def __repr__(self) -> str:
        return f"ds {self.disj.num}, {self.neg.num}"


class DisjunctiveElimination(Argument):
    def __init__(self, disj: Line, imp1: Line, imp2: Line) -> None:
        self.disj = disj
        self.imp1 = imp1
        self.imp2 = imp2

    def typecheck(self, expected: Prop) -> bool:
        imp = univ_coprod(self.imp1.typ, self.imp2.typ)
        stack = apply(imp, self.disj.typ)
        return stack == expected

    def __repr__(self) -> str:
        return f"de {self.disj.num}, {self.imp1.num}, {self.imp2.num}"


class Hypothesis(Argument):
    def typecheck(self, expected: Prop) -> bool:
        return True

    def __repr__(self) -> str:
        return "hyp"


class Deduction(Argument):
    def __init__(self, hyp: Prop, ded: Set[Prop]) -> None:
        self.hyp = hyp
        self.ded = ded

    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(
            expected, Imp
        ), f"Cannot use deduction rule on `{expected}`, as its not an implication!"
        hyp = expected.p
        ded = expected.q
        assert ded in self.ded, f"Cannot deduce `{ded}` from proof!"
        assert hyp == self.hyp, f"Proof does not take `{hyp}` as its hypothesis!"
        return True


class Conjunction(Argument):
    def __init__(self, p: Line, q: Line) -> None:
        self.p = p
        self.q = q

    def typecheck(self, expected: Prop) -> bool:
        assert (
            And(self.p.typ, self.q.typ) == expected
        ), f"Expected `{expected}`, but got type `{And(self.p.typ, self.q.typ)}`!"
        return True


class Disjunction(Argument):
    def __init__(self, p: Line, q: Line) -> None:
        self.p = p
        self.q = q

    def typecheck(self, expected: Prop) -> bool:
        assert (
            Or(self.p.typ, self.q.typ) == expected
        ), f"Expected `{expected}`, but got type `{Or(self.p.typ, self.q.typ)}`!"
        return True


class UniversalInstantiation(Argument):
    def __init__(self, quant: Line) -> None:
        self.quant = quant

    def verify(self, line: Line, _):
        assert isinstance(
            self.quant.typ, ForAll
        ), "Cannot universally instantiate a formula that is not universally quantified!"
        subst: Dict[ModelRef, ModelRef] = {}
        assert isinstance(
            self.quant.typ.var, ModelRef
        )  # shouldn't be any holes in the proof anyway!
        # check to make sure there's a unique rewrite and you aren't instantiating into a quantified variable
        alpha_renaming(self.quant.typ.formula, line.typ, self.quant.typ.var, subst)
        assert self.quant.typ.var in subst, "Could not determine a unique substitution!"
        if subst[self.quant.typ.var] == self.quant.typ.var or not formula_uses(
            self.quant.typ.formula, subst[self.quant.typ.var]
        ):
            # add this to the set of variables that can be generalized later
            line.variables[subst[self.quant.typ.var].name] = set()
        return True


class UniversalGeneralization(Argument):
    def __init__(self, form: Line) -> None:
        self.form = form

    def verify(self, line: Line, _):
        assert isinstance(
            line.typ, ForAll
        ), "Cannot universally generalize to a formula that is not universally quantified!"
        subst: Dict[ModelRef, ModelRef] = {}
        assert isinstance(
            line.typ.var, ModelRef
        )  # shouldn't be any holes in the proof anyway! ;)
        alpha_renaming(line.typ.formula, self.form.typ, line.typ.var, subst)
        assert line.typ.var in subst, "Could not determine a unique substitution!"
        assert (
            subst[line.typ.var].name in line.variables
        ), f"Cannot generalize `{line.typ.var}`: variable not instantiated!"
        dependents = line.variables[subst[line.typ.var].name].intersection(
            get_symbols(line.typ.formula)[0]
        )
        assert (
            len(dependents) == 0
        ), f"Cannot generalize {line.typ.var}: dependent e.i. variables are still in scope! ({dependents})"
        del line.variables[subst[line.typ.var].name]
        return True


class ExistentialInstantiation(Argument):
    def __init__(self, quant: Line) -> None:
        self.quant = quant

    def verify(self, line: Line, constants: Set[ModelRef]):
        assert isinstance(
            self.quant.typ, Exists
        ), "Cannot existentially instantiate a formula that is not existentially quantified!"

        subst: Dict[ModelRef, ModelRef] = {}
        assert isinstance(
            self.quant.typ.var, ModelRef
        )  # shouldn't be any holes in the proof anyway!
        # check to make sure there's a unique rewrite and you aren't instantiating into a quantified variable
        alpha_renaming(self.quant.typ.formula, line.typ, self.quant.typ.var, subst)
        assert self.quant.typ.var in subst, "Could not determine a unique substitution!"

        # make sure that the instantiated constant is fresh
        assert (
            subst[self.quant.typ.var] not in constants
        ), f"`{subst[self.quant.typ.var]}` is not a fresh constant!"

        # mark a dependence on all ui's currently in scope
        for ui in line.variables:
            line.variables[ui].add(subst[self.quant.typ.var].name)
        return True

    # def verify(self, line: Line):
    #     assert isinstance(self.quant.typ, Exists), 'Cannot existentially instantiate a formula that is not existentially quantified!'
    #     subst: Dict[ModelRef, ModelRef] = {}
    #     assert isinstance(self.quant.typ.var, ModelRef) # shouldn't be any holes in the proof anyway!
    #     # check to make sure there's a unique rewrite and you aren't instantiating into a quantified variable
    #     alpha_renaming(self.quant.typ.formula, line.typ, self.quant.typ.var, subst)
    #     assert self.quant.typ.var in subst, 'Could not determine a unique substitution!'
    #     print(self.quant.typ.formula, subst[self.quant.typ.var])
    #     assert subst[self.quant.typ.var] == self.quant.typ.var or not formula_uses(self.quant.typ.formula, subst[self.quant.typ.var]), \
    #         f'Cannot existentially instantiate to {subst[self.quant.typ.var]}, not a fresh constant!'

    #     for ui in line.variables:
    #         line.variables[ui].add(subst[self.quant.typ.var].name)
    #     return True


class ExistentialGeneralization(Argument):
    def __init__(self, form: Line) -> None:
        self.form = form

    def verify(self, line: Line, _):
        line.variables.update(self.form.variables)
        assert isinstance(
            line.typ, Exists
        ), "Cannot existentially generalize to a formula that is not existentially quantified!"
        subst: Dict[ModelRef, ModelRef] = {}
        assert isinstance(line.typ.var, ModelRef)
        alpha_renaming(line.typ.formula, self.form.typ, line.typ.var, subst)
        assert line.typ.var in subst, "Could not determine a unique substitution!"
        for ui in line.variables:
            line.variables[ui].discard(subst[line.typ.var].name)
        return True


argument_lookup: Dict[str, Callable[[List[Line]], Argument]] = {
    "mp": lambda args: ModusPonens(*args),
    "mt": lambda args: ModusTollens(*args),
    "simpl": lambda args: Simplify(*args),
    "add": lambda args: Addition(*args),
    "hs": lambda args: HypotheticalSyllogism(*args),
    "ds": lambda args: DisjunctiveSyllogism(*args),
    "de": lambda args: DisjunctiveElimination(*args),
    "conj": lambda args: Conjunction(*args),
    "disj": lambda args: Disjunction(*args),
    "hyp": lambda args: Hypothesis(*args),  # type: ignore
    "prem": lambda args: Hypothesis(*args),  # type: ignore
    "or_comm": lambda args: OrComm(*args),
    "and_comm": lambda args: AndComm(*args),
    "or_assoc": lambda args: OrAssoc(*args),
    "and_assoc": lambda args: AndAssoc(*args),
    "dn": lambda args: DoubleNeg(*args),
    "imp": lambda args: ImplEquiv(*args),
    "dist_ao": lambda args: DistribAndOr(*args),
    "dist_oa": lambda args: DistribOrAnd(*args),
    "dm_ao": lambda args: DemorganAndOr(*args),
    "dm_oa": lambda args: DemorganOrAnd(*args),
    "dm_fe": lambda args: DemorganForallExists(*args),
    "dm_ef": lambda args: DemorganExistsForall(*args),
    "exp": lambda args: Exportation(*args),
    "cp": lambda args: Contrapositive(*args),
    "or_self": lambda args: SelfOr(*args),
    "and_self": lambda args: SelfAnd(*args),
    "ei": lambda args: ExistentialInstantiation(*args),
    "eg": lambda args: ExistentialGeneralization(*args),
    "ui": lambda args: UniversalInstantiation(*args),
    "ug": lambda args: UniversalGeneralization(*args),
}


def combine_variable_contexts(ctxs: tuple[Dict[str, Set[str]]]):
    acc: Dict[str, Set[str]] = defaultdict(set)
    for ctx in ctxs:
        for val in ctx:
            acc[val].update(ctx[val])
    return dict(acc)


# Represents an uninterpreted justification for a step in a proof, to be
# dynamically interpreted based on its name.
class UninterpJust:
    def __init__(self, name: str, args: List[int]) -> None:
        self.name = name
        self.args = args

    # Interprets the justification within the given proof context, returning
    # the corresponding Argument instance.
    def interpret(self, ctx: Context) -> tuple[Argument, Dict[str, Set[str]]]:

        variables = combine_variable_contexts(
            tuple(ctx.lines[arg].variables for arg in self.args)
        )

        # Specific handling for deduction and other named justifications.
        if self.name == "ded":
            assert (
                tuple(sorted(self.args)) in ctx.proofs
            ), f"{min(self.args)}-{max(self.args)} does not denote a complete proof!"
            proof = ctx.proofs[tuple(sorted(self.args))]
            hyp, ded = ctx.proof_types[proof]
            assert (
                len(hyp) == 1
            ), f"A proof that uses multiple hypotheses cannot be used in the deduction rule! (hypotheses={hyp})"
            return Deduction(list(hyp)[0], ded), variables

        assert (
            self.name in argument_lookup
        ), f"{self.name} is not a recognized justification!"
        lines = [ctx.lines[arg] for arg in self.args]
        return argument_lookup[self.name](lines), variables

    def __repr__(self) -> str:
        return f"{self.name} {self.args}"
