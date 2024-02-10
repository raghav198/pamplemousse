

from __future__ import annotations
from collections import defaultdict
from typing import List, Dict, Set

from props import *
from arguments import Hypothesis, UninterpJust
from unification import *
from unification import get_symbols

# Represents a single line in a proof, encapsulating a proposition, its
# numerical identifier, and its logical justification.
class Line:
    """
    Represents a single line in a proof, encapsulating a proposition, its numerical identifier,
    and its logical justification.
    """
    def __init__(self, num: int, typ: Prop, just: UninterpJust) -> None:
        """
        Initializes a Line instance.
        
        Parameters:
        - num (int): The line number in the proof.
        - typ (Prop): The proposition represented by this line.
        - just (UninterpJust): The justification for the proposition, which may need to be interpreted.
        """
        self.num = num
        self.typ = typ
        self.just = just
        self.variables: Dict[str, Set[str]] = {}

    def check(self, ctx: Context):
        """
        Verifies the line within the context of the proof, utilizing its justification.
        
        Parameters:
        - ctx (Context): The proof context for verification.
        """
        self.arg, self.variables = self.just.interpret(ctx)
        assert self.arg.verify(
            self, ctx.constants
        ), f"Cannot use `{self.arg}` to produce {self.typ}!"

    def __repr__(self) -> str:
        """
        Returns a string representation of the line.
        """
        return f"{self.num}. {self.typ} {self.just}"


class Proof:
    """
    Represents a complete proof, consisting of multiple lines.
    """
    def __init__(self, lines: List[Line]):
        """
        Initializes a Proof instance with a list of lines.
        
        Parameters:
        - lines (List[Line]): The lines that make up the proof.
        """
        self.lines: Dict[int, Line] = {}
        for line in lines:
            self.lines[line.num] = line

    def compile(self, ctx: Context) -> tuple[Set[Prop], Set[Prop]]:
        """
        Compiles the proof within the given context, extracting assumptions and results.
        
        Parameters:
        - ctx (Context): The context in which to compile the proof.
        
        Returns:
        - A tuple of sets containing assumptions and results derived from the proof.
        """
        assumptions: Set[Prop] = set()
        results: Set[Prop] = set()

        for line in self.lines.values():
            if isinstance(line.arg, Hypothesis):
                assumptions.add(line.typ)
            results.add(line.typ)
        ctx.register_type(self, (assumptions, results))
        return assumptions, results

    def __repr__(self) -> str:
        """
        Returns a string representation of the proof, showing all lines.
        """
        return "\n".join(map(repr, self.lines.values()))


class Context:
    """
    Manages the broader context for a set of proofs, including dependencies and verification status.
    """
    def __init__(self) -> None:
        self.lines: Dict[int, Line] = {}
        self.proof_types: Dict[Proof, tuple[Set[Prop], Set[Prop]]] = {}
        self.proofs: Dict[tuple[int, ...], Proof] = {}
        self.main_proof: Proof | None = None
        self.dependences: Dict[int, Set[int]] = defaultdict(set)
        self.constants: Set[ModelRef] = set()

    def add_proof(self, proof: Proof):
        """
        Adds a proof to the context, updating lines and proof collections.
        
        Parameters:
        - proof (Proof): The proof to add.
        """
        self.lines.update(proof.lines)
        self.proofs[tuple(sorted(proof.lines.keys()))] = proof
        self.main_proof = proof

    def register_type(self, proof: Proof, typ: tuple[Set[Prop], Set[Prop]]):
        """
        Registers the types (assumptions and results) of a proof within the context.
        
        Parameters:
        - proof (Proof): The proof to register.
        - typ (tuple): The assumptions and results of the proof.
        """
        self.proof_types[proof] = typ

    def check(self) -> bool:
        """
        Verifies all proofs within the context, ensuring logical consistency and completeness.
        
        Returns:
        - True if all proofs are verified successfully; False otherwise.
        """
        if self.main_proof is None:
            print("** No proofs added! **")
            return False
        try:
            remaining_proofs = set(self.proofs.values())
            lines_checked: Set[int] = set()

            # initialize constants from premises
            for num in sorted(self.lines.keys()):
                if self.lines[num].just.name == "prem":
                    sym, var = get_symbols(self.lines[num].typ)
                    self.constants |= sym - var

            for num in sorted(self.lines.keys()):
                print(f"{self.lines[num]}", end="\t")
                self.lines[num].check(self)
                sym, var = get_symbols(self.lines[num].typ)
                self.constants |= sym - var
                print("\u2713")  # check mark
                lines_checked.add(num)

                for lines in self.proofs:
                    if self.proofs[lines] in remaining_proofs and (
                        set(lines).issubset(lines_checked)
                    ):
                        self.proofs[lines].compile(self)
                        remaining_proofs.remove(self.proofs[lines])

            return True
        except AssertionError as e:
            print("\u2717")  # x mark
            print(f"Error: {e}")
            return False

    def transitive_dependences(self, line_number: int):
        """
        Computes the transitive dependencies of a given line number within the proof context.
        
        Parameters:
        - line_number (int): The line number to compute dependencies for.
        
        Returns:
        - A set of line numbers that are dependencies of the given line.
        """
        deps = set(self.lines[line_number].just.args)
        return deps | set().union(*(self.transitive_dependences(dep) for dep in deps))
