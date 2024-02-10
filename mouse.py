# Main program

# Standard libraries
from pyparsing import ParseException, delimited_list
from typing import List 
from argparse import ArgumentParser

# The rest of the codebase
from proof_parser import proof, form, ProofActionWithContext # For parsing proofs and forms with context
from proof import Context # For handling proof contexts
from props import Not, Or, Prop, PropHole # Logical proposition components
from unification import unify # For unification process in logical propositions, a common technique

# Deduction method parsed to move | to bounded { }, for simplicity
def preprocess(lines: List[str]) -> List[str]:

    processed_lines: List[str] = [] # Stores the processed lines to return at the end
    block = [] # Temporarily holds lines within a deduction block, as recursion happens
    
    # Loop over all lines of proof
    for line in lines:
        if line.startswith("| "): 
            block.append(line[2:]) # Adds line to the block, skipping "| "
            continue
        if len(block):
            # Processes the block recursively and wraps it with "{" and "}"
            processed_lines += ["{"] + preprocess(block) + ["}"]
            block = [] # Resets the block for the next deduction
        processed_lines.append(line.strip()) # Adds the current line to the processed lines

    return processed_lines


# specific axiom that is a production instead of a simplification: a |- a or ~a
def is_axiom(p: Prop):
    a = PropHole("a") # Creates a proposition hole as a placeholder

    # Checks if the proposition matches the axiom pattern a or ~a (or its inverse)
    return unify(p, Or(a, Not(a)), {}) or unify(p, Or(Not(a), a), {})


def main():

    # Initialize a context for the proof verification process
    ctx = Context()
    # Associate proof parsing actions with the current context to ensure proofs are parsed within this context
    proof.add_parse_action(ProofActionWithContext(ctx))

    # Initialize an argument parser to handle command-line inputs
    parser = ArgumentParser()
    parser.add_argument("input_file", type=str)
    args = parser.parse_args()

    # Attempt to open and read the proof file specified by the user
    try:
        lines = open(args.input_file).readlines()

        # Parse the first line as a list of obligations, separated by commas
        obligations = delimited_list(form, ",").parse_string(lines[0], parse_all=True)
        # obligation = form.parse_string(lines[0], parse_all=True)[0]

        # Preprocess the remaining lines (excluding the first) to handle proof scopes correctly
        text = "\n".join(preprocess(lines[1:]))

        # Parse the preprocessed text as a proof
        proof.parse_string(text, parse_all=True)

        # After parsing, check the proof context for validity
        if ctx.check():

            # Ensure the main proof object is not None after context check
            assert ctx.main_proof is not None

            # Retrieve hypotheses and deductions from the main proof context
            hyp, deds = ctx.proof_types[ctx.main_proof]


            # Filter out hypotheses that are not axioms
            non_axiom_hyp = {h for h in hyp if not is_axiom(h)}
            for obligation in obligations:

                # Check if each obligation is met within the deductions
                if obligation in deds:
                    # Print the non-axiom hypotheses leading to the obligation
                    print(f"{non_axiom_hyp} |- {obligation}")
                else:
                    raise Exception(f"Proof obligation {obligation} not met!")

    except ParseException as e:
        print(e.explain(depth=0))


if __name__ == "__main__":
    main()
