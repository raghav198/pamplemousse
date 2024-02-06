import pyparsing as pp

from props import And, BaseProp, Exists, ForAll, Imp, Not, Or, ModelRef, Predicate
from arguments import UninterpJust
from proof import Line, Proof, Context

r"""
Grammar:
form ::= disj -> form | disj
disj ::= disj \/ conj | conj
conj ::= conj /\ prop | prop
prop ::= [A-Z] | (form) | ~prop

num = [0-9]*
line ::= num. form just | { proof } line
proof ::= line*
just ::= [a-z]* args?
args ::= num | num, args
"""


def BaseAction(n):
    return BaseProp(n[0])


def NotAction(n):
    return Not(n[1])


def ConjAction(n):
    if len(n) == 1:
        return n[0]
    return And(ConjAction(n[:-1]), n[-1])


def DisjAction(n):
    if len(n) == 1:
        return n[0]
    return Or(DisjAction(n[:-1]), n[-1])


def FormAction(n):
    if len(n) == 1:
        return n[0]
    return Imp(n[0], FormAction(n[1:]))


def ForAllAction(n):
    return ForAll(ModelRef(n[0]), n[1])


def ExistsAction(n):
    return Exists(ModelRef(n[0]), n[1])


def PredicateAction(n):
    return Predicate(BaseProp(n[0]), tuple(map(ModelRef, n[1:])))


model_ref = pp.Word(init_chars=pp.alphas)
predicate = (
    pp.Word(init_chars=pp.alphas)
    + pp.Suppress("(")
    + pp.delimited_list(model_ref, ",")
    + pp.Suppress(")")
)
form = pp.Forward()
prop = pp.Forward()
prop <<= (
    predicate.set_parse_action(PredicateAction)
    | pp.Char(pp.alphas.upper()).set_parse_action(BaseAction)
    | (pp.Suppress("(") + form + pp.Suppress(")"))
    | ("~" + prop).set_parse_action(NotAction)
)
conj = pp.ZeroOrMore((prop + pp.Suppress("/\\"))) + prop
disj = pp.ZeroOrMore((conj + pp.Suppress("\\/"))) + conj
form <<= (
    (disj + pp.ZeroOrMore((pp.Suppress("->") + disj)))
    | (pp.Suppress("exists") + model_ref + pp.Suppress(",") + form).set_parse_action(
        ExistsAction
    )
    | (pp.Suppress("forall") + model_ref + pp.Suppress(",") + form).set_parse_action(
        ForAllAction
    )
)

conj.set_parse_action(ConjAction)
disj.set_parse_action(DisjAction)
form.set_parse_action(FormAction)


def NumAction(result):
    return int(result[0])


def ArgRange(result):
    return list(range(result[0], result[1] + 1))


def JustAction(result):
    return UninterpJust(result[0], result[1:])


def LineAction(result):
    return Line(result[0], result[1], result[2])


def ProofActionWithContext(ctx: Context):
    def ProofAction(result):
        external_proofs = []
        main_proof = []
        for line in result:
            if isinstance(line[0], Proof):
                external_proofs.append(line[0])
            else:
                main_proof.append(line[0])

        proof = Proof(main_proof)
        ctx.add_proof(proof)

        return proof

    return ProofAction


proof = pp.Forward()
num = pp.Word(pp.nums).set_parse_action(NumAction)
line_start = pp.Combine(num + pp.Suppress(".")).set_parse_action(NumAction)
args = (num + pp.Suppress("-") + num).set_parse_action(ArgRange) | pp.delimited_list(
    num, ","
)
just = (pp.Word(pp.alphas.lower() + "_") + pp.Optional(args)).set_parse_action(
    JustAction
)
comment_line = pp.Suppress(
    pp.QuotedString(quote_char="/*", end_quote_char="*/", multiline=True)
)
single_line = (line_start + form + just).set_parse_action(LineAction) + pp.Suppress(";")
embedded_proof = pp.Suppress("{") + proof + pp.Suppress("}")
line = single_line | embedded_proof
proof <<= pp.OneOrMore(pp.Group(line) | comment_line)

if __name__ == "__main__":
    print(form.parse_string(r"P /\ Q"))

# text = r'''1. ~(Q /\ ~Z) prem;
# 2. ~Q \/ ~~Z dm 1;
# /* comment */
# 3. ~Q \/ Z dn 2;
# 4. Q -> Z imp 3;
# 5. R -> P prem;
# 6. R prem;
# 7. P mp 5, 6;
# 8. P -> Q prem;
# 9. Q mp 8, 7;
# 10. Z mp 4, 9;'''

# text2 = r'''1. ~(Q /\ Z) prem;
# {
# 2. ~Q \/ ~~Z dm 1;
# }'''

# import sys

# try:
#     proof.parse_file(sys.argv[1], parse_all=True)
#     print('Parsed successfully!')
#     ctx.check()
# except pp.ParseException as e:
#     print(e.explain())


# try:
#     print(form.parse_string(r'~Q \/ ~~Z', parse_all = True))
# except pp.ParseException as e:
#     print(e.explain())

# try:
#     print(proof.parse_file('examples/a.proof', parse_all=False))
# except pp.ParseException as e:
#     print(e.explain())
