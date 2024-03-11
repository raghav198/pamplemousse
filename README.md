# ProofMouse
ProofMouse is a proof assistant for a propositional and predicate logic based on Gentzen-style proofs.

## Table of Contents
* [Getting Started](#getting-started)
    * [Installation](#installation)
    * [Writing Proofs](#writing-proofs)
    * [Checking Proofs](#checking-proofs)
*  [Inference Rules Reference](#inference-rules-reference)
    * [Directional Inference Rules](#directional-inference-rules)
    * [Deduction Method](#peculiarities-of-hypothetical-worlds-and-deduction-blocks)
    * [Equivalence Rules](#equivalence-rules)
## Getting Started

### Installation
ProofMouse is bundled as a [Python](https://www.python.org) package, and requires Python version 3.8 or higher to run.
It can be installed via `pip`, either by cloning this repository locally and then running 
```
$ pip install /path/to/repository
```
or by installing directly from GitHub:
```
$ pip install git+https://github.com/Jmw150/proof-mouse
```
This will install the `mouse` executable.

### Writing Proofs
A ProofMouse proof is an ASCII text file.
The first line of the file is a comma-separated list of formulae that specifies your proof obligations, and each subsequent line is a single proof step.

A proof step consists of an explicit line number, the formula being proved in that step, and finally a justification (the inference rule being used, and an optional comma-separated list of line numbers for arguments).
All lines must end with a semicolon.

A formula is a well-formed expression built out of of propositions (denoted by capital letters) and the following logical connectives:
* Conjunction (`/\`)
* Disjunction (`\/`)
* Implication (`->`)
* Negation (`~`)

To enter a hypothetical world, preface the line number with a vertical line: `|`.
An example proof of the exportation property is shown below:
```
A -> (B -> C)
1. A /\ B -> C prem;
| 2. A hyp;
| | 3. B hyp;
| | 4. A /\ B conj 2, 3;
| | 5. C mp 1, 4;
| 6. B -> C ded 3-5;
7. A -> (B -> C) ded 2, 6;
```
Note that the order of arguments to an inference rule matters! For example, proof checking would fail if line 5 instead read `| | 5. C mp 4, 1;`

A full list of inference rules and their semantics can be found [below](#inference-rules-reference).
For more example proofs, see [examples/](/examples/).

### Checking Proofs
Once you have written a Gentzen-style proof and saved it to a text file, the `mouse` checker can automatically verify that your proof is correct:

```
$ mouse /path/to/proof.txt
```

ProofMouse will record the proof obligation and then check your proof line by line, attempting to unify the formula on each line with the inference rule written as the justification.

If unification fails for a line, ProofMouse will print out an error detailing what went wrong and exit.
Once all lines have been successfully verified, ProofMouse checks the list of formulas proven against the proof obligations, failing if any proof obligations have not been met.

### Predicate Logic
ProofMouse also supports predicate logic proofs, using the `forall` and `exists` quantifiers.
Quantified formulae can be combined with the same logical connectives as for propositions, and can contain instances of any constants (free variables) or quantified variables. 
Quantifiers have a lower precedence than all other connectives, so a formula like 
```
forall x, P(x) -> exists y, Q(y)
```
must be parenthesized as
```
forall x, P(x) -> (exists y, Q(y))
```
and the scope of the quantified `x` is assumed to extend to the entire formula.
Extra parentheses can always be inserted to disambiguate.
## Inference Rules Reference
The tables below present all the inference rules available to ProofMouse.
The inference rules are written using type variables (`a`, `b`, `c`).
These type variables can be substituted for _any well-formed formula_, however, the same formula must be substitued for _every instance_ of the same type variable in the same row of the table. 

Remember that the order of the arguments matters, so e.g. the Modus Ponens rule `mp` will fail if you give it the proof of the antecedent before the proof of the implication.

### Directional Inference Rules

|Name | Given | Conclude|
|-----|------|---|
| `mp` | `a -> b`, `a` | `b`|
| `mt` | `a -> b`, `~b` | `~a` |
| `simpl` | `a /\ b` | `a` or `b` |
| `add` | `a` | `a \/ b` or `b \/ a` |
| `hs` | `a -> b`, `b -> c` | `a -> c`|
| `ds` | (`a \/ b` or `b \/ a`), `~a` | `b`|
| `de` | `a \/ b`, `a -> c`, `b -> c` | `c` |
| `hyp`, `prem` | | `a` |
| `conj` | `a`, `b` | `a /\ b` |
| `disj` | `a`, `b` | `a \/ b` |

There is also the deduction rule: `ded` which takes a list of line numbers corresponding to the lines of the "hypothetical world" proof.

### Peculiarities of Hypothetical Worlds and Deduction Blocks
1. When using the deduction rule, it may be more convenient to write a range of line numbers instead of a list; this can be accomplished with the `x-y` syntax, which expands to the list of lines from `x` to `y`, inclusive on both ends.
1. In the case of nested hypothetical worlds, the line numbers of the inner world do not also belong to the other world. For example, the exportation proof presented [above](#writing-proofs) would fail if line 7 instead read `7. A -> (B -> C) ded 2-6`
1. A hypothetical world can only introduce a single hypothesis. However, ProofMouse does not distinguish between premises and hypotheses, which means all premises must be introduced outside of any hypothetical world.

### Equivalence Rules
The semantics of the equivalence rules differ from those of the directional inference rules in two ways:
1. Equivalence rules can be applied backwards (i.e. they can be used to construct the pattern in either the `Left` or `Right` column, given the pattern in the other column)
2. Each pattern only needs to match a subformula, unlike the patterns above, which need to match the _entire_ formula to be applied.

Notice that common rules like `self`, `dm`, and `comm`/`assoc` have specialized versions for `and` and `or`.

|Name | Left | Right |
|-----|------|---|
| `or_comm` | `a \/ b`| `b \/ a`|
| `and_comm` | `a /\ b` | `b /\ a` |
| `or_assoc` | `a \/ (b \/ c)` | `(a \/ b) \/ c` |
| `and_assoc` | `a /\ (b /\ c)` | `(a /\ b) /\ c` |
| `dn`| `a` | `~~a` |
| `imp` | `a -> b` | `~a \/ b` |
| `dist_ao` | `a /\ (b \/ c)` | `(a /\ b) \/ (a /\ c)` |
| `dist_oa` | `a \/ (b /\ c)` | `(a \/ b) /\ (a \/ c)` |
| `dm_ao` | `~(a /\ b)` | `~a \/ ~b` |
| `dm_oa`| `~(a \/ b)` | `~a /\ ~b` |
| `exp` | `a -> (b -> c)` | `(a /\ b) -> c` |
| `cp` | `a -> b` | `~b -> ~a` |
| `or_self` | `a \/ a` | `a` |
| `and_self` | `a /\ a` | `a` |


### Predicate Logic Rules
In the rules that follow, `x` stands for any (quantified) variable, and `c` stands for any constant (free variable).
`P(x)` stands for any formula in which the symbol `x` appears.

The predicate logic versions of DeMorgan's laws:
| Name | Left | Right |
|------|------|-------|
| `dm_fe` | `~(forall x, P(x))` | `exists x, ~P(x)` |
| `dm_ef` | `~(exists x, P(x))` | `forall x, ~P(x)` |

The instantiation/generalization rules:

|Name | Given | Conclude|
|-----|-------|---------|
| `ui` | `forall x, P(x)` | `P(c)`|
| `ug` | `P(c)` | `forall x, P(x)`|
| `ei` | `exists x, P(x)` | `P(c)` |
| `eg` | `P(c)` | `exists x, P(x)` |

Note that for `ei`, `c` must not have been used as a free variable in any prior lines, or in any premises.
For `eg` and `ug`, `x` must not be a symbol in `P(c)`, unless `x = c`.
The constant `c` created by `ei` carries a dependence on _all_ universally instantiated constants in `P`. 
`ug` will fail to generalize a universally instantiated constant `c` if there are any existentially instantiated constants that still carry a dependence on it.

The precise semantics of these rules are as follows:
* A proof accumulates the set of free variables used in any line. Existential instantiation (`ei`) fails if the constant being instantiated (`c`) appears in this set.
* The premise rule (`prem`) fails if the formula being assumed as a premise contains an existentially instantiated constant.
* Each line has a "context", which maps each universally instantiated constant in that line to the set of existentially instantiated constants that depend on it.
* Using the `ui` rule adds `c` to the context of the instantiated line `P(c)`, and maps it to an empty set of dependents. 
* Using the `ei` rule copies the context of the original line (`exists x, P(x)`) to the context of the instantiated line (`P(c)`) and adds `c` to the set of dependents of every universally instantiated variable in the copied context.
* Universal generalization (`ug`) fails if the constant being generalized doesn't appear in the context of the original line (`P(c)`), or if the constant has a nonempty set of dependents. If `ug` succeeds, the context is copied over to the context of the generalized line (`forall x, P(x)`) and `c` is deleted from it.
