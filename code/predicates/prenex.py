""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prenex.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.util import *

ADDITIONAL_QUANTIFICATION_AXIOMS = [
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {"x", "R"}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {"x", "R"}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {"x", "R", "Q"}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {"x", "y", "R", "Q"}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {"x", "y", "R", "Q"})]


def is_quantifier_free(formula):
    """ Return whether the given formula contains any quantifiers """
    assert type(formula) is Formula
    # Task 11.3.1
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    if is_quantifier(formula.root):
        return False
    return True


def is_in_prenex_normal_form(formula):
    """ Return whether the given formula is in prenex normal form """
    assert type(formula) is Formula
    # Task 11.3.2
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    return True


def equivalence_of(formula1, formula2):
    """ Return the formula '((formula1->formula2)&(formula2->formula1))', which
        states the equivalence of the two given formulae """
    assert type(formula1) is Formula
    assert type(formula2) is Formula
    return Formula("&", Formula("->", formula1, formula2),
                   Formula("->", formula2, formula1))


def has_uniquely_named_variables(formula):
    """ Return whether the given formula has uniquely named variables """
    assert type(formula) is Formula
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_recursive(formula):
        if is_unary(formula.root):
            return has_uniquely_named_variables_recursive(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_recursive(formula.first) and \
                   has_uniquely_named_variables_recursive(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_recursive(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_recursive(formula)


def uniquely_rename_quantified_variables(formula):
    """ Given a formula, return a pair: an equivalent formula with the exact
        same structure with the additional property of having uniquely named
        variables; and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well as
        from ADDITIONAL_QUANTIFICATION_AXIOMS. All quantified variable names
        should be replaced by new variable names, each generated using
        next(fresh_variable_name_generator) - it is assumed that the original
        formula does not contain variable names that you have generated this way
    """
    assert type(formula) is Formula
    # Task 11.5


def pull_out_quantifications_across_negation(formula):
    """ Given a formula whose root is a negation, i.e., a formula of the form
        ~Q1x1[Q2x2[...Qnxn[inner_formula]...]] (where n>=0, each Qi is a
        quantifier, each xi is a variable name, and inner_formula does not
        start with a quantifier), return a pair: an equivalent formula of the
        form Q'1x1[Q'2x2[...Q'nxn[~inner_formula]...]] (where each Q'i is a
        quantifier, and where the xi's and inner_formula are the same as in the
        given formula); and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) is Formula
    assert is_unary(formula.root)
    # Task 11.6
    if formula.first.root is "A":
        new_quantifier = "E"
        axioms = ADDITIONAL_QUANTIFICATION_AXIOMS[0], ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    else:
        new_quantifier = "A"
        axioms = ADDITIONAL_QUANTIFICATION_AXIOMS[1], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    if is_quantifier_free(formula.first):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof
    new_predicate, new_predicate_proof = pull_out_quantifications_across_negation(Formula('~', formula.first.predicate))
    quantified_new_predicate = Formula(new_quantifier, formula.first.variable, new_predicate)
    r_key = "R(" + formula.first.variable + ")"
    q_key = "Q(" + formula.first.variable + ")"
    instantiation_map = {"x": formula.first.variable, "y": formula.first.variable,
                         r_key: Formula('~', formula.first.predicate).__repr__(),
                         q_key: new_predicate.__repr__()}
    a = Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.first)
    b = Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.second)
    new_quantifiers_formula = equivalence_of(a, b)
    quantifier_formula = Formula("->", new_predicate_proof.conclusion, new_quantifiers_formula)
    conclusion = equivalence_of(formula, quantified_new_predicate)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    quantifying_equivalent = prover.add_instantiated_assumption(quantifier_formula, axioms[1], instantiation_map)
    new_q_formula = Formula(new_quantifier, formula.first.variable, Formula('~', formula.first.predicate))
    step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    mp = prover.add_mp(new_quantifiers_formula, step, quantifying_equivalent)
    pull_negation_formula = equivalence_of(formula, new_q_formula)
    instantiation_map_axioms = {r_key: formula.first.predicate.__repr__(), "x": formula.first.variable}
    axiom_instantiation_step = prover.add_instantiated_assumption(pull_negation_formula, axioms[0],
                                                                  instantiation_map_axioms)
    prover.add_tautological_inference(conclusion.__repr__(), {mp, axiom_instantiation_step})
    return quantified_new_predicate, prover.proof


def find_new_q(formula):
    new_quantifier = "A"
    if formula.first.root is "E":
        new_quantifier = "E"
    if new_quantifier is "E" and formula.root == "->":
        new_quantifier = "A"
    elif new_quantifier is "A" and formula.root == "->":
        new_quantifier = "E"
    return new_quantifier


def find_gorer_quantifier(formula):
    if formula.first.root is "A":
        return "E"
    return "A"


def pull_out_quantifications_from_left_across_binary_operator(formula):
    """ Given a formula with uniquely named variables whose root is a binary
        operator, i.e., a formula with uniquely named variables that is of the
        form (Q1x1[Q2x2[...Qnxn[inner_first]...]]*second) (where * is a binary
        operator, n>=0, each Qi is a quantifier, each xi is a variable name,
        and inner_first does not start with a quantifier), return a pair: an
        equivalent formula of the form
        Q'1x1[Q'2x2[...Q'nxn[(inner_first*second)]...]] (where each Q'i is a
        quantifier, and where the operator *, the xi's, inner_first, and second
        are the same as in the given formula); and a proof of the equivalence
        (i.e., a proof of equivalence_of(formula, returned_formula)) from
        Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) is Formula
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    if is_quantifier_free(formula.first):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof
    if formula.root is "->":
        quantifier = find_gorer_quantifier(formula)
    else:
        quantifier = formula.first.root
    new_quantifier = find_new_q(formula)
    RELEVANT_AXIOMS = {("A", "&"): (14, 2), ("A", "|"): (14, 6),
                       ("A", "->"): (14, 11), ("E", "&"): (15, 3), ("E", "|"): (15, 7),
                       ("E", "->"): (15, 10)}
    predicate = Formula(formula.root, formula.first.predicate, formula.second)
    new_predicate, new_predicate_proof = pull_out_quantifications_from_left_across_binary_operator(predicate)
    a, b = Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.first), \
           Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.second)
    quantifiers_equivalence_formula = equivalence_of(a, b)
    add_quantifier_formula = Formula("->", new_predicate_proof.conclusion, quantifiers_equivalence_formula)
    quantified_new_predicate = Formula(new_quantifier, formula.first.variable, new_predicate)
    conclusion = equivalence_of(formula, quantified_new_predicate)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    last_proof_step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    r_key = 'R(' + formula.first.variable + ")"
    q_key = 'Q(' + formula.first.variable + ")"
    instantiation_map = {"x": formula.first.variable, "y": formula.first.variable,
                         r_key: predicate.__repr__(), q_key: new_predicate.__repr__()}
    quantifying_equivalent = prover.add_instantiated_assumption(add_quantifier_formula,
                                                                ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                                    RELEVANT_AXIOMS[(quantifier, formula.root)][1]],
                                                                instantiation_map)
    binary_formula = equivalence_of(formula, Formula(new_quantifier, formula.first.variable, predicate))
    instantiation_map = {"x": formula.first.variable, r_key: formula.first.predicate.__repr__(),
                         "Q()": formula.second.__repr__()}
    mp = prover.add_mp(quantifiers_equivalence_formula, last_proof_step, quantifying_equivalent)
    axiom_instantiation_step = prover.add_instantiated_assumption(binary_formula,
                                                                  ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                                      RELEVANT_AXIOMS[(quantifier, formula.root)][0]],
                                                                  instantiation_map)
    prover.add_tautological_inference(conclusion.__repr__(), {mp, axiom_instantiation_step})
    return quantified_new_predicate, prover.proof


def pull_out_quantifications_from_right_across_binary_operator(formula):
    """ Given a formula with uniquely named variables whose root is a binary
        operator, i.e., a formula with uniquely named variables that is of the
        form (first*Q1x1[Q2x2[...Qnxn[inner_second]...]]) (where * is a binary
        operator, n>=0, each Qi is a quantifier, each xi is a variable name,
        and inner_second does not start with a quantifier), return a pair: an
        equivalent formula of the form
        Q'1x1[Q'2x2[...Q'nxn[(first*inner_second)]...]] (where each Q'i is a
        quantifier, and where the operator *, the xi's, first, and inner_second
        are the same as in the given formula), and a proof of the equivalence
        (i.e., a proof of equivalence_of(formula, returned_formula)) from
        Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) is Formula
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    if is_quantifier_free(formula.second):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof
    RELEVANT_AXIOMS = {("A", "&"): (14, 4), ("A", "|"): (14, 8), ("A", "->"): (14, 12), ("E", "&"): (15, 5),
                       ("E", "|"): (15, 9), ("E", "->"): (15, 13)}
    quantifier = formula.second.root
    new_predicate, new_predicate_proof = pull_out_quantifications_from_right_across_binary_operator(
        Formula(formula.root, formula.first, formula.second.predicate))
    quantifiers_equivalence_formula = equivalence_of(
        Formula(quantifier, formula.second.variable, new_predicate_proof.conclusion.first.first),
        Formula(quantifier, formula.second.variable, new_predicate_proof.conclusion.first.second))
    add_quantifier_formula = Formula("->", new_predicate_proof.conclusion, quantifiers_equivalence_formula)
    quantified_new_predicate = Formula(quantifier, formula.second.variable, new_predicate)
    conclusion = equivalence_of(formula, quantified_new_predicate)
    r_key = 'R(' + formula.second.variable + ")"
    q_key = 'Q(' + formula.second.variable + ")"
    instantiation_map = {"x": formula.second.variable, "y": formula.second.variable,
                         r_key: Formula(formula.root, formula.first, formula.second.predicate).__repr__(),
                         q_key: new_predicate.__repr__()}
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    quantifying_equivalent = prover.add_instantiated_assumption(add_quantifier_formula,
                                                                ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                                    RELEVANT_AXIOMS[(quantifier, formula.root)][1]],
                                                                instantiation_map)
    mp = prover.add_mp(quantifiers_equivalence_formula, step, quantifying_equivalent)
    binary_formula = equivalence_of(formula, Formula(quantifier, formula.second.variable,
                                                     Formula(formula.root, formula.first,
                                                             formula.second.predicate)))
    instantiation_map = {"x": formula.second.variable, r_key: formula.second.predicate.__repr__(),
                         'Q()': formula.first.__repr__()}
    axiom_instantiation_step = prover.add_instantiated_assumption(binary_formula,
                                                                  ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                                      RELEVANT_AXIOMS[(quantifier, formula.root)][0]],
                                                                  instantiation_map)
    prover.add_tautological_inference(conclusion.__repr__(), {mp, axiom_instantiation_step})
    return quantified_new_predicate, prover.proof


def pull_out_quantifications_across_binary_operator(formula):
    """ Given a formula with uniquely named variables whose root is a binary
        operator, i.e., a formula with uniquely named variables that is of the
        form (Q1x1[Q2x2[...Qnxn[inner_first]...]]*
              P1y1[P2y2[...Pmym[inner_second]...]]) (where * is a binary
        operator, n>=0, m>=0, each Qi and each Pi is a quantifier, each xi and
        each yi is a variable name,  and neither inner_first nor inner_second
        starts with a quantifier), return a pair: an equivalent formula of the
        form
        Q'1x1[Q'2x2[...Q'nxn[P'1y1[P'2y2[...P'mym[(inner_first*
                                                   inner_second)]...]]]...]]
        (where each Q'i and each P'i is a quantifier, and where the operator *,
        the xi's, the yi's, inner_first, and inner_second are the same as in
        the given formula), and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) is Formula
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    pull_left_across = pull_out_quantifications_from_left_across_binary_operator(formula)
    quantify, vars = list(), list()
    left_formula = pull_left_across[0]
    while is_quantifier(left_formula.root):
        quantify.append(left_formula.root)
        vars.append(left_formula.variable)
        left_formula = left_formula.predicate
    pull_right_across = pull_out_quantifications_from_right_across_binary_operator(left_formula)
    final_line = pull_right_across[0]
    i = len(quantify) - 1
    while i >= 0:
        final_line = Formula(quantify[i], vars[i], final_line)
        i -= 1
    new_formula = equivalence_of(left_formula, pull_right_across[0])
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, equivalence_of(formula, final_line))
    step = prover.add_proof(pull_right_across[1].conclusion, pull_right_across[1])
    i = len(quantify) - 1
    while i >= 0:
        quantified_formula = equivalence_of(
            Formula(quantify[i], vars[i], new_formula.first.first),
            Formula(quantify[i], vars[i], new_formula.first.second))
        instantiation_map = {'R({})'.format(vars[i]): new_formula.first.first.__repr__(),
                             'Q({})'.format(vars[i]): new_formula.first.second.__repr__(),
                             "x": vars[i], "y": vars[i]}
        if not quantify[i] is "A":
            aqd = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        else:
            aqd = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        axiom = prover.add_instantiated_assumption(Formula("->", new_formula, quantified_formula), aqd,
                                                   instantiation_map)
        step = prover.add_mp(quantified_formula, step, axiom)
        new_formula = quantified_formula
        i -= 1
    prover.add_tautological_inference(equivalence_of(formula, final_line).__repr__(),
                                      {step, prover.add_proof(pull_left_across[1].conclusion, pull_left_across[1])})
    return final_line, prover.proof


def to_prenex_normal_form_from_unique_quantified_variables(formula):
    """ Given a formula with uniquely named variables, return a pair: an
        equivalent formula in prenex normal form, and a proof of the equivalence
        (i.e., a proof of equivalence_of(formula, returned_formula)) from
        Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) is Formula
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula):
    """ Given a formula, return a pair: an equivalent formula in prenex normal
        form, and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well as
        from ADDITIONAL_QUANTIFICATION_AXIOMS. All quantified variable names
        should be replaced by new variable names, each generated using
        next(fresh_variable_name_generator) - it is assumed that the original
        formula does not contain variable names that you have generated this way
    """
    assert type(formula) is Formula
    # Task 11.10
