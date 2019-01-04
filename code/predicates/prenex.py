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
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'})]


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
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


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
        pull_negation_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
        add_quantifier_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    else:
        new_quantifier = "A"
        pull_negation_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[1]
        add_quantifier_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    if is_quantifier_free(formula.first):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof
    new_predicate, new_predicate_proof = pull_out_quantifications_across_negation(Formula('~', formula.first.predicate))
    instantiation_map = {'x': formula.first.variable, 'y': formula.first.variable,
                         'R(' + formula.first.variable + ')': Formula('~', formula.first.predicate).__repr__(),
                         'Q(' + formula.first.variable + ')': new_predicate.__repr__()}
    a = Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.first)
    b = Formula(new_quantifier, formula.first.variable, new_predicate_proof.conclusion.first.second)
    new_quantifiers_formula = equivalence_of(a, b)
    add_quantifier_formula = Formula('->', new_predicate_proof.conclusion, new_quantifiers_formula)
    quantified_new_predicate = Formula(new_quantifier, formula.first.variable, new_predicate)
    conclusion = equivalence_of(formula, quantified_new_predicate)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    quantifying_equivalent = prover.add_instantiated_assumption(add_quantifier_formula, add_quantifier_axiom,
                                                                instantiation_map)
    last_proof_step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    mp_step = prover.add_mp(new_quantifiers_formula, last_proof_step, quantifying_equivalent)
    linking_formula = Formula(new_quantifier, formula.first.variable, Formula('~', formula.first.predicate))
    pull_negation_formula = equivalence_of(formula, linking_formula)
    instantiation_map_axioms = {'x': formula.first.variable,
                                'R(' + formula.first.variable + ')': str(formula.first.predicate)}
    axiom_instantiation_step = prover.add_instantiated_assumption(pull_negation_formula, pull_negation_axiom,
                                                                  instantiation_map_axioms)
    prover.add_tautological_inference(str(conclusion), {mp_step, axiom_instantiation_step})
    return quantified_new_predicate, prover.proof


def from_left_find_axioms(binary_operator, quantifier):
    """ This function determines which of the "ADD QUANTIFIER" axioms to use - 15 or 16,
         and also determines the right axiom from 1-14 according to the binary operator."""
    if binary_operator == '&':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[2], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[3], ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    elif binary_operator == '|':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[6], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[7], ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    elif binary_operator == '->':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[11], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[10], ADDITIONAL_QUANTIFICATION_AXIOMS[15]


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
    else:  
        var = formula.first.variable
        new_quantifier = 'A'
        if formula.first.root == 'E':
            new_quantifier = 'E'
        if formula.root == '->' and new_quantifier == 'A':
            new_quantifier = 'E'
        elif formula.root == '->' and new_quantifier == 'E':
            new_quantifier = 'A'
        pull_binary_axiom, add_quantifier_axiom = from_left_find_axioms(formula.root, new_quantifier)
        predicate_to_recursion = Formula(formula.root, formula.first.predicate, formula.second)
        new_predicate, new_predicate_proof = pull_out_quantifications_from_left_across_binary_operator(predicate_to_recursion)
        first_formula = new_predicate_proof.conclusion.first.first
        second_formula = new_predicate_proof.conclusion.first.second
        quantifiers_equivalence_formula = Formula('&', Formula('->',
                                                               Formula(new_quantifier, var, first_formula),
                                                               Formula(new_quantifier, var, second_formula)),
                                                  Formula('->',
                                                          Formula(new_quantifier, var, second_formula),
                                                          Formula(new_quantifier, var, first_formula)))
        add_quantifier_formula = Formula('->',
                                         new_predicate_proof.conclusion,
                                         quantifiers_equivalence_formula)
        quantified_new_predicate = Formula(new_quantifier, var, new_predicate)
        conclusion = equivalence_of(formula, quantified_new_predicate)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        last_proof_step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
        quantifying_equivalent = prover.add_instantiated_assumption(add_quantifier_formula,
                                                                    add_quantifier_axiom,
                                                                    {'x': var, 'y': var,
                                                                     'R(' + var + ')': str(predicate_to_recursion),
                                                                     'Q(' + var + ')': str(new_predicate)})
        mp_step = prover.add_mp(quantifiers_equivalence_formula, last_proof_step, quantifying_equivalent)
        linking_formula = Formula(new_quantifier, var, predicate_to_recursion)
        pull_binary_formula = Formula('&', Formula('->', formula, linking_formula),
                                      Formula('->', linking_formula, formula))
        axiom_instantiation_step = prover.add_instantiated_assumption(pull_binary_formula,
                                                                      pull_binary_axiom,
                                                                      {'x': var,
                                                                       'R(' + var + ')': str(formula.first.predicate),
                                                                       'Q()': str(formula.second)})
        prover.add_tautological_inference(str(conclusion), {mp_step, axiom_instantiation_step})
        return quantified_new_predicate, prover.proof


def from_right_find_axioms(binary_operator, quantifier):
    """ This function determines which of the "ADD QUANTIFIER" axioms to use - 15 or 16,
     and also determines the right axiom from 1-14 according to the binary operator."""
    if binary_operator == '&':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[4], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[5], ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    elif binary_operator == '|':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[8], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[9], ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    elif binary_operator == '->':
        if quantifier == 'A':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[12], ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        elif quantifier == 'E':
            return ADDITIONAL_QUANTIFICATION_AXIOMS[13], ADDITIONAL_QUANTIFICATION_AXIOMS[15]


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

    var = formula.second.variable
    quantifier = formula.second.root
    pull_binary_axiom, add_quantifier_axiom = from_right_find_axioms(formula.root, quantifier)
    predicate_to_recursion = Formula(formula.root, formula.first, formula.second.predicate)
    new_predicate, new_predicate_proof = pull_out_quantifications_from_right_across_binary_operator(predicate_to_recursion)
    first_formula = new_predicate_proof.conclusion.first.first
    second_formula = new_predicate_proof.conclusion.first.second
    quantifiers_equivalence_formula = equivalence_of(Formula(quantifier, var, first_formula),
                                                         Formula(quantifier, var, second_formula))
    add_quantifier_formula = Formula('->', new_predicate_proof.conclusion, quantifiers_equivalence_formula)
    quantified_new_predicate = Formula(quantifier, var, new_predicate)
    conclusion = equivalence_of(formula, quantified_new_predicate)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    last_proof_step = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    quantifying_equivalent = prover.add_instantiated_assumption(add_quantifier_formula,
                                                                    add_quantifier_axiom,
                                                                    {'x': var, 'y': var,
                                                                     'R(' + var + ')': str(predicate_to_recursion),
                                                                     'Q(' + var + ')': str(new_predicate)})
    mp_step = prover.add_mp(quantifiers_equivalence_formula, last_proof_step, quantifying_equivalent)
        # right side of Axioms 5 / 6 / 9 / 10 / 13 / 14: Ex[phi(x)] / Ax[phi(x)]
    linking_formula = Formula(quantifier, var, predicate_to_recursion)
    pull_binary_formula = Formula('&', Formula('->', formula, linking_formula),
                                      Formula('->', linking_formula, formula))
        # Adds axiom 5 / 6 / 9 / 10 / 13 / 14
    axiom_instantiation_step = prover.add_instantiated_assumption(pull_binary_formula,
                                                                      pull_binary_axiom,
                                                                      {'x': var,
                                                                       'R(' + var + ')': str(formula.second.predicate),
                                                                       'Q()': str(formula.first)})
    prover.add_tautological_inference(str(conclusion), {mp_step, axiom_instantiation_step})
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
    second_in_first, second_in_first_proof = pull_out_quantifications_from_left_across_binary_operator(formula)

    left_predicate, left_formula_quantifiers, left_formula_vars = strip_q_and_v_from_left(second_in_first)

    # Prove that first can go into second's predicate:
    first_in_second, first_in_second_proof = pull_out_quantifications_from_right_across_binary_operator(left_predicate)

    # construct the punch line, and proof conclusion:
    punch_line = add_left_quantifiers(left_formula_quantifiers, left_formula_vars, first_in_second)
    conclusion = equivalence_of(formula, punch_line)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    step_0 = prover.add_proof(second_in_first_proof.conclusion, second_in_first_proof)
    step_1 = prover.add_proof(first_in_second_proof.conclusion, first_in_second_proof)
    new_formula = equivalence_of(left_predicate, first_in_second)
    step_2, prover = quantify_formula(new_formula, step_1, left_formula_quantifiers, left_formula_vars, prover)
    prover.add_tautological_inference(str(conclusion), {step_0, step_2})
    return punch_line, prover.proof


def strip_q_and_v_from_left(formula):
    """strips the formula of its quantifiers and variables"""
    quantifiers, variables = list(), list()
    while is_quantifier(formula.root):
        quantifiers.append(formula.root)
        variables.append(formula.variable)
        formula = formula.predicate

    return formula, quantifiers, variables


def add_left_quantifiers(quantifiers, variables, formula):
    """Now add the left formula's quantifiers upon the second formula."""
    for i in reversed(range(len(quantifiers))):
        formula = Formula(quantifiers[i], variables[i], formula)
    return formula


def quantify_formula(formula, current_step, quantifiers, variables, prover):
    for i in reversed(range(len(quantifiers))):
        quantifier, variable = quantifiers[i], variables[i]
        quantified_first = Formula(quantifier, variable,
                                   formula.first.first)
        quantified_second = Formula(quantifier, variable,
                                    formula.first.second)
        quantified_formula = equivalence_of(quantified_first, quantified_second)
        axiom_verse = Formula("->", formula, quantified_formula)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14] if quantifiers[i] == "A" else ADDITIONAL_QUANTIFICATION_AXIOMS[15]

        axiom_index = prover.add_instantiated_assumption(axiom_verse, axiom,
                                                         {"x": variable, 'y': variable, 'R({})'.format(
                                                             variable): str(formula.first.first),
                                                          'Q({})'.format(variable): str(formula.first.second)})
        formula = quantified_formula

        current_step = prover.add_mp(axiom_verse.second, current_step, axiom_index)

    return current_step, prover


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
