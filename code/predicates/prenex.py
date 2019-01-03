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
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
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

def is_in_prenex_normal_form(formula):
    """ Return whether the given formula is in prenex normal form """
    assert type(formula) is Formula
    # Task 11.3.2

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
