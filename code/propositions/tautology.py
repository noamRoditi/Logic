""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.axiomatic_systems import *

def formulae_capturing_model(model):
    """ Return the list of formulae that capture the given model: for each
        variable x that is assigned the value True in the model, the
        corresponding capturing formula is 'x', and for each variable that is
        assigned the value False, the corresponding capturing formula '~x'.
        The list of these formulae should be returned, ordered alphabetically
        by the name of the variable. Example: if the model is {'p2': False,
        'p1': True, 'q': True} then the list of formulae represented by 'p1',
        '~p2', 'q', in this order, should be returned """
    assert is_model(model)
    # Task 6.1a
def prove_in_model(formula, model):
    """ If formula evaluates to True in model, return a proof of formula from
        the formulae that capture model as assumption (in the order returned
        by formulae_capturing_model) via AXIOMATIC_SYSTEM. If formula evaluates
        to False in model, return a proof of ~formula from the same assumptions
        via AXIOMATIC_SYSTEM. formula may contain no operators beyond '->' and
        '~' """  
    assert type(formula) is Formula
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

def reduce_assumption(proof_from_affirmation, proof_from_negation):
    """ Given two proofs of the same conclusion via the same set of inference
        rules, where the assumptions of the two proofs coincide except for the
        last assumption of each, where the last assumption of
        proof_from_negation is the negation of the last assumption of
        proof_from_affirmation, return a proof of the same conclusion, from only
        the common assumptions, via the same set of inference rules, and in
        addition MP, I0, I1, I2, R. E.g., the two input proofs may be of
        [p, q] ==> (q->p) and of [p, ~q] ==> (q->p), and in this case the
        returned proof should be of [p] ==> (q->p) """
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    assert proof_from_affirmation.is_valid() and proof_from_negation.is_valid()
    # Task 6.2

def prove_tautology(tautology, model={}):
    """ Given a tautology and a model of some (possibly empty) prefix of its
        variables (with respect to the alphabetical order), return a proof of
        tautology via AXIOMATIC_SYSTEM from the assumptions that capture model.
        tautology may contain no operators beyond '->' and '~'. In particular,
        when model is the empty dictionary, the function returns a proof of
        tautology from an empty list of assumptions """
    assert is_tautology(tautology)
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

def proof_or_counterexample(formula):
    """ Return either a proof of formula from no assumptions via
        AXIOMATIC_SYSTEM, or a model where formula does not hold. formula may
        contain no operators beyond '->' and '~' """
    assert type(formula) is Formula
    # Task 6.3b

def encode_as_formula(rule):
    """ Given an inference rule with assumptions [p1, p2, ..., pn] and
        conclusion q, return its "encoding" as a formula
        (p1->(p2->...(pn->q)...)) """
    assert type(rule) is InferenceRule
    # Task 6.4a

def prove_sound_inference(rule):
    """ Return a proof of the given sound inference rule via AXIOMATIC_SYSTEM
    """
    assert is_sound_inference(rule)
    # Task 6.4b

def model_or_contradiction(formulae):
    """ Return either a model that satisfies (all of) formulae, or a proof of
        '~(p->p)' via AXIOMATIC_SYSTEM from formulae as assumptions. No formula
        in formulae may contain operators beyond '->' and '~' """
    for formula in formulae:
        assert type(formula) is Formula
    # Task 6.5

def prove_in_model_full(formula, model):
    """ If formula evaluates to True in model, return a proof of formula from
        the formulae that capture model as assumption (in the order returned
        by formulae_capturing_model) via AXIOMATIC_SYSTEM_FULL. If formula
        evaluates to False in model, return a proof of ~formula from the same
        assumptions via AXIOMATIC_SYSTEM_FULL """
    assert type(formula) is Formula
    assert is_model(model)
    # Optional Task 6.6
