""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prover_test.py """

from predicates.some_proofs import *

def test_prover_basic(debug=False):
    proof = syllogism_proof(debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

    # Partial run - verifies all steps until stopped
    right_neutral_proof(True, True, True, True, debug)

def test_add_universal_instantiation(debug=False):
    proof = syllogism_proof_with_universal_instantiation(debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

    # With a difference variable name
    prover = Prover({'Ay[(Man(y)->Mortal(y))]', 'Man(aristotle)'},
                    'Mortal(aristotle)', debug)
    step1 = prover.add_assumption('Ay[(Man(y)->Mortal(y))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    # Will be tested with the course staff's implementation of is_valid
    assert prover.proof.is_valid()

    proof = syllogism_all_all_proof(debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

def test_add_tautological_inference(debug=False):
    proof = syllogism_all_all_proof_with_tautological_inference(debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

    proof = syllogism_all_exists_proof()
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

def test_add_existential_derivation(debug=False):
    proof = syllogism_all_exists_proof_with_existential_derivation(debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

def test_add_flipped_equality(debug=False):
    # Partial run - verifies all steps until stopped
    proof = right_neutral_proof(False, True, True, True, debug)
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(proof, 'x=plus(0,x)')
    assert _contains_line_with_formula(proof, '0=plus(minus(x),x)')
    assert _contains_line_with_formula(
        proof, 'plus(x,plus(y,z))=plus(plus(x,y),z)')

def test_add_free_instantiation(debug=False):
    # Partial run - verifies all steps until stopped
    proof = right_neutral_proof(False, False, True, True, debug)    
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(
        proof, '0=plus(minus(minus(x)),minus(x))')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))')
    assert _contains_line_with_formula(proof, 'plus(0,0)=0')
    assert _contains_line_with_formula(proof, 'plus(x,0)=plus(0,plus(x,0))')
    assert _contains_line_with_formula(
        proof, 'plus(0,plus(x,0))=plus(plus(0,x),0)')

def test_add_substituted_equality(debug=False):
    # Partial run - verifies all steps until stopped
    proof = right_neutral_proof(False, False, False, True, debug)
    # Verify that the critical conclusion were indeed derived
    assert _contains_line_with_formula(
        proof,
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)')
    assert _contains_line_with_formula(
        proof,
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)')
    assert _contains_line_with_formula(
        proof, 'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)')
    assert _contains_line_with_formula(
        proof, 'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))')
    assert _contains_line_with_formula(
        proof, 'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)')

def test_add_chained_equality(debug=False):
    proof = right_neutral_proof(False, False, False, False, debug)
    # Will be tested with the course staff's implementation of is_valid
    assert proof.is_valid()

def _contains_line_with_formula(proof, formula):
    for line in proof.lines:
        if str(line.formula) == formula:
            return True
    return False

def test_ex10(debug=False):
    test_prover_basic(debug)
    test_add_universal_instantiation(debug)
    test_add_tautological_inference(debug)
    test_add_existential_derivation(debug)
    test_add_flipped_equality(debug)
    test_add_free_instantiation(debug)
    test_add_substituted_equality(debug)
    test_add_chained_equality(debug)

def test_all(debug=False):
    test_ex10(debug)
