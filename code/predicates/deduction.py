""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof, assumption, print_as_proof_forms=False):
    """ Given a proof, whose assumptions/axioms include Prover.AXIOMS, of a
        conclusion from a set of assumptions/axioms that includes the given
        assumption as a simple formula (i.e., without any templates), where no
        step of the proof is a UG step over a variable that is free in the
        given assumption, return a proof of (assumption->conclusion) from the
        same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is Formula
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        assert line.justification[0] != 'UG' or \
               line.justification[1] not in assumption.free_variables()
    # Task 11.1

def proof_by_contradiction(proof, assumption, print_as_proof_forms=False):
    """ Given a proof, whose assumptions/axioms include Prover.AXIOMS, of a
        contradiction (a formula whose negation is a tautology) from a set of
        assumptions/axioms that includes the given assumption as a simple
        formula (i.e., without any templates), where no step of the proof is a
        UG step over a variable that is free in the given assumption, return a
        proof of ~assumption from the same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is Formula
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        assert line.justification[0] != 'UG' or \
               line.justification[1] not in assumption.free_variables()
    # Task 11.2
