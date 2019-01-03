""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
import copy
Unray_string_var = '~'
Gorer_string_var = '->'

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
    copied_assumptions = list(copy.deepcopy(proof.assumptions))
    assumption_schema = Schema(assumption, set())
    # remove the assumption
    copied_assumptions.remove(assumption_schema)
    prover = Prover(copied_assumptions, Formula(Gorer_string_var, assumption, proof.conclusion),
                    print_as_proof_forms)
    prover.add_tautology(Formula(Gorer_string_var, assumption, assumption))
    for line in proof.lines:
        if line.justification[0] == 'A' and line.justification[1].formula == assumption:
            continue
        if line.justification[0] == 'A':
            prover.add_mp(Formula(Gorer_string_var, assumption, line.formula),
                          prover.add_instantiated_assumption(line.formula,
                                                             line.justification[1],
                                                             line.justification[2]),
                          prover.add_tautology(Formula(Gorer_string_var, line.formula,
                                                       Formula(Gorer_string_var,
                                                               assumption,
                                                               line.formula))))

        elif line.justification[0] == 'T':
            prover.add_tautology(Formula(Gorer_string_var, assumption, line.formula))
        elif line.justification[0] == 'MP':
            first_justification = get_number_of_line(prover.proof,
                                                     Formula(Gorer_string_var, assumption, proof.lines[line.justification[1]].formula))
            second_justification = get_number_of_line(prover.proof,
                                                      Formula(Gorer_string_var, assumption, proof.lines[line.justification[2]].formula))
            prover.add_tautological_inference(str(Formula(Gorer_string_var, assumption, line.formula)),
                                              {first_justification, second_justification})
        elif line.justification[0] == 'UG':
            var = line.formula.variable
            predicate = line.formula.predicate
            predicate_assumption = Formula(Gorer_string_var, assumption, predicate)
            quantified_assumption_to_predicate = Formula('A', var, predicate_assumption)
            conclusion = Formula(Gorer_string_var, assumption,
                                       Formula('A', var, predicate))
            prover.add_mp(conclusion,
                          prover.add_ug(quantified_assumption_to_predicate,
                                        get_number_of_line(prover.proof, predicate_assumption)),
                          prover.add_instantiated_assumption(
                            Formula(Gorer_string_var, quantified_assumption_to_predicate, conclusion),
                            Prover.US,
                            {'R(' + var + ')': str(predicate),
                             'x': var, 'Q()': assumption}))
    return prover.proof

def get_number_of_line(proof, formula_to_find):
    proof_lines = [x.formula for x in reversed(proof.lines)]
    index = proof_lines.index(formula_to_find)
    return len(proof.lines) - 1 - index

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
    main_assumption = assumption
    new_proof = remove_assumption(proof, assumption, print_as_proof_forms)
    prover = Prover(new_proof.assumptions,
                    Formula(Unray_string_var,main_assumption),
                    print_as_proof_forms)
    #build new prover
    [prover._add_line(x.formula, x.justification) for x in new_proof.lines]
    index = len(prover.proof.lines) - 1
    formula_tautology = Formula(Gorer_string_var,
                                   Formula(Gorer_string_var, main_assumption,proof.conclusion),
                                   Formula(Gorer_string_var, Formula(Unray_string_var, proof.conclusion),
                                   Formula(Unray_string_var, main_assumption)))
    prover.add_mp(formula_tautology.second.second,
                  prover.add_tautology(Formula(Unray_string_var,proof.conclusion)),
                  prover.add_mp(formula_tautology.second, index,
                  prover.add_tautology(formula_tautology)))

    return prover.proof