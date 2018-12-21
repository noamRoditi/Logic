""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/deduction.py """
from copy import deepcopy

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof, consequent, conditional):
    """ Given a proof of a formula antecedent, given a formula consequent, and
        and given an assumptionless inference rule conditional of which the
        assumptionless inference rule with conclusion (antecedent->consequent)
        is a specialization, return a proof of consequent using the same set of
        assumptions and same set of inference rules used in the given proof of
        antecedent, and in addition MP and conditional """
    assert type(antecedent_proof) is Proof and antecedent_proof.is_valid()
    assert type(consequent) is Formula
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
def combine_proofs(antecedent1_proof, antecedent2_proof, consequent,
                   double_conditional):
    """ Given respective proofs of formulae antecedent1 and antecedent2 that
        have the same assumptions and use the same inference rules, given a
        formula consequent, and given an assumptionless inference rule
        double_conditional of which the assumptionless inference rule with
        conclusion (antecedent1->(antecedent2->consequent)) is a specialization,
        return a proof of consequent from the same assumptions and same set of
        inference rules used in the two given proofs, and in addition MP and
        double_conditional """
    assert type(antecedent1_proof) is Proof and antecedent1_proof.is_valid()
    assert type(antecedent2_proof) is Proof and antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert type(consequent) is Formula
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b


def remove_assumption(proof):
    """ Given a proof of some conclusion q from some nonempty list of
        assumptions, the last of which we denote by p, where the proof uses
        some set of inference rules all of which have empty assumptions lists,
        except perhaps MP, return a valid proof of '(p->q)' from the same
        list of assumptions but without the last one, using the same set of
        inference rules, and in addition MP, I0, I1, I2 """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or rule.assumptions == []
    # Task 5.4

    newRules = proof.rules.union({MP, I0, I1, I2})
    newLines = []
    p_assumptions = proof.statement.assumptions[-1]
    q_conclusion = proof.statement.conclusion
    newLines.append(Proof.Line(Formula('->', p_assumptions, p_assumptions), I0, []))
    implies_self_index = len(newLines)-1
    LineConclusionDic = dict()
    for i, line in enumerate(proof.lines):
        if line.formula == p_assumptions:
            LineConclusionDic[i] = implies_self_index
        elif line.rule is None or len(line.assumptions) == 0:
            newLines.append(line)
            newLines.append(
                Proof.Line(Formula('->', line.formula, Formula('->', p_assumptions, line.formula)), I1, []))
            newLines.append(
                Proof.Line(Formula('->', p_assumptions, line.formula), MP,
                           [len(newLines)-2, len(newLines)-1]))
            LineConclusionDic[i] = len(newLines)-1
        elif len(line.assumptions)>0 and line.rule is not None:
            assump1 = proof.lines[line.assumptions[0]].formula
            MP2_formula = Formula('->', p_assumptions, line.formula)
            MP1_formula = Formula('->', Formula('->', p_assumptions, assump1), MP2_formula)
            newLines.append(
                Proof.Line(Formula('->',
                                   Formula('->', p_assumptions,Formula('->', assump1, line.formula)),
                                   MP1_formula), I2, []))
            assump2 = LineConclusionDic[line.assumptions[1]]
            newLines.append(
                Proof.Line(MP1_formula, MP, [assump2, len(newLines) - 1]))
            newLines.append(
                Proof.Line(MP2_formula, MP, [LineConclusionDic[line.assumptions[0]], len(newLines)-1]))
            LineConclusionDic[i] = len(newLines) - 1
    #create new inference rule
    newAssumptions = []
    for assumption in proof.statement.assumptions:
        if assumption != p_assumptions:
            newAssumptions.append(deepcopy(assumption))
    newConclusion = Formula('->', p_assumptions, q_conclusion)
    newProof = Proof(InferenceRule(newAssumptions, newConclusion), newRules, newLines)
    return newProof
def proof_from_inconsistency(proof_of_affirmation, proof_of_negation,
                             conclusion):
    """ Given two proofs, one of a formula f and the other of its negation '~f',
        both from the same list of assumptions and via the same set of inference
        rules, a set that contains MP and I3, and given an arbitrary formula
        conclusion, return a proof of conclusion from the same assumptions via
        the same set of inference rules """
    assert proof_of_affirmation.is_valid() and proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    assert proof_of_affirmation.rules.issuperset({MP, I3})
    assert type(conclusion) is Formula
    # Task 5.6
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I3)

def prove_by_contradiction(proof):
    """ Given a proof of the contradiction '~(p->p)' from a list of
        assumptions, the last assumption of which is '~f' for some formula f,
        return a proof of f from the same list of assumptions but without the
        last one, using the same set of inference rules, and in addition MP,
        I0, I1, I2, and N """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert proof.statement.assumptions[-1].root == '~'
    # Task 5.7
