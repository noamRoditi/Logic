""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

from propositions.syntax import *
from propositions.semantics import *


class InferenceRule:
    """ An inference rule, i.e., a list of zero or more assumed formulae, and a
        conclusion formula """

    def __init__(self, assumptions, conclusion):
        assert type(conclusion) is Formula
        assert type(assumptions) is list
        for assumption in assumptions:
            assert type(assumption) is Formula
        self.assumptions = assumptions
        self.conclusion = conclusion

    def __eq__(self, other):
        return (type(other) is InferenceRule and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))
        
    def __repr__(self):
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self):
        """ Return the set of atomic propositions (variables) used in the
            assumptions and in the conclusion of self """
        # Task 4.1
        atomic_propositions = self.conclusion.variables()
        for assumption in self.assumptions:
            atomic_propositions = atomic_propositions | assumption.variables()
        return atomic_propositions

    def specialize(self, specialization_map):
        """ Return the specialization of the self inference rule obtained by
            simultaneously substituting each variable that is a key in
            specialization_map with the formula to which this value is mapped
            by specialization_map """
        for variable in specialization_map:
            assert is_variable(variable)
            assert type(specialization_map[variable]) is Formula
        # Task 4.4
        specialization_assumption_list = list()
        for assumption in self.assumptions:
            specialized_formula = assumption.substitute_variables(specialization_map)
            specialization_assumption_list.append(specialized_formula)
        specialization_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(specialization_assumption_list, specialization_conclusion)

    @staticmethod
    def merge_specialization_maps(specialization_map1, specialization_map2):
        """ Given two dictionaries specialization_map1 and specialization_map2,
            each of which may be None (instead of being a dictionary), return a
            single dictionary containing all (key, value) pairs that appear in
            either dictionary. If one of specialization_map1 or
            specialization_map2 is None, or if some key appears in both
            specialization_map1 and specialization_map2 but with different
            values, also return None """
        assert specialization_map1 is None or type(specialization_map1) is dict
        assert specialization_map2 is None or type(specialization_map2) is dict
        # Task 4.5a
        if specialization_map1 is None or specialization_map2 is None:
            return None
        keys_specialization_map1 = specialization_map1.keys()
        keys_specialization_map2 = specialization_map2.keys()
        for key in keys_specialization_map1:
            if key in keys_specialization_map2:
                if specialization_map1[key] != specialization_map2[key]:
                    return None
        combine_dict = dict()
        combine_dict.update(specialization_map1)
        combine_dict.update(specialization_map2)
        return combine_dict


    @staticmethod
    def formula_specialization_map(general, specialization):
        """ Return a dictionary specifying the (minimal) map by which the given
            general formula specializes to the given specialization. Return None
            if specialization is in fact not a specialization of general """
        assert type(general) is Formula and type(specialization) is Formula
        # Task 4.5b
        specialization_map = dict()
        result = InferenceRule.__formula_specialization_map_helper(general, specialization, specialization_map)
        if result is False:
            return None
        return specialization_map

    @staticmethod
    def __formula_specialization_map_helper(general, specialization, specialization_map):
        if is_variable(general.root):
            if general.root not in specialization_map.keys():
                specialization_map[general.root] = specialization
            else:
                if specialization_map[general.root] != specialization:
                    return False
            return True
        if general.root != specialization.root:
            return False
        if is_unary(general.root):
            return InferenceRule.__formula_specialization_map_helper(general.first, specialization.first, specialization_map)
        if is_binary(general.root):
            left_branch = InferenceRule.__formula_specialization_map_helper(general.first, specialization.first, specialization_map)
            right_branch = InferenceRule.__formula_specialization_map_helper(general.second, specialization.second, specialization_map)
            return left_branch and right_branch

    def specialization_map(self, specialization):
        """ Return a dictionary specifying the (minimal) map by which the self
            rule specializes to the given specialization. Return None if
            specialization is fact not a specialization of self """
        assert type(specialization) is InferenceRule
        # Task 4.5c
        specialization_map = dict()
        if len(self.assumptions) != len(specialization.assumptions):
            return None
        for i in range(len(self.assumptions)):
            current_map = InferenceRule.formula_specialization_map(self.assumptions[i], specialization.assumptions[i])
            if current_map is None:
                return None
            specialization_map = InferenceRule.merge_specialization_maps(specialization_map, current_map)
            if specialization_map is None:
                return None
        conclusion_map = InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion)
        if conclusion_map is None:
            return None
        specialization_map = InferenceRule.merge_specialization_maps(specialization_map, conclusion_map)
        return specialization_map

    def is_specialization_of(self, general):
        """ Is the self rule as specialization of the given general rule? """
        return general.specialization_map(self) is not None


class Proof:
    """ A deductive proof comprised of a statement of a "lemma" in the form of
        an inference rule, a set of inference rules that may be used in the
        proof, and a proof in the form of a list of lines that prove the lemma
        using these inference rules """

    def __init__(self, statement, rules, lines):
        assert type(statement) is InferenceRule
        assert type(rules) is set
        for rule in rules:
            assert type(rule) is InferenceRule
        assert type(lines) is list
        for line in lines:
            assert type(line) is Proof.Line
        self.statement = statement
        self.rules = rules
        self.lines = lines

    class Line:
        """ A line in a proof.  A line is comprised of a formula and a
            assumption for it via an inference rule. The rule may be None,
            meaning that the line is simply one of the assumptions of the
            lemma being proven (rather than an actual conclusion of an
            inference rule), or it may be one of the inferenece rules of the
            proof, in which case a list of indices of previous lines in the
            proof that constitute the assumptions of a specialization of this
            rule should be supplied (if this rule is assuptionless, then an
            an empty list, and not None, should be specified), and the line
            formula itself should be the conclusion of this specialization """

        def __init__(self, formula, rule=None, assumptions=None):
            assert type(formula) is Formula
            if rule is not None:
                assert type(rule) is InferenceRule
                assert type(assumptions) is list
                for assumption in assumptions:
                    assert type(assumption) is int
            self.formula = formula
            self.rule = rule
            self.assumptions = assumptions

        def __repr__(self):
            if (self.rule is None):
                return str(self.formula)
            return str(self.formula) + ' Inference Rule ' + str(self.rule) + \
                   ((" on " + str(self.assumptions))
                    if len(self.assumptions) > 0 else '')

        def is_assumption(self):
            return self.rule is None
        
    def __repr__(self):
        r = 'Proof for ' + str(self.statement) + ' using inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number):
        """ Returns the InferenceRule whose conclusion is the formula in the
            line whose number is given, and whose assumptions are the formulae
            in the lines specified as the assumptions of that line, in the
            order of the specificaions of the line numbers. Return None if that
            line is justified as an assumption """
        # Task 4.6a
        if self.lines[line_number].assumptions is None:
            return None
        assumptions = [self.lines[line_num].formula for line_num in self.lines[line_number].assumptions]
        return InferenceRule(assumptions, self.lines[line_number].formula)

    def is_line_valid(self, line_number):
        """ Does the line with the given number indeed validly follow from its
            assumption? If the line rule is None, then return whether the
            line formula is an assumption of the proof. Otherwise, return
            whether the line formula is the conclusion of a specialization of
            one of the inference rules of this proof that is specified as the
            line rule, whose assumptions are the formulae of the lines by which
            the line is justified, in the order of the specification of the line
            numbers """
        # Task 4.6b
        if self.lines[line_number].is_assumption():
            if self.lines[line_number].formula in self.statement.assumptions:
                return True
            return False
        if self.lines[line_number].rule not in self.rules:
            return False
        if self.rule_for_line(line_number).is_specialization_of(self.lines[line_number].rule):
            for assumption in self.lines[line_number].assumptions:
                if line_number <= assumption:
                    return False
            return True
        return False

    def is_valid(self):
        """ Return whether self indeed contains a valid proof of its claimed
            statement using its inference rules """
        # Task 4.6c
        for my_rule in self.rules:
            if not is_sound_inference(my_rule):
                return False
        for line_num in range(len(self.lines)):
            if not self.is_line_valid(line_num):
                return False
        return self.lines[-1].formula == self.statement.conclusion

    def offending_line(self):
        """ For debugging: return an error message containing the line number
            and string representation of the first invalid line in self. Return
            None if all lines are valid """
        for i in range(len(self.lines)):
            if not self.is_line_valid(i):
                return "Invalid Line " + str(i) + ": " + str(self.lines[i])

# Chapter 5 tasks


def __specialize(formula, instantiation_map):
    if is_variable(formula.root):
        if formula.root in instantiation_map.keys():
            return instantiation_map[formula.root]
        return Formula(formula.root)
    if is_unary(formula.root):
        return Formula('~', __specialize(formula.first, instantiation_map))
    if is_binary(formula.root):
        return Formula(formula.root,    __specialize(formula.first, instantiation_map),
                       __specialize(formula.second, instantiation_map))


def prove_specialization(proof, specialization):
    """ Given a proof of an inference rule and given a specialization of that
        rule, return a proof of the specialization using the same set of
        inference rules that is used in the given proof """
    assert type(proof) is Proof
    assert type(specialization) is InferenceRule
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    new_lines = []
    specialization_map = proof.statement.specialization_map(specialization)
    for line in proof.lines:
        specialized_formula = __specialize(line.formula, specialization_map)
        new_lines.append(Proof.Line(specialized_formula, line.rule, line.assumptions))
    return Proof(specialization, proof.rules, new_lines)


def inline_proof_once(proof, line_number, lemma_proof):
    """ Given a proof and another proof that proves the inference rule that
        justifies the line in the first proof whose number is given, return a
        new proof where that line is replaced by the full (specialized) list of
        lines proving it from the lines by which it is justified. The resulting
        proof is a valid proof of the original statement using the set of rules
        that is the union of the rules used in the two given proofs, but where
        the rule that was originally used in the line with the given number is
        no longer used in the corresponding lines in the returned proof (and
        thus, this rule is used one less time in the returned proof than in the
        original proof) """
    assert type(proof) is Proof
    assert type(lemma_proof) is Proof
    assert proof.lines[line_number].rule == lemma_proof.statement
    # Task 5.2a
    assumption_num = 0
    proof_lines = [line for i, line in enumerate(proof.lines) if i < line_number]
    num_of_assumptions = len(proof.lines[line_number].assumptions)
    specialized_lemma = prove_specialization(lemma_proof, proof.rule_for_line(line_number))
    assumptions = []
    for line in specialized_lemma.lines:
        index_map = {}
        if assumption_num < num_of_assumptions:
            j = 0
            for proof_line in proof_lines:
                if line.formula is proof_line.formula:
                    index_map[assumption_num] = j
                j += 1
        else:
            if line.assumptions is not None:
                [assumptions.append(index_map[index]) if index in index_map else assumptions.append((index + line_number - num_of_assumptions)) for index in line.assumptions]
            proof_lines.append(Proof.Line(line.formula, line.rule, assumptions))
            assumptions = []
        assumption_num += 1
    assumptions = []
    for line in proof.lines[line_number + 1:]:
        if line.assumptions is not None:
            [assumptions.append(index - 1 - num_of_assumptions + len(lemma_proof.lines)) for index in line.assumptions]
        proof_lines.append(Proof.Line(line.formula, line.rule, assumptions))
        assumptions = []
    return Proof(proof.statement, proof.rules.union(lemma_proof.rules), proof_lines)


def inline_proof(main_proof, lemma_proof):
    """ Given a proof and a proof of an inference rule that is used (any number
        of times) in the main proof, return a new proof where all uses of the
        "lemma" inference rule are replaced by an inlined proof of (the
        appropriate specialization of) that rule from the lines by which it is
        justified. The resulting proof is a valid proof of the original
        statement using the set of rules that is the union of the rules used in
        both proofs but without the "lemma" inference rule """
    assert type(main_proof) is Proof
    assert type(lemma_proof) is Proof
    # Task 5.2b
    rules = set([rule for rule in main_proof.rules])
    rules.remove(lemma_proof.statement)
    main_proof_lines = main_proof.lines
    proof_without_lemma = Proof(main_proof.statement, rules, main_proof_lines)
    proof_rule_to_exclude = [line_num for line_num, line in enumerate(main_proof_lines) if line.rule == lemma_proof.statement]
    line_offset = 0
    for line_num in proof_rule_to_exclude:
        proof_without_lemma_lines_len = len(proof_without_lemma.lines)
        proof_without_lemma = inline_proof_once(proof_without_lemma, line_num + line_offset, lemma_proof)
        line_offset += len(proof_without_lemma.lines) - proof_without_lemma_lines_len
    return proof_without_lemma


