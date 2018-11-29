""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from predicates.syntax import *

class Model:
    """ A model for first-order expressions: contains a universe - a set of
        elements, and a dictionary that maps each constant name to an element,
        each k-ary relation name to a set of k-tuples of elements, and each
        k-ary function name to a map from k-tuples of elements to an element """

    def __init__(self, universe, meaning):
        assert type(universe) is set
        assert type(meaning) is dict
        for key in meaning:
            if is_constant(key): # element (in universe)
                assert meaning[key] in universe
            elif is_function(key): # mapping from tuples of elements to elements
                mapping = meaning[key]
                assert type(mapping) is dict
                for mapping_key in mapping:
                    assert type(mapping_key) is tuple
                    for element in mapping_key:
                        assert element in universe
                    assert mapping[mapping_key] in universe
            else: # set of tuples of elements (for which the relation holds)
                assert is_relation(key)
                mapping = meaning[key]
                assert type(mapping) is set
                for mapping_key in mapping:
                    assert type(mapping_key) is tuple
                    for element in mapping_key:
                        assert element in universe
        self.universe = universe
        self.meaning = meaning

    def __repr__(self):
        return 'Universe=' + str(self.universe) + '; Meaning=' + str(self.meaning)
        
    def evaluate_term(self, term, assignment={}):
        """ Return the value of the given term in this model, where variables   
            get their value from the given assignment """
        assert term.variables().issubset(assignment.keys())
        # Task 7.7
        if is_constant(term.root):
            return self.meaning[term.root]
        if is_variable(term.root):
            return assignment[term.root]
        if is_function(term.root):
            values = tuple([Model.evaluate_term(self, argument, assignment) for argument in term.arguments])
            return self.meaning[term.root].get(values)

    def evaluate_formula(self, formula, assignment={}):
        """ Return the value of the given formula in this model, where
            variable occurrences that are free in the formula get their values
            from the given assignment """
        assert formula.free_variables().issubset(assignment.keys())
        # Task 7.8
        if is_unary(formula.root):
            return not Model.evaluate_formula(self, formula.first, assignment)
        if is_binary(formula.root):
            return self.formula_evaluation_is_binary(formula,assignment)
        if is_equality(formula.root):
            return Model.evaluate_term(self, formula.first, assignment) is Model.evaluate_term(self, formula.second, assignment)
        if is_relation(formula.root):
            argument = tuple([Model.evaluate_term(self, argument, assignment) for argument in formula.arguments])
            return argument in self.meaning[formula.root]
        if is_quantifier(formula.root):
            return self.formula_evaluation_is_quantifier(formula, assignment)

    def formula_evaluation_is_binary(self, formula, assignment):
        if formula.root == '&':
            return Model.evaluate_formula(self, formula.first, assignment) and \
                   Model.evaluate_formula(self, formula.second, assignment)
        if formula.root == '|':
            return Model.evaluate_formula(self, formula.first, assignment) or \
                   Model.evaluate_formula(self, formula.second, assignment)
        return Model.evaluate_formula(self, formula.first, assignment) or not \
            Model.evaluate_formula(self, formula.second, assignment)

    def formula_evaluation_is_quantifier(self,formula, assignment):
        if formula.root == 'A':
            for element in self.universe:
                assignment[formula.variable] = element
                if Model.evaluate_formula(self, formula.predicate, assignment):
                    continue
                return False
            return True
        if formula.root == 'E':
            for element in self.universe:
                assignment[formula.variable] = element
                if Model.evaluate_formula(self, formula.predicate, assignment):
                    return True
            return False

    def is_model_of(self, formulae):
        """ Return whether self is a model of the given formulae. For this to be
            true, each of the formulae must be satisfied, and if the formula has
            free variables, then it must be satisfied for every assignment of
            elements of the universe to the free variables """
        for formula in formulae:
            assert type(formula) is Formula
        # Task 7.9
