""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable
# from predicates.util import *

class ForbiddenVariableError(Exception):
    """ Raised when a substituted expression contains a free variable that is
        forbidden in that context. See the docstrings of Term.substitute and
        Formula.substitute for more details """

    def __init__(self, variable_name):
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_variable(s):
    """ Is s a variable name? """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_constant(s):
    """ Is s a constant name? """
    return  ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) \
            and s.isalnum()

def is_function(s):
    """ Is s a function name? """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

class Term:
    """ A term in a first-order logical formula, composed from variable names
        and constant names, and function names applied to them """

    def __init__(self, root, arguments=None):
        if is_variable(root) or is_constant(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert type(arguments) is list and len(arguments) > 0
            for argument in arguments:
                assert type(argument) is Term
            self.root = root
            self.arguments = arguments

    def __eq__(self, other):
        return type(other) is Term and str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        """ Return the usual (functional) representation of self """
        # Task 7.1

    @staticmethod
    def parse_prefix(s):
        """ Parse a term from a prefix of the given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        assert type(s) is str
        # Task 7.3.1

    @staticmethod
    def parse(s):
        """ Return a term parsed from the given string representation """
        assert type(s) is str
        # Task 7.3.2

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1

    def substitute(self, substitution_map, forbidden_variables=set()):
        """ Return a term obtained from this term where all the occurrences of
            each constant name or variable name element_name that appears as a
            key in the dictionary substitution_map are simultaneously replaced
            with the term substitution_map[element_name]. Raise a
            ForbiddenVariableError if a term that is used in the requested
            substitution contains a variable from forbidden_variables. For
            example, if the self term corresponds to 'x=c' and substitution_map
            is {'c':'plus(d,y)'}, then the exception ForbiddenVariableError('y')
            is raised if y is in forbidden_variables """
        assert type(substitution_map) is dict
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
            assert type(substitution_map[element_name]) is Term
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

def is_equality(s):
    """ Is s the equality relation? """
    return s == '='

def is_relation(s):
    """ Is s a relation name? """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_unary(s):
    """ Is s a unary Boolean operator? """
    return s == '~'

def is_binary(s):
    """ Is s a binary Boolean operator? """
    return s == '&' or s == '|' or s == '->'

def is_quantifier(s):
    """ Is s a quantifier? """
    return s == 'A' or s == 'E'

class Formula:
    """ A Formula in first-order logic """
    
    def __init__(self, root, first=None, second=None):
        if is_equality(root): # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_relation(root): # Populate self.root and self.arguments
            assert second is None
            assert type(first) is list
            for argument in first:
                assert type(argument) is Term
            self.root, self.arguments = root, first
        elif is_unary(root): # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        elif is_binary(root): # Populate self.first and self.second
            assert type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second           
        else: # Populate self.variable and self.predicate
            assert is_quantifier(root) and is_variable(first) and \
                   type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        # Task 7.2

    def __eq__(self, other):
        return type(other) is Formula and str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def parse_prefix(s):
        """ Parse a first-order formula from a prefix of the given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        assert type(s) is str
        # Task 7.4.1

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from the given string
            representation """
        assert type(s) is str
        # Task 7.4.2

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3

    def substitute(self, substitution_map, forbidden_variables=set()):
        """ Return a first-order formula obtained from this formula where the
            all occurrences of each constant name element_name and all *free*
            occurrences of each variable name element_name for element_name
            that appears as a key in the dictionary substitution_map are
            simultaneously replaced with the term
            substitution_map[element_name]. Raise a ForbiddenVariableError if a
            term that is used in the requested substitution contains a variable
            from forbidden_variables or contains a variable occurrence that
            becomes bound when that term is substituted into the self formula.
            For example, if the self formula corresponds to 'Ay[x=c]' and
            substitution_map is {'c':'plus(d,y)'}, then the exception
            ForbiddenVariableError('y') is raised since the y in 'plus(d,y)'
            becomes bound by the universal quantification 'Ay' when the
            substitution is performed """
        assert type(substitution_map) is dict
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
            assert type(substitution_map[element_name]) is Term
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(self):
        """ Return a pair. The first element of the returned pair is a
            PropositionalFormula that is the skeleton of this one, where the
            variables in the propositional formula have the names z1,z2,...
            (obtained by calling next(fresh_variable_name_generator)), starting
            from left to right. The second element in the pair is a map from
            variable names in the propositional formula to subformulae of the
            original formula """
        # Task 9.6

    @staticmethod
    def from_propositional_skeleton(skeleton, substitution_map):
        """ Return a first-order predicate logic formula obtained from the given
            propositional skeleton by substituting each variable with the
            formula mapped to it by substitution_map """
        assert type(skeleton) is PropositionalFormula
        assert type(substitution_map) is dict
        for key in substitution_map:
            assert is_propositional_variable(key) and \
                   type(substitution_map[key]) is Formula
        # Task 9.10
