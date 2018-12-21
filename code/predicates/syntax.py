""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula, \
    is_variable as is_propositional_variable
from predicates.util import *


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
    return ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) \
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
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        else:
            result = self.root + '('
            for arg in self.arguments:
                result = result + str(arg) + ','
            return result[:len(result) - 1] + ')'

    @staticmethod
    def parse_prefix(s):
        """ Parse a term from a prefix of the given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        assert type(s) is str
        # Task 7.3.1
        if is_constant(s[0]) or is_variable(s[0]):
            for i in range(1, len(s) + 1):
                if is_constant(s[:i]) or is_variable(s[:i]):
                    continue
                return Term(s[:i - 1]), s[i - 1:]
            return Term(s), ""
        if is_function(s[0]):
            remainder = s[s.find('(') + 1:]
            arguments, remainder = Formula.find_reminder_arguments(remainder)
            fx = s[:s.find('(')]
            return Term(fx, arguments), remainder[1:]

    @staticmethod
    def parse(s):
        """ Return a term parsed from the given string representation """
        assert type(s) is str
        # Task 7.3.2
        return Term.parse_prefix(s)[0]

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5
        if is_constant(self.root):
            return set()
        if is_variable(self.root):
            return {self.root}
        if is_function(self.root):
            result = set()
            for argument in self.arguments:
                result = result | argument.variables()
            return result

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1
        term_pairs = set()
        if is_function(self.root):
            function_pair = self.root, len(self.arguments)
            term_pairs.add(function_pair)
            for argument in self.arguments:
                term_pairs = term_pairs | argument.functions()
        return term_pairs

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
        return self.substitute_helper(substitution_map, forbidden_variables)

    def substitute_helper(self, substitution_map, forbidden_variables=set(), bound_variables=set()):
        if is_function(self.root):
            new_args = []
            for arg in self.arguments:
                new_args.append(arg.substitute(substitution_map, forbidden_variables))
            return Term(self.root, new_args)
        else:
            if self.root in substitution_map and self.root not in bound_variables:
                variables = substitution_map[self.root].variables()
                for variable in variables:
                    if variable in forbidden_variables:
                        raise ForbiddenVariableError(variable)
                return substitution_map[self.root]
            else:
                return Term(self.root)


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


def find_closing_bracket_index(s, start_index, open_bracket="(", closed_bracket=")"):
    """ helper function that given start_index that is an open bracket will return
    last index of the closing bracket"""
    numOfOpenBrackets = 1
    lastBracketIndex = start_index
    # find the last bracket for the formula
    while numOfOpenBrackets > 0 and lastBracketIndex + 1 < len(s):
        if s[lastBracketIndex + 1] == open_bracket:
            numOfOpenBrackets += 1
        elif s[lastBracketIndex + 1] == closed_bracket:
            numOfOpenBrackets -= 1
        lastBracketIndex += 1
    if s[lastBracketIndex] != closed_bracket or numOfOpenBrackets > 0:
        return None
    return lastBracketIndex


class Formula:
    """ A Formula in first-order logic """

    def __init__(self, root, first=None, second=None):
        if is_equality(root):  # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_relation(root):  # Populate self.root and self.arguments
            assert second is None
            assert type(first) is list
            for argument in first:
                assert type(argument) is Term
            self.root, self.arguments = root, first
        elif is_unary(root):  # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        elif is_binary(root):  # Populate self.first and self.second
            assert type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second
        else:  # Populate self.variable and self.predicate
            assert is_quantifier(root) and is_variable(first) and \
                   type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        # Task 7.2
        if is_constant(self.root) or is_variable(self.root):
            return '(' + self.root + ')'
        if is_unary(self.root):
            return str(self.root) + str(self.first)
        if is_binary(self.root):
            return "(" + str(self.first) + self.root + str(self.second) + ")"
        if is_equality(self.root):
            return str(self.first) + self.root + str(self.second)
        if is_quantifier(self.root):
            return str(self.root) + self.variable + '[' + str(self.predicate) + "]"
        return Formula.__term__repr(self)

    def __term__repr(self):
        term = str(self.root) + "("
        for argument in self.arguments:
            term = term + str(argument) + ","
        if term[-1] == ",":
            return term[:-1] + ")"
        return term + ")"

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

        if is_unary(s[0]):
            formula, remainder = Formula.parse_prefix(s[1:])
            return Formula('~', formula), remainder
        if s[0] is "(":  # binary case
            left_formula, remainder = Formula.parse_prefix(s[1:])
            if remainder[0] is "-":
                root = "->"
            else:
                root = remainder[0]
            right_formula, remainder = Formula.parse_prefix(remainder[len(root):])
            return Formula(root, left_formula, right_formula), remainder[1:]
        if is_relation(s[0]):
            remainder = s[s.find('(') + 1:]
            relation = s[:s.find('(')]
            arguments, remainder = Formula.find_reminder_arguments(remainder)
            return Formula(relation, arguments), remainder[1:]
        if is_quantifier(s[0]):
            remainder = s[s.find('['):]
            variable = s[1:s.find('[')]
            formula, remainder = Formula.parse_prefix(remainder[1:])
            return Formula(s[0], variable, formula), remainder[1:]
        if "=" in s:
            first, remainder = Term.parse_prefix(s)
            second, remainder = Term.parse_prefix(remainder[1:])
            return Formula('=', first, second), remainder

    @staticmethod
    def find_reminder_arguments(remainder):
        arguments = []
        while remainder.index(")") > 0:
            formula, remainder = Term.parse_prefix(remainder)
            arguments.append(formula)
            if remainder[0] == ',':
                remainder = remainder[1:]
        return arguments, remainder

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from the given string
            representation """
        assert type(s) is str
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6
        if is_unary(self.root):
            return self.first.free_variables()
        if is_binary(self.root):
            return self.first.free_variables() | (self.second.free_variables())
        if is_equality(self.root):
            return Term.variables(self.first) | (Term.variables(self.second))
        if is_quantifier(self.root):
            return self.predicate.free_variables() - set(self.variable)
        if is_relation(self.root):
            free_variables = set()
            for item in self.arguments:
                free_variables = free_variables | Term.variables(item)
            return free_variables

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2
        formula_pairs = set()
        if is_quantifier(self.root):
            formula_pairs = formula_pairs | self.predicate.functions()
        if is_unary(self.root):
            formula_pairs = formula_pairs | self.first.functions()
        if is_binary(self.root):
            formula_pairs = formula_pairs | self.first.functions() | self.second.functions()
        if is_equality(self.root):
            formula_pairs = formula_pairs | self.first.functions() | self.second.functions()
        if is_relation(self.root):
            for argument in self.arguments:
                formula_pairs = formula_pairs | argument.functions()
        if is_function(self.root):
            formula_pairs.add((self.root, len(self.arguments)))
            for argument in self.arguments:
                formula_pairs = formula_pairs | argument.functions()
        return formula_pairs

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3
        formula_relations_pairs = set()
        if is_quantifier(self.root):
            formula_relations_pairs = formula_relations_pairs | self.predicate.relations()
        if is_unary(self.root):
            if type(self.first) is Formula:
                formula_relations_pairs = formula_relations_pairs | self.first.relations()
        if is_binary(self.root) or is_equality(self.root):
            if type(self.first) is Formula:
                formula_relations_pairs = formula_relations_pairs | self.first.relations()
            if type(self.second) is Formula:
                formula_relations_pairs = formula_relations_pairs | self.second.relations()
        if is_relation(self.root):
            formula_relations_pairs.add((self.root, len(self.arguments)))
            for argument in self.arguments:
                if type(argument) is Formula:
                    formula_relations_pairs = formula_relations_pairs | argument.relations()
        return formula_relations_pairs

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
        return self.substitute_helper(substitution_map, forbidden_variables, set())

    def substitute_helper(self, substitution_map, forbidden_variables=set(), bound_variables=set()):
        if is_unary(self.root):
            return Formula(self.root,
                           self.first.substitute_helper(substitution_map, forbidden_variables, bound_variables))
        if is_quantifier(self.root):
            forbidden_vars = forbidden_variables.copy()
            forbidden_vars.add(self.variable)
            bound_variables.add(self.variable)
            return Formula(self.root, self.variable, self.predicate.substitute_helper(substitution_map,
                                                                                      forbidden_vars, bound_variables))
        if is_relation(self.root):
            new_args = []
            for arg in self.arguments:
                new_args.append(arg.substitute_helper(substitution_map, forbidden_variables, bound_variables))
            return Formula(self.root, new_args)
        else:
            first = self.first.substitute_helper(substitution_map, forbidden_variables, bound_variables)
            second = self.second.substitute_helper(substitution_map, forbidden_variables, bound_variables)
            return Formula(self.root, first, second)

    def propositional_skeleton(self):
        """ Return a pair. The first element of the returned pair is a
            PropositionalFormula that is the skeleton of this one, where the
            variables in the propositional formula have the names z1,z2,...
            (obtained by calling next(fresh_variable_name_generator)), starting
            from left to right. The second element in the pair is a map from
            variable names in the propositional formula to subformulae of the
            original formula """
        # Task 9.6
        z_dict = dict()
        return self.propositional_skeleton_helper(z_dict), {y: x for x, y in z_dict.items()}

    def propositional_skeleton_helper(self, z_dict):
        """ Recursive Helper function. This function return a PropositionalFormula that is the skeleton
            of this one, with the variables in the Formula being z1, z2 etc. The Recursive function also
            keeps track of the  previous z-items that were created, to avoid double naming for identical
            objects.
            For unary and binary operands, the function goes deeper into the recursion, and otherwise
            we create a new z-item."""
        if self in z_dict:
            return z_dict[self]
        if is_unary(self.root):
            return PropositionalFormula(self.root, self.first.propositional_skeleton_helper(z_dict))
        if is_binary(self.root):
            return PropositionalFormula(self.root, self.first.propositional_skeleton_helper(z_dict),
                                        self.second.propositional_skeleton_helper(z_dict))
        z_dict[self] = PropositionalFormula(next(fresh_variable_name_generator))
        return z_dict[self]

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
        formula_str = str(skeleton)
        for key in substitution_map:
            formula_str = formula_str.replace(key, str(substitution_map[key]))
        return Formula.parse(formula_str)