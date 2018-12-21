""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/proofs.py """

from propositions.semantics import is_tautology as is_propositional_tautology
from predicates.syntax import *


class Schema:
    """ A schema of first-order formulae. A schema is given by an object of
        type Formula together with a set of constant, variable, and relation
        names that are to be considered as templates. A template constant name
        stands for any term. A template variable name stands for any variable
        name. A template relation name R stands for any first-order formula
        that does not "confuse" variables, that is, it can can refer to
        variables in the schema formula only through its instantiated formal
        parameters. The number of formal parameters of the template must
        be the same as the number of parameters in each relation invocation
        of the matching relation name in the schema formula """

    def __init__(self, formula, templates=set()):
        """ Create a schema from a Formula alongside a set of names of elements
            that are considered to be templates in it """
        assert type(formula) is Formula
        assert type(templates) is set
        for template in templates:
            assert is_constant(template) or is_variable(template) or \
                   is_relation(template)
        self.formula = formula
        self.templates = templates

    def __repr__(self):
        return "Schema: " + str(self.formula) + " [templates: " + \
               str(self.templates) + "]"

    def __eq__(self, other):
        return type(other) is Schema and self.formula == other.formula and \
               self.templates == other.templates

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    class BoundVariableError(Exception):
        """ Raised by instantiate_formula in case of a variable becoming bound
            during an instantiation in a way that is disallowed. See the
            docstring of instantiate_formula for more details """

        def __init__(self, variable_name, relation_name):
            assert is_variable(variable_name)
            assert is_relation(relation_name)
            self.variable_name = variable_name
            self.relation_name = relation_name

    @staticmethod
    def instantiate_formula(formula, constants_and_variables_instantiation_map,
                            relations_instantiation_map, bound_variables=set()):
        """ Return the Formula resulting in simultaneously making the following
            substitutions in formula:
            1) Replace every occurrence of every constant name or variable name
               element_name that is a key of
               constants_and_variables_instantiation_map with the term
               constants_and_variables_instantiation_map[element_name].
            2) Replace every relation invocation of relation_name that is a key
               of relations_instantiation_map as follows: let
               (formal_parameters,template)=
                   relations_instantiation_map[relation_name],
               then formal_parameters is an n-tuple of variable names and
               template is an object of type Formula; the free occurrences in
               template of the n variables names in formal_parameters should be
               simultaneously replaced with the respective arguments of the
               relation invocation in formula (where in each of them all
               relevant variables and constants should be replaced according to
               rule 1) above), and the result should be used to replace the
               corresponding relation invocation in formula.
            Raise a Schema.BoundVariableError exception if either of the
            following occurs during a replacement of rule 2) above:
               a) any variable that is free in template (as defined above) but
                  is not in formal_parameters becomes bound template is
                  substituted into formula, or is in the set bound_variables.
                  For example, if the self formula corresponds to
                  'Ax[Q(z)->R(x)]', constants_and_variables_instantiation_map is
                  {}, and relations_instantiation_map is {'Q': (('v',),'x=v')},
                  then Schema.BoundVariableError('x', 'Q') is raised since when
                  Q(z) is replaced with 'x=z', x becomes bound. For the same
                  arguments but with the above relations_instantiation_map
                  replaced with {'Q': (('v',),'y=v')}, a
                  Schema.BoundVariableError is raised if and only if 'y' is in
                  bound_variables.
               b) any variable in any of the arguments of the relation
                  invocation, after substituting into these arguments according
                  to rule 1) above, becomes bound by a quantification in
                  template when that argument is substituted into template.
                  For example, if the self formula corresponds to
                  'Ax[Q(z)->R(x)]', constants_and_variables_instantiation_map is
                  {'z':'plus(d,y)'}, and relations_instantiation_map is
                  {'Q': (('v',),'Ey[y=v]')}, then
                  Schema.BoundVariableError('y', 'Q') is raised since when v is
                  replaced with 'plus(d,y)' in 'Ey[y=v]', then y in 'plus(d,y)'
                  becomes bound by the existential quantification 'Ey' """
        assert type(formula) is Formula
        assert type(constants_and_variables_instantiation_map) is dict
        for element in constants_and_variables_instantiation_map:
            assert is_constant(element) or is_variable(element)
            assert type(constants_and_variables_instantiation_map[element]) is \
                   Term
            if is_variable(element):
                assert is_variable(
                    constants_and_variables_instantiation_map[element].root)
        assert type(relations_instantiation_map) is dict
        for relation in relations_instantiation_map:
            assert is_relation(relation)
            formal_parameters, template = relations_instantiation_map[relation]
            for parameter in formal_parameters:
                assert is_variable(parameter)
            assert type(template) is Formula
        for variable in bound_variables:
            assert is_variable(variable)
        # Task 9.3

        if is_unary(formula.root):
            first = Schema.instantiate_formula(formula.first,
                                               constants_and_variables_instantiation_map,
                                               relations_instantiation_map,
                                               bound_variables)
            return Formula(formula.root, first)
        if is_binary(formula.root):
            first = Schema.instantiate_formula(formula.first,
                                               constants_and_variables_instantiation_map,
                                               relations_instantiation_map,
                                               bound_variables)
            second = Schema.instantiate_formula(formula.second,
                                                constants_and_variables_instantiation_map,
                                                relations_instantiation_map,
                                                bound_variables)
            return Formula(formula.root, first, second)
        if is_equality(formula.root):
            return formula.substitute(constants_and_variables_instantiation_map)
        if is_relation(formula.root):
            formula_arguments = list()
            for arg in formula.arguments:
                formula_arguments.append(arg.substitute(constants_and_variables_instantiation_map))
            if formula.root in relations_instantiation_map:
                new_relations = dict()
                new_formula = relations_instantiation_map[formula.root][1]
                for var in new_formula.free_variables():
                    if var not in relations_instantiation_map[formula.root][0] and var in bound_variables:
                        raise Schema.BoundVariableError(var, formula.root)
                for index, item in enumerate(relations_instantiation_map[formula.root][0]):
                    new_relations[item] = formula_arguments[index]
                return new_formula.substitute(new_relations)
            else:
                return Formula(formula.root, formula_arguments)
        if is_quantifier(formula.root):
            var = formula.variable
            if var in constants_and_variables_instantiation_map:
                var = str(constants_and_variables_instantiation_map[var])
            bound_variables.add(var)
            return Formula(formula.root, var,
                           Schema.instantiate_formula(formula.predicate,
                                                      constants_and_variables_instantiation_map,
                                                      relations_instantiation_map,
                                                      bound_variables))

    def instantiate(self, instantiation_map):
        """ Return the first-order formula obtained by applying the mapping
            specified by instantiation_map to this schema. Each template
            constant name can be mapped to a term to be substituted for all
            occurrences of that template constant name, each template variable
            name can be mapped to a variable name to be substituted for all
            occurrences of that template variable name, and for each template
            relation name the mapping can have as a key a "signature" specifying
            formal parameters (variable names) for this relation name, and this
            key should be mapped to a first-order formula parametrized by these
            formal parameters, to be substituted for all occurrences of that
            template relation name. For example, if we instantiate
            s = Schema(Formula.parse('(Q(c1,c2)->(R(c1)->R(c2))'),
                       {'c1', 'c2', 'R'})
            with
            s.instantiate({'c1':Term.parse('plus(x,1)'), 'c2':Term.parse('c2'),
                           'R(z)':Formula.parse('Q(z,y)')})
            then the returned Formula object should have string representation
            '(Q(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))'. For any relation
            signature relation_signature, any free variables in the formula
            instantiation_map[relation_signature] beyond the formal parameters
            (i.e., the arguments/variables in relation_signatures) may not
            become bound by quantifications in the schema formula. Additionally,
            no quantifications in instantiation_map[relation_signature] may
            cause variables in terms that are substituted into
            instantiation_map[relation_signature] to become bound. If any of
            these is violated, then None should be returned. For example, we
            can instantiate
            s = Schema(Formula.parse('(Q(y)->Ax[R(x)->Q(y)])'), {'R', 'Q'})
            with
            s.instantiate({'R(w)':Formula.parse('w=0'),
                           'Q(v)':Formula.parse('z=v')})
            to get the Formula object represented by '(z=y->Ax[x=0->z=y])'.
            However, attempting to instantiate this schema with
            s.instantiate({'R(w)':Formula.parse('w=0'),
                           'Q(v)':Formula.parse('s(x)=v')})
            should return None since the assignment to Q(v) may not contain any
            variable name (except for the formal parameter v of Q(v)) that would
            become bound by a quantification in the schema formula. Attempting
            to instantiate the same schema with
            s.instantiate({'R(w)':Formula.parse('w=0'),
                           'Q(v)':Formula.parse('Ay[s(y)=v]')})
            should also return None since the assignment to Q(v) may not contain
            a quantification that causes any variable name in the terms
            substituted for its formal parameters to become bound """
        assert type(instantiation_map) is dict
        for key in instantiation_map:
            assert type(key) is str
            if is_variable(key):
                assert is_variable(instantiation_map[key])
            elif is_constant(key):
                assert type(instantiation_map[key]) is Term
            else:
                parsed_key = Formula.parse(key)
                assert is_relation(parsed_key.root)
                for argument in parsed_key.arguments:
                    assert is_variable(argument.root)
                assert type(instantiation_map[key]) is Formula
        # Task 9.4
        var_dic, relation_dic = dict(), dict()
        for key, value in instantiation_map.items():
            if is_variable(key):
                if key not in self.templates:
                    return None
                var_dic[key] = Term.parse(value)
            elif is_constant(key):
                if key not in self.templates:
                    return None
                var_dic[key] = value
            else:
                relation = Formula.parse(key)
                if relation.root not in self.templates:
                    return None
                new_arguments = []
                for argument in relation.arguments:
                    new_arguments.append(str(argument))
                relation_dic[relation.root] = (new_arguments, value)
        try:
            return Schema.instantiate_formula(self.formula, var_dic, relation_dic, set())
        except ForbiddenVariableError:
            return None
        except Schema.BoundVariableError:
            return None


class Proof:
    """A Proof of a first-order formula from a list of assumptions/axioms, each
       of which is a scheme. A proof holds a list of lines. Each line in the
       proof may be of one of the following forms:
       1) an instance of one of the assumption/axiom schemes,
       2) a tautology,
       3) derived from two previous lines via Modus Ponens, or
       4) derived from previous lines using universal generalization.
       The proof is valid if each line is validly deduced, and the last line
       deduces the conclusion """

    def __init__(self, assumptions, conclusion, lines):
        assert type(conclusion) is Formula
        for assumption in assumptions:
            assert type(assumption) is Schema
        self.assumptions = assumptions
        self.conclusion = conclusion
        self.lines = lines

    class Line:
        """ A line in a proof, containing a first-order formula deduced in this
            line, alongside a justificaiton that is a tuple of one of the
            following forms (corresponding to the four respective forms of
            lines listed above):
            1) ('A', assumption, instantiation_map), where assumption is an
               assumption/axiom and instantiation_map is a map from the
               templates of this assumption/axiom to substitution elements
            2) ('T',)
            3) ('MP', line1, line2), where line1 and line2 are line indices
            4) ('UG', line), where line is a line index """

        def __init__(self, formula, justification):
            assert type(formula) is Formula
            assert justification[0] in {'A', 'T', 'MP', 'UG'}
            self.formula = formula
            self.justification = justification

        def __repr__(self):
            return str(self.formula) + "     {" + str(self.justification) + "}"

    def __repr__(self):
        s = "Assumptions/Axioms:\n"
        for assumption in self.assumptions:
            s = s + str(assumption) + "\n"
        s = s + "Conclusion: " + str(self.conclusion) + "\nProof:\n"
        for line in self.lines:
            s = s + str(line) + "\n"
        return s

    def verify_a_justification(self, line):
        """ Returns whether the line with the given number is a valid
            instantiation of an assumption/axiom of this proof given in its
            justification via an instantiation map given in its justification
        """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'A'
        assert len(justification) == 3
        assert type(justification[1]) is Schema
        assert type(justification[2]) is dict
        for key in justification[2]:
            assert type(key) is str
            if is_variable(key):
                assert is_variable(justification[2][key])
            elif is_constant(key):
                assert type(justification[2][key]) is Term
            else:
                parsed_key = Formula.parse(key)
                assert is_relation(parsed_key.root)
                for argument in parsed_key.arguments:
                    assert is_variable(argument.root)
                assert type(justification[2][key]) is Formula
        # Task 9.5
        for assumption in self.assumptions:
            if assumption.instantiate(justification[2]) == self.lines[line].formula:
                return True
        return False

    def verify_t_justification(self, line):
        """ Returns whether the line with the given number is a (first-order
            logic) tautology """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'T'
        assert len(justification) == 1
        # Task 9.7

        formula = self.lines[line].formula.propositional_skeleton()[0]
        return is_propositional_tautology(formula)

    def verify_mp_justification(self, line):
        """ Returns whether the line with the given number is validly obtained
            by applying Modus Ponens to previous lines whose numbers are given
            in its justification """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'MP'
        assert len(justification) == 3
        assert type(justification[1]) == int
        assert type(justification[2]) == int
        # Task 9.8

        if justification[1] > line or justification[2] > line:
            return False
        p_implies_q = self.lines[justification[2]].formula
        return p_implies_q.first == self.lines[justification[1]].formula and self.lines[
            line].formula == p_implies_q.second

    def verify_ug_justification(self, line):
        """ Returns whether the line with the given number a valid universal
            generalization of a previous line whose number is given in its
            justification """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'UG'
        assert len(justification) == 2
        assert type(justification[1]) == int
        # Task 9.9
        formula = self.lines[line].formula
        return not (justification[1] >= line or formula.root == "E" or not is_quantifier(formula.root) or self.lines[
            justification[1]].formula != formula.predicate)

    def verify_justification(self, line):
        """ Returns whether the line with the given number is validly justified
        """
        justification_type = self.lines[line].justification[0]
        if justification_type == 'A':
            return self.verify_a_justification(line)
        if justification_type == 'T':
            return self.verify_t_justification(line)
        if justification_type == 'MP':
            return self.verify_mp_justification(line)
        if justification_type == 'UG':
            return self.verify_ug_justification(line)
        else:
            assert False

    def is_valid(self):
        """ Returns whether this proof validly proves its conclusion from its
            assumptions/axioms """
        if len(self.lines) == 0 or self.lines[-1].formula != self.conclusion:
            return False
        for line in range(len(self.lines)):
            if not self.verify_justification(line):
                return False
        return True


from propositions.proofs import Proof as PropositionalProof, \
    InferenceRule as PropositionalInferenceRule
from propositions.axiomatic_systems import AXIOMATIC_SYSTEM as \
    PROPOSITIONAL_AXIOMATIC_SYSTEM, \
    MP, I0, I1, I2, I3, N, NI, NN, R
from propositions.tautology import prove_tautology as \
    prove_propositional_tautology

# Schemata corresponding to the propositional-logic axioms for implies and not
I0_SCHEMA = Schema(Formula.parse('(P()->P())'), {'P'})
I1_SCHEMA = Schema(Formula.parse('(Q()->(P()->Q()))'), {'P', 'Q'})
I2_SCHEMA = Schema(Formula.parse(
    '((P()->(Q()->R()))->((P()->Q())->(P()->R())))'), {'P', 'Q', 'R'})
I3_SCHEMA = Schema(Formula.parse('(~P()->(P()->Q()))'), {'P', 'Q'})
N_SCHEMA = Schema(Formula.parse('((~Q()->~P())->(P()->Q()))'), {'P', 'Q'})
NI_SCHEMA = Schema(Formula.parse('(P()->(~Q()->~(P()->Q())))'), {'P', 'Q'})
NN_SCHEMA = Schema(Formula.parse('(P()->~~P())'), {'P'})
R_SCHEMA = Schema(Formula.parse(
    '((Q()->P())->((~Q()->P())->P()))'), {'P', 'Q'})

PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMATA = {I0_SCHEMA, I1_SCHEMA, I2_SCHEMA,
                                           I3_SCHEMA, N_SCHEMA, NI_SCHEMA,
                                           NN_SCHEMA, R_SCHEMA}

PROPOSITIONAL_AXIOM_TO_SCHEMA = {
    I0: I0_SCHEMA, I1: I1_SCHEMA, I2: I2_SCHEMA, I3: I3_SCHEMA, N: N_SCHEMA,
    NI: NI_SCHEMA, NN: NN_SCHEMA, R: R_SCHEMA}


def axiom_specialization_map_to_schema_instantiation_map(
        propositional_specialization_map, substitution_map):
    """ Given a specialization map that specifies how a propositional axiom from
        AXIOMATIC_SYSTEM specializes into some specialization, and given a
        substitution map from the propositional atoms of that specialization to
        predicate-logic formulae that was returned by some call to
        propositional_skeleton, return an instantiation map for instantiating
        the schema equivalent of that propositional axiom into a predicate-
        logic formula to which the above specialization is mapped by the given
        substitution map """
    assert type(propositional_specialization_map) is dict
    for variable in propositional_specialization_map:
        assert is_propositional_variable(variable)
        assert type(propositional_specialization_map[variable]) is \
               PropositionalFormula
    assert type(substitution_map) is dict
    for key in substitution_map:
        assert is_propositional_variable(key) and \
               type(substitution_map[key]) is Formula
    # Task 9.11.1


def prove_from_skeleton_proof(formula, skeleton_proof, substitution_map):
    """ Given a predicate-logic formula and a propositional proof from no
        assumptions, via AXIOMATIC_SYSTEM, of the propositional skeleton of
        formula, a skeleton that is mapped to formula by the given
        substitution_map, return a predicate-logic proof of formula from the
        axioms PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMATA that only uses 'A' and
        'MP' justifications """
    assert type(formula) is Formula
    assert type(skeleton_proof) is PropositionalProof
    assert skeleton_proof.statement.assumptions == [] and \
           skeleton_proof.rules.issubset(PROPOSITIONAL_AXIOMATIC_SYSTEM) and \
           skeleton_proof.is_valid()
    assert Formula.from_propositional_skeleton(
        skeleton_proof.statement.conclusion, substitution_map) == formula
    # Task 9.11.2


def prove_tautology(tautology):
    """ Return a proof of the given predicate-logic tautology from the axioms
        PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMATA that only uses 'A' and 'MP'
        justifications """
    assert type(tautology) is Formula
    # Task 9.12
