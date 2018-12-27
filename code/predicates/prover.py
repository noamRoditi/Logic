""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prover.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.util import *


class Prover:
    """ A class for gradually constructing a first-order Proof for a given
        conclusion, from given assumptions as well as from the six AXIOMS
        Universal Instantiation (UI), Existential Introduction (EI), Universal
        Simplification (US), Existential Simplification (ES), Reflexivity (RX),
        and Meaning of Equality (ME) """
    UI = Schema(Formula.parse('(Ax[R(x)]->R(c))'), {'R', 'x', 'c'})
    EI = Schema(Formula.parse('(R(c)->Ex[R(x)])'), {'R', 'x', 'c'})
    US = Schema(Formula.parse('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'),
                {'Q', 'R', 'x'})
    ES = Schema(Formula.parse('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())'),
                {'Q', 'R', 'x'})
    RX = Schema(Formula.parse('c=c'), {'c'})
    ME = Schema(Formula.parse('(c=d->(R(c)->R(d)))'), {'R', 'c', 'd'})
    AXIOMS = {UI, EI, US, ES, RX, ME}

    def __init__(self, assumptions, conclusion, print_as_proof_forms=False):
        """ Constructs a new Prover. Each element in assumptions may either be
            a Schema, a formula, or the string representation of a formula, with
            the latter two interpreted as a schema with no templates whose
            unique instance is the given or represented formula. Prover.AXIOMS
            are automatically added to the assumptions. conclusion is the
            conclusion formula or its string representation. The Boolean flag
            print_as_proof_forms specifies whether the proof being constructed
            is to be printed in real time as it is being constructed """
        self.proof = Proof(
            Prover.AXIOMS.union(
                {assumption if type(assumption) is Schema
                 else Schema(assumption) if type(assumption) is Formula
                else Schema(Formula.parse(assumption))
                 for assumption in assumptions}),
            conclusion if type(conclusion) is Formula
            else Formula.parse(conclusion),
            [])
        self.print_as_proof_forms = print_as_proof_forms
        if self.print_as_proof_forms:
            print("Starting Proof")
            print("Assumptions: AXIOMS +", assumptions)
            print("Conclusion:", self.proof.conclusion)

    def _add_line(self, statement, justification):
        """ Append to the proof being constructed the validly justified line
            whose formula is statement and whose justification is given. The
            validity of the added line is asserted, and its number in this
            proof is returned. statement may also be given as a string
            representation (instead of a Formula) """
        if type(statement) is str:
            statement = Formula.parse(statement)
        assert type(statement) is Formula
        line = len(self.proof.lines)
        self.proof.lines.append(Proof.Line(statement, justification))
        assert self.proof.verify_justification(line)
        if self.print_as_proof_forms:
            print(str(line) + ")", statement)
        return line

    def add_instantiated_assumption(self, instance, schema, instantiation_map):
        """ Append to the proof being constructed a validly justified line
            whose formula is instance, which is the result of an instantiation
            via instantiation_map of the given schema, which must be one of the
            assumptions/axioms of this proof. The number of the added line in
            this proof is returned. instance may also be given as a string
            representation (instead of a Formula), and so may any value of
            instantiation_map (instead of a Term or a Formula) """
        assert type(instance) in {Formula, str}
        assert type(schema) is Schema
        instantiation_map = instantiation_map.copy()
        for key in instantiation_map:
            assert type(key) is str
            if is_variable(key):
                assert is_variable(instantiation_map[key])
            elif is_constant(key):
                if type(instantiation_map[key]) is str:
                    instantiation_map[key] = Term.parse(instantiation_map[key])
                assert type(instantiation_map[key]) is Term
            else:
                parsed_key = Formula.parse(key)
                assert is_relation(parsed_key.root)
                for argument in parsed_key.arguments:
                    assert is_variable(argument.root)
                if type(instantiation_map[key]) is str:
                    instantiation_map[key] = \
                        Formula.parse(instantiation_map[key])
                assert type(instantiation_map[key]) is Formula
        return self._add_line(instance, ('A', schema, instantiation_map))

    def add_assumption(self, assumption):
        """ Append to the proof being constructed a validly justified line
            whose formula is assumption, which is the (unique) instance of a
            schema with no templates that is one of the assumptions/axioms of
            this proof. The number of the added line in this proof is returned.
            assumption may also be given as a string representation (instead of
            a Formula) """
        if type(assumption) is str:
            assumption = Formula.parse(assumption)
        assert type(assumption) is Formula
        return self.add_instantiated_assumption(assumption, Schema(assumption),
                                                {})

    def add_tautology(self, tautology):
        """ Append to the proof being constructed a validly justified line
            whose formula is tautology, which is a tautology. The number of the
            added line in this proof is returned. tautology may also be given as
            a string representation (instead of a Formula) """
        assert type(tautology) in {Formula, str}
        return self._add_line(tautology, ('T',))

    def add_mp(self, consequent, antecedent_line, conditional_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is consequent, and which is a result of applying
            Modus Ponens over lines atecedent_line and conditional_line in this
            proof. The number of the added line in this proof is returned.
            consequent may also be given as a string representation (instead of
            a Formula) """
        assert type(consequent) in {Formula, str}
        return self._add_line(consequent,
                              ('MP', antecedent_line, conditional_line))

    def add_ug(self, quantified, unquantified_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is quantified, and which is a return of universal
            generalization over line unquantified_line in this proof. The
            number of the added line in this proof is returned. quantified may
            also be given as a string representation (instead of a Formula) """
        assert type(quantified) in {Formula, str}
        return self._add_line(quantified, ('UG', unquantified_line))

    def add_proof(self, conclusion, proof):
        """ Append to the proof being constructed a whole copy of the
            given proof, where the formula of the last line is conclusion.
            The given proof must not use any additional assumptions, and this
            method takes care of the required line-shift in the justifications.
            The number of the (new) line in this proof containing conclusion is
            returned. conclusion may also be given as a string representation
            (instead of a Formula) """
        if type(conclusion) is str:
            conclusion = Formula.parse(conclusion)
        assert type(conclusion) is Formula
        assert type(proof) is Proof
        assert proof.conclusion == conclusion
        assert proof.assumptions.issubset(self.proof.assumptions)
        line_shift = len(self.proof.lines)
        for line in proof.lines:
            if line.justification[0] == 'A' or line.justification[0] == 'T':
                self._add_line(line.formula, line.justification)
            if line.justification[0] == 'MP':
                self.add_mp(line.formula, line.justification[1] + line_shift,
                            line.justification[2] + line_shift)
            if line.justification[0] == 'UG':
                self.add_ug(line.formula, line.justification[1] + line_shift)
        line_number = len(self.proof.lines) - 1
        assert self.proof.lines[line_number].formula == conclusion
        return line_number

    def add_universal_instantiation(self, instantiation, line_number, term):
        """ Append a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement, which
            is an instantiation of the formula in Line line_number in this
            proof, where the instantiation is to the universally
            quantified variable appearing at the beginning of the formula in
            the given line number. Example: if Line line_number has the formula
            'Ay[Az[f(x,y)=g(z,y)]]', then when calling this method with the
            term 'h(w)', the instantiation should be
            'Az[f(x,h(w))=g(z,h(w))]'. The number of the (new) line in this
            proof containing instantiation is returned. instantiation may also
            be given as a string representation (instead of a Formula), and so
            may term (instead of a Term) """
        if type(instantiation) is str:
            instantiation = Formula.parse(instantiation)
        assert type(instantiation) is Formula
        assert type(line_number) is int
        assert line_number < len(self.proof.lines)
        assert self.proof.lines[line_number].formula.root == 'A'
        if type(term) is str:
            term = Term.parse(term)
        assert type(term) is Term
        assert instantiation == \
               self.proof.lines[line_number].formula.predicate.substitute(
                   {self.proof.lines[line_number].formula.variable: term})
        # Task 10.1
        formula = self.proof.lines[line_number].formula
        instantiated_predicate = formula.predicate.substitute({formula.variable: Term('v')})
        step1 = self.add_instantiated_assumption(Formula("->", formula, instantiation),
                                                 Prover.UI, {'R(v)': instantiated_predicate, "c": term,
                                                             "x": formula.variable})
        return self.add_mp(instantiation, line_number, step1)

    def add_tautological_inference(self, conclusion, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is conclusion,
            which is a tautological inference of the formulae in the lines in
            this proof whose numbers are given in the set line_numbers. The
            number of the (new) line in this proof containing conclusion is
            returned. conclusion may also be given as a string representation
            (instead of a Formula) """
        if type(conclusion) is str:
            conclusion = Formula.parse(conclusion)
        assert type(conclusion) is Formula
        assert type(line_numbers) is set
        for line_number in line_numbers:
            assert type(line_number) is int
            assert line_number < len(self.proof.lines)
        # Task 10.2
        line_numbers = [x for x in line_numbers]
        inference = Formula("->", self.proof.lines[line_numbers[-1]].formula, conclusion)
        for line_num in reversed(line_numbers[:-1]):
            inference = Formula("->", self.proof.lines[line_num].formula, inference)
        second_justification = self.add_tautology(inference)
        for line_num in line_numbers:
            inference_second = inference.second
            second_justification = self.add_mp(inference_second, line_num, second_justification)
            inference = inference_second
        return second_justification

    def add_existential_derivation(self, statement, line_number1, line_number2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement.
            The formula in Line line_number1 must be of the form 'Ex[cond(x)]'
            (for some variable x), and the formula in Line line_number2 must be
            of the form '(cond(x)->statement)' (where x is not free in
            statement). The number of the (new) line in this proof containing
            statement is returned. statement may also be given as a string
            representation (instead of a Formula) """
        if type(statement) is str:
            statement = Formula.parse(statement)
        assert type(statement) is Formula
        assert type(line_number1) is int
        assert line_number1 < len(self.proof.lines)
        assert type(line_number2) is int
        assert self.proof.lines[line_number1].formula.root == 'E'
        assert line_number2 < len(self.proof.lines)
        assert self.proof.lines[line_number2].formula == \
               Formula('->', self.proof.lines[line_number1].formula.predicate,
                       statement)
        assert self.proof.lines[line_number1].formula.variable not in \
               statement.free_variables()
        # Task 10.3
        step1 = self.add_ug(Formula('A', self.proof.lines[line_number1].formula.variable,
                                    self.proof.lines[line_number2].formula), line_number2)
        step2 = Formula("->", Formula('&', self.proof.lines[step1].formula, self.proof.lines[line_number1].formula),
                        self.proof.lines[line_number2].formula.second)
        step2 = self.add_instantiated_assumption(step2, Prover.ES,
                                                 {'x': self.proof.lines[line_number1].formula.variable,
                                                  'Q()': self.proof.lines[line_number2].formula.second,
                                                  'R(v)': self.proof.lines[line_number1].formula.predicate.substitute(
                                                      {self.proof.lines[line_number1].formula.variable: Term('v')})})
        return self.add_tautological_inference(statement, {line_number1, step1, step2})

    def add_flipped_equality(self, flipped, line_number):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is flipped,
            which is an equality of the form 'c=d' (for some terms c, d) where
            the formula in Line line_number in this proof is 'd=c'. The number
            of the (new) line in this proof containing flipped is returned.
            flipped may also be given as a string representation (instead of a
            Formula) """
        if type(flipped) is str:
            flipped = Formula.parse(flipped)
        assert type(flipped) is Formula
        assert is_equality(flipped.root)
        assert type(line_number) is int
        assert line_number < len(self.proof.lines)
        assert self.proof.lines[line_number].formula == \
               Formula('=', flipped.second, flipped.first)
        # Task 10.6
        first, second = flipped.first, flipped.second
        me = Formula('->', Formula('=', second, first),
                                Formula('->', Formula('=', second, second), Formula('=', first, second)))
        mid_step = self.add_instantiated_assumption(me, Prover.ME,
                                                 {'c': second, 'd': first, 'R(v)': 'v=' + str(second)})
        last_step = self.add_mp(me.second, line_number, mid_step)
        return self.add_mp(me.second.second,
                           self.add_instantiated_assumption(Formula('=', second, second), Prover.RX, {'c': second}),
                           last_step)

    def add_free_instantiation(self, instantiation, line_number,
                               substitution_map):
        """ Append a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement, which
            is an instantiation of the formula in Line line_number in this
            proof, where the instantiation is simultaneously to the free
            variables appearing as keys in the substitution map. Example: if
            Line line_number has the formula 'Az[f(x,y)=g(z,y)]', then when
            calling this method with the substitution map
            {'y':Term.parse('h(w)')}, the instantiation should be
            'Az[f(x,h(w))=g(z,h(w))]'. The number of the (new) line in this
            proof containing instantiation is returned. instantiation may also
            be given as a string representation (instead of a Formula), and so
            may any value of substitution_map (instead of are Term) """
        if type(instantiation) is str:
            instantiation = Formula.parse(instantiation)
        assert type(instantiation) is Formula
        assert type(line_number) is int
        assert line_number < len(self.proof.lines)
        substitution_map = substitution_map.copy()
        for variable in substitution_map:
            assert is_variable(variable)
            if type(substitution_map[variable]) is str:
                substitution_map[variable] = \
                    Term.parse(substitution_map[variable])
            assert type(substitution_map[variable]) is Term
        assert instantiation == \
               self.proof.lines[line_number].formula.substitute(
                   substitution_map)
        # Task 10.7
        line, formula, final_dict = self.add_free_instantiation_helper(line_number, substitution_map)
        for k in final_dict:
            variable_dic = dict()
            variable_dic[k] = Term.parse(str(final_dict[k]))
            line = self.add_universal_instantiation(
                str(formula.substitute(variable_dic)),
                self.add_ug(Formula("A", k, self.proof.lines[line].formula),line),
                final_dict[k])
            formula = formula.substitute(variable_dic)
        return line

    def add_free_instantiation_helper(self, line_number, substitution_map):
        line = line_number
        current_formula = self.proof.lines[line_number].formula
        result_dic = dict()
        z_var_name = fresh_variable_name_generator
        for key in substitution_map:
            current_z = next(z_var_name)
            z_dict = dict()
            z_dict[key] = Term.parse(current_z)
            result_dic[current_z] = substitution_map[key]
            current_formula = current_formula.substitute(z_dict)
            line = self.add_universal_instantiation(
                str(current_formula),
                self.add_ug(Formula("A", key, self.proof.lines[line].formula), line),
                current_z)
        return line, current_formula, result_dic
    def add_substituted_equality(self, substituted, line_number,
                                 term_with_free_v):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is substituted,
            which is an equality of two terms, each of which is derived by
            substituting a term for the variable v in term_with_free_v. The
            two terms to be substituted for v are the two sides of the equality
            that is the formula in Line line_number in this proof. Example: if
            Line line_number has the formula 'g(x)=h(y)' and term_with_free_v
            is 'v+7', then substituted should be 'g(x)+7=h(y)+7'. The number of
            the (new) line in this proof containing substituted is returned.
            substituted may also be given as a string representation (instead
            of a Formula), and so may term_with_free_v (instead of a Term) """
        if type(substituted) is str:
            substituted = Formula.parse(substituted)
        assert type(substituted) is Formula
        assert is_equality(substituted.root)
        assert type(line_number) is int
        assert line_number < len(self.proof.lines)
        assert is_equality(self.proof.lines[line_number].formula.root)
        if type(term_with_free_v) is str:
            term_with_free_v = Term.parse(term_with_free_v)
        assert type(term_with_free_v) is Term
        assert substituted == \
               Formula('=',
                       term_with_free_v.substitute(
                           {'v': self.proof.lines[line_number].formula.first}),
                       term_with_free_v.substitute(
                           {'v': self.proof.lines[line_number].formula.second}))
        # Task 10.8
        formula = self.proof.lines[line_number].formula
        c = term_with_free_v.substitute({'v': formula.first})
        formula_rx = Formula('=', c, c)
        formula_me = Formula("->", formula, Formula("->",
                                                formula_rx,
                                                substituted))
        mp = self.add_mp(formula_me.second,
                               line_number,
                               self.add_instantiated_assumption(formula_me, Prover.ME,
                                                                {"c": str(formula.first), "d": str(formula.second),
                                                                 "R(v)": str(Formula("=", c, term_with_free_v))}))
        return self.add_mp(substituted,
                           self.add_instantiated_assumption(formula_rx,Prover.RX, {"c": str(c)}), mp)

    def _add_chained_two_equalities(self, line_number1, line_number2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is an equality of
            the form 'c=d' (for some terms c, d) where the formulae in Lines
            line_number1 and line_number2 in this proof are respectively 'c=a'
            and 'a=d' (for some term a). Example: if Line 7 holds 'a=b', and
            Line 3 holds 'b=f(b)', then if line_number1=7 and line_number2=3,
            then the formula of the last line added will be the chained equality
            'a=f(b)'. The number of the (new) line in this proof containing the
            chained equality is returned """
        assert type(line_number1) is int
        assert line_number1 < len(self.proof.lines)
        assert is_equality(self.proof.lines[line_number1].formula.root)
        assert type(line_number2) is int
        assert line_number2 < len(self.proof.lines)
        assert is_equality(self.proof.lines[line_number2].formula.root)
        assert self.proof.lines[line_number1].formula.second == \
               self.proof.lines[line_number2].formula.first
        # Task 10.9.1
        first_formula = self.proof.lines[line_number1].formula
        second_formula = self.proof.lines[line_number2].formula
        flipped_formula_1 = Formula("=",first_formula.second, first_formula.first)
        equal_formula = Formula('=', first_formula.first, second_formula.second)
        formula_implies = Formula("->", second_formula, equal_formula)
        line_flipped = self.add_flipped_equality(str(flipped_formula_1),line_number1)
        me = Formula("->", flipped_formula_1, formula_implies)
        mp = self.add_mp(me.second, line_flipped, self.add_instantiated_assumption(str(me), Prover.ME, {"R(v)" :
            "v="+ str(second_formula.second),"c":str(flipped_formula_1.first),"d" :str(flipped_formula_1.second)}))
        return self.add_mp(me.second.second, line_number2, mp)

    def add_chained_equality(self, chained, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is chained, which
            is an equality of the form 'c=d' (for some terms c, d) where the
            formulae in the lines in this proof whose numbers are given in the
            list line_numbers are of the form (in order) 'c=a1', 'a1=a2', ...,
            'an=d' (for some n and some terms a1,a2,...,an). Example: if Line 7
            holds 'a=b', Line 3 holds 'b=f(b)' and Line 9 holds 'f(b)=0', then
            if line_numbers=[7,3,9], then chained should be 'a=0'. The number of
            the (new) line in this proof containing substituted is returned.
            chained may also be given as a string representation (instead
            of a Formula) """
        if type(chained) is str:
            chained = Formula.parse(chained)
        assert type(chained) is Formula
        assert is_equality(chained.root)
        assert type(line_numbers) is list
        assert len(line_numbers) >= 2
        for line_number in line_numbers:
            assert type(line_number) is int
            assert line_number < len(self.proof.lines)
            assert is_equality(self.proof.lines[line_number].formula.root)
        assert chained.first == self.proof.lines[line_numbers[0]].formula.first
        for (line_number1, line_number2) in zip(line_numbers, line_numbers[1:]):
            assert self.proof.lines[line_number1].formula.second == \
                   self.proof.lines[line_number2].formula.first
        assert self.proof.lines[line_numbers[-1]].formula.second == \
               chained.second
        # Task 10.9.2
        line_result = line_numbers[0]
        num_of_lines = len(line_numbers)
        i = 1
        while i < num_of_lines:
            line_result = self._add_chained_two_equalities(line_result,line_numbers[i])
            i += 1
        return line_result
