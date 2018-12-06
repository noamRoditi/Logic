""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/functions.py """
from copy import copy

from predicates.syntax import *
from predicates.semantics import *
from predicates.util import *

def function_name_to_relation_name(function):
    """ Return a relation name that is the same as the given function name,
        except that the first letter is capitalized """
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation):
    """ Return a function name that is the same as the given function name,
        except that the first letter is not capitalized """
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model):
    """ Return a new model obtained from the given model by replacing every
        function meaning with the corresponding relation meaning (i.e.,
        (x1,...,xn) is in the meaning if and only if x1 is the output of the
        function meaning for the arguments x2,...,xn), assigned to a relation
        with the same name as the function, except that the first letter is
        capitalized """
    assert type(model) is Model
    for key in model.meaning:
        if is_function(key):
            assert function_name_to_relation_name(key) not in model.meaning
    # Task 8.2
    new_model_meaning = {}
    new_model_universe = model.universe
    for element in model.meaning:
        relation = set()
        if is_function(element):
            [relation.add((model.meaning[element][assign],).__add__(assign)) for assign in model.meaning[element]]
            new_model_meaning[function_name_to_relation_name(element)] = relation
        else:
            new_model_meaning[element] = model.meaning[element]
    return Model(new_model_universe, new_model_meaning)


def replace_relations_with_functions_in_model(model, original_functions):
    """ Return a new model original_model with function names
        original_functions such that:
        model == replace_functions_with_relations_in_model(original_model)
        or None if no such original_model exists """
    assert type(model) is Model
    assert type(original_functions) is set
    for function in original_functions:
        assert is_function(function)
        assert function not in model.meaning
        assert function_name_to_relation_name(function) in model.meaning
    # Task 8.3
    new_model_meaning = {}
    for element in model.meaning:
        if relation_name_to_function_name(element) in original_functions:
            former_formula_candidate = relation_name_to_function_name(element)
            new_model_meaning[former_formula_candidate] = __handle_former_function_in_model(model, element)
            if new_model_meaning[former_formula_candidate] is None:
                return None
            continue
        new_model_meaning[element] = model.meaning[element]
    return Model(model.universe, new_model_meaning)


def __handle_former_function_in_model(model, element):
    # compare to check if we have the correct cardinal number
    if (len(model.universe) ** (len(list(model.meaning[element])[0]) - 1)) == len(model.meaning[element]):
        functions = {}
        for relation in model.meaning[element]:
            if relation[1:] in functions:
                return None
            functions[relation[1:]] = relation[0]
        return functions


def compile_term(term):
    """ Return a list of steps that result from compiling the given term,
        whose root is a function invocation (possibly with nested function
        invocations down the term tree). Each of the returned steps is a
        Formula of the form y=f(x1,...,xk), where the y is a new variable name
        obtained by calling next(fresh_variable_name_generator) (it is assumed
        that such variables do not occur in the given term), f is a
        single function invocation, and each of the xi is either a constant or
        a variable. The steps should be ordered left-to-right between the
        arguments, and within each argument, the computation of a variable
        value should precede its usage. The left-hand-side variable of the last
        step should evaluate to the value of the given term """
    assert type(term) is Term and is_function(term.root)
    # Task 8.4
    return compile_term_helper(term)[1]


def compile_term_helper(term):
    """ Parses the term "bottom-to-top" and replace every function with z1,z2,...
    function and return a list of equality formulae"""
    arguments = list()
    steps_list = list()
    for argument in term.arguments:
        if is_function(argument.root):
            new_term, step = compile_term_helper(argument)
            arguments.append(new_term)
            steps_list += step
            continue
        arguments.append(argument)
    next_term = Term(next(fresh_variable_name_generator))
    steps_list.append(Formula("=", next_term, Term(term.root, arguments)))
    return next_term, steps_list


def replace_functions_with_relations_in_formula(formula):
    """ Return a function-free analog of the given formula. Every k-ary
        function that is used in the given formula should be replaced with a
        k+1-ary relation with the same name except that the first letter is
        capitalized (e.g., the function plus(x,y) should be replaced with the
        relation Plus(z,x,y) that stands for z=plus(x,y)). (It is assumed that
        such relation names do not occur in the given formula, which furthermore
        does not contain any variables names starting with z.) The returned
        formula need only be equivalent to the given formula for models where
        each new relation encodes a function, i.e., is guaranteed to have a
        single possible value for the first relation argument for every k-tuple
        of the other arguments """
    assert type(formula) is Formula
    assert len({function_name_to_relation_name(f[0])
                for f in formula.functions()}.intersection(
                    {r[0] for r in formula.relations()})) == 0
    # Task 8.5

def replace_functions_with_relations_in_formulae(formulae):
    """ Return a set of function-free formulae that is equivalent to the given
        formulae set that may contain function invocations. This equivalence
        is in the following sense: for every model of the given formulae,
        replace_functions_with_relations_in_model(model) should be a model of
        the returned formulae, and for every model of the returned formulae,
        replace_relations_with_functions_in_model(model) should be a model of
        the given formulae. Every k-ary function that is used in the given
        formulae should be replaced with a k+1-ary relation with the same name
        except that the first letter is capitalized (e.g., the function
        plus(x,y) should be replaced with the relation Plus(z,x,y) that stands
        for z=plus(x,y)). (It is assumed that such relation names do not occur
        in the given formulae, which furthermore does not contain any variables
        names starting with z.) The returned set should have one formula for
        each formula in the given set, as well as one additional formula for
        every relation that replaces a function name from the given set """
    for formula in formulae:
        assert type(formula) is Formula
    assert len(set.union(*[{function_name_to_relation_name(f[0])
                            for f in formula.functions()}
                           for formula in formulae]).intersection(
                               set.union(*[{r[0] for r in formula.relations()}
                                           for formula in formulae]))) == 0
    # Task 8.6
        
def replace_equality_with_SAME(formulae):
    """ Return a set of equality-free formulae that is equivalent to the given
        function-free formulae set that may contain the equality symbol. Every
        occurrence of equality should be replaced with a matching invocation of
        the relation SAME, which is assumed to not occur in the given formulae.
        The returned set should have one formula for each formula in the given
        set, as well as additional formulae that ensure that SAME is reflexive,
        symmetric, transitive, and respected by all relations in the given
        formulae """
    for formula in formulae:
        assert type(formula) is Formula
        assert len(formula.functions()) == 0
        assert 'SAME' not in {f[0] for f in formula.functions()}
    # Task 8.7


def add_SAME_as_equality(model):
    """ Return a new model obtained from the given model by adding the relation
        SAME that behaves like equality """
    assert type(model) is Model
    assert 'SAME' not in model.meaning
    # Task 8.8
    new_model = copy(model)
    elements_set = set()
    [elements_set.add((item, item)) for item in model.universe]
    new_model.meaning["SAME"] = elements_set
    return new_model


def make_equality_as_SAME(model):
    """ Return a new model where equality is made to coincide with the
        reflexive, symmetric, transitive, and respected by all relations,
        relation SAME in the given function-free model. The requirement is that
        for every model and every set formulae, if we take
        new_formulae=replace_equality_with_SAME(formulae) and
        new_model=make_equality_as_SAME(model) then model is a valid model
        of new_formulae if and only if new_model is a valid model of formulae.
        The universe of the returned model should correspond to the equivalence
        classes of the SAME relation in the given model """
    assert type(model) is Model
    assert 'SAME' in model.meaning
    for key in model.meaning:
        assert not is_function(key)
    # Task 8.9
