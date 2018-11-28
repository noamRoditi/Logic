""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """

from propositions.syntax import *
import re
import itertools
from propositions.proofs import *
def is_model(model):
    """ Is m a model over some set of variables? """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model):
    """ Return the set of variables over which model is a model """
    return model.keys()
                
                
def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    assert is_model(model) and type(formula) is Formula
    assert formula.variables().issubset(variables(model)),\
           'Missing value for variable(s): ' + str(formula.variables().difference(variables(model)))
    # Task 2.1
    stringFormula = str(formula)
    for key in model:
        stringFormula = stringFormula.replace(key,str(model[key])[0])
    while len(stringFormula) > 1:
        stringFormula = stringFormula.replace('~~','')
        stringFormula = evaluateUnray(stringFormula)
        stringFormula = replaceAtomic(stringFormula)
    return True if stringFormula == 'T' else False

def evaluateUnray(stringFormula):
    ''' evaluates a formula that contains an unray operator'''
    notConstRegex = '[~]+[TF]'
    while re.search(notConstRegex, stringFormula) is not None:
        match = re.search(notConstRegex, stringFormula)
        reminder = (match.end() - match.start() - 1) % 2
        if reminder == 1:
            if stringFormula[match.end() - 1] == 'T':
                stringFormula = stringFormula[:match.start()] + 'F' + stringFormula[match.end():]
            else:
                stringFormula = stringFormula[:match.start()] + 'T' + stringFormula[match.end():]
        else:
            stringFormula = stringFormula[:match.start()] + stringFormula[match.end()] + stringFormula[match.end():]
    return stringFormula
def replaceAtomic(stringFormula):
    ''' a function that calculates the outcome of an atomic formula'''
    stringFormula = stringFormula.replace('(T&T)','T')
    stringFormula = stringFormula.replace('(T&F)', 'F')
    stringFormula = stringFormula.replace('(F&T)', 'F')
    stringFormula = stringFormula.replace('(F&F)', 'F')
    stringFormula = stringFormula.replace('(T|T)', 'T')
    stringFormula = stringFormula.replace('(T|F)', 'T')
    stringFormula = stringFormula.replace('(F|T)', 'T')
    stringFormula = stringFormula.replace('(F|F)', 'F')
    stringFormula = stringFormula.replace('(T->T)', 'T')
    stringFormula = stringFormula.replace('(T->F)', 'F')
    stringFormula = stringFormula.replace('(F->T)', 'T')
    stringFormula = stringFormula.replace('(F->F)', 'T')
    stringFormula = stringFormula.replace('(T<->T)', 'T')
    stringFormula = stringFormula.replace('(T<->F)', 'F')
    stringFormula = stringFormula.replace('(F<->T)', 'F')
    stringFormula = stringFormula.replace('(F<->F)', 'T')
    stringFormula = stringFormula.replace('(T-&T)', 'F')
    stringFormula = stringFormula.replace('(T-&F)', 'T')
    stringFormula = stringFormula.replace('(F-&T)', 'T')
    stringFormula = stringFormula.replace('(F-&F)', 'T')
    stringFormula = stringFormula.replace('(T-|T)', 'F')
    stringFormula = stringFormula.replace('(T-|F)', 'F')
    stringFormula = stringFormula.replace('(F-|T)', 'F')
    stringFormula = stringFormula.replace('(F-|F)', 'T')
    stringFormula = stringFormula.replace('(T+T)', 'F')
    stringFormula = stringFormula.replace('(T+F)', 'T')
    stringFormula = stringFormula.replace('(F+T)', 'T')
    stringFormula = stringFormula.replace('(F+F)', 'F')
    return stringFormula
def all_models(variables):
    """ Return a list (or preferably, a more memory-efficient iterable) of all
        possible models over the variables in the given list of variables. The
        order of the models should be lexicographic according to the order of
        the variables in the given list, where False precedes True """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    numOfVar = len(variables)
    combinations = list(itertools.product([False, True], repeat=numOfVar))
    result = []
    for combination in combinations:
        result.append(dict(zip(variables, combination)))
    return result
def truth_values(formula, models):
    """ Return a list (or preferably, a more memory-efficient iterable) of the
        respective truth values of the given formula in each model in the given
        list (or preferably, support models to be an arbitrary iterable) """
    assert type(formula) is Formula
    # Task 2.3
    result = []
    for model in models:
        result.append(evaluate(formula,model))
    return result

def print_truth_table(formula):
    """ Print the truth table of the given formula """
    assert type(formula) is Formula
    # Task 2.4
    result = '| '
    variables = sorted(formula.variables())
    seperator = '|'
    # print header and separator
    for var in variables:
        result += var + ' | '
        seperator += '-'*(len(var)+2) + '|'
    seperator += '-' * (len(str(formula))+2) + '|\n'
    result += str(formula) + ' |\n' + str(seperator)
    #print model
    allModels = all_models(variables)
    for idx, model in enumerate(allModels):
        result += '| '
        for const in model:
            result += str(model[const])[0] + ' '*len(const) + '| '
        if idx != len(allModels) -1:
            result += str(evaluate(formula, model))[0] + ' '*len(str(formula)) + '|\n'
        else:
            result += str(evaluate(formula, model))[0] + ' ' * len(str(formula)) + '|'
    print(result)


def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    assert type(formula) is Formula
    # Task 2.5a
    allModels = all_models(formula.variables())
    for model in allModels:
        if not evaluate(formula, model):
            return False
    return True

def is_contradiction(formula):
    """ Return whether the given formula is a contradiction """
    assert type(formula) is Formula
    # Task 2.5b
    allModels = all_models(formula.variables())
    for model in allModels:
        if evaluate(formula, model):
            return False
    return True

def is_satisfiable(formula):
    """ Return whether the given formula is satisfiable """
    assert type(formula) is Formula
    # Task 2.5c
    allModels = all_models(formula.variables())
    for model in allModels:
        if evaluate(formula, model):
            return True
    return False
def get_string_formula(model):
    ''' a function that returns a string formula for a specific model'''
    if len(model) == 1:
        for var in model:
            return var if model[var] else '~'+var
    formula = '(' if len(model) > 2 else ''
    for idx, var in enumerate(model):
        if idx < len(model) - 2:
            if model[var]:
                formula += var + '&('
            else:
                formula += '~' + var + '&('
        elif idx == len(model) - 2:
            if model[var]:
                formula += var + '&'
            else:
                formula += '~' + var + '&'
        else:
            if model[var]:
                formula += var + ')'
            else:
                formula += '~' + var + ')'
            if len(model) > 2:
                formula += ')'*(len(model)-2)
            return formula
def synthesize_for_model(model):
    """ Return a propositional formula in the form of a single clause that
        evaluates to True in the given model, and to False in any other model
        over the same variables """
    assert is_model(model)
    # Task 2.6
    result = '('+get_string_formula(model) if len(model) == 2 else get_string_formula(model)
    return Formula.parse(result)
def synthesize(models, values):
    """ Return a propositional formula in DNF that has the given list of
        respective truth values in the given list of models (or preferably,
        support models and values to be arbitrary iterables), which are all
        over the same nonempty set of variables """
    # Task 2.7
    formulaList = []
    stringFormula = ''
    for idx, model in enumerate(models):
        # check if all the possible values are false if so create a formula with no solution
        if idx == 0 and True not in values:
            for value in model:
                if stringFormula != '':
                    stringFormula = '(' + stringFormula + '|' +'(' + value + '&~' + value +'))'
                else:
                    stringFormula = '(' + value + '&~' + value + ')'
            return Formula.parse(stringFormula.replace('~~',''))
        # if the current model should return true insert to bnf
        if values[idx]:
            fl = ''
            if len(model) == 1:
                fl = get_string_formula(model).replace(')', '')
            elif len(model) == 2:
                fl = '(' + get_string_formula(model)
            else:
                fl = get_string_formula(model)
            formulaList.append(fl)
    # construct the formula string
    for idx, formula in enumerate(set(formulaList)):
        if idx == 0:
            stringFormula += formula
        else:
            stringFormula = '(' + stringFormula + '|' + formula +')'
    return Formula.parse(stringFormula.replace('~~',''))
# Tasks for Chapter 4

def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    assert type(rule) is InferenceRule
    assert is_model(model)
    # Task 4.2
    allHold = True
    for assumption in rule.assumptions:
        if not evaluate(assumption, model):
            allHold = False
    if allHold and not evaluate(rule.conclusion, model):
        return False
    return True

def is_sound_inference(rule):
    """ Return whether the given inference rule is sound, i.e., whether its
        conclusion is a semantically correct implication of its assumptions """
    assert type(rule) is InferenceRule
    # Task 4.3
    variables = rule.variables()
    allmodels = all_models(variables)
    #go over all models and see if there is one that is not correct
    for model in allmodels:
        if not evaluate_inference(rule,model):
            return False
    return True

