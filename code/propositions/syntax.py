""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """
import itertools
import re
def is_variable(s):
    """ Is s an atomic proposition?  """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'

def is_binary(s):
    """ Is s a binary operator? """
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}

def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'

class Formula:
    """ A Propositional Formula """

    def __init__(self, root, first=None, second=None):
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other):
        return str(self) == str(other)

    def __ne__(self, other):
        return str(self) != str(other)

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        """ Return a string representation of self """
        # Task 1.1
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + str(self.first)
        else:
            return "(" + str(self.first) + self.root + str(self.second) + ")"

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        # Task 1.2
        result = set()
        """ A recursive function to find the variables """
        def rec_func(formula):
            if is_constant(formula.root):
                return
            elif is_variable(formula.root):
                result.add(formula.root)
            elif is_unary(formula.root):
                result.add(rec_func(formula.first))
            else:
                result.add(rec_func(formula.first))
                result.add(rec_func(formula.second))
        rec_func(self)
        if None in result:
            result.remove(None)
        return result

    def operators(self):
        """ Return the set of operators (including T and F) used in self """
        # Task 1.3
        result = set()
        """ A recursive function to find the variables """
        def rec_func(formula):
            if is_constant(formula.root):
                result.add(formula.root)
            elif is_variable(formula.root):
                return
            elif is_unary(formula.root):
                result.add(formula.root)
                result.add(rec_func(formula.first))
            else:
                result.add(formula.root)
                result.add(rec_func(formula.first))
                result.add(rec_func(formula.second))
        rec_func(self)
        if None in result:
            result.remove(None)
        return result
    @staticmethod
    def parse_prefix(s):
        """ Parse a prefix of the string s into a formula.  Return a
            pair: the parsed formula and the unparsed suffix of the string.
            If no prefix of s is a valid formula then returned pair should
            be None and an error message, where the error message must
            be a string (with some human-readable content) """
        assert type(s) is str
        # Task 1.4
        if len(s) == 0:
            return None, ''
        if s[0] == ")":
            return None, 'Unexpected symbol )'
        elif is_variable(s[0]) or is_constant(s[0]):
            numOfOpenBrackets = 1
            while numOfOpenBrackets < len(s):
                if s[numOfOpenBrackets].isdigit():
                    numOfOpenBrackets += 1
                else:
                    break
            return Formula(s[:numOfOpenBrackets],None,None), s[numOfOpenBrackets:]
        elif is_unary(s[0]):
            if len(s) == 1:
                return None, 'A formula should follow after ~'
            x = Formula.parse_prefix(s[1:])
            if x[0] == None:
                return None, 'A valid formula should follow after ~'
            return Formula(s[0],x[0],None), s[len(str(x[0]))+1:]
        elif s[0] == "(":
            return Formula.start_with_open_bracket(s)
        else:
            return None, 'Unfamilar input'
    @staticmethod
    def create_formula(s, leftFoumulaStart, leftFoumulaEnd, rightFoumulaStart, rightFormulaEnd, root, lastIndex):
        """A function to parse a prefix"""
        leftFormula = Formula.parse_prefix(s[leftFoumulaStart:leftFoumulaEnd])
        rightFormula = Formula.parse_prefix(s[rightFoumulaStart:rightFormulaEnd])
        if leftFormula[0] is None or rightFormula[0] is None:
            return None, 'not valid formula structure'
        return Formula(root, leftFormula[0], rightFormula[0]), s[lastIndex:]
    @staticmethod
    def start_with_open_bracket(s):
        """A function when a string starts with ( """
        if len(s) == 1:
            return None, 'A formula should follow after ('
        numOfOpenBrackets = 1
        lastBracketIndex = 0
        # find the last bracket for the formula
        while numOfOpenBrackets > 0 and lastBracketIndex + 1 < len(s):
            if s[lastBracketIndex + 1] == "(":
                numOfOpenBrackets += 1
            elif s[lastBracketIndex + 1] == ")":
                numOfOpenBrackets -= 1
            lastBracketIndex += 1
        if s[lastBracketIndex] != ")":
            return None, 'invalid brackets'
        # check if there is a reminder of s and it's valid
        if len(s[lastBracketIndex:]) > 1 and s[lastBracketIndex + 1:].find("(") != -1:
            openBracket = s.count("(", lastBracketIndex)
            closeBracket = s.count(")", lastBracketIndex + 1)
            if closeBracket - openBracket != 1:
                return None, 'invalid structure'
        # check if (x&y) and it's valid
        openBracket = s.count("(", 1)
        closeBracket = s.count(")", 1, lastBracketIndex)
        if openBracket != closeBracket:
            return None, 'not valid'
        if openBracket == 0 and closeBracket == 0:
            regex = re.compile('\([~]*([p-z]|[TF])[\d]*([&|+]|->|<->|-&|-\|)[~]*([p-z]|[TF])[\d]*\)')
            if regex.match(s) is None :
                return None, 'missing formula inside brackets'
            binaryIndex = 1
            while binaryIndex < len(s[1:lastBracketIndex]):
                if is_binary(s[binaryIndex]):
                    return Formula.create_formula(s, 1, binaryIndex, binaryIndex + 1, lastBracketIndex,
                                                  s[binaryIndex],
                                                  lastBracketIndex + 1)
                if binaryIndex + 2 <= len(s[1:lastBracketIndex]):
                    if is_binary(s[binaryIndex:binaryIndex + 2]):
                        return Formula.create_formula(s, 1, binaryIndex, binaryIndex + 2, lastBracketIndex,
                                                      s[binaryIndex:binaryIndex + 2], lastBracketIndex + 1)
                if binaryIndex + 3 <= len(s[1:lastBracketIndex]):
                    if is_binary(s[binaryIndex:binaryIndex + 3]):
                        return Formula.create_formula(s, 1, binaryIndex, binaryIndex + 3, lastBracketIndex,
                                                      s[binaryIndex:binaryIndex + 3], lastBracketIndex + 1)
                binaryIndex += 1
                if binaryIndex + 1 == lastBracketIndex:
                    return None, 'missing formula inside brackets'
        firstOpenBracket = s[1:lastBracketIndex].find("(") + 1
        # this state(x&())
        if firstOpenBracket - 1 > 0:
            while firstOpenBracket - 1 > 0 and is_unary(s[firstOpenBracket - 1]):
                firstOpenBracket -=1
            if firstOpenBracket - 3 > 0 and is_binary(s[firstOpenBracket - 3: firstOpenBracket]):
                return Formula.create_formula(s, 1, firstOpenBracket - 3, firstOpenBracket,
                                              lastBracketIndex, s[firstOpenBracket - 3: firstOpenBracket]
                                              , lastBracketIndex + 1)
            elif firstOpenBracket - 2 > 0 and is_binary(s[firstOpenBracket - 2: firstOpenBracket]):
                return Formula.create_formula(s, 1, firstOpenBracket - 2, firstOpenBracket,
                                              lastBracketIndex, s[firstOpenBracket - 2: firstOpenBracket],
                                              lastBracketIndex + 1)
            elif is_binary(s[firstOpenBracket - 1]):
                return Formula.create_formula(s, 1, firstOpenBracket-1, firstOpenBracket,
                                              lastBracketIndex, s[firstOpenBracket-1],
                                              lastBracketIndex + 1)
        # (()&x)
        i = s[:lastBracketIndex].rfind(')')
        if i != lastBracketIndex - 1:
            if is_binary(s[i + 1]):
                return Formula.create_formula(s, 1, i + 1, i + 2, lastBracketIndex, s[i + 1], lastBracketIndex + 1)
            elif len(s) > i + 3 and is_binary(s[i + 1:i + 3]):
                return Formula.create_formula(s, 1, i + 1, i + 3,lastBracketIndex,
                                              s[i+1:i + 3], lastBracketIndex + 1)
            elif len(s) > i + 4 and is_binary(s[i + 1:i + 4]):
                return Formula.create_formula(s, 1, i + 1, i + 4, lastBracketIndex,
                                              s[i+1:i + 4], lastBracketIndex + 1)
        numOfOpenBrackets = 2
        leftFormulaEnd = s[1:lastBracketIndex].find("(") + 1
        # not a atomic formula (()())
        while numOfOpenBrackets > 1 and leftFormulaEnd + 1 < len(s[1:lastBracketIndex]):
            if s[leftFormulaEnd + 1] == "(":
                numOfOpenBrackets += 1
            elif s[leftFormulaEnd + 1] == ")":
                numOfOpenBrackets -= 1
            leftFormulaEnd += 1
        if s[leftFormulaEnd] != ")":
            return None, 'invalid brackets'
        if is_binary(s[leftFormulaEnd + 1]):
            return Formula.create_formula(s, 1, leftFormulaEnd + 1, leftFormulaEnd + 2, lastBracketIndex, s[leftFormulaEnd + 1], lastBracketIndex + 1)
        elif len(s) > leftFormulaEnd + 3 and is_binary(s[leftFormulaEnd + 1:leftFormulaEnd + 3]):
            return Formula.create_formula(s, 1, leftFormulaEnd + 1, leftFormulaEnd + 3, lastBracketIndex,
                                          s[leftFormulaEnd + 1:leftFormulaEnd + 3], lastBracketIndex + 1)
        elif len(s) > leftFormulaEnd + 4 and is_binary(s[leftFormulaEnd + 1:leftFormulaEnd + 4]):
            return Formula.create_formula(s, 1, leftFormulaEnd + 1, leftFormulaEnd + 4, lastBracketIndex,
                                          s[leftFormulaEnd + 1:leftFormulaEnd + 4], lastBracketIndex + 1)
        else:
            return None, 'not valid structure'
    @staticmethod
    def is_formula(s):
        """ Is s a valid formula? """
        assert type(s) is str
        # Task 1.5
        ff, rr = Formula.parse_prefix(s)
        if ff is None:
            return False
        while rr != '':
            if len(rr) > 1 and is_binary(rr[0]) and not\
                    (str(ff).find('(') == -1 and (is_variable(rr[1:]) or is_constant(rr[1:]))):
                    ff, rr = Formula.parse_prefix(rr[1:])
            elif len(rr) > 2 and is_binary(rr[0:2]) and not\
                    (str(ff).find('(') == -1 and (is_variable(rr[2:]) or is_constant(rr[2:]))):
                    ff, rr = Formula.parse_prefix(rr[2:])
            elif len(rr) > 3 and is_binary(rr[0:3]) and not\
                    (str(ff).find('(') == -1 and (is_variable(rr[3:]) or is_constant(rr[3:]))):
                    ff, rr = Formula.parse_prefix(rr[3:])
            else:
                return False
            if ff is None:
                return False
        return True
    @staticmethod
    def parse(s):
        """ Return a propositional formula whose infix representation is s """
        assert Formula.is_formula(s), "Expected formula; got " + s
        # Task 1.6
        if not Formula.is_formula(s):
            return None
        ff, rr = Formula.parse_prefix(s)
        while rr != '':
            if len(rr) > 1 and is_binary(rr[0]):
                ff, rr = Formula.parse_prefix(rr[1:])
            elif len(rr) > 2 and is_binary(rr[0:2]):
                ff, rr = Formula.parse_prefix(rr[2:])
            elif len(rr) > 3 and is_binary(rr[0:3]):
                ff, rr = Formula.parse_prefix(rr[3:])
            else:
                return None
        return ff


# Optional tasks for Chapter 1

    def prefix(self):
        """ Return a prefix representation of self """
        # Optional Task 1.7

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        assert type(s) is str
        # Optional Task 1.8

# Tasks for Chapter 3

    def substitute_variables(self,d):
        """ Return a formula that is derived from self by substituting
            for each variable v that is a key in d, the Formula d[v].
            E.g., if self is the formula "((p->p)|z)" and
            d={"p":Formula.parse("(q&r)") then the returned formula should
            be (a Formula object of) "(((q&r)->(q&r))|z)" """
        for v in d:
            assert is_variable(v)
            assert type(d[v]) is Formula
        # Task 3.3
        formulaStr = str(self)
        for key in d:
            formulaStr = formulaStr.replace(key,str(d[key]))
        return Formula.parse(formulaStr)

    def substitute_operators(self,d):
        """ Return a formula that is derived from self by replacing
            every operator op that is a key in d by the formula d[op] applied
            to its (zero or one or two) operands, where the first operand
            is used for every occurence of "p" in the formula and the second
            for every occurence of "q".  (In the case of the nullary operators
            F and T, d[op] itself is used.)  E.g. if self is the formula
            "((x&y)&~z)" and d={"&":Formula.parse("~(~p|~q)")} then the returned
            formula should be (a Formula object of): "~(~~(~x|~y)|~~z)" """
        for op in d:
            assert is_binary(op) or is_unary(op) or is_constant(op)
            assert d[op].variables().issubset({"p","q"})
        # Task 3.4
        formulaStr = str(self)
        if not Formula.is_formula(formulaStr):
            return None
        if formulaStr == 'T' and 'T' in d:
            return d['T']
        if formulaStr == 'F' and 'F' in d:
            return d['F']
        # in case p or q are in the variables of the original formula
        variables = self.variables()
        pInVars = False
        qInVars = False
        var1 = 'x1'
        var2 = 'y1'
        formulaStr = str(self)
        if 'p' in variables:
            pInVars = True
            while var1 in variables:
                var1 = var1 + '1'
            formulaStr = formulaStr.replace('p',var1)
        if 'q' in variables:
            qInVars = True
            while var2 in variables:
                var2 = var2 + '1'
            formulaStr = formulaStr.replace('q',var2)
        if pInVars or qInVars:
            self = Formula.parse(formulaStr)
        # if self is an atomic formula
        atomicRegex = re.compile('\([~]*([p-z]|[TF])[\d]*([&|+]|->|<->|-&|-\|)[~]*([p-z]|[TF])[\d]*\)')
        if atomicRegex.match(str(self)) is not None and atomicRegex.match(str(self)).start() == 0:
            if self.root in d:
                leftVar = self.first
                i = 0
                while is_unary(leftVar.root):
                    i += 1
                    leftVar = leftVar.first
                rightVar = self.second
                j = 0
                while is_unary(rightVar.root):
                    j += 1
                    rightVar = rightVar.first
                # if either is F or T
                if leftVar in d:
                    leftVar = str(d[leftVar])
                if rightVar in d:
                    rightVar = str(d[rightVar])
                if '~' not in d:
                    leftVar = '~'*i + str(leftVar)
                    rightVar = '~'*j + str(rightVar)
                else:
                    for x in range(i):
                        leftVar = str(d['~']).replace('p',str(leftVar))
                    for x in range(j):
                        rightVar = str(d['~']).replace('p',str(rightVar))
                formula = str(d[self.root])
                formula = formula.replace('p',str(leftVar))
                formula = formula.replace('q',str(rightVar))
                if pInVars:
                    formula = formula.replace(var1, 'p')
                if qInVars:
                    formula = formula.replace(var2, 'q')
                return Formula.parse(formula)
            else:
                formula = str(self)
                if pInVars:
                    formula = formula.replace(var1, 'p')
                if qInVars:
                    formula = formula.replace(var2, 'q')
                return Formula.parse(formula)
        else:
            # not an atomic formula
            if is_binary(self.root):
                leftFormula = self.first.substitute_operators(d)
                rightFormula = self.second.substitute_operators(d)
                if self.root in d:
                    formula = str(d[self.root])
                    formula = formula.replace('p', str(leftFormula))
                    formula = formula.replace('q', str(rightFormula))
                    if pInVars:
                        formula = formula.replace(var1, 'p')
                    if qInVars:
                        formula = formula.replace(var2, 'q')
                    return Formula.parse(formula)
                return Formula(self.root, leftFormula, rightFormula)
            if is_unary(self.root):
                if '~' not in d:
                    return Formula('~', self.first.substitute_operators(d), None)
                else:
                    return Formula.parse(str(d['~']).replace('p', str(self.first.substitute_operators(d))))
            if is_constant(self.root) and self.root in d:
                self.root = d[self.root]
                return self
            else:
                return self