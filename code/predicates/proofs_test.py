""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/proofs_test.py """

from predicates.syntax import *
from predicates.proofs import *

def test_instantiate_formula(debug=False):
    for formula,templates,constant_and_variable_instantiation_map,relations_instantiation_map,instance in [
            ('R(c)', {'c'}, {'c': Term('9')}, {},  'R(9)'),
            ('(R(0)->R(x))', {'R'}, {}, {'R': (['v'], Formula.parse('v=1'))},
             '(0=1->x=1)'),
            ('(Ax[R(x)]->R(c))', {'c', 'R'}, {'c': Term('9')},
             {'R': (['v'], Formula.parse('(Q(y)|v=0)'))},
             '(Ax[(Q(y)|x=0)]->(Q(y)|9=0))'),
            ('((R(0)&Az[(R(z)->R(s(z)))])->Az[R(z)])', {'R'}, {},
             {'R': (['v'], Formula.parse('plus(x,v)=plus(v,x)'))},
             '((plus(x,0)=plus(0,x)&Az[(plus(x,z)=plus(z,x)->plus(x,s(z))=plus(s(z),x))])->Az[plus(x,z)=plus(z,x)])'),
            ('Ax[R(x)]', {'R'}, {}, {'R':(['v'],Formula.parse('v=1'))},
             'Ax[x=1]'),
            ('Ax[R(x)]', {'R', 'x'}, {'x': Term('z')},
             {'R':(['v'],Formula.parse('v=x'))}, 'Az[z=x]'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {}, {}, '(Ax[R(x)]->R(c))'),
            ('(Ax[R(x)]->R(c))', {'x', 'c', 'R'},
             {'x': Term('z'), 'c': Term('z')},
             {'R': (['z'],Formula.parse('Ay[(L(x,y)->L(z,x))]'))},
             '(Az[Ay[(L(x,y)->L(z,x))]]->Ay[(L(x,y)->L(z,x))])')]:
        formula = Formula.parse(formula)
        schema = Schema(formula, templates)
        if debug:
            print('Substituting constant and variable instantiation map',
                  constant_and_variable_instantiation_map,
                  'and relations instantiation map',
                  relations_instantiation_map,
                  'in schema', schema, '...')
        result = schema.instantiate_formula(
            formula, constant_and_variable_instantiation_map,
            relations_instantiation_map, set())
        if debug:
            print('... yields', result)
        assert str(result) == instance

    for formula,templates,constant_and_variable_instantiation_map,relations_instantiation_map,variable_name,relation_name in [
            ('Ax[R(0)]', {'R'}, {}, {'R':(['v'],Formula.parse('x=1'))}, 'x', 'R'),
            ('Ax[Q(0)]', {'Q', 'x'}, {'x': Term('z')},
             {'Q':(['v'],Formula.parse('z=1'))}, 'z', 'Q'),
            ('(Ax[R(x)]->R(c))', {'R','x','c'}, {},
             {'R':(['v'],Formula.parse('Ex[v=7]'))}, 'x', 'R')
            ]:
        formula = Formula.parse(formula)
        schema = Schema(formula, templates)
        if debug:
            print('Substituting constant and variable instantiation map',
                  constant_and_variable_instantiation_map,
                  'and relations instantiation map',
                  relations_instantiation_map,
                  'in schema', schema, '...')
        try:
            result = schema.instantiate_formula(
                formula, constant_and_variable_instantiation_map,
                relations_instantiation_map, set())
            assert False, 'Expected exception'
        except Schema.BoundVariableError as e:
            if debug:
                print('Threw a BoundVariableError as expected')
            assert e.variable_name == variable_name
            assert e.relation_name == relation_name
        except:
            if debug:
                print('Threw an exception as expected, though not a '
                      'BoundVariableError.')

def test_instantiate(debug=False):
    for formula,templates,instantiation_map,instance in [
            ('R(c)', {'c'}, {'c':Term('9')}, 'R(9)'),
            ('(R(0)->R(x))', {'R'}, {'R(v)':Formula.parse('v=1')},
             '(0=1->x=1)'),
            ('(Ax[R(x)]->R(c))', {'c', 'R'},
             {'R(v)':Formula.parse('(Q(y)|v=0)'), 'c':Term('9')},
             '(Ax[(Q(y)|x=0)]->(Q(y)|9=0))'),
            ('((R(0)&Az[(R(z)->R(s(z)))])->Az[R(z)])', {'R'},
             {'R(v)':Formula.parse('plus(x,v)=plus(v,x)')},
             '((plus(x,0)=plus(0,x)&Az[(plus(x,z)=plus(z,x)->plus(x,s(z))=plus(s(z),x))])->Az[plus(x,z)=plus(z,x)])'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R(v)':Formula.parse('Q(v)')},
             '(Ay[Q(y)]->Q(0))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R(x)':Formula.parse('Q(x)')},
             '(Ay[Q(y)]->Q(0))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R(xyz)':Formula.parse('Q(xyz)')},
             '(Ay[Q(y)]->Q(0))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('0'), 'x':'y', 'R(xyz)':Formula.parse('Q(v)')},
             '(Ay[Q(v)]->Q(v))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term.parse('f(g(a),g(a))'), 'x':'x',
              'R(vvv)':Formula.parse('(vvv=0|R(vvv,z))')},
             '(Ax[(x=0|R(x,z))]->(f(g(a),g(a))=0|R(f(g(a),g(a)),z)))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {}, '(Ax[R(x)]->R(c))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'Q(v)':Formula.parse('v=0')},
             None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R(z)':Formula.parse('Q(0)'), 'a':Term('b')}, None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'c':Term.parse('f(x)')},
             '(Ax[R(x)]->R(f(x)))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'}, {'c':Term('x'), 'x':'z'},
             '(Az[R(z)]->R(x))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R(v)':Formula.parse('Q(v,z)')}, '(Ax[Q(x,z)]->Q(c,z))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'R(v)':Formula.parse('Q(v,x)')}, None),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'x':'z', 'R(v)':Formula.parse('Q(v,x)')},
             '(Az[Q(z,x)]->Q(c,x))'),
            ('(Ax[R(x)]->R(c))', {'c', 'x', 'R'},
             {'c':Term('z'), 'R(v)':Formula.parse('Q(v,z)')},
             '(Ax[Q(x,z)]->Q(z,z))'),
            ('(Ax[R(x)]->R(c))', {'x', 'c', 'R'},
             {'x':'z', 'c':Term('z'),
              'R(z)':Formula.parse('Ay[(L(x,y)->L(z,x))]')},
             '(Az[Ay[(L(x,y)->L(z,x))]]->Ay[(L(x,y)->L(z,x))])'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c1':Term.parse('f(x)'), 'R(v)':Formula.parse('v=c')},
             '(f(x)=c2->(f(x)=c->c2=c))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c2':Term('c1'), 'c1':Term('c2')}, '(c2=c1->(R(c2)->R(c1)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'R(v)':Formula.parse('R(c1,c2,v)')},
             '(c1=c2->(R(c1,c2,c1)->R(c1,c2,c2)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'c1':Term('c2'), 'c2':Term('c1'),
              'R(v)':Formula.parse('R(c1,c2,v)')},
             '(c2=c1->(R(c1,c2,c2)->R(c1,c2,c1)))'),
            ('(c1=c2->(R(c1)->R(c2)))', {'c1', 'c2', 'R'},
             {'R(v)':Formula.parse('(Q(v)&Av[S(v)])')},
             '(c1=c2->((Q(c1)&Av[S(v)])->(Q(c2)&Av[S(v)])))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('v=0'), 'R(v)':Formula.parse('S(v)')},
             '(Ax[(v=0->S(x))]->(v=0->Ax[S(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('v=0'), 'R(v)':Formula.parse('S(v)'),
              'x':'z'},
             '(Az[(v=0->S(z))]->(v=0->Az[S(z)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('z=0')},
             '(Ax[(z=0->R(x))]->(z=0->Ax[R(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('x=0')}, None),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('Ax[x=0]')},
             '(Ax[(Ax[x=0]->R(x))]->(Ax[x=0]->Ax[R(x)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('x=0'), 'x':'z'},
             '(Az[(x=0->R(z))]->(x=0->Az[R(z)]))'),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('z=0'), 'x':'z'}, None),
            ('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'R', 'Q', 'x'},
             {'Q()':Formula.parse('Az[z=0]'), 'x':'z'},
             '(Az[(Az[z=0]->R(z))]->(Az[z=0]->Az[R(z)]))'),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'RRR(zzz)':Formula.parse('zzz=yyy'), 'yyy':'xxx'},
             '(Axxx[xxx=yyy]->Exxx[QQQ(xxx)])'),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'QQQ(v)':Formula.parse('v=0')}, None),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'},
             {'QQQ(v)':Formula.parse('RRR(v)')}, None),
            ('(Axxx[RRR(xxx)]->Eyyy[QQQ(yyy)])', {'RRR', 'yyy'}, {'xxx':'z'},
             None),
            ('(Ax[R(x)]->R(c))', {'R','x','c'},
             {'R(v)':Formula.parse('Ex[v=7]')}, None)
            ]:
        schema = Schema(Formula.parse(formula), templates)
        if debug:
            print('Substituting instantiation map', instantiation_map,
                  'in schema', schema, '...')
        result = schema.instantiate(instantiation_map)
        if debug:
            print('... yields', result)
        if instance is None:
            assert result is None
        else:
            assert str(result) == instance

def test_verify_a_justification(debug=False):
    for assumption,templates,instantiation_map,conclusion,validity in [
            ('u=0', {'u'}, {'u': 'x'}, 'x=0', True),
            ('(u=0->v=1)', {'u', 'v'}, {'u': 'x', 'v': 'y'},
             '(x=0->y=1)', True),
            ('Ev[u=f(v)]', {'v'}, {'v': 'x'}, 'Ex[u=f(x)]', True),
            ('u=0', {'u'}, {'u': 'x'}, 'y=0', False),
            ('Av[u=v]', {'u'}, {'u': 'x'}, 'Av[u=v]', False),
            ('Av[u=v]', {'u'}, {'u': 'x'}, 'Ax[u=x]', False),
            ('Ax[(Q(z)->R(x))]', {'Q'}, {'Q(v)': Formula.parse('x=v')},
             'Ax[(x=z->R(x))]', False)]:
        assumption = Schema(Formula.parse(assumption), templates)
        conclusion = Formula.parse(conclusion)
        lines = [Proof.Line(conclusion, ('A', assumption, instantiation_map))]
        proof = Proof({assumption}, conclusion, lines)
        checked_line = 0
        if debug:
            print('Verifying A justification of line ' + str(checked_line) +
                  ' in proof:\n' + str(proof))
        result = proof.verify_a_justification(checked_line)
        if debug:
            print('... yields', result)
        assert result == validity

        assumption = Schema(Formula.parse('u=0'), {'u'})
        conclusion = Formula.parse('x=0')
        lines = [Proof.Line(conclusion, ('A', assumption, instantiation_map))]
        proof = Proof({Schema(Formula.parse('u=1'), {'u'})}, conclusion, lines)
        checked_line = 0
        if debug:
            print('Verifying A justification of line ' + str(checked_line) +
                  ' in proof:\n' + str(proof))
        result = proof.verify_a_justification(checked_line)
        if debug:
            print('... yields', result)
        assert not result

def test_verify_t_justification(debug=False):
    for conclusion,validity in [
            ('(R(c)|~R(c))', True),
            ('(x=0->x=0)', True),
            ('(((R(x)->Q(y))&(Q(y)->S(z)))->(R(x)->S(z)))', True),
            ('(Ex[x=0]->Ex[x=0])', True),
            ('x=0', False),
            ('x=x', False),
            ('Ax[(R(0)|~R(0))]', False)]:
        conclusion = Formula.parse(conclusion)
        lines = [Proof.Line(conclusion, ('T',))]
        proof = Proof([], conclusion, lines)
        checked_line = 0
        if debug:
            print('Verifying T justification of line ' + str(checked_line) +
                  ' in proof:\n' + str(proof))
        result = proof.verify_t_justification(checked_line)
        if debug:
            print('... yields', result)
        assert result == validity

def test_verify_mp_justification(debug=False):
    # Test valid line
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    conclusion = Formula.parse('v=1')
    lines = [Proof.Line(Formula.parse('x=0'), ('A', assumption1, {'u': 'x'})),
             Proof.Line(Formula.parse('(x=0->y=1)'),
                        ('A', assumption2, {'u': 'x', 'v': 'y'})),
             Proof.Line(Formula.parse('y=1'), ('MP', 0, 1))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 2
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test valid line reversed order assumption
    assumption1 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    assumption2 = Schema(Formula.parse('u=0'), {'u'})
    conclusion = Formula.parse('v=1')
    lines = [Proof.Line(Formula.parse('(f(x)=0->g(y)=1)'),
                        ('A', assumption1, {'u': 'f(x)', 'v': 'g(y)'})),
             Proof.Line(Formula.parse('f(x)=0'), ('A', assumption2, {'u': 'f(x)'})),
             Proof.Line(Formula.parse('g(y)=1'), ('MP', 1, 0))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 2
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test valid line with quantifier
    assumption1 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    assumption2 = Schema(Formula.parse('u=0'), {'u'})
    conclusion = Formula.parse('v=1')
    lines = [Proof.Line(Formula.parse('(Ax[f(x)=0]->Ey[f(y)=1])'),
                        ('A', assumption1,
                         {'u': 'Ax[f(x)=0]', 'v': 'Ey[f(y)=1]'})),
             Proof.Line(Formula.parse('Ax[f(x)=0]'),
                        ('A', assumption2, {'u': 'Ax[f(x)=0]'})),
             Proof.Line(Formula.parse('Ey[f(y)=1]'), ('MP', 1, 0))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 2
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert result

    # Test invalid line - type 1
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=1->v=1)'), {'u', 'v'})
    conclusion = Formula.parse('v=1')
    lines = [Proof.Line(Formula.parse('x=0'), ('A', assumption1, {'u': 'x'})),
             Proof.Line(Formula.parse('(x=1->y=1)'),
                        ('A', assumption2, {'u': 'x', 'v': 'y'})),
             Proof.Line(Formula.parse('y=1'), ('MP', 0, 1))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 2
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert not result

    # Test invalid line - type 2
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    conclusion = Formula.parse('v=0')
    lines = [Proof.Line(Formula.parse('x=0'), ('A', assumption1, {'u': 'x'})),
             Proof.Line(Formula.parse('(x=0->y=1)'),
                        ('A', assumption2, {'u': 'x', 'v': 'y'})),
             Proof.Line(Formula.parse('y=0'), ('MP', 0, 1))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 2
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert not result

    # Test pointing to lines that appear after the conclusion
    assumption1 = Schema(Formula.parse('u=0'), {'u'})
    assumption2 = Schema(Formula.parse('(u=0->v=1)'), {'u', 'v'})
    conclusion = Formula.parse('v=1')
    lines = [Proof.Line(Formula.parse('x=0'), ('A', assumption1, {'u': 'x'})),
             Proof.Line(Formula.parse('y=1'), ('MP', 0, 2)),
             Proof.Line(Formula.parse('(x=0->y=1)'),
                        ('A', assumption2, {'u': 'x', 'v': 'y'}))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    checked_line = 1
    if debug:
        print('Verifying MP justification of line ' + str(checked_line) +
              ' in proof:\n' + str(proof))
    result = proof.verify_mp_justification(checked_line)
    if debug:
        print('... yields', result)
    assert not result

def test_verify_ug_justification(debug=False):
    for assumption, templates, conclusion, validity in [
            ('x=0', {'x'}, 'Ax[x=0]', True),
            ('x=0', {'x'}, 'Ay[x=0]', True),
            ('Ax[x=0]', set(), 'Ax[Ax[x=0]]', True),
            ('(x=0&y=0)', {'x', 'y'}, 'Ax[(x=0&y=0)]', True),
            ('R(c)', {'c'}, 'Axyz[R(c)]', True),
            ('x=0', {'x'}, 'Ex[x=0]', False),
            ('x=0', {'x'}, 'Ax[z=0]', False),
            ('(x=0&y=0)', {'x', 'y'}, '(Ax[x=0]&y=0)', False)]:
        assumption = Schema(Formula.parse(assumption), templates)
        conclusion = Formula.parse(conclusion)
        lines = [Proof.Line(assumption.formula,
                            ('A', assumption, {})),
                 Proof.Line(conclusion, ('UG', 0))]
        proof = Proof({assumption}, conclusion, lines)
        checked_line = 1
        if debug:
            print('Verifying UG justification of line ' + str(checked_line) +
                  ' in proof:\n' + str(proof))
        result = proof.verify_ug_justification(checked_line)
        if debug:
            print('... yields', result)
        assert result == validity

        # Test pointing to lines that appear after the conclusion
        assumptions = Schema(Formula.parse('x=0'), {'x'})
        conclusion = Formula.parse('Ax[x=0]')
        lines = [Proof.Line(Formula.parse('Ax[x=0]'), ('UG', 1)),
                 Proof.Line(Formula.parse('x=0'), ('A', assumption, {}))]
        proof = Proof({assumption}, conclusion, lines)
        checked_line = 0
        if debug:
            print('Verifying UG justification of line ' + str(checked_line) +
                  ' in proof:\n' + str(proof))
        result = proof.verify_ug_justification(checked_line)
        if debug:
            print('... yields', result)
        assert not result

def test_is_valid(debug=False):
    assumptions = []
    conclusion=Formula.parse('(R(0)|~R(0))')
    proof = Proof(assumptions,conclusion, [])
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    proof.lines.append(Proof.Line(Formula.parse('(R(0)|R(0))'), ('T',)))
    assert not proof.verify_t_justification(0)
    proof.lines[0] = Proof.Line(Formula.parse('(R(0)->R(0))'), ('T',))
    assert proof.verify_t_justification(0)
    assert not proof.is_valid()
    proof.lines[0] = Proof.Line(conclusion, ('T',))
    assert proof.verify_t_justification(0)
    if debug:
        print('Added a line and got:', proof)
    assert proof.is_valid()

    assumption1 = Schema(Formula.parse('R(0)'))
    assumption2 = Schema(Formula.parse('(R(0)->Q(1))'))
    conclusion = Formula.parse('Q(1)')
    lines = [Proof.Line(assumption1.formula,('A',assumption1,{})),
             Proof.Line(assumption2.formula,('A',assumption2,{})),
             Proof.Line(conclusion, ('MP',0,1))]
    proof = Proof({assumption1, assumption2}, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.is_valid()


    assumption = Schema(Formula.parse('R(x)'))
    conclusion = Formula.parse('Ax[R(x)]')
    lines = [Proof.Line(assumption.formula, ('A',assumption,{})),
             Proof.Line(conclusion, ('UG',0))]
    proof = Proof({assumption}, conclusion, lines)
    if debug:
        print('\n*************\nCreated a Proof:', proof)
    assert proof.is_valid()

def test_axiom_specialization_map_to_schema_instantiation_map(debug=False):
    propositional_specialization_map = {
        'p': PropositionalFormula.parse('(z1->z2)'),
        'q': PropositionalFormula.parse('z1'),
        'r': PropositionalFormula.parse('~(z3&z2)')}
    substitution_map = {'z1': Formula.parse('Ax[x=5]'),
                        'z2': Formula.parse('M()'),
                        'z3': Formula.parse('z2=5')}
    expected = {'P()': Formula.parse('(Ax[x=5]->M())'),
                'Q()': Formula.parse('Ax[x=5]'),
                'R()': Formula.parse('~(z2=5&M())')}
    if debug:
        print('Testing conversion of propositional specialization map',
              propositional_specialization_map,
              'to instantiation_map via substitution map', substitution_map)
    instantiation_map = axiom_specialization_map_to_schema_instantiation_map(
        propositional_specialization_map, substitution_map)
    assert instantiation_map == expected, instantiation_map

def test_prove_from_skeleton_proof(debug=False):
    from propositions.tautology import prove_tautology

    for formula,skeleton,substitution_map in [
        ('(R(c)->R(c))', '(z23->z23)', {'z23':Formula.parse('R(c)')}),
        ('(x=0->x=0)', '(z24->z24)', {'z24':Formula.parse('x=0')}),
        ('(Ex[x=0]->Ex[x=0])', '(z25->z25)', {'z25':Formula.parse('Ex[x=0]')}),
        ('((~y=1->~x=1)->(x=1->y=1))', '((~z26->~z27)->(z27->z26))',
         {'z26':Formula.parse('y=1'), 'z27':Formula.parse('x=1')}),
        ('(~~Ex[y=2]->Ex[y=2])', '(~~z28->z28)',
         {'z28':Formula.parse('Ex[y=2]')}),
        ('(Ex[Ey[x=y]]->~~Ex[Ey[x=y]])', '(z29->~~z29)',
         {'z29':Formula.parse('Ex[Ey[x=y]]')}),
        ('((~Ex[(x=2->x=3)]->~R(y,4))->((Ex[(x=2->x=3)]->~R(y,4))->~R(y,4)))',
         '((~z30->~z31)->((z30->~z31)->~z31))',
         {'z30':Formula.parse('Ex[(x=2->x=3)]'), 'z31':Formula.parse('R(y,4)')}),
        ('((Ey[~x=y]->(y=3->y=74))->(y=3->(Ey[~x=y]->y=74)))',
         '((z32->(z33->z34))->(z33->(z32->z34)))',
         {'z32':Formula.parse('Ey[~x=y]'), 'z33':Formula.parse('y=3'),
          'z34':Formula.parse('y=74')}),
        ('(~~~~Q()->~~Q())', '(~~~~z35->~~z35)', {'z35':Formula.parse('Q()')})]:
        if debug:
            print('Testing proving', formula, 'from proof of', skeleton)
        formula = Formula.parse(formula)
        skeleton = PropositionalFormula.parse(skeleton)
        skeleton_proof = prove_tautology(skeleton)
        assert skeleton_proof.is_valid(), 'Bug in prove_tautology!'
        proof = prove_from_skeleton_proof(formula, skeleton_proof,
                                          substitution_map)
        assert proof.assumptions == PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMATA
        assert proof.conclusion == formula
        assert proof.is_valid()

def test_prove_tautology(debug=False):
    for tautology in [
            '(R(c)->R(c))', '(x=0->x=0)', '(Ex[x=0]->Ex[x=0])',
            '((~y=1->~x=1)->(x=1->y=1))', '(~~Ex[y=2]->Ex[y=2])',
            '(Ex[Ey[x=y]]->~~Ex[Ey[x=y]])',
            '((~Ex[(x=2->x=3)]->~R(y,4))->((Ex[(x=2->x=3)]->~R(y,4))->~R(y,4)))',
            '((Ey[~x=y]->(y=3->y=74))->(y=3->(Ey[~x=y]->y=74)))',
            '(~~~~Q()->~~Q())']:
        if debug:
            print('Testing proving the tautology', tautology)
        tautology = Formula.parse(tautology)
        proof = prove_tautology(tautology)
        assert proof.assumptions == PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMATA
        assert proof.conclusion == tautology
        for line in proof.lines:
            assert line.justification[0] in {'A', 'MP'}
        assert proof.is_valid()

def test_ex9(debug=False):
    test_instantiate_formula(debug)
    test_instantiate(debug)
    test_verify_a_justification(debug)
    test_verify_t_justification(debug)
    test_verify_mp_justification(debug)
    test_verify_ug_justification(debug)
    test_is_valid(debug)
    test_axiom_specialization_map_to_schema_instantiation_map
    test_prove_from_skeleton_proof(debug)
    test_prove_tautology(debug)

def test_all(debug=False):
    test_ex9(debug)
