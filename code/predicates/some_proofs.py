""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/some_proofs.py """

from predicates.prover import *


# from predicates.deduction import *
# from predicates.prenex import equivalence_of

def syllogism_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) All men are mortal, and
        2) Socrates is a man
        derives the conclusion:
        Socrates is mortal.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    'Mortal(aristotle)', print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R(v)': '(Man(v)->Mortal(v))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.proof


def syllogism_proof_with_universal_instantiation(print_as_proof_forms=False):
    """ Return a proof, constructed using the method
        Prover.add_universal_instantiation, that from the assumptions (in
        addition to Prover.AXIOMS):
        1) All men are mortal, and
        2) Socrates is a man
        derives the conclusion:
        Socrates is mortal.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    'Mortal(aristotle)', print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.proof


def syllogism_all_all_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) All Greeks are human, and
        2) All humans are mortal
        derives the conclusion:
        All Greeks are mortal.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    'Ax[(Greek(x)->Mortal(x))]', print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.proof


def syllogism_all_all_proof_with_tautological_inference(print_as_proof_forms=
                                                        False):
    """ Return a proof, constructed using the method
        Prover.add_tautological_inference, that from the assumptions (in
        addition to Prover.AXIOMS):
        1) All Greeks are human, and
        2) All humans are mortal
        derives the conclusion:
        All Greeks are mortal.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    'Ax[(Greek(x)->Mortal(x))]', print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_inference(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.proof


def syllogism_all_exists_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) All men are mortal, and
        2) Some men exist
        derives the conclusion:
        Some mortals exist.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'}, 'Ex[Mortal(x)]',
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R(v)': 'Mortal(v)', 'c': 'x'})
    step5 = prover.add_tautological_inference(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R(v)': 'Man(v)', 'Q()': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_inference(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.proof


def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms=
                                                           False):
    """ Return a proof, constructed using the method
        Prover.add_existential_derivation, that from the assumptions (in
        addition to Prover.AXIOMS):
        1) All men are mortal, and
        2) Some men exist
        derives the conclusion:
        Some mortals exist.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'}, 'Ex[Mortal(x)]',
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R(v)': 'Mortal(v)', 'c': 'x'})
    step5 = prover.add_tautological_inference(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.proof


def lovers_proof(print_as_proof_forms=False):
    """ Return a proof that from assumptions (in addition to Prover.AXIOMS):
        1) Everybody loves somebody and
        2) Everybody loves a lover
        derives the conclusion:
        Everybody loves everybody.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    'Ax[Az[Loves(z,x)]]', print_as_proof_forms)
    # Task 10.4
    step1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step2 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step1, 'x')
    step3 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step3, 'x')
    step5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step4, 'z')
    step6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step5, 'y')
    step7 = prover.add_existential_derivation('Loves(z,x)', step2, step6)
    step8 = prover.add_ug('Az[Loves(z,x)]', step7)
    prover.add_ug('Ax[Az[Loves(z,x)]]', step8)
    return prover.proof


def homework_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) No homework is fun, and
        2) Some reading is homework
        derives the conclusion:
        Some reading is not fun.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'},
                    'Ex[(Reading(x)&~Fun(x))]', print_as_proof_forms)
    # Task 10.5
    step1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step2 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    step3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])',
                                               Prover.EI,
                                               {'c': 'x', 'x': 'x', 'R(v)': '(Homework(v)&Fun(v))'})
    step4 = prover.add_tautological_inference('(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x))',
                                              {step3})
    step5 = prover.add_mp('~(Homework(x)&Fun(x))', step1, step4)
    step6 = prover.add_tautological_inference('(Homework(x)->~Fun(x))',
                                              {step5})
    step7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])',
                                               Prover.EI,
                                               {'c': 'x', 'x': 'x', 'R(v)': '(Reading(v)&~Fun(v))'})
    step8 = prover.add_tautological_inference('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))',
                                              {step6})
    step9 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])',
                                              {step7, step8})
    prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step2, step9)
    return prover.proof


GROUP_AXIOMS = {'plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))'}


def right_neutral_proof(stop_before_flipped_equality,
                        stop_before_free_instantiation,
                        stop_before_substituted_equality,
                        stop_before_chained_equality,
                        print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        proves x+0=x. If the Boolean flag step_before_flipped_equality is True,
        then construction of the proof (including verification of all
        justifications) is stopped just before the first call to
        Prover.add_flipped_equality, and the partial proof is returned. If the
        Boolean flag stop_before_free_instantiation is True, then construction
        of the proof (including verification of all justifications) is stopped
        just before the first call to Prover.add_free_instantiation, and the
        partial proof is returned. If the Boolean flag
        stop_before_substituted_equality is True, then construction of the proof
        (including verification of all justifications) is stopped just before
        the first call to Prover.add_substituted_equality, and the partial proof
        is returned. If the Boolean flag stop_before_chained_equality is True,
        then construction of the proof (including verification of
        all justifications) is stopped just before the (first) call to
        Prover.add_chained_equality, and the partial proof is returned. The
        Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS, 'plus(x,0)=x', print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.proof
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.proof
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.proof
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(v,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(v,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),v),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),v)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),v)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)',
        flipped_associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(v,x)')
    if stop_before_chained_equality:
        return prover.proof
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.proof


def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), 'c=0',
                    print_as_proof_forms)
    # Task 10.10

    step1 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)',
                                            prover.add_assumption('plus(a,c)=a'), 'plus(minus(a),v)')
    step2 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))',
                                          prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))'),
                                          {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    step3 = prover.add_free_instantiation('plus(minus(a),a)=0', prover.add_assumption('plus(minus(x),x)=0'), {"x": "a"})
    step4 = prover.add_chained_equality("plus(plus(minus(a),a),c)=plus(""minus(a),a)", [step2, step1])
    step5 = prover.add_chained_equality("plus(plus(minus(a),a),c)=0", [step4, step3])
    step6 = prover.add_substituted_equality("plus(plus(minus(a),a),c)=plus(""0,c)", step3, 'plus(v,c)')
    step7 = prover.add_flipped_equality("plus(0,c)=plus(plus(minus(a)," "a),c)", step6)
    step8 = prover.add_chained_equality("plus(0,c)=0", [step7, step5])
    step9 = prover.add_free_instantiation('plus(0,c)=c', prover.add_assumption('plus(0,x)=x'), {"x": 'c'})
    step10 = prover.add_flipped_equality('c=plus(0,c)', step9)
    prover.add_chained_equality('c=0', [step10, step8])

    return prover.proof


FIELD_AXIOMS = GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'})


def multiply_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the field axioms (in addition to Prover.AXIOMS)
        proves 0*x=0. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(FIELD_AXIOMS, 'times(0,x)=0', print_as_proof_forms)
    # Task 10.11
    step1 = prover.add_assumption('plus(0,x)=x')
    step2 = prover.add_free_instantiation('plus(0,times(x,0))=times(x,'
                                          '0)', step1, {'x': 'times(x,0)'})
    step3 = prover.add_flipped_equality("times(x,0)=plus(0,times(x,0))",
                                        step2)
    step4 = prover.add_assumption('times(x,y)=times(y,x)')
    step5 = prover.add_free_instantiation('times(0,x)=times(x,0)',
                                          step4, {'x': '0', 'y': 'x'})

    step6 = prover.add_assumption('plus(minus(x),x)=0')
    step7 = prover.add_free_instantiation(
        "plus(minus(times(x,0)),times(x,0))=0", step6,
        {'x': 'times(x,0)'})
    step8 = prover.add_flipped_equality(
        "0=plus(minus(times(x,0)),times(x,0))", step7)
    step9 = prover.add_substituted_equality(
        "plus(0,times(x,0))=plus(plus(minus(times(x,0)),times(x,0)),times(x,0))", step8, "plus(v,times(x,0))")
    step10 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step11 = prover.add_free_instantiation(
        'plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))',
        step10,
        {'x': 'minus(times(x,0))', 'y': 'times(x,0)', 'z': 'times(x,0)'})
    step12 = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    step13 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))', step12,
                                           {'x': 'x', 'y': '0', 'z': '0'})
    step14 = prover.add_flipped_equality('plus(times(x,0),times(x,0))=times(x,plus(0,0))', step13)
    step15 = prover.add_substituted_equality('plus(minus(times(x,0)),plus(times(x,0),'
                                             'times(x,0)))=plus(minus(times(x,0)),times(x,plus(0,0)))', step14,
                                             "plus(minus(times(x,0)),v)")
    step16 = prover.add_free_instantiation('plus(0,0)=0', step1, {'x': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(times(x,0)),times(x,plus(0,0)))=plus(minus(times(x,0)),times(x,0))', step16,
        "plus(minus(times(x,0)),times(x,v))")
    step18 = prover.add_free_instantiation("plus(minus(times(x,0)),times(x,0))=0", step6, {'x': 'times(x,0)'})
    prover.add_chained_equality("times(0,x)=0", [step5, step3, step9, step11, step15, step17, step18])
    return prover.proof


INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
PEANO_AXIOMS = {'(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                'times(x,s(y))=plus(times(x,y),x)', INDUCTION_AXIOM}


def peano_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the Peano axioms (in addition to Prover.AXIOMS)
        proves 0+x=x. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(PEANO_AXIOMS, 'plus(0,x)=x', print_as_proof_forms)
    # Task 10.12
    return prover.proof


COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})


def russell_paradox_proof(print_as_proof_forms=False):
    """ Return a proof that from the axiom schema of (unrestricted)
        comprehension (in addition to Prover.AXIOMS) proves the falsehood
        (z=z&~z=z). The Boolean flag print_as_proof_forms specifies whether the
        proof being constructed is to be printed in real time as it is being
        constructed """
    prover = Prover({COMPREHENSION_AXIOM}, '(z=z&~z=z)', print_as_proof_forms)
    # Task 10.13
    step1 = prover.add_instantiated_assumption(
        '(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))',
        prover.UI, {"R(v)": "((In(v,y)->~In(v,v))&(~In(v,v)->In(v,y))))", "c": "y"})
    step2 = prover.add_instantiated_assumption('Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]', COMPREHENSION_AXIOM,
                                               {"R(v)": "~In(v,v)"})
    step3 = prover.add_tautology("(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))")
    step4 = prover.add_tautological_inference("(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))",
                                              {step1, step3})
    prover.add_existential_derivation("(z=z&~z=z)", step2, step4)
    return prover.proof


def not_exists_not_implies_all_proof(formula, variable,
                                     print_as_proof_forms=False):
    """ Return a proof of (~Evariable[~formula]->Avariable[formula]) """
    assert type(formula) is Formula
    assert is_variable(variable)
    # Optional Task 11.4.1


def exists_not_implies_not_all_proof(formula, variable,
                                     print_as_proof_forms=False):
    """ Return a proof of (Evariable[~formula]->~Avariable[formula]) """
    assert type(formula) is Formula
    assert is_variable(variable)
    # Optional Task 11.4.2


def not_all_iff_exists_not_proof(formula, variable,
                                 print_as_proof_forms=False):
    """ Return a proof of
        equivalence_of(~Avariable[formula], Evariable[~formula]) """
    assert type(formula) is Formula
    assert is_variable(variable)
    # Optional Task 11.4.3
