""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/axiomatic_systems.py """

from propositions.proofs import *

# Axiomatic inference rules that only contain implies
MP = InferenceRule([Formula.parse('p'), Formula.parse('(p->q)')],
                   Formula.parse('q'))
I0 = InferenceRule([], Formula.parse('(p->p)'))
I1 = InferenceRule([], Formula.parse('(q->(p->q))'))
I2 = InferenceRule([], Formula.parse('((p->(q->r))->((p->q)->(p->r)))'))
I3 = InferenceRule([], Formula.parse('(~p->(p->q))'))

# Axiomatic inference rules for not (and implies)
N  = InferenceRule([], Formula.parse('((~q->~p)->(p->q))'))
NI = InferenceRule([], Formula.parse('(p->(~q->~(p->q)))'))
NN = InferenceRule([], Formula.parse('(p->~~p)'))
R  = InferenceRule([], Formula.parse('((q->p)->((~q->p)->p))'))

# Axiomatic systems for implies and not
AXIOMATIC_SYSTEM = {MP, I0, I1, I2, I3, N, NI, NN, R}
HILBERT_AXIOMATIC_SYSTEM = {MP, I1, I2, N}

# Axiomatic inference rules for and (and implies and not)
A   = InferenceRule([], Formula.parse('(p->(q->(p&q)))'))
NA1 = InferenceRule([], Formula.parse('(~p->~(p&q))'))
NA2 = InferenceRule([], Formula.parse('(~q->~(p&q))'))

# Axiomatic inference rules for or (and implies and not)
O1  = InferenceRule([], Formula.parse('(p->(p|q))'))
O2  = InferenceRule([], Formula.parse('(q->(p|q))'))
NO  = InferenceRule([], Formula.parse('(~p->(~q->~(p|q)))'))

# Axiomatic inference rules for constants (and implies and not)
T   =  InferenceRule([], Formula.parse('T'))
NF  = InferenceRule([], Formula.parse('~F'))

# Axiomatic systems for all operators
AXIOMATIC_SYSTEM_FULL = AXIOMATIC_SYSTEM.union({A, NA1, NA2, O1, O2, NO, T, NF})

# Alternative for N
N_ALTERNATIVE = InferenceRule([], Formula.parse('((~q->~p)->((~q->p)->q))'))

HILBERT_AXIOMATIC_SYSTEM_ALTERNATIVE = {MP, I1, I2, N_ALTERNATIVE}

# Alternatives for NA1, NA2, NO without not
A2 = InferenceRule([], Formula.parse('((p&q)->p)'))
A3 = InferenceRule([], Formula.parse('((p&q)->q)'))
O3 = InferenceRule([], Formula.parse('((p->r)->((q->r)->((p|q)->r)))'))

HILBERT_AXIOMATIC_SYSTEM_FULL = \
    HILBERT_AXIOMATIC_SYSTEM.union({A, A2, A3, O1, O2, O3, T, NF})
