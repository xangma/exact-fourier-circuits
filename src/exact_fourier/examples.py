"""Small, independently specified exact examples; none claims a finite win."""
from fractions import Fraction
from .scalars import GaussianRational as QI, I
from .circuit import CircuitBuilder, append_matrix
from .words import KERNEL_C, Word, shear_steps, tensor_axis_word, tensor_matrix
from .network import NetworkParameters, iter_scalar_shears


def scalar_exchange_word(h=3, *, max_wires=256, max_shears=10000):
    p = NetworkParameters(h)
    if p.wires > max_wires or p.scalar_shears > max_shears:
        raise ValueError('scalar exchange exceeds materialization limits')
    steps = []
    for shear in iter_scalar_shears(p):
        steps.extend(shear_steps(shear.target, shear.source, shear.coefficient))
    return Word(KERNEL_C,p.wires,tuple(steps))


def scalar_exchange_matrix(h=3):
    p = NetworkParameters(h)
    if p.wires > 256: raise ValueError('matrix exceeds example limit')
    rows = [[QI(0) for _ in range(p.wires)] for _ in range(p.wires)]
    for i in range(p.bank_size):
        rows[i][p.bank_size+i] = QI(-1)
        rows[p.bank_size+i][i] = QI(1)
    for i in range(2*p.bank_size,p.wires): rows[i][i] = QI(1)
    return rows


def demo_cases():
    word = Word(KERNEL_C,2,shear_steps(0,1,QI(Fraction(1,2),Fraction(1,4))))
    tensor = tensor_axis_word(KERNEL_C,3)
    exchange = scalar_exchange_word()
    f4 = tuple(tuple(I**(j*k) for k in range(4)) for j in range(4))
    builder = CircuitBuilder(4)
    fourier = builder.build(append_matrix(builder,f4,range(4)))
    return [('three-call-shear',word.compile(),((1,QI(Fraction(1,2),Fraction(1,4))),(0,1))),
            ('C-tensor-cubed',tensor.compile(),tensor_matrix(KERNEL_C,3)),
            ('dirty-auxiliary-scalar-exchange-h3',exchange.compile(),scalar_exchange_matrix()),
            ('positive-sign-Fourier-4',fourier,f4)]
