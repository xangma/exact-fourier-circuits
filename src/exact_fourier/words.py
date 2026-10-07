"""Finite words in a fixed kernel; permutations are free, scalings charged.

Words store chronological steps. Basis verification checks an actual finite
matrix identity; call-count savings and scalar-gate counts are separate.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .circuit import Circuit, CircuitBuilder, append_matrix, exact_matrix
from .scalars import GaussianRational as QI, I, ONE

A = (ONE + I) / 2
B = (ONE - I) / 2
KERNEL_C = ((A, B), (B, A))


@dataclass(frozen=True)
class Call:
    coordinates: tuple[int, ...]

    def __post_init__(self):
        object.__setattr__(self, 'coordinates', tuple(self.coordinates))
        if len(set(self.coordinates)) != len(self.coordinates):
            raise ValueError('call coordinates must be distinct')


@dataclass(frozen=True)
class Scale:
    coordinate: int
    coefficient: QI

    def __post_init__(self):
        object.__setattr__(self, 'coefficient', QI.coerce(self.coefficient))
        if not self.coefficient:
            raise ValueError('monomial scalings must be invertible')


@dataclass(frozen=True)
class Permute:
    """Output i reads the old coordinate sources[i]."""
    sources: tuple[int, ...]

    def __post_init__(self):
        object.__setattr__(self, 'sources', tuple(self.sources))
        if sorted(self.sources) != list(range(len(self.sources))):
            raise ValueError('sources must be a permutation')


@dataclass(frozen=True)
class Word:
    kernel: tuple[tuple[QI, ...], ...]
    width: int
    steps: tuple[Call | Scale | Permute, ...]

    def __post_init__(self):
        matrix = exact_matrix(self.kernel)
        q = len(matrix)
        if q < 1 or any(len(row) != q for row in matrix):
            raise ValueError('kernel must be a nonempty square matrix')
        if type(self.width) is not int or self.width < q:
            raise ValueError('word width must be at least the kernel width')
        object.__setattr__(self, 'kernel', matrix)
        object.__setattr__(self, 'steps', tuple(self.steps))
        for step in self.steps:
            if isinstance(step, Call):
                if len(step.coordinates) != q:
                    raise ValueError('call tuple must match the kernel width')
                coords = step.coordinates
            elif isinstance(step, Scale):
                coords = (step.coordinate,)
            elif isinstance(step, Permute):
                if len(step.sources) != self.width:
                    raise ValueError('permutation must match word width')
                coords = step.sources
            else:
                raise ValueError('unsupported word step')
            if any(type(i) is not int or not 0 <= i < self.width for i in coords):
                raise ValueError('coordinate outside word width')

    @property
    def call_count(self):
        return sum(isinstance(s, Call) for s in self.steps)

    def compile(self, *, max_inputs=4096, max_gates=250000) -> Circuit:
        if self.width > max_inputs:
            raise ValueError('word exceeds materialization input limit')
        builder = CircuitBuilder(self.width, max_gates=max_gates)
        refs = list(range(self.width))
        for step in self.steps:
            if isinstance(step, Scale):
                refs[step.coordinate] = builder.scale(step.coefficient, refs[step.coordinate])
            elif isinstance(step, Permute):
                refs = [refs[i] for i in step.sources]
            else:
                coordinates = step.coordinates
                old = [refs[i] for i in coordinates]
                if self.kernel == KERNEL_C:
                    # C(u,v)=(u+b(v-u),v-b(v-u)): four charged scalar gates.
                    difference = builder.sub(old[1], old[0])
                    t = builder.scale(B, difference)
                    new = (builder.add(old[0], t), builder.sub(old[1], t))
                else:
                    new = append_matrix(builder, self.kernel, old)
                for i, ref in zip(coordinates, new):
                    refs[i] = ref
        return builder.build(refs)

    def to_dict(self):
        def encode(s):
            if isinstance(s, Call): return {'op':'call','coordinates':list(s.coordinates)}
            if isinstance(s, Scale): return {'op':'scale','coordinate':s.coordinate,'coefficient':s.coefficient.to_dict()}
            return {'op':'permute','sources':list(s.sources)}
        return {'schema':'exact-fourier-word/v1','width':self.width,
                'kernel':[[c.to_dict() for c in row] for row in self.kernel],
                'steps':[encode(s) for s in self.steps]}

    @classmethod
    def from_dict(cls, data, *, max_inputs=4096, max_steps=250000, max_kernel_entries=4096):
        if not isinstance(data,dict) or set(data) != {'schema','width','kernel','steps'} or data['schema'] != 'exact-fourier-word/v1':
            raise ValueError('invalid word schema')
        if type(data['width']) is not int or not 1 <= data['width'] <= max_inputs:
            raise ValueError('word width exceeds import limit')
        matrix = data['kernel']
        if not isinstance(matrix,list) or not matrix or any(not isinstance(row,list) for row in matrix):
            raise ValueError('kernel must be a matrix array')
        q = len(matrix)
        if q*q > max_kernel_entries or any(len(row)!=q for row in matrix):
            raise ValueError('kernel shape or entry limit invalid')
        if not isinstance(data['steps'],list) or len(data['steps']) > max_steps:
            raise ValueError('steps exceed import limit')
        steps = []
        for s in data['steps']:
            if not isinstance(s,dict): raise ValueError('word step must be an object')
            if s.get('op') == 'call' and set(s) == {'op','coordinates'}:
                if not isinstance(s['coordinates'],list) or len(s['coordinates']) != q:
                    raise ValueError('call coordinates must match kernel width')
                steps.append(Call(tuple(s['coordinates'])))
            elif s.get('op') == 'scale' and set(s) == {'op','coordinate','coefficient'}:
                steps.append(Scale(s['coordinate'],QI.from_dict(s['coefficient'])))
            elif s.get('op') == 'permute' and set(s) == {'op','sources'}:
                if not isinstance(s['sources'],list) or len(s['sources']) != data['width']:
                    raise ValueError('permutation must match word width')
                steps.append(Permute(tuple(s['sources'])))
            else: raise ValueError('invalid word step')
        return cls(tuple(tuple(QI.from_dict(c) for c in row) for row in data['kernel']),
                   data['width'],tuple(steps))


def shear_steps(target: int, source: int, coefficient, *, fixed_six_calls=False):
    """Compile y+=t*x using three forward C calls and invertible monomials.

    General zero-safe fixed patterns split t into kappa and t-kappa (six calls).
    Without fixed_six_calls, a literal zero is the empty word.
    """
    if target == source: raise ValueError('shear coordinates must be distinct')
    t = QI.coerce(coefficient)
    if fixed_six_calls:
        kappa = QI(1+t.norm_squared())
        return shear_steps(target, source, kappa) + shear_steps(target, source, t-kappa)
    if not t: return ()
    steps = [Scale(target,5/(4*t))]

    def hadamard():
        # H' = a^-1 S C S, S=diag(1,i).
        steps.extend((Scale(source,I),Call((target,source)),
                      Scale(target,1/A),Scale(source,I/A)))
    hadamard()
    steps.append(Scale(target,-3))
    hadamard()
    steps.append(Scale(target,2))
    hadamard()
    steps.extend((Scale(target,QI('-1/8')),Scale(source,QI('-1/6')),
                  Scale(target,4*t/5)))
    return tuple(steps)


def tensor_axis_word(kernel, exponent: int, *, max_inputs=4096):
    matrix = exact_matrix(kernel)
    q = len(matrix)
    if type(exponent) is not int or exponent < 1 or q < 2:
        raise ValueError('baseline needs q>=2 and exponent>=1')
    width = 1
    for _ in range(exponent):
        width *= q
        if width > max_inputs: raise ValueError('tensor baseline exceeds input limit')
    steps = []
    for axis in range(exponent):
        stride = q**(exponent-axis-1)
        for start in range(0,width,q*stride):
            for offset in range(stride):
                steps.append(Call(tuple(start+offset+d*stride for d in range(q))))
    return Word(matrix,width,tuple(steps))


def tensor_matrix(kernel, exponent: int, *, max_entries=262144):
    matrix = exact_matrix(kernel)
    q = len(matrix)
    if type(exponent) is not int or exponent < 0 or q < 1 or any(len(row)!=q for row in matrix):
        raise ValueError('tensor matrix needs square kernel and nonnegative integer exponent')
    width = 1
    for _ in range(exponent):
        width *= q
        if width*width > max_entries: raise ValueError('tensor matrix exceeds entry limit')
    def entry(i,j):
        value = ONE
        for _ in range(exponent):
            value *= matrix[i%q][j%q]
            i //= q; j //= q
        return value
    return tuple(tuple(entry(i,j) for j in range(width)) for i in range(width))


def is_invertible(matrix):
    a = [list(row) for row in exact_matrix(matrix)]
    n = len(a)
    if not n or any(len(row)!=n for row in a):
        raise ValueError('invertibility needs a nonempty square matrix')
    for col in range(n):
        pivot = next((i for i in range(col,n) if a[i][col]),None)
        if pivot is None: return False
        a[col],a[pivot] = a[pivot],a[col]
        for i in range(col+1,n):
            t = a[i][col]/a[col][col]
            for j in range(col,n): a[i][j] -= t*a[col][j]
    return True


def verify_finite_win(word: Word, exponent: int, *, max_inputs=256):
    """Accept only an actual, bounded, exact finite-win word; no tolerance."""
    q = len(word.kernel)
    if type(exponent) is not int or exponent < 2 or q < 2:
        raise ValueError('finite win needs q,b>=2')
    # Determine the required width incrementally; do not allocate huge q**b.
    width = 1
    for _ in range(exponent):
        width *= q
        if width > max_inputs: raise ValueError('exact verification exceeds input limit')
    if word.width != width: raise ValueError('word width is not q**b')
    if not is_invertible(word.kernel): raise ValueError('kernel is singular')
    if all(sum(bool(c) for c in row) == 1 for row in word.kernel):
        raise ValueError('kernel is monomial')
    baseline = exponent*width//q
    if word.call_count >= baseline: raise ValueError('word does not strictly save calls')
    circuit = word.compile(max_inputs=max_inputs)
    expected = tensor_matrix(word.kernel,exponent)
    certificate = circuit.linear_map_certificate(expected)
    if not certificate['passed']:
        raise ValueError('word does not equal the exact tensor power')
    return {'schema':'exact-finite-win/v1','verified':True,'q':q,'b':exponent,
            'width':width,'calls':word.call_count,'baseline_calls':baseline,
            'scalar_gates':circuit.gate_count,'matrix_certificate':certificate}
