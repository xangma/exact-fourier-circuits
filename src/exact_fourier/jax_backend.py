"""Optional floating-point execution of bounded projected circuit records.

JAX is imported only when a compiler is called. Compiled shears retain the
chronological scalings and three C calls emitted by ``words.shear_steps``;
XLA may fuse those operations, so their rounding need not match an unfused
interpreter. This executes an algebraic quotient, not the full saving word.
Enable JAX x64 before compiling/calling when complex128 is required. This
module does not change global JAX settings or select a device.
"""

from __future__ import annotations

from fractions import Fraction
from math import isfinite

from .projection import ProjectedProgram
from .scalars import GaussianRational as QI
from .words import Call, Scale, shear_steps

_MAX_RECORDS = 250_000
_MAX_STATE_ENTRIES = 1_048_576


def _jax():
    try:
        import jax
        import jax.numpy as jnp
    except ImportError as exc:
        raise ImportError("The JAX backend requires the optional jax package.") from exc
    return jax, jnp


def _integer(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _complex(value):
    result = complex(float(value.real), float(value.imag))
    if not isfinite(result.real) or not isfinite(result.imag):
        raise ValueError("coefficient exceeds floating-point range")
    return result


def _validate(program, max_records, max_state_entries):
    if not isinstance(program, ProjectedProgram):
        raise TypeError("expected a ProjectedProgram")
    _integer(max_records, "max_records")
    _integer(max_state_entries, "max_state_entries", 1)
    roles = _integer(program.metadata.get("roles"), "roles", 1)
    width = _integer(program.metadata.get("width"), "width", 1)
    bits = program.projection.address_bits
    role_bits = _integer(program.metadata.get("role_bits", 0), "role_bits")
    if width != 1 << bits or roles * width > max_state_entries:
        raise ValueError("projected state exceeds its shape/materialization limit")
    if role_bits and roles != 1 << role_bits:
        raise ValueError("role_bits must describe the entire padded role axis")
    if len(program.records) > max_records:
        raise ValueError("projected tape exceeds record materialization limit")
    if program.metadata.get("record_count", len(program.records)) != len(program.records):
        raise ValueError("record_count does not match the tape")
    for record in program.records:
        if len(record) != 6:
            raise ValueError("a projected record must have six fields")
        op, target, arg, num, den, inverse = record
        _integer(op, "opcode")
        _integer(target, "target")
        _integer(arg, "argument")
        if type(num) is not int or type(inverse) is not bool:
            raise ValueError("record numerator/inverse must be int/bool")
        _integer(den, "denominator", 1)
        if op > 4 or target >= roles:
            raise ValueError("invalid opcode or target role")
        if op in (0, 3) and arg >= width:
            raise ValueError("xor mask exceeds address width")
        if op in (1, 2) and (arg >= roles or arg == target):
            raise ValueError("shear/exchange requires distinct in-range roles")
        if op == 4 and (not arg or arg & (arg - 1) or arg >= roles or roles & (roles - 1)):
            raise ValueError("role C requires a valid bit of a power-of-two role axis")
    return roles, width, bits, role_bits


def _check_array(values, jnp, *, shape=None, max_entries=_MAX_STATE_ENTRIES):
    values = jnp.asarray(values)
    if shape is not None and values.shape != shape:
        raise ValueError(f"expected amplitudes shaped {shape}, got {values.shape}")
    if values.size > max_entries:
        raise ValueError("array exceeds state materialization limit")
    if values.dtype not in (jnp.dtype("complex64"), jnp.dtype("complex128")):
        raise TypeError("amplitudes must have complex64 or complex128 dtype")
    return values


def _c_pair(u, v, jnp):
    t = jnp.asarray(0.5 - 0.5j, dtype=u.dtype) * (v - u)
    return u + t, v - t


def _paired(values, mask, jnp, *, axis=-1, inverse=False, literal=False):
    """Vectorized disjoint pairs, oriented by the mask's least set bit."""
    axis %= values.ndim
    indexes = jnp.arange(values.shape[axis], dtype=jnp.int32)
    pivot = mask & -mask
    low = (indexes & pivot) == 0
    first = jnp.where(low, indexes, indexes ^ mask)
    u = jnp.take(values, first, axis=axis)
    v = jnp.take(values, first ^ mask, axis=axis)
    if literal:
        a = jnp.asarray(0.5 + 0.5j, dtype=values.dtype)
        b = jnp.asarray(0.5 - 0.5j, dtype=values.dtype)
        lo, hi = a * u + b * v, b * u + a * v
    else:
        lo, hi = _c_pair(u, v, jnp)
    lo, hi = jnp.where(inverse, hi, lo), jnp.where(inverse, lo, hi)
    broadcast = [1] * values.ndim
    broadcast[axis] = values.shape[axis]
    return jnp.where(low.reshape(broadcast), lo, hi)


def _shear_pattern():
    pattern = []
    scale_index = 0
    for step in shear_steps(0, 1, 1):
        if isinstance(step, Scale):
            pattern.append((step.coordinate, scale_index))
            scale_index += 1
        elif isinstance(step, Call) and step.coordinates == (0, 1):
            pattern.append((2, 0))
        else:
            raise AssertionError("unexpected step in the three-C shear compiler")
    return tuple(pattern), scale_index


def _shear_scales(coefficient, pattern):
    if not coefficient:
        return (1 + 0j,) * sum(coordinate != 2 for coordinate, _ in pattern)
    steps = shear_steps(0, 1, coefficient)
    if tuple(2 if isinstance(step, Call) else step.coordinate for step in steps) != tuple(
            coordinate for coordinate, _ in pattern):
        raise AssertionError("shear compiler changed its chronological pattern")
    return tuple(_complex(step.coefficient) for step in steps if isinstance(step, Scale))


def _shear_operator(jax, jnp, compiled_shears):
    pattern, _ = _shear_pattern()

    def apply(u, v, coefficient, scales, nonzero):
        if not compiled_shears:
            return u + coefficient * v, v

        def compiled(pair):
            u, v = pair
            for coordinate, index in pattern:
                if coordinate == 2:
                    u, v = _c_pair(u, v, jnp)
                elif coordinate == 0:
                    u = u * scales[index]
                else:
                    v = v * scales[index]
            return u, v

        return jax.lax.cond(nonzero, compiled, lambda pair: pair, (u, v))

    return apply


def compile_projected(program, compiled_shears=True, *, max_records=_MAX_RECORDS,
                      max_state_entries=_MAX_STATE_ENTRIES):
    """Return a JIT function on ``(roles,width)`` complex amplitudes.

    A single ``lax.scan`` interprets the bounded tape, rather than unrolling
    every record into the compiled graph. It retains zero directions and
    zero shear records. Complex128 requires the caller's JAX x64 setting.
    """
    if type(compiled_shears) is not bool:
        raise ValueError("compiled_shears must be bool")
    roles, width, _, _ = _validate(program, max_records, max_state_entries)
    jax, jnp = _jax()
    pattern, _ = _shear_pattern()
    coefficients, scales, indexes, tape = [0j], [_shear_scales(QI(0), pattern)], {}, []
    for op, target, arg, num, den, inverse in program.records:
        index = 0
        if op == 1:
            value = Fraction(num, den)
            if value not in indexes:
                indexes[value] = len(coefficients)
                coefficients.append(_complex(QI(value)))
                scales.append(_shear_scales(QI(value), pattern) if compiled_shears else scales[0])
            index = indexes[value]
        tape.append((op, target, arg, index, int(inverse), int(num != 0)))
    apply_shear = _shear_operator(jax, jnp, compiled_shears)

    @jax.jit
    def execute(values):
        values = _check_array(values, jnp, shape=(roles, width), max_entries=max_state_entries)
        if not tape:
            return values
        instructions = jnp.asarray(tape, dtype=jnp.int32)
        mu = jnp.asarray(coefficients, dtype=values.dtype)
        scale_bank = jnp.asarray(scales, dtype=values.dtype)
        addresses = jnp.arange(width, dtype=jnp.int32)

        def directional(args):
            state, record = args
            _, target, mask, _, inverse, _ = record
            row = jax.lax.cond(mask == 0, lambda row: row,
                               lambda row: _paired(row, mask, jnp, inverse=inverse != 0),
                               state[target])
            return state.at[target].set(row)

        def shear(args):
            state, record = args
            _, target, source, index, _, nonzero = record
            u, v = apply_shear(state[target], state[source], mu[index], scale_bank[index], nonzero != 0)
            return state.at[target].set(u).at[source].set(v)

        def exchange(args):
            state, record = args
            _, target, source, _, _, _ = record
            u, v = state[target], state[source]
            return state.at[target].set(v).at[source].set(-u)

        def translate(args):
            state, record = args
            _, target, mask, _, _, _ = record
            return state.at[target].set(state[target][addresses ^ mask])

        def role_c(args):
            state, record = args
            return _paired(state, record[2], jnp, axis=0)

        def step(state, record):
            return jax.lax.switch(record[0], (directional, shear, exchange, translate, role_c),
                                  (state, record)), None

        return jax.lax.scan(step, values, instructions)[0]

    return execute


def compile_shear(coefficient, compiled_shears=True):
    """JIT one ``(target,source)`` shear on a complex array shaped ``(2,width)``.

    The coefficient follows the exact compiler's Q(i) input conventions:
    int, Fraction, rational string, GaussianRational or a rational pair.
    """
    if type(compiled_shears) is not bool:
        raise ValueError("compiled_shears must be bool")
    coefficient = QI.coerce(coefficient)
    jax, jnp = _jax()
    pattern, _ = _shear_pattern()
    scales = _shear_scales(coefficient, pattern) if compiled_shears else (1 + 0j,)
    mu = _complex(coefficient)
    apply = _shear_operator(jax, jnp, compiled_shears)

    @jax.jit
    def execute(values):
        values = _check_array(values, jnp)
        if values.ndim != 2 or values.shape[0] != 2:
            raise ValueError("expected amplitudes shaped (2,width)")
        u, v = apply(values[0], values[1], jnp.asarray(mu, dtype=values.dtype),
                     jnp.asarray(scales, dtype=values.dtype), bool(coefficient))
        return jnp.stack((u, v))

    return execute


def compile_c_tensor(bits, *, max_state_entries=_MAX_STATE_ENTRIES):
    """JIT ordinary C^bits on the last axis, with optional leading batches.

    A general projected program has a different Walsh spectrum; use
    ``compile_projected_target`` for a same-operator comparison there.
    """
    _integer(bits, "bits")
    _integer(max_state_entries, "max_state_entries", 1)
    if bits >= max_state_entries.bit_length():
        raise ValueError("tensor width exceeds materialization limit")
    width = 1 << bits
    jax, jnp = _jax()

    @jax.jit
    def execute(values):
        values = _check_array(values, jnp, max_entries=max_state_entries)
        if values.ndim < 1 or values.shape[-1] != width:
            raise ValueError(f"expected last axis of length {width}")
        for bit in range(bits):
            values = _paired(values, 1 << bit, jnp)
        return values

    return execute


def _spectrum(program, width):
    # Integer Walsh transform of basis-image multiplicities. This avoids a
    # full ambient-axis scan for each projected frequency.
    counts = [0] * width
    for image in program.projection.images:
        counts[image] += 1
    stride = 1
    while stride < width:
        for start in range(0, width, 2 * stride):
            for offset in range(stride):
                a, b = start + offset, start + offset + stride
                u, v = counts[a], counts[b]
                counts[a], counts[b] = u + v, u - v
        stride *= 2
    phases = (1 + 0j, 1j, -1 + 0j, -1j)
    return tuple(phases[((program.projection.ambient_bits - count) // 2) % 4] for count in counts)


def compile_projected_target(program, *, max_state_entries=_MAX_STATE_ENTRIES):
    """Independent Walsh-phase target, including the final role-bit tensor.

    This uses neither the network records nor its three-C shear compiler to
    calculate the action. It implements ``projected_target_exact`` in JAX.
    """
    roles, width, bits, role_bits = _validate(program, _MAX_RECORDS, max_state_entries)
    spectrum = _spectrum(program, width)
    jax, jnp = _jax()

    def walsh(values):
        indexes = jnp.arange(width, dtype=jnp.int32)
        for bit in range(bits):
            mask = 1 << bit
            low = (indexes & mask) == 0
            first = indexes & ~mask
            u, v = values[:, first], values[:, first | mask]
            values = jnp.where(low, u + v, u - v)
        return values

    @jax.jit
    def execute(values):
        values = _check_array(values, jnp, shape=(roles, width), max_entries=max_state_entries)
        values = walsh(walsh(values) * jnp.asarray(spectrum, dtype=values.dtype)) / width
        for bit in range(role_bits):
            values = _paired(values, 1 << bit, jnp, axis=0, literal=True)
        return values

    return execute
