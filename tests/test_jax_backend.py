"""CPU floating-point comparisons with exact Q(i) and independent targets."""

import importlib.util
import os
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction

from exact_fourier.jax_backend import (compile_c_tensor, compile_projected,
                                      compile_projected_target, compile_shear)
from exact_fourier.projection import (BinaryProjection, ProjectedProgram,
                                     build_projected_program, evaluate_projected_exact,
                                     projected_target_exact)
from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import KERNEL_C, tensor_axis_word


def dirty_values(roles, width):
    return tuple(tuple(QI(Fraction((17 * role + 5 * address) % 29 - 14, 8),
                          Fraction((11 * role + 7 * address) % 31 - 15, 16))
                       for address in range(width)) for role in range(roles))


def as_complex(values):
    return [[complex(float(value.real), float(value.imag)) for value in row] for row in values]


def program(records=(), projection=None, roles=4, role_bits=2):
    projection = projection or BinaryProjection((1, 2, 3, 0), 2)
    return ProjectedProgram(projection, tuple(records), (),
                            {"roles": roles, "width": 1 << projection.address_bits,
                             "role_bits": role_bits, "record_count": len(records)})


class OptionalImportTests(unittest.TestCase):
    def test_backend_import_does_not_import_jax(self):
        code = """
import sys
class NoJax:
    def find_spec(self, fullname, path=None, target=None):
        if fullname == 'jax' or fullname.startswith('jax.'):
            raise ImportError('JAX deliberately unavailable')
sys.meta_path.insert(0, NoJax())
from exact_fourier.jax_backend import compile_c_tensor
assert 'jax' not in sys.modules
try:
    compile_c_tensor(1)
except ImportError as error:
    assert 'optional jax package' in str(error)
else:
    raise AssertionError('missing JAX was not reported')
"""
        result = subprocess.run([sys.executable, "-c", code], env=os.environ.copy(),
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)


@unittest.skipUnless(importlib.util.find_spec("jax"), "optional JAX is not installed")
class JaxBackendTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import jax
        import jax.numpy as jnp
        import numpy as np
        cls.jax, cls.jnp, cls.np = jax, jnp, np
        if hasattr(jax, "enable_x64"):
            cls.enable_x64 = staticmethod(jax.enable_x64)
        else:
            from jax.experimental import enable_x64
            cls.enable_x64 = staticmethod(enable_x64)

    def check_close(self, actual, expected, dtype, *, atol=None):
        tolerance = (3e-5 if dtype == "complex64" else 3e-13) if atol is None else atol
        self.np.testing.assert_allclose(self.np.asarray(actual), self.np.asarray(expected),
                                        rtol=tolerance, atol=tolerance)
        self.assertEqual(str(actual.dtype), dtype)

    def test_every_opcode_compiled_and_direct_against_exact(self):
        records = ((0, 0, 1, 0, 1, False), (0, 1, 3, 0, 1, True),
                   (0, 2, 0, 0, 1, True), (1, 2, 0, -3, 2, False),
                   (1, 0, 3, 2, 7, False), (1, 1, 2, 0, 1, False),
                   (2, 0, 1, 0, 1, False), (3, 2, 3, 0, 1, False),
                   (3, 3, 0, 0, 1, False), (4, 0, 1, 0, 1, False),
                   (4, 0, 2, 0, 1, False))
        values = dirty_values(4, 4)
        for dtype in ("complex64", "complex128"):
            with self.enable_x64(dtype == "complex128"):
                inputs = self.jnp.asarray(as_complex(values), dtype=dtype)
                for compiled in (True, False):
                    for selected in (*((record,) for record in records), records):
                        with self.subTest(dtype=dtype, compiled=compiled, records=selected):
                            p = program(selected)
                            expected = evaluate_projected_exact(p, values, compiled_shears=compiled).final
                            actual = compile_projected(p, compiled)(inputs).block_until_ready()
                            self.check_close(actual, as_complex(expected), dtype)

    def test_shear_source_restore_and_complex_coefficients(self):
        values = dirty_values(2, 7)
        for coefficient in (QI(0), QI(1), QI(Fraction(-3, 7)), QI(Fraction(2, 3), Fraction(-5, 4))):
            expected = [[u + coefficient * v for u, v in zip(values[0], values[1])], list(values[1])]
            for dtype in ("complex64", "complex128"):
                with self.enable_x64(dtype == "complex128"):
                    inputs = self.jnp.asarray(as_complex(values), dtype=dtype)
                    for compiled in (True, False):
                        actual = compile_shear(coefficient, compiled)(inputs).block_until_ready()
                        self.check_close(actual, as_complex(expected), dtype)
                        self.check_close(actual[1], as_complex([values[1]])[0], dtype)

    def test_zero_direction_and_compiled_zero_shear_are_literal_noops(self):
        p = program(((0, 0, 0, 0, 1, False), (0, 1, 0, 0, 1, True),
                     (1, 0, 1, 0, 1, False)))
        inputs = self.jnp.asarray([[complex(float("inf"), 0), complex(float("nan"), 1), 2j, 3],
                                  [1j, 2j, 3j, 4j], [1, 2, 3, 4], [5, 6, 7, 8]], dtype="complex64")
        actual = self.np.asarray(compile_projected(p)(inputs).block_until_ready())
        self.assertTrue(self.np.array_equal(actual, self.np.asarray(inputs), equal_nan=True))

    def test_empty_tape_and_unit_address_width(self):
        p = program(projection=BinaryProjection((0,), 0))
        inputs = self.jnp.asarray([[1j], [2], [3j], [4]], dtype="complex64")
        self.np.testing.assert_array_equal(compile_projected(p)(inputs), inputs)
        self.np.testing.assert_array_equal(compile_c_tensor(0)(inputs), inputs)

    def test_tensor_baseline_matches_exact_words_with_batches(self):
        for bits in (1, 2, 3):
            values = dirty_values(4, 1 << bits)
            exact = tensor_axis_word(KERNEL_C, bits).compile()
            expected = [exact.evaluate(row) for row in values]
            for dtype in ("complex64", "complex128"):
                with self.enable_x64(dtype == "complex128"):
                    inputs = self.jnp.asarray(as_complex(values), dtype=dtype).reshape(2, 2, 1 << bits)
                    actual = compile_c_tensor(bits)(inputs).block_until_ready()
                    self.check_close(actual.reshape(4, 1 << bits), as_complex(expected), dtype)

    def test_projected_target_has_the_actual_walsh_spectrum(self):
        p = program(projection=BinaryProjection((1, 2, 3, 3, 0), 2))
        values = dirty_values(4, 4)
        expected = projected_target_exact(p, values)
        for dtype in ("complex64", "complex128"):
            with self.enable_x64(dtype == "complex128"):
                inputs = self.jnp.asarray(as_complex(values), dtype=dtype)
                actual = compile_projected_target(p)(inputs).block_until_ready()
                self.check_close(actual, as_complex(expected), dtype)
        # Even with no role-bit transform, a projected basis is not generally
        # the ordinary two-axis tensor; both baselines are kept distinct.
        unpadded = program(projection=p.projection, role_bits=0)
        inputs = self.jnp.asarray(as_complex(values), dtype="complex64")
        self.assertGreater(float(self.jnp.max(self.jnp.abs(
            compile_projected_target(unpadded)(inputs) - compile_c_tensor(2)(inputs)))), 0.1)

    def test_full_dirty_network_both_precisions_and_shear_modes(self):
        p = build_projected_program(h=4, bits=1, include_padding=True)
        values = dirty_values(p.metadata["roles"], p.metadata["width"])
        expected = as_complex(projected_target_exact(p, values))
        # Exact direct replay checks the complete record path independently;
        # the opcode tests above also execute every compiled scaling in Q(i).
        self.assertEqual(evaluate_projected_exact(p, values, compiled_shears=False).final,
                         projected_target_exact(p, values))
        for dtype in ("complex64", "complex128"):
            with self.enable_x64(dtype == "complex128"):
                inputs = self.jnp.asarray(as_complex(values), dtype=dtype)
                self.check_close(compile_projected_target(p)(inputs), expected, dtype)
                for compiled in (True, False):
                    with self.subTest(dtype=dtype, compiled=compiled):
                        actual = compile_projected(p, compiled)(inputs).block_until_ready()
                        self.check_close(actual, expected, dtype, atol=1e-3 if dtype == "complex64" else 1e-11)

    def test_unpadded_and_sixteen_address_networks(self):
        for bits, padded in ((2, False), (4, True)):
            p = build_projected_program(h=4, bits=bits, include_padding=padded)
            values = dirty_values(p.metadata["roles"], p.metadata["width"])
            expected = as_complex(projected_target_exact(p, values))
            for dtype in ("complex64", "complex128"):
                with self.enable_x64(dtype == "complex128"):
                    inputs = self.jnp.asarray(as_complex(values), dtype=dtype)
                    self.check_close(compile_projected_target(p)(inputs), expected, dtype)
                    for compiled in (True, False):
                        with self.subTest(bits=bits, padded=padded, dtype=dtype, compiled=compiled):
                            actual = compile_projected(p, compiled)(inputs).block_until_ready()
                            self.check_close(actual, expected, dtype,
                                             atol=1e-3 if dtype == "complex64" else 1e-11)

    def test_tape_is_one_scan_not_record_unrolling(self):
        p = program(((1, 0, 1, 1, 1, False),) * 100)
        function = compile_projected(p)
        inputs = self.jnp.zeros((4, 4), dtype="complex64")
        closed = self.jax.make_jaxpr(function)(inputs)
        def scans(jaxpr):
            result = []
            for equation in jaxpr.eqns:
                if equation.primitive.name == "scan":
                    result.append(equation.params["length"])
                for value in equation.params.values():
                    if hasattr(value, "jaxpr"):
                        result.extend(scans(value.jaxpr))
            return result
        self.assertEqual(scans(closed.jaxpr), [100])

    def test_shape_dtype_and_materialization_guards(self):
        p = program()
        for bad in (((5, 0, 1, 0, 1, False),), ((0, 0, 4, 0, 1, False),),
                    ((1, 0, 0, 1, 1, False),), ((1, 0, 1, 1, 0, False),),
                    ((2, 0, 4, 0, 1, False),), ((4, 0, 3, 0, 1, False),),
                    ((0, 0, 1, 0, 1, 1),)):
            with self.assertRaises(ValueError):
                compile_projected(program(bad))
        for bad in (replace(p, metadata={**p.metadata, "roles": 1_048_577}),
                    replace(p, metadata={**p.metadata, "width": 3}),
                    replace(p, metadata={**p.metadata, "record_count": 1}),
                    replace(p, metadata={**p.metadata, "role_bits": 3})):
            with self.assertRaises(ValueError):
                compile_projected(bad)
        with self.assertRaises(ValueError):
            compile_projected(program(((0, 0, 1, 0, 1, False),)), max_records=0)
        with self.assertRaises(ValueError):
            compile_projected(p, max_state_entries=15)
        with self.assertRaises(ValueError):
            compile_c_tensor(30)
        with self.assertRaises(ValueError):
            compile_projected(p, compiled_shears=1)
        with self.assertRaises(ValueError):
            compile_projected(p)(self.jnp.zeros((2, 4), dtype="complex64"))
        with self.assertRaises(TypeError):
            compile_projected(p)(self.jnp.zeros((4, 4), dtype="float32"))
        with self.assertRaises(ValueError):
            compile_shear(1)(self.jnp.zeros((4, 4), dtype="complex64"))
        with self.assertRaises(ValueError):
            compile_c_tensor(1)(self.jnp.zeros((4, 4), dtype="complex64"))
        with self.assertRaises(ValueError):
            compile_c_tensor(1, max_state_entries=2)(self.jnp.zeros((2, 2), dtype="complex64"))
        with self.assertRaises(TypeError):
            compile_shear(1.0)


if __name__ == "__main__":
    unittest.main()
