import importlib.util
import os
import subprocess
import sys
import unittest
from unittest.mock import patch

from exact_fourier.jax_newton import compile_newton, newton_factors


def dense_positive_matrix(n):
    import numpy as np
    j = np.arange(n, dtype=np.float64)
    return np.exp(2j * np.pi * np.outer(j, j) / n)


class OptionalNewtonTests(unittest.TestCase):
    def test_lazy_import_and_missing_backend(self):
        subprocess.run([sys.executable, "-c",
                        "import exact_fourier.jax_newton; import sys; assert 'jax' not in sys.modules"],
                       env=os.environ.copy(), check=True, capture_output=True)
        with patch("exact_fourier.jax_fft.import_module", side_effect=ModuleNotFoundError("jax")):
            with self.assertRaisesRegex(ImportError, "require JAX and jaxlib"):
                compile_newton(3)

    def test_materialization_guard_before_backend_loading(self):
        for factory in (compile_newton, newton_factors):
            for n in (0, -1, 65):
                with self.subTest(factory=factory.__name__, n=n), self.assertRaises(ValueError):
                    factory(n)
            for n in (True, 2.5, "4"):
                with self.subTest(factory=factory.__name__, n=n), self.assertRaises(TypeError):
                    factory(n)
            with self.assertRaisesRegex(ValueError, "materialization limit 2"):
                factory(3, max_n=2)


@unittest.skipUnless(importlib.util.find_spec("jax") and importlib.util.find_spec("jaxlib"),
                     "optional JAX backend is unavailable")
class NewtonFactorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import jax
        import jax.numpy as jnp
        import numpy as np
        cls.previous_x64 = jax.config.jax_enable_x64
        jax.config.update("jax_enable_x64", True)
        cls.jax, cls.jnp, cls.np = jax, jnp, np

    @classmethod
    def tearDownClass(cls):
        cls.jax.config.update("jax_enable_x64", cls.previous_x64)

    def test_factor_entries_and_ordinary_transpose_identity(self):
        np = self.np
        for n in range(1, 9):
            for dtype in (np.complex64, np.complex128):
                with self.subTest(n=n, dtype=dtype):
                    N, diagonal = map(np.asarray, newton_factors(n, dtype))
                    # Independent Newton polynomial evaluation, without H-ratios.
                    u = np.exp(2j * np.pi / n)
                    direct = np.zeros((n, n), dtype=np.complex128)
                    for i in range(n):
                        for k in range(i + 1):
                            direct[i, k] = np.prod([u**i - u**j for j in range(k)])
                    eps = np.finfo(N.real.dtype).eps
                    np.testing.assert_allclose(N, direct, atol=64 * n * eps, rtol=64 * n * eps)
                    np.testing.assert_array_equal(diagonal, np.diag(N))
                    self.assertTrue(np.all(abs(diagonal) > 0))
                    factor_matrix = N @ (N.T / diagonal[:, None])
                    # Forward error scales with the absolute factor product.
                    envelope = np.abs(N) @ (np.abs(N.T) / np.abs(diagonal[:, None]))
                    tolerance = 64 * n * eps * max(1, float(envelope.max()))
                    self.assertLessEqual(float(abs(factor_matrix - dense_positive_matrix(n)).max()), tolerance)
        N, d = map(np.asarray, newton_factors(5, np.complex128))
        wrong = N @ (N.conj().T / d[:, None])
        self.assertGreater(float(abs(wrong - dense_positive_matrix(5)).max()), 0.5)

    def test_small_dfts_impulse_tone_random_and_precision(self):
        np = self.np
        rng = np.random.default_rng(130)
        for n in range(1, 9):
            transform = compile_newton(n)
            impulse = np.zeros(n, dtype=np.complex128)
            impulse[min(1, n - 1)] = 1
            frequency = min(1, n - 1)
            tone = np.exp(-2j * np.pi * frequency * np.arange(n) / n)
            random = rng.normal(size=n) + 1j * rng.normal(size=n)
            for dtype in (np.complex64, np.complex128):
                N, d = map(np.asarray, newton_factors(n, dtype))
                eps = np.finfo(N.real.dtype).eps
                for name, values in (("impulse", impulse), ("tone", tone), ("random", random)):
                    with self.subTest(n=n, dtype=dtype, family=name):
                        x = values.astype(dtype)
                        actual = np.asarray(transform(x))
                        self.assertEqual(actual.shape, (n,))
                        self.assertEqual(actual.dtype, np.dtype(dtype))
                        envelope = abs(N) @ ((abs(N.T) @ abs(x)) / abs(d))
                        tolerance = 128 * n * eps * max(1, float(envelope.max()))
                        self.assertLessEqual(float(abs(actual - dense_positive_matrix(n) @ x).max()), tolerance)
                result = np.asarray(transform(tone.astype(dtype)))
                self.assertEqual(int(np.argmax(abs(result))), frequency)
                self.assertAlmostEqual(abs(result[frequency]), n, delta=1e-3 if dtype == np.complex64 else 1e-10)
                if n >= 3:
                    self.assertLess(abs(result[(n - frequency) % n]), 1e-3)

    def test_no_fft_calls_and_shape_real_promotion(self):
        np = self.np
        with patch.object(self.jnp.fft, "fft", side_effect=AssertionError("FFT called")), \
             patch.object(self.jnp.fft, "ifft", side_effect=AssertionError("IFFT called")):
            transform = compile_newton(4)
            for dtype, expected in ((np.float32, np.complex64), (np.float64, np.complex128)):
                x = np.arange(4, dtype=dtype)
                actual = np.asarray(transform(x))
                self.assertEqual(actual.dtype, np.dtype(expected))
                np.testing.assert_allclose(actual, dense_positive_matrix(4) @ x, atol=1e-5)
        for shape in ((3,), (2, 2), ()):
            with self.subTest(shape=shape), self.assertRaisesRegex(ValueError, "one-dimensional"):
                transform(np.zeros(shape))
        with self.assertRaises(TypeError):
            newton_factors(4, "float64")

    def test_factor_precision_guard(self):
        self.jax.config.update("jax_enable_x64", False)
        try:
            with self.assertRaisesRegex(ValueError, "jax_enable_x64"):
                newton_factors(4, "complex128")
            N, diagonal = newton_factors(4)
            self.assertEqual(N.dtype, self.jnp.complex64)
            self.assertEqual(diagonal.dtype, self.jnp.complex64)
        finally:
            self.jax.config.update("jax_enable_x64", True)


if __name__ == "__main__":
    unittest.main()
