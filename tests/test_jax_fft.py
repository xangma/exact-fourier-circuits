import importlib.util
import os
import subprocess
import sys
import unittest
from unittest.mock import patch

from exact_fourier.jax_fft import compile_bluestein, compile_radix2


def dense_positive_dft(x):
    import numpy as np
    x = np.asarray(x, dtype=np.complex128)
    indices = np.arange(len(x), dtype=np.float64)
    return np.exp(2j * np.pi * np.outer(indices, indices) / len(x)) @ x


class OptionalBackendTests(unittest.TestCase):
    def test_import_is_lazy(self):
        subprocess.run([sys.executable, "-c",
                        "import exact_fourier.jax_fft; import sys; assert 'jax' not in sys.modules"],
                       env=os.environ.copy(), check=True, capture_output=True)

    def test_missing_backend_has_clear_error(self):
        with patch("exact_fourier.jax_fft.import_module", side_effect=ModuleNotFoundError("jax")):
            with self.assertRaisesRegex(ImportError, "require JAX and jaxlib"):
                compile_bluestein(3)

    def test_invalid_lengths_before_backend_loading(self):
        for factory in (compile_radix2, compile_bluestein):
            for n in (0, -1, -8):
                with self.subTest(factory=factory.__name__, n=n), self.assertRaises(ValueError):
                    factory(n)
            for n in (True, 2.5, "4"):
                with self.subTest(factory=factory.__name__, n=n), self.assertRaises(TypeError):
                    factory(n)
        for n in (3, 6, 15):
            with self.assertRaisesRegex(ValueError, "power of two"):
                compile_radix2(n)


@unittest.skipUnless(importlib.util.find_spec("jax") and importlib.util.find_spec("jaxlib"),
                     "optional JAX backend is unavailable")
class JAXDFTTests(unittest.TestCase):
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

    def compare(self, factory, lengths):
        np = self.np
        rng = np.random.default_rng(130)
        for n in lengths:
            transform = factory(n)
            impulse = np.zeros(n, dtype=np.complex128)
            impulse[min(1, n - 1)] = 1
            tone_index = min(2, n - 1)
            tone = np.exp(-2j * np.pi * tone_index * np.arange(n) / n)
            random = rng.normal(size=n) + 1j * rng.normal(size=n)
            for dtype, rtol, atol in ((np.complex128, 3e-12, 3e-12),
                                      (np.complex64, 2e-5, 2e-5)):
                for name, values in (("impulse", impulse), ("tone", tone), ("random", random)):
                    x = values.astype(dtype)
                    with self.subTest(factory=factory.__name__, n=n, dtype=dtype, family=name):
                        actual = np.asarray(transform(x))
                        self.assertEqual(actual.shape, (n,))
                        self.assertEqual(actual.dtype, np.dtype(dtype))
                        np.testing.assert_allclose(actual, dense_positive_dft(x), rtol=rtol, atol=atol)
                actual_tone = np.asarray(transform(tone.astype(dtype)))
                self.assertEqual(int(np.argmax(abs(actual_tone))), tone_index)
                self.assertAlmostEqual(abs(actual_tone[tone_index]), n, delta=n * rtol)
                if n > 2 and tone_index != (n - tone_index) % n:
                    self.assertLess(abs(actual_tone[(n - tone_index) % n]), n * rtol)

    def test_radix2_against_independent_dense_dft(self):
        self.compare(compile_radix2, (1, 2, 4, 8, 16, 32, 64))

    def test_bluestein_prime_and_composite_lengths(self):
        self.compare(compile_bluestein, (1, 2, 3, 5, 6, 7, 9, 11, 12, 17, 25, 31, 64))

    def test_radix2_never_calls_library_fft(self):
        with patch.object(self.jnp.fft, "fft", side_effect=AssertionError("FFT called")), \
             patch.object(self.jnp.fft, "ifft", side_effect=AssertionError("IFFT called")):
            x = self.np.arange(8, dtype=self.np.float64)
            self.np.testing.assert_allclose(compile_radix2(8)(x), dense_positive_dft(x), atol=1e-12)

    def test_bluestein_convolution_uses_fft_and_ifft(self):
        with patch.object(self.jnp.fft, "fft", wraps=self.jnp.fft.fft) as fft, \
             patch.object(self.jnp.fft, "ifft", wraps=self.jnp.fft.ifft) as ifft:
            compile_bluestein(5)(self.np.ones(5, dtype=self.np.complex128)).block_until_ready()
            self.assertEqual(fft.call_count, 2)
            self.assertEqual(ifft.call_count, 1)

    def test_shape_validation_and_real_promotion(self):
        for factory in (compile_radix2, compile_bluestein):
            transform = factory(4)
            for shape in ((3,), (2, 2), ()):
                with self.subTest(factory=factory.__name__, shape=shape), self.assertRaisesRegex(ValueError, "one-dimensional"):
                    transform(self.np.zeros(shape))
            for dtype, result_dtype in ((self.np.float32, self.np.complex64),
                                         (self.np.float64, self.np.complex128)):
                x = self.np.arange(4, dtype=dtype)
                actual = self.np.asarray(transform(x))
                self.assertEqual(actual.dtype, result_dtype)
                self.np.testing.assert_allclose(actual, dense_positive_dft(x), atol=1e-6)


if __name__ == "__main__":
    unittest.main()
