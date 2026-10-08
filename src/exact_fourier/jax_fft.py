"""Optional JAX baselines for the positive, unnormalized discrete Fourier transform.

The returned functions accept one vector and return
``y[k] = sum_j x[j] * exp(+2*pi*i*j*k/n)``. Real inputs are promoted to
complex; complex64/complex128 inputs retain their precision. Enable JAX x64
in the caller before passing complex128 inputs. Importing this module does
not import JAX or initialize a device.
"""

from importlib import import_module
from operator import index


def _length(n):
    if isinstance(n, bool):
        raise TypeError("DFT length must be an integer, not bool")
    try:
        n = index(n)
    except TypeError as exc:
        raise TypeError("DFT length must be an integer") from exc
    if n < 1:
        raise ValueError("DFT length must be positive")
    return n


def _jax():
    try:
        return import_module("jax"), import_module("jax.numpy")
    except ImportError as exc:
        raise ImportError("These optional DFT baselines require JAX and jaxlib") from exc


def _vector(jnp, x, n):
    x = jnp.asarray(x)
    if x.ndim != 1 or x.shape != (n,):
        raise ValueError(f"Expected a one-dimensional vector of length {n}, got {x.shape}")
    dtype = jnp.complex128 if x.dtype in (jnp.float64, jnp.complex128) else jnp.complex64
    return x.astype(dtype)


def compile_radix2(n):
    """Return a jitted iterative radix-two DFT; no FFT library calls.

    Bit reversal is fixed integer indexing. Each butterfly stage computes its
    positive-sign complex twiddles with JAX exponential arithmetic.
    """
    n = _length(n)
    if n & (n - 1):
        raise ValueError("Radix-two DFT length must be a power of two")
    jax, jnp = _jax()
    bits = n.bit_length() - 1
    permutation = tuple(int(f"{j:0{bits}b}"[::-1], 2) if bits else 0 for j in range(n))

    def transform(x):
        x = _vector(jnp, x, n)
        real_dtype = x.real.dtype
        imaginary_unit = jnp.asarray(1j, dtype=x.dtype)
        x = x[jnp.asarray(permutation)]
        size = 2
        while size <= n:
            half = size // 2
            phase = jnp.asarray(2, dtype=real_dtype) * jnp.pi * jnp.arange(half, dtype=real_dtype) / size
            twiddle = jnp.exp(imaginary_unit * phase)
            blocks = x.reshape((-1, size))
            left = blocks[:, :half]
            right = blocks[:, half:] * twiddle
            x = jnp.concatenate((left + right, left - right), axis=1).reshape((n,))
            size *= 2
        return x

    return jax.jit(transform)


def compile_bluestein(n):
    """Return a jitted positive DFT of arbitrary positive integer length.

    Bluestein's chirps turn the transform into a linear convolution, padded
    to a power of two >= 2*n-1. JAX fft/ifft compute that convolution with
    their standard normalization; no further 1/n factor is applied.
    """
    n = _length(n)
    jax, jnp = _jax()
    padded = 1 << (2 * n - 2).bit_length()
    # Exact integer phase residues avoid overflowing int32 or first rounding
    # j*j in float32. Complex chirps themselves are computed by JAX.
    residues = tuple((j * j) % (2 * n) for j in range(n))

    def transform(x):
        x = _vector(jnp, x, n)
        real_dtype = x.real.dtype
        imaginary_unit = jnp.asarray(1j, dtype=x.dtype)
        phase = jnp.pi * jnp.asarray(residues, dtype=real_dtype) / n
        chirp = jnp.exp(imaginary_unit * phase)
        inverse_chirp = jnp.conj(chirp)
        kernel = jnp.concatenate((inverse_chirp,
                                  jnp.zeros((padded - (2 * n - 1),), dtype=x.dtype),
                                  inverse_chirp[1:][::-1]))
        data = jnp.pad(x * chirp, (0, padded - n))
        convolution = jnp.fft.ifft(jnp.fft.fft(data) * jnp.fft.fft(kernel))
        return chirp * convolution[:n]

    return jax.jit(transform)
