"""Optional JAX experiment for the companion paper's dense Newton reduction.

For the positive, unnormalized Fourier matrix, the paper gives
``F = N @ diag(1/diag(N)) @ N.T``. The transpose is ordinary, without
conjugation. These dense factors illustrate that identity; they do not
implement the paper's shallow Toeplitz compiler or uniform fast algorithm.
Roundoff and cancellation become severe as the length grows.

JAX is imported only when a factory is called. Complex128 requires the
caller to enable JAX x64. Dense materialization is limited to 64 by default.
"""

from .jax_fft import _jax, _length, _vector


def _bounded_length(n, max_n):
    n, max_n = _length(n), _length(max_n)
    if n > max_n:
        raise ValueError(f"Dense Newton length {n} exceeds materialization limit {max_n}")
    return n


def _factors(jnp, n, dtype):
    real_dtype = jnp.empty((), dtype=dtype).real.dtype
    one = jnp.asarray(1, dtype=dtype)
    imaginary_unit = jnp.asarray(1j, dtype=dtype)
    u = jnp.exp(imaginary_unit * (jnp.asarray(2, dtype=real_dtype) * jnp.pi / n))
    k = jnp.arange(n, dtype=jnp.int32)
    # H_0=1; all H_j for j<n are mathematically nonzero for primitive u.
    H = jnp.concatenate((one[None], jnp.cumprod(one - u ** k[1:])))
    phase = jnp.where(k % 2 == 0, one, -one) * u ** (k * (k - 1) // 2)
    difference = k[:, None] - k[None, :]
    # Use H_0 above the diagonal so masked cells never introduce a zero
    # denominator. The actual lower-triangular entries use H_(i-k).
    ratios = H[:, None] / H[jnp.maximum(difference, 0)]
    N = jnp.where(difference >= 0, ratios * phase[None, :], jnp.zeros((), dtype=dtype))
    return N, jnp.diag(N)


def newton_factors(n, dtype="complex64", *, max_n=64):
    """Return JAX arrays ``(N, diagonal)`` for inspecting the Newton factors.

    ``N[i,k] = (-1)**k * u**(k*(k-1)/2) * H[i]/H[i-k]`` for i>=k,
    and zero otherwise. ``diagonal`` contains N's diagonal entries.
    Supported dtypes are complex64 and complex128. An explicit ``max_n``
    overrides the default dense-size guard; no numerical stability is implied.
    """
    n = _bounded_length(n, max_n)
    jax, jnp = _jax()
    dtype = jnp.dtype(dtype)
    if dtype not in (jnp.dtype("complex64"), jnp.dtype("complex128")):
        raise TypeError("Newton factors require complex64 or complex128 dtype")
    if dtype == jnp.dtype("complex128") and not jax.config.jax_enable_x64:
        raise ValueError("complex128 Newton factors require jax_enable_x64")
    return _factors(jnp, n, dtype)


def compile_newton(n, *, max_n=64):
    """Return a jitted dense Newton positive, unnormalized DFT experiment.

    Accepts one vector of length n. Real32/64 are promoted to complex64/128;
    complex precision is retained subject to the caller's JAX x64 setting.
    Computes ``N @ ((N.T @ x) / diagonal)`` using JAX arithmetic and no FFT.
    This O(n^2) experiment exposes finite-precision instability, especially
    beyond small lengths; it is not a fast implementation of either paper.
    """
    n = _bounded_length(n, max_n)
    jax, jnp = _jax()

    def transform(x):
        x = _vector(jnp, x, n)
        N, diagonal = _factors(jnp, n, x.dtype)
        return N @ ((N.T @ x) / diagonal)

    return jax.jit(transform)
