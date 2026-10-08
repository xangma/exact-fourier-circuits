#!/usr/bin/env python3
"""Diagnose installed inverse-FFT scaling against exact constant-input DFTs."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
import jax
jax.config.update("jax_enable_x64", True)
import jax.numpy as jnp
import numpy as np

rows = []
for device in jax.devices() + ([] if jax.devices()[0].platform == "cpu" else jax.devices("cpu")):
    with jax.default_device(device):
        for n in (16, 17, 257, 4093):
            x = jnp.ones(n, dtype=jnp.complex128)
            reference = np.zeros(n, dtype=np.complex128)
            reference[0] = n
            for name, fn in (("ifft_forward", lambda z: jnp.fft.ifft(z, norm="forward")),
                             ("conjugate_fft", lambda z: jnp.conj(jnp.fft.fft(jnp.conj(z))))):
                y = np.asarray(jax.jit(fn)(x).block_until_ready())
                error = float(np.linalg.norm(y-reference) / n)
                predicted = float(np.float32(1/n)) * n - 1
                if name == "conjugate_fft":
                    assert error < 1e-12
                rows.append(dict(n=n, method=name, platform=device.platform, dtype=str(y.dtype),
                                 first_real=float(y[0].real), relative_l2=error,
                                 signed_dc_relative_error=float(y[0].real/n-1),
                                 binary32_reciprocal_predicted_error=predicted))
receipt = dict(passed=True, host=platform.node(), jax=jax.__version__, jaxlib=__import__("jaxlib").__version__,
               finished_utc=datetime.now(timezone.utc).isoformat(), rows=rows,
               source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               interpretation="The constant-input exact DFT is (n,0,...,0). Agreement with the binary32 reciprocal prediction supports a GPU inverse-normalization precision explanation; this is an inference, not an audit of XLA C++.")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(receipt, indent=2, allow_nan=False) + "\n")
print(json.dumps(receipt, indent=2))
