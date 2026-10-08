# JAX replication evidence

These are observed proof and numerical checks from 2026-10-08. See
[the investigation](../../docs/jax-investigation.md) for interpretation and
[the playground](../../notebooks/paper-playground.ipynb) for editable experiments.

| Evidence | Scope |
| --- | --- |
| `upstream-axioms.txt`, `kernel-axioms.txt` | Original three theorems and five exact kernel identities |
| `lean-construction.json` | 1,101 constructive declaration closures, including the closed saving seed |
| `newton-axioms.txt` | 48 exact local Newton component closures |
| `python-tests.txt` | 98 local Python tests |
| `tests.log`, `newton-tests.log` | 19 plus 6 CUDA tests on len |
| `fft.json` | 82 synchronized classical DFT comparisons |
| `projection-dyadic.json`, `projection.json` | 12 dyadic plus 12 random small projected network comparisons |
| `shear.json` | 244 source-preservation observations |
| `newton.json` | 32 dense Newton/FFT comparisons; larger Newton errors are explicit diagnostics |
| `normalization.json` | Constant-input GPU and CPU controls for the installed JAX inverse normalization |
| `notebook-kernel.json` | Actual default Jupyter kernel execution on CPU |
| `notebook-gpu.json` | Default notebook code cells executed on CUDA, with DEVICE overridden to gpu |
| `gate-counts.json` | Exact integer formulas; only h=100 is the closed Lean witness |

The failed first FFT benchmark is retained in `fft-attempt-1.json` and its log.
The subsequent driver uses conjugated forward FFT as its calibrated positive
DFT baseline. It retains the installed IFFT's accuracy failures as diagnostics;
it does not raise the acceptance tolerance to hide them.

Each benchmark records source hashes. Driver hashes resolve as follows:

- First failure: `benchmark-attempt-1.py`.
- FFT, shear and dyadic projection: `benchmark-dyadic.py`.
- Random projection: `benchmark-random.py`.
- Newton: the current `scripts/benchmark-jax.py`.

`source-manifest.json` identifies the final source snapshot;
`artifact-manifest.json` hashes retained evidence and exported figures.
The CPU agent receipts describe their own earlier snapshots, while the final
notebook checks identify the final notebook directly. PID files are
historical job identifiers, not evidence of currently running processes.

`notebook-attempt-1.log` and `paper-playground-attempt-1.ipynb` retain the
initial CUDA setup failure. JAX 0.4.20 expands the `gpu` platform selector
to CUDA and ROCm; explicit `cuda` succeeds on this build. The final notebook
maps its CUDA device choice accordingly, and its CPU/GPU execution checks
identify the corrected source hash.

Passing required numerical checks does not certify every diagnostic's
accuracy. None of these runs executes the full saving seed, verifies the
Python generator against the Lean word, or completes the stronger uniform
algorithm theorem. The shared GPU timings are exploratory.
