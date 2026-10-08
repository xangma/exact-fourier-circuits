# Paper playground

Open [paper-playground.ipynb](paper-playground.ipynb) in Jupyter using a Python 3.10+ kernel with JAX/jaxlib and NumPy. From the checkout:

```sh
uv pip install --python .venv/bin/python -e '.[jax,research,notebook]'
.venv/bin/python -m jupyterlab notebooks/paper-playground.ipynb
```

Edit the first code cell and run all cells. Defaults use CPU, complex128, a 32-point classical DFT and an 8-point dense Newton identity. To use CUDA, set `DEVICE="gpu"` in a fresh kernel with a compatible GPU JAX installation. Matplotlib and ipywidgets are optional; nothing is installed automatically. Set `REPO_HINT` if the notebook is launched outside this checkout.

Controls include the symbolic `H`/`COLUMNS` budget, shear target amplitude, C tensor exponent, classical DFT length and dense Newton length. The optional complete projected toy network is disabled by default; enable `RUN_FULL_PROJECTED` and choose one or four projected address bits. It compares with the same operator's independent Walsh-phase target.

The notebook separates the original Lean-verified exact result from numerical experiments. The astronomical saving seed stays symbolic. The companion's dense local factorization is an identity experiment; its full uniform fast algorithm remains unproved here. Neither construction has a practical FFT speedup claim. Saved notebook outputs are empty; recorded CPU/CUDA receipts are read from `verification/jax-replication/`.
