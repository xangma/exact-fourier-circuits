#!/usr/bin/env python3
"""Execute the playground's default code cells without altering saved outputs."""
import argparse
import ast
from contextlib import redirect_stdout, redirect_stderr
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--device", choices=("cpu", "gpu"), default="cpu")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    notebook = root / "notebooks/paper-playground.ipynb"
    original = notebook.read_bytes()
    cells = json.loads(original)["cells"]
    os.environ["MPLBACKEND"] = "Agg"
    os.environ["XLA_PYTHON_CLIENT_PREALLOCATE"] = "false"
    os.chdir(root)
    namespace = {"__name__": "__main__"}
    count = 0
    started = time.perf_counter()
    for i, cell in enumerate(cells):
        if cell["cell_type"] != "code":
            continue
        assert not cell["outputs"] and cell["execution_count"] is None
        source = "".join(cell["source"])
        ast.parse(source, feature_version=(3, 10))
        # Keep stdout a machine-readable receipt; cell output goes to the log.
        with redirect_stdout(sys.stderr), redirect_stderr(sys.stderr):
            exec(compile(source, f"playground cell {i}", "exec"), namespace)
        count += 1
        if count == 1:
            namespace["DEVICE"] = args.device
    assert notebook.read_bytes() == original
    assert namespace["chosen_device"].platform == args.device
    assert not namespace["RUN_FULL_PROJECTED"] and not namespace["ENABLE_WIDGETS"]
    import jax
    report = dict(passed=True, host=platform.node(), pid=os.getpid(),
                  platform=args.device, python=sys.version, jax=jax.__version__,
                  device=str(namespace["chosen_device"]), code_cells_executed=count,
                  seconds=time.perf_counter()-started, saved_outputs_empty=True,
                  notebook_sha256=hashlib.sha256(original).hexdigest(),
                  source_sha256={str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sorted((root/"src/exact_fourier").glob("jax_*.py"))})
    args.output.resolve().parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
