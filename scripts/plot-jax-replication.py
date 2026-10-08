#!/usr/bin/env python3
"""Render measured GPU receipts into standalone scientific figures."""
import argparse
import json
from fractions import Fraction
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    data = {kind: json.loads((args.input_dir / f"{kind}.json").read_text()) for kind in ("fft", "projection", "shear", "newton")}
    if not all(d["passed"] and d["platforms"] == ["gpu"] for d in data.values()):
        raise SystemExit("Require completed GPU receipts for all four suites")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "savefig.dpi": 180, "figure.constrained_layout.use": True})
    colors = {"jax_fft": "#2672ae", "radix2": "#c27319", "bluestein": "#35915d", "dense_dft": "#9665b4", "legacy_ifft_forward": "#777777"}
    labels = {"jax_fft": "JAX FFT via conjugation", "radix2": "JAX radix-2 butterflies", "bluestein": "JAX Bluestein", "dense_dft": "Dense DFT", "legacy_ifft_forward": "JAX 0.4.20 IFFT diagnostic"}

    def save(fig, name):
        for suffix in ("png", "pdf", "svg"):
            destination = args.output_dir / f"{name}.{suffix}"
            fig.savefig(destination)
            if suffix == "svg":
                destination.write_text("\n".join(line.rstrip() for line in destination.read_text().splitlines())+"\n")
        plt.close(fig)

    fig, axes = plt.subplots(2, 2, figsize=(11, 7), sharex="col")
    for col, dtype in enumerate(("complex64", "complex128")):
        rows = [r for r in data["fft"]["fft"] if r["dtype"] == dtype]
        for method in colors:
            power = sorted((r for r in rows if r["method"] == method and r["n"] & (r["n"] - 1) == 0), key=lambda r: r["n"])
            primes = [r for r in rows if r["method"] == method and r["n"] & (r["n"] - 1) != 0]
            if power:
                median = np.array([r["warm_median_seconds"] * 1e6 for r in power])
                low = np.array([r["warm_min_seconds"] * 1e6 for r in power])
                high = np.array([r["warm_max_seconds"] * 1e6 for r in power])
                axes[0,col].errorbar([r["n"] for r in power], median, yerr=[median-low, high-median], fmt="o-", capsize=2,
                                     linewidth=1, color=colors[method], label=labels[method])
                axes[1,col].loglog([r["n"] for r in power], [max(r["random_error"]["relative_l2"], 1e-17) for r in power], "o-", color=colors[method])
            if primes:
                axes[0,col].scatter([r["n"] for r in primes], [r["warm_median_seconds"] * 1e6 for r in primes], marker="x", s=60, color=colors[method])
                axes[1,col].scatter([r["n"] for r in primes], [max(r["random_error"]["relative_l2"], 1e-17) for r in primes], marker="x", s=60, color=colors[method])
        axes[0,col].set_title(dtype)
        axes[0,col].set_xscale("log")
        axes[0,col].set_yscale("log")
        axes[0,col].legend(fontsize=8)
        axes[1,col].set_xlabel("DFT length n (× marks non-power-of-two lengths)")
        for ax in axes[:,col]:
            ax.grid(alpha=.22, which="both")
    axes[0,0].set_ylabel("Warm synchronized call (µs)")
    axes[1,0].set_ylabel("Relative L2 error vs host complex128 FFT")
    fig.suptitle("Classical positive DFTs on len / RTX 4090\nCompile and transfer costs excluded; shared GPU, not an isolated performance study", fontsize=12)
    save(fig, "jax-fft-comparison")

    fig, axes = plt.subplots(1, 2, figsize=(11, 4))
    methods = ("independent_target", "compiled_three_C", "direct_shear")
    labels2 = ("Independent tensor target", "Network: three-C shears", "Network: direct shears")
    rows = data["projection"]["projection"]
    groups = sorted({(r["bits"], r["dtype"]) for r in rows})
    x = np.arange(len(groups))
    for k, (method, label) in enumerate(zip(methods, labels2)):
        selected = [next(r for r in rows if (r["bits"], r["dtype"]) == group and r["method"] == method) for group in groups]
        for ax, field, factor in ((axes[0], "warm_median_seconds", 1000), (axes[1], "relative_l2", 1)):
            values = [max((r[field] if field in r else r["error"][field]) * factor, 1e-17) for r in selected]
            ax.bar(x+(k-1)*.25, values, width=.25, label=label)
    for ax in axes:
        ax.set_xticks(x, [f"{bits} bits\n{dtype}" for bits, dtype in groups])
        ax.set_yscale("log")
        ax.grid(alpha=.22, axis="y")
    axes[0].set_ylabel("Synchronized call (ms; one warm sample)")
    axes[1].set_ylabel("Relative L2 error vs exact Q(i) target")
    axes[0].legend(fontsize=8)
    fig.suptitle("Same tensor operator, different implementations\n72,842-instruction h=4 projected network; no saving claim; this is not a DFT", fontsize=12)
    save(fig, "jax-projected-network")

    fig, axes = plt.subplots(1, 2, figsize=(11, 4), sharey=True)
    for col, dtype in enumerate(("complex64", "complex128")):
        for compiled, color, name in ((True, "#c34e46", "Literal three-C shear"), (False, "#2672ae", "Direct shear")):
            rows = [r for r in data["shear"]["shear"] if r["dtype"] == dtype and r["compiled"] == compiled]
            axes[col].plot([r["exponent"] for r in rows], [r["source_absolute_error"] for r in rows], color=color, label=name)
        axes[col].set_title(dtype)
        axes[col].set_xlabel("Target exponent k: input (2ᵏ, 1), coefficient t=1")
        axes[col].grid(alpha=.22)
        axes[col].legend(fontsize=8)
    axes[0].set_ylabel("Absolute error in source (exact output = 1)")
    fig.suptitle("A small source can be lost by intermediate rounding\nExact algebra restores it; the executed floating-point word may not", fontsize=12)
    save(fig, "jax-shear-source-loss")

    fig, axes = plt.subplots(1, 2, figsize=(11, 4), sharey=True)
    for col, dtype in enumerate(("complex64", "complex128")):
        for method, color, label in (("newton", "#c34e46", "Dense Newton factorization"),
                                     ("jax_fft", "#2672ae", "JAX FFT via conjugation")):
            rows = [r for r in data["newton"]["newton"] if r["dtype"] == dtype and r["method"] == method]
            axes[col].loglog([r["n"] for r in rows], [max(r["error"]["relative_l2"], 1e-17) for r in rows], "o-", color=color, label=label)
        axes[col].set_title(dtype)
        axes[col].set_xlabel("DFT length n")
        axes[col].set_xticks((2, 4, 8, 16, 32, 64), labels=("2", "4", "8", "16", "32", "64"))
        axes[col].set_xticks([], minor=True)
        axes[col].grid(alpha=.22, which="both")
        axes[col].legend(fontsize=8)
    axes[0].set_ylabel("Relative L2 error vs host complex128 FFT")
    fig.suptitle("Companion's local Newton identity in floating-point arithmetic\nDense factors on len / RTX 4090; this is not the all-length fast compiler", fontsize=12)
    save(fig, "jax-newton-instability")

    counts = json.loads((args.input_dir / "gate-counts.json").read_text())
    saving = [r for r in counts["rows"] if r["saving"]]
    seed = next(r for r in saving if r["h"] == 100)
    fig, axes = plt.subplots(1, 2, figsize=(11, 4))
    axes[0].semilogy([r["h"] for r in saving], [r["b"] for r in saving], "o-", color="#2672ae")
    axes[0].scatter([100], [seed["b"]], color="#c34e46", zorder=4, label="Closed Lean witness")
    axes[0].set_xlabel("Network parameter h")
    axes[0].set_ylabel("Address bits b (number of amplitudes = 2ᵇ)")
    axes[0].legend(fontsize=8)
    offsets = list(range(-3, 13))
    gains = [float(Fraction(seed["Delta"]*(seed["f"]+k)-2*seed["H"],
                           seed["W_star"]*(seed["m"]*(seed["f"]+k)+seed["r"]))) * 1e20 for k in offsets]
    axes[1].plot(offsets, gains, "o-", color="#35915d")
    axes[1].scatter([0], [gains[3]], color="#c34e46", zorder=4)
    axes[1].axhline(0, color="black", linewidth=.7)
    axes[1].axvline(0, color="#c34e46", linestyle=":", linewidth=.8)
    axes[1].set_xlabel("Columns minus checked choice f=6,544,863")
    axes[1].set_ylabel("Saved C-call fraction × 10²⁰")
    for ax in axes:
        ax.grid(alpha=.22)
    fig.suptitle("Why the proved saving does not fit on a GPU\nExact integer-derived C-call counts; other h values are formulas, not separately checked witnesses", fontsize=12)
    save(fig, "exact-saving-scale")
    print(args.output_dir)


if __name__ == "__main__":
    main()
