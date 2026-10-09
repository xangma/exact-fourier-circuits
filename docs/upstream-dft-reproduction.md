# Reproducing the unchanged upstream DFT theorem

Baseline: OpenAI `math` commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
The verifier recovers the exact Git blobs for `FourierTransform.Main` and its
project import cone into an isolated workspace. It never edits upstream proofs,
configuration, or the existing comparison snapshot.

Run from this repository:

```sh
python3 scripts/verify-upstream-dft.py \
  --upstream-repo /path/to/local/upstream-git-repository \
  --cache-root /path/to/matching/lean-project \
  --output logs/upstream-dft-baseline-fresh
```

The local Git repository must already contain the baseline commit. The script
does not fetch, check out, or mutate it. `--output` must be fresh, preventing
accidental reuse of project `.olean` files.

The cone contains 88 `FourierTransform` modules and the imported
`FourierCircuit.Core` module: 89 freshly compiled modules in total. Only external
dependency caches are reused. Their Git revisions must match the upstream lock
file, including Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`;
Lean is pinned to `v4.34.1`. The isolated `LEAN_PATH` contains the fresh build
directory and these dependency libraries, excluding this project's proof cache.
The command passes `autoImplicit=false`, matching upstream's Lake configuration,
and does not change resource limits.
The recorded compiler is the certified macOS arm64 binary; the driver currently
requires its exact SHA-256. Another platform needs a separate compiler identity
record rather than inheriting this receipt.

After compilation the verifier audits `transform_main`, `transform_main_order`,
`convolution_main`, and `convolution_main_order`. It then audits every declaration
whose defining module belongs to the cone, including generated and private
declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
Source/configuration and compiler SHA-256 maps are checked before and after the
build. All installed external main artifacts and their present server, private,
IR and IR-signature parts are likewise hashed before and after; previously
absent parts must remain absent. Fresh project artifacts are checked again
after the declaration audit. Compiler warnings fail verification. A
comment-aware source check rejects `sorry`, `admit`, `native_decide`, and custom
`axiom` declarations in the recovered cone.

The theorem is an exact positive-sign DFT for every positive input length. Its
`DFTProgram` includes a separate finite integer root-order program, one canonical
root provision, the transform program, validity, polynomial word/storage bounds,
and a combined work allowance. `TimeBounds` includes the paper bound, the decimal
exponent `1 - 10⁻¹³`, and little-o of `n log n`. Convolution uses the model's
explicit multiplication extension. This reproduction checks that upstream result;
it does not establish translation of our separate bytecode into that model.

The current run's detailed evidence is under
`logs/upstream-dft-baseline-v3-20261009/`; the machine-readable final summary is
`verification/upstream-dft-baseline-result.json`. Treat a receipt's `status` as
authoritative: source inspection or a partial build alone is not a successful
reproduction.

The independent run on 2026-10-09 **passed**: all 89 fresh source compilations
completed without warnings or errors; extraction, compilation, artifact checks
and both audits took 390.563 seconds total. All four final theorem closures use
exactly the three permitted axioms. The complete defining-module census contains
4,247 declarations, including 221 private declarations; every closure passed.
All recovered source and configuration hashes matched before and after. The nine
reused external dependency checkouts were also verified clean for tracked files.
No source resource-limit settings were present, and none were added. The run
snapshotted 11,446 external modules and checked all 10,744 actually imported
external modules against that inventory. This is a fresh upstream proof build
using verified dependency caches, not a fresh build of those dependencies.

Receipt SHA-256:
`dcd536f9deaf72d816f527745e3676b1accc4184053ea14c9de2cc65ad2e8ba9`.
The baseline commit was available in the existing comparison snapshot's Git
database; it was absent from the separate `/Users/xangma/repos/math` checkout's
local object database. Recovery used the former directly, without network or Git
mutations. The source manifest records the exact bytes rather than relying on the
snapshot's working files.
