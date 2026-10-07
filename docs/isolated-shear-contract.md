# Isolated three-C shear experiment

The exact action is `(y,x) ↦ (y+t*x,x)`. Each generated three-C word is
verified on the full two-dimensional matrix with Gaussian rationals before
CUDA execution. References use exact rational values of the stored floating
point input and output components, including subtraction when measuring error.

Predeclared diagnostic criterion: every output is finite; target component
error is at most `64u * max_j(|y_j|+|t*x_j|)`; source component error is at
most `64u * max_j|x_j|`, where `u` is unit roundoff. Also retain relative
error against the target output for cancellation cases. This is a diagnostic
criterion, not a theorem or a universal stability guarantee.

Compare direct shear, literal compiled shear, common power-of-two input/output
normalization, and diagonal source conditioning (`x'=t*x`, coefficient one,
then `x=x'/t`). The latter two preserve the exact action; neither is assumed
to improve floating point accuracy. Source conditioning's restored source is
checked separately. Cases include balanced values, cancelling outputs, large
targets with small sources, normal inputs near exponent limits, and tiny
nonzero coefficients. The tiny coefficients are generic compiler stress
controls, outside the scalar network's fixed coefficients.

FP32 and FP64, FMA on and off, default round-to-nearest, explicit `--ftz=false`.
The kernel is generated from the same `shear_steps` implementation as the
projected network. All four variants share input bytes and exact references.
No runtime or FFT speedup claim is made.

Execution: len RTX 4090, separate `/tmp/fourier-isolated-shear-20261007-v1`,
180-second worker deadline plus at most ten seconds for cleanup. Arrays are
below 1 MiB. Retain CUDA source, source hashes, raw NPZ arrays, per-case input
and output hexadecimal values, exact target fractions, controller terminal
state, and process exit evidence. Existing GPU services are untouched.
