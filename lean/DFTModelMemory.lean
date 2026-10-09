import DFTModelMemoryAffinePointwise

/-! Cost-preserving typed-RAM translations of the actual pointwise17 and kernel-save15
blocks. Affine data carries prepared offsets separately from homogeneous input;
saved prepared kernels retain scalar type. The recursive clocks and complete
DFT compiler remain separate obligations. -/
