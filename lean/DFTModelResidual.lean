import DFTModelResidualCore
import DFTModelResidualXor
import DFTModelResidualTable
import DFTModelResidualBlockXor
import DFTModelResidualAddresses
import DFTModelResidualAddressProof
import DFTModelResidualMovement

/-!
Bounded upstream typed-RAM residual components. The XOR producer computes its
complete table. Address construction receives that table and a readonly unit-image
tape, and agrees with the source DFS address definition. Generic gather and true
inverse scatter transport complete elements, including both affine channels and
the tag. This module does not assert that the source basis/descriptor producer,
recursive child dispatcher, or complete DFT caller has been compiled.
-/
