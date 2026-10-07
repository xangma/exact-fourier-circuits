import Lake
open Lake DSL

package ExactFourierCircuits where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI where
  roots := #[`OAI]
  globs := #[`OAI.+]

lean_lib KernelIdentities

lean_lib ProjectionIdentities

lean_lib ConstructiveBridge

lean_lib SavingBudget

lean_lib BinaryFrames

lean_lib BinaryTensor

lean_lib TypedKernelWords

lean_lib BinaryComplement

lean_lib DirectionalWords

lean_lib ExplicitSeedBudget

lean_lib ScalarNetwork

lean_lib FrameSpectrum

lean_lib TensorWords

lean_lib FrameCommutation

lean_lib TripleNetwork

lean_lib RoleWords

lean_lib FrameWords

lean_lib BinaryResiduals

lean_lib TripleCounting

lean_lib BinaryProjection

lean_lib BinaryColumns

lean_lib NetworkTerminal

lean_lib RoleFrameWords

lean_lib ScalarSupport

lean_lib RectangularWords

lean_lib StageFrames

lean_lib FramedScheduleWords

lean_lib ResidualBudget

lean_lib TensorFusion

lean_lib GateFrames

lean_lib PaddingWords

lean_lib ColumnSchedule

lean_lib TerminalWords

lean_lib TripleInvocationFrames

lean_lib TripleStageAction

lean_lib TripleSchedule

lean_lib TripleColumnAction

lean_lib InvocationBudget

lean_lib MasterBudget

lean_lib ColumnTerminalFlat

lean_lib ExplicitSeed
