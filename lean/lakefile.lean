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

lean_lib UniformMachine

lean_lib UniformExponent

lean_lib UniformRoots

lean_lib UniformLocalShear

lean_lib UniformBatching

lean_lib UniformChirp

lean_lib UniformScalarPreparation

lean_lib UniformTraversal

lean_lib UniformWorkingLength

lean_lib UniformAsymptotics

lean_lib UniformCyclic

lean_lib UniformDiagonal

lean_lib UniformMachineRuns

lean_lib UniformCRT

lean_lib UniformTraversalMachine

lean_lib UniformSelectedCRT

lean_lib UniformDirectMachine

lean_lib UniformWorkingPreparation

lean_lib UniformPowerMachine

lean_lib UniformNewton

lean_lib UniformDirectBounds

lean_lib UniformNetworkCost

lean_lib UniformPreparationMachine

lean_lib UniformIntegerScalarMachine

lean_lib UniformCRTMachine

lean_lib UniformLinearMachine

lean_lib UniformSectorPacking

lean_lib UniformRadixTwoDAG

lean_lib UniformAssembly

lean_lib UniformDAGLowering

lean_lib UniformAssembledDirect

lean_lib UniformReplayPrint

lean_lib UniformPrimeMachine
lean_lib UniformRadixTwoMachine

lean_lib UniformWorkingMachine

lean_lib UniformColoring

lean_lib UniformDFSProgram

lean_lib UniformWorkingCompletion

lean_lib UniformLayeredReplay

lean_lib UniformContext

lean_lib UniformInPlaceMachine

lean_lib UniformConvolutionDAG

lean_lib UniformMasterRootMachine

lean_lib UniformPairMachine

lean_lib UniformFixedNetwork

lean_lib UniformReciprocalPreparation

lean_lib UniformCKernelPreparation
