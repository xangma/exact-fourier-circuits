import UniformActualGlobalConstants
import UniformJointKernelDiagonalLinks
import UniformGlobalClockTickExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualGlobalTickContext
open UniformMachine UniformAssembly UniformKernelDiagonalBanks UniformSectorPackingMachine
open UniformActualGlobalConstants (constants roles_positive reserve_le)
noncomputable section
attribute [local irreducible] Nat.add Nat.mul

/-- Geometry of the genuine per-axis printed banks. Contents are supplied
separately by actual producer executions. -/
structure Geometry (n:ℕ) where
 entries:List UniformGlobalDiagonalRowsMachine.Entry
 selected:entries.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n)
 poolFit:∀a∈entries,a.pool+9*a.radix ≤ 2*UniformJointAllocation.slab constants n
 physical:List PhysicalAxis
 placement:UniformJointDiagonalContext.PhysicalPlacement constants n physical

def kernel {n:ℕ} (hn:0 < n) (a:Geometry n):
 Kernel (W:=UniformRecursiveSelfCallMachine.W)
  (F:=12*UniformJointAllocation.slab constants n) (R:=UniformRecursiveReserve.reserve):=
 UniformJointConditionalKernelContext.context constants n hn roles_positive
  UniformRecursiveReserve.reserve reserve_le a.physical a.placement.shape

def diagonal {n:ℕ} (hn:0 < n) (a:Geometry n):Diagonal UniformRecursiveSelfCallMachine.W:=
 UniformJointDiagonalContext.context constants n hn roles_positive a.entries a.selected a.poolFit a.physical a.placement

def links {n:ℕ} (hn:0 < n) (a:Geometry n):Links (kernel hn a) (diagonal hn a):=
 UniformJointDiagonalContext.links constants n hn roles_positive a.entries a.selected a.poolFit
  a.physical a.placement UniformRecursiveReserve.reserve reserve_le

lemma kernel_bound {n:ℕ} (hn:0 < n) (a:Geometry n):
 (kernel hn a).metadata.B=UniformJointAllocation.envelope constants n:=rfl
lemma source_link {n:ℕ} (hn:0 < n) (a:Geometry n):
 (kernel hn a).packing.source=(diagonal hn a).tensor.source:=rfl

/-- This specialization has no free kernel Context, shared Links, recursive
reserve, role positivity, or recursive numerical execution premise. -/
theorem execution {n:ℕ} (hn:0 < n) (a:Geometry n) (prepare:Program)
 (v:ℕ→Fin (kernel hn a).packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (input:UniformKernelHeaderInstallation.Input (kernel hn a) s)
 (diagonalInput:UniformDiagonalHeaderInstallation.Input (diagonal hn a).rows (diagonal hn a).tensor s)
 (banks:UniformGlobalRolePackingMachine.Banks (kernel hn a).packing a.physical s)
 (source:UniformGlobalRolePackingMachine.Source (kernel hn a).packing v s)
 (directory:UniformGlobalDiagonalRowsMachine.Directory (diagonal hn a).rows.directory a.entries 0 s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools a.entries s)
 (constantsReady:UniformBinaryCStageMachine.Constants s)
 (code:(UniformGlobalClockConductor.programFor prepare UniformRecursiveSavingProgram.program
  UniformRecursiveSelfCallMachine.W).length ≤ (kernel hn a).metadata.B)
 (pc:s.pc=0) (wb:WordBound (kernel hn a).metadata.B s)
 (one:s.natReg 5939=1) (unfinished:s.natReg 5920 < s.natReg 5921):
 ∃u ticks,BoundedRuns
  (UniformGlobalClockConductor.programFor prepare UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  n x (kernel hn a).metadata.B (placed (UniformGlobalClockConductor.kernelBase prepare) s) ticks u ∧
 ticks ≤ UniformGlobalKernelDiagonalRetention.budget (kernel hn a) (diagonal hn a) UniformRecursiveChildInduction.cost+2 ∧u.pc=5 ∧
 u.natReg 5920=s.natReg 5920+1 ∧
 (∀r,r < UniformRecursiveSelfCallMachine.W→∀j:Fin (diagonal hn a).packing.volume,
  (u.scalarHeap ((diagonal hn a).tensor.source+r*(diagonal hn a).tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier (diagonal hn a) j*kernelValue (kernel hn a) (diagonal hn a) (links hn a) v r j)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < (links hn a).natEnd→q < (diagonal hn a).rows.rows→q < (diagonal hn a).rows.permutation→
  q < (diagonal hn a).tensor.natStack→u.natHeap q=s.natHeap q) ∧
 (∀q,q < (links hn a).scalarEnd→q < (diagonal hn a).rows.coefficient→q < (diagonal hn a).tensor.scalarStack→
  q < (diagonal hn a).tensor.source→q < (diagonal hn a).tensor.destination→u.scalarHeap q=s.scalarHeap q) ∧
 (∀j,5920 ≤ j→j < 5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000 ≤ j ∧j < 6200 ∨6300 ≤ j)→u.natReg j=s.natReg j) ∧
 (∀j,100 ≤ j→j < 107→u.natReg j=s.natReg j):=
 UniformGlobalClockTickExecution.execution prepare (kernel hn a) (diagonal hn a) (links hn a) v x s input diagonalInput
  banks source directory pools constantsReady (Nat.le_refl _) UniformRecursiveSelfCallMachine.W_positive code pc wb one unfinished
end
end ExactFourierCircuits.UniformActualGlobalTickContext
