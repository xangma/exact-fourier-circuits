import UniformAxisCachePreparationInputs
import UniformFourierClockBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheClockPreparation
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheTimingExecution (Ready)

/-- The executed maximum update is exactly the next prefix maximum over the
actual selected Fourier schedules. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (p:Program)(base after:ℕ)
 (prepareCode:CodeAt UniformAxisCacheTimingProgram.program p base after)
 (horizonCode:UniformTensorMonomialMachine.BlockAt UniformGlobalClockHorizon.block p after)
 (codeBound:base+370≤A.envelope c n)(horizonRoom:after+7≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(selected:Selected c n j.val s)(input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=base)(wb:WordBound (A.envelope c n) s):
 ∃ta t u,BoundedRuns p n x (A.envelope c n) s
  (4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7) u∧u.pc=after+7∧
 ta≤(2*Seed.radix n j+1)*UniformLocalCacheTreeExecution.nodeBudget (Seed.radix n j)+18∧
 t≤UniformLocalCacheTimingExecution.printerBudget (Seed.radix n j) 0
  (UniformJointCacheAllocation.axis c n j).requests∧
 Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Selected c n j.val u∧Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=UniformFourierClockBounds.clockPrefix n (j.val+1)∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀q,q<natAt c n j.val→u.natHeap q=s.natHeap q)∧
 (∀q,¬UniformAxisCacheTimingProgram.changed q→q≠5921→(q<5934∨5937≤q)→u.natReg q=s.natReg q):=by
 obtain ⟨ta,t,u,run,up,treeCost,timingCost,ready,out,finalInput,finalBank,value,scalars,heap,regs⟩:=
  UniformAxisCachePreparationInputs.execution c n hn j p base after prepareCode horizonCode
   codeBound horizonRoom x s selected input bank pc wb
 refine ⟨ta,t,u,run,up,treeCost,timingCost,ready,out,finalInput,finalBank,?_,scalars,heap,regs⟩
 rw [value,clock,UniformFourierClockBounds.prefix_step n j.val j.isLt]
 rfl

end ExactFourierCircuits.UniformAxisCacheClockPreparation
