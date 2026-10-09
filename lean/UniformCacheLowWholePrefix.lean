import UniformCacheLowRectanglePhase
import UniformAxisCacheWholePrefix
import UniformAxisCacheRectanglePhase
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheWholePrefix
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs UniformAxisCacheForestHeader
open UniformAxisCacheCanonicalRequests UniformAxisCachePhysical
theorem rectangle_axis_low (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (x:Fin n→ℂ) (s:State)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃ta t tr u,BoundedRuns UniformAxisCacheWholeProgram.program n x (A.envelope c n) s
  (4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7+8+tr) u∧u.pc=4181∧
 ta≤(2*Seed.radix n j+1)*UniformLocalCacheTreeExecution.nodeBudget (Seed.radix n j)+18∧
 t≤UniformLocalCacheTimingExecution.printerBudget (Seed.radix n j) 0
  (UniformJointCacheAllocation.axis c n j).requests∧
 tr≤Q.costPrefix n j (canonical c n j) (canonical c n j).length+23∧
 Q.Ready c n j (canonical c n j) (UniformJointCacheAllocation.axis c n j).requests
  (UniformJointCacheAllocation.axis c n j).requestStarts (geometry c n hn j) x (canonical c n j).length u∧
 Q.Endpoints c n j (canonical c n j) (UniformJointCacheAllocation.axis c n j).requests
  (UniformJointCacheAllocation.axis c n j).requestStarts u∧
 UniformAxisCacheForestSource.Source c n j u∧Prepared c n j u∧Control n j.val u∧
 UniformAxisCacheAllocationMachine.Result (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=UniformFourierClockBounds.clockPrefix n (j.val+1)∧
 u.natReg 6909=s.natReg 6909∧u.natReg 6910=s.natReg 6910∧
 u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀i:Fin (C.ell n),i.val<j.val→Heaps c n i s u)∧u.natReg 6800=Seed.radix n j ∧ UniformCacheLowRetention.Frame n s u:=by
 have fit:=code_fits c n
 exact UniformAxisCacheRectanglePhase.execution_low c n hn j UniformAxisCacheWholeProgram.program
  20 390 4181 UniformAxisCacheWholeProgram.prepareCode_at UniformAxisCacheWholeProgram.horizonCode_at
  UniformAxisCacheWholeProgram.headerCode_at UniformAxisCacheWholeProgram.requestCode_at
  (by omega) (by omega) (by omega) x s selected input bank clock pc wb

end ExactFourierCircuits.UniformAxisCacheWholePrefix
