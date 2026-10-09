import UniformCacheLowRectangleExecution
import UniformAxisCacheRectanglePhase
import UniformAxisCacheForestSource
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRectanglePhase
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs UniformAxisCacheForestHeader
open UniformAxisCacheCanonicalRequests UniformAxisCachePhysical
/-- The whole pre-leaf axis phase runs continuously: actual370, horizon7,
header8, and every actual request. Its only semantic entry is original Inputs. -/
theorem execution_low (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (p:Program) (base after finish:ℕ)
 (prepareCode:CodeAt UniformAxisCacheTimingProgram.program p base after)
 (horizonCode:UniformTensorMonomialMachine.BlockAt UniformGlobalClockHorizon.block p after)
 (headerCode:UniformNatBlockMachine.BlockAt UniformAxisCacheForestHeader.ops p (after+7))
 (requestCode:CodeAt Q.program p (after+15) finish)
 (codeBound:base+370≤A.envelope c n) (requestRoom:after+15+3776≤A.envelope c n)
 (finishBound:finish≤A.envelope c n) (x:Fin n→ℂ) (s:State)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=base) (wb:WordBound (A.envelope c n) s):
 ∃ta t tr u,BoundedRuns p n x (A.envelope c n) s
  (4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7+8+tr) u∧u.pc=finish∧
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
 obtain ⟨ta,t,a,first,ap,treeCost,timeCost,ready,out,ai,ab,ac,scalars,heap,regs⟩:=
  UniformAxisCacheClockPreparation.execution c n hn j p base after prepareCode horizonCode
   codeBound (by omega) x s selected input bank clock pc wb
 have second:=UniformAxisCacheForestHeader.execution c n hn j p (after+7) headerCode (by omega)
  x a ready out ai ab ap first.final_bound
 let b:=UniformNatBlockMachine.applyBlock UniformAxisCacheForestHeader.ops a
 have bp:b.pc=after+15:=by have:=second.2.1;omega
 obtain ⟨u,tr,last,requestCost,up,requestReady,ends,requestFrame,control,alloc,prepared,ui,ub,
   uc,un,us,ur,low⟩:=UniformAxisCacheRectangleExecution.execution_low c n hn j p (after+15) finish
    requestCode requestRoom finishBound x b second.2.2.2.1 second.2.2.2.2.1 second.2.2.1
    second.2.2.2.2.2.1 second.2.2.2.2.2.2.1 bp second.1.final_bound
 have source:=UniformAxisCacheForestSource.requests (UniformAxisCacheForestSource.of_ready second.2.2.2.1) requestFrame
 have bn:b.natReg 6909=a.natReg 6909:=UniformAxisCacheForestHeader.registers a _ (by decide)
 have bs:b.natReg 6910=a.natReg 6910:=UniformAxisCacheForestHeader.registers a _ (by decide)
 have bc:b.natReg 5921=a.natReg 5921:=UniformAxisCacheForestHeader.registers a _ (by decide)
 have an:a.natReg 6909=s.natReg 6909:=regs _
  (by unfold UniformAxisCacheTimingProgram.changed;omega) (by omega) (by omega)
 have as_:a.natReg 6910=s.natReg 6910:=regs _
  (by unfold UniformAxisCacheTimingProgram.changed;omega) (by omega) (by omega)
 refine ⟨ta,t,tr,u,?_,up,treeCost,timeCost,requestCost,requestReady,ends,source,prepared,
  control,alloc,ui,ub,uc.trans (bc.trans ac),un.trans (bn.trans an),us.trans (bs.trans as_),
  requestFrame.outputs.trans scalars.outputs,requestFrame.roots.trans scalars.rootOrders,?_,ur,?_⟩
 · have all:=(first.trans second.1).trans last
   simpa only [Nat.add_assoc] using all
 · intro i old
   exact (UniformAxisCachePhysical.preparation c n i j old s a heap scalars.scalarHeap).trans
    ((Heaps.of_eq (show b.natHeap=a.natHeap from rfl) (show b.scalarHeap=a.scalarHeap from rfl)).trans
      (UniformAxisCachePhysical.requests c n i j old b u requestFrame))

 · have lower:UniformCacheLowRetention.z n≤natAt c n j.val:=
    (UniformAxisCachePreparationRetention.slab_above_seed_word c n).trans
     (UniformAxisCachePreparationRetention.frontier_above_slab c n j.val)
   exact ⟨fun a ha=>(low.nat a ha).trans (heap a (ha.trans_le lower)),
    fun a ha=>(low.scalar a ha).trans (congrFun scalars.scalarHeap a)⟩

end ExactFourierCircuits.UniformAxisCacheRectanglePhase
