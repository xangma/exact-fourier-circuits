import UniformAxisCacheInputs
import UniformAxisCacheHorizon
import UniformLocalRectangleWorkspaceHeaders
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePreparationInputs
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheTimingExecution (Ready)
open UniformTensorMonomialMachine (setPC)

/-- Subsequent axes need original data and coefficient pools, plus the real
reused workspace bank. The startup-only seed loop header is unnecessary. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (p:Program)(base after:ℕ)
 (prepareCode:CodeAt UniformAxisCacheTimingProgram.program p base after)
 (horizonCode:UniformTensorMonomialMachine.BlockAt UniformGlobalClockHorizon.block p after)
 (codeBound:base+370≤A.envelope c n)(horizonRoom:after+7≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(selected:Selected c n j.val s)(input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=base)(wb:WordBound (A.envelope c n) s):
 ∃ta t u,BoundedRuns p n x (A.envelope c n) s
  (4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7) u∧u.pc=after+7∧
 ta≤(2*Seed.radix n j+1)*UniformLocalCacheTreeExecution.nodeBudget (Seed.radix n j)+18∧
 t≤UniformLocalCacheTimingExecution.printerBudget (Seed.radix n j) 0
  (UniformJointCacheAllocation.axis c n j).requests∧
 Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Selected c n j.val u∧Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=max (s.natReg 5921)
  (2*UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan (Seed.radix n j))+5)∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀q,q<natAt c n j.val→u.natHeap q=s.natHeap q)∧
 (∀q,¬UniformAxisCacheTimingProgram.changed q→q≠5921→(q<5934∨5937≤q)→u.natReg q=s.natReg q):=by
 let start:=setPC s 0
 have bw:WordBound (A.envelope c n) start:=⟨by simp [start,setPC],wb.2⟩
 obtain ⟨ta,t,b,prepare,treeCost,timingCost,ready,out,scalars,heap,regs⟩:=
  UniformAxisCacheSelectedPreparation.execution c n hn j x start selected.withPC rfl bw
 have retained:Inputs n x b:=transport c n j.val hn x start b input.withPC scalars heap
  (fun q lo hi=>regs q (by unfold UniformAxisCacheTimingProgram.changed;omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed prepareCode
  (by rw [UniformAxisCacheTimingProgram.program_length];exact codeBound) (by omega) prepare
 have entry:placed base start=s:=by
  change {s with pc:=base}=s
  rw [←pc]
 rw [entry] at placedRun
 let a:=setPC b after
 have ar:Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) a:=
  UniformAxisCacheHorizon.ready_transport ready rfl (fun _ _=>rfl)
 obtain ⟨horizon,value,hheap,hscalars,hsregs,houtputs,hroots,hregs⟩:=
  UniformGlobalClockHorizon.execution p x a _ (UniformAxisCacheRootDuration.root_duration ar)
   (UniformAxisCacheHorizonBounds.selected_horizon_fits c n hn j) horizonCode rfl horizonRoom placedRun.final_bound
 let u:=UniformTensorMonomialMachine.applyBlock UniformGlobalClockHorizon.block a
 have unchanged:∀q,q<5921∨5937≤q→u.natReg q=a.natReg q:=
  fun q hq=>hregs q (by omega) (by omega)
 have finalInput:Inputs n x u:=transport c n j.val hn x a u retained.withPC
  ⟨hscalars,hsregs,houtputs,hroots⟩ (fun q _=>congrFun hheap q)
  (fun q lo hi=>unchanged q (Or.inl (by omega)))
 have prior:a.natReg 5921=s.natReg 5921:=
  regs 5921 (by unfold UniformAxisCacheTimingProgram.changed;omega)
 refine ⟨ta,t,u,placedRun.trans horizon,?_,treeCost,timingCost,
  UniformAxisCacheHorizon.ready_transport ar hheap unchanged,
  UniformAxisCacheHorizon.selected_transport out.withPC unchanged,finalInput,?_,?_,?_,?_,?_⟩
 · rw [UniformTensorMonomialMachine.applyBlock_pc,UniformGlobalClockHorizon.block_length]
   rfl
 · intro f
   have hf:=f.isLt
   exact (unchanged _ (Or.inr (by omega))).trans
    ((regs _ (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans (bank f))
 · rw [prior] at value
   exact value
 · exact ⟨hscalars.trans scalars.scalarHeap,hsregs.trans scalars.scalarReg,
   houtputs.trans scalars.outputs,hroots.trans scalars.rootOrders⟩
 · intro q hq
   exact (congrFun hheap q).trans (heap q hq)
 · intro q hp ne outside
   exact (hregs q ne outside).trans (regs q hp)

end ExactFourierCircuits.UniformAxisCachePreparationInputs
