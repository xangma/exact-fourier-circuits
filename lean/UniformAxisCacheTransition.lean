import UniformAxisCachePreparationRetention
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTransition
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCachePreparationRetention
open UniformTensorMonomialMachine (setPC)

lemma result_withPC {r N S pc:ℕ}{s:State}
 (h:UniformAxisCacheAllocationMachine.Result r N S s):
 UniformAxisCacheAllocationMachine.Result r N S (setPC s pc):=by
 cases h
 constructor <;>assumption

/-- The actual nine-instruction transition loads the next radix and advances
both allocated frontiers. Its placement is independent of consumer lengths. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (more:j.val+1<C.ell n)(p:Program)(base finish:ℕ)
 (code:CodeAt UniformAxisCacheAdvanceMachine.program p base finish)
 (codeBound:base+9≤A.envelope c n)(finishBound:finish≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(control:Control n j.val s)(core:Core n x s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) s)
 (pc:s.pc=base)(wb:WordBound (A.envelope c n) s):
 ∃u,BoundedRuns p n x (A.envelope c n) s 9 u∧u.pc=finish∧
 Selected c n (j.val+1) u∧Core n x u∧Frame s u:=by
 let start:=setPC s 0
 have bw:WordBound (A.envelope c n) start:=⟨by simp [start,setPC],wb.2⟩
 obtain ⟨a,run,ap,out,frontiers,radix,source,index,frame⟩:=
  UniformAxisCacheAdvanceMachine.execution c n hn j more x start
   (show Control n j.val start from
    ⟨control.zero,control.one,control.two,control.nine,control.source,control.count,control.index⟩)
   (result_withPC result) core.seed.withPC rfl bw
 have selected:Selected c n (j.val+1) a:=
  ⟨out,frontiers,radix.trans (UniformAllAxisSeedPreparation.radixAt_eq n ⟨j.val+1,more⟩).symm,
   source,index⟩
 have retained:Core n x a:=transport c n j.val hn x start a core.withPC
  ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
  (fun q _=>congrFun frame.natHeap q)
  (fun q hq=>frame.natReg q (by
   simp only [UniformAxisCacheStartupMachine.changed,List.mem_cons,List.not_mem_nil,or_false]
   omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed code
  (by rw [UniformAxisCacheAdvanceMachine.program_length];exact codeBound) finishBound run
 have entry:placed base start=s:=by
  cases s
  simp only [start,placed,setPC] at pc ⊢
  simp only [Nat.add_zero,pc]
 rw [entry] at placedRun
 refine ⟨setPC a finish,?_,rfl,selected.withPC,retained.withPC,?_,?_,?_,?_,?_,?_⟩
 · simpa only [placed,setPC] using placedRun
 · exact frame.natHeap
 · exact frame.scalarHeap
 · exact frame.scalarReg
 · exact frame.outputs
 · exact frame.roots
 · exact frame.natReg

end ExactFourierCircuits.UniformAxisCacheTransition
