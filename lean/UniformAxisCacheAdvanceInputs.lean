import UniformAxisCacheInputs
import UniformLocalRectangleWorkspaceHeaders
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAdvanceInputs
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformTensorMonomialMachine (setPC)

theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (more:j.val+1<C.ell n)(p:Program)(base finish:ℕ)
 (code:CodeAt UniformAxisCacheAdvanceMachine.program p base finish)
 (codeBound:base+9≤A.envelope c n)(finishBound:finish≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(control:Control n j.val s)(input:Inputs n x s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=base)(wb:WordBound (A.envelope c n) s):
 ∃u,BoundedRuns p n x (A.envelope c n) s 9 u∧u.pc=finish∧
 Selected c n (j.val+1) u∧Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=s.natReg 5921∧u.natReg 6909=s.natReg 6909∧u.natReg 6910=s.natReg 6910∧
 Frame s u:=by
 let start:=setPC s 0
 have bw:WordBound (A.envelope c n) start:=⟨by simp [start,setPC],wb.2⟩
 obtain ⟨a,run,ap,out,frontiers,radix,source,index,frame⟩:=
  UniformAxisCacheAdvanceMachine.execution c n hn j more x start
   (show Control n j.val start from
    ⟨control.zero,control.one,control.two,control.nine,control.source,control.count,control.index⟩)
   (by cases result;constructor <;>assumption) input.original.withPC rfl bw
 have selected:Selected c n (j.val+1) a:=
  ⟨out,frontiers,radix.trans (UniformAllAxisSeedPreparation.radixAt_eq n ⟨j.val+1,more⟩).symm,
   source,index⟩
 have retained:Inputs n x a:=transport c n j.val hn x start a input.withPC
  ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
  (fun q _=>congrFun frame.natHeap q)
  (fun q lo hi=>frame.natReg q (by
   simp only [UniformAxisCacheStartupMachine.changed,List.mem_cons,List.not_mem_nil,or_false]
   omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed code
  (by rw [UniformAxisCacheAdvanceMachine.program_length];exact codeBound) finishBound run
 have entry:placed base start=s:=by
  change {s with pc:=base}=s
  rw [←pc]
 rw [entry] at placedRun
 refine ⟨setPC a finish,?_,rfl,selected.withPC,retained.withPC,?_,?_,?_,?_,
  frame.natHeap,frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots,frame.natReg⟩
 · simpa only [placed,setPC] using placedRun
 · intro f
   have hf:=f.isLt
   exact (frame.natReg _ (by
    simp only [UniformAxisCacheStartupMachine.changed,List.mem_cons,List.not_mem_nil,or_false]
    omega)).trans (bank f)
 · exact frame.natReg _ (by decide)
 · exact frame.natReg _ (by decide)
 · exact frame.natReg _ (by decide)

end ExactFourierCircuits.UniformAxisCacheAdvanceInputs
