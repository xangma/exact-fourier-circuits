import UniformCacheLowWholeLoop
import UniformAxisCacheWholeExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheWholeExecution
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheLoopState UniformAxisCacheWholeLoop UniformAxisCachePreparationRetention
noncomputable section

/-- One actual fixed4654-cell controller initializes its clock/frontiers,
prepares every selected axis, and reaches its genuine final halt. -/
theorem execution_low (c:A.Constants) (n:ℕ) (hn:0<n) (x:Fin n→ ℂ) (s:State)
 (core:Core n x s) (slab:s.natReg 6020=A.slab c n)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=0) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks≤ 20+C.ell n*maxBudget c n+1∧u.pc=4653∧Output c n hn x s u ∧ UniformCacheLowRetention.Frame n s u:=by
 have fit:=UniformAxisCacheWholePrefix.code_fits c n
 obtain ⟨a,boot,ap,selected,input,bankA,clock,savedNat,savedScalar,nh,sh,_,outputs,roots⟩:=
  UniformAxisCacheBootInputs.execution c n hn UniformAxisCacheWholeProgram.program 0
   UniformAxisCacheWholeProgram.resetCode_at UniformAxisCacheWholeProgram.startupCode_at
   UniformAxisCacheWholeProgram.saveCode_at (by omega) x s core slab bank pc wb
 have positive:0<C.ell n:=by change 0<UniformWorkingLength.axisCount n+1;omega
 have relation:0+(C.ell n-1)+1=C.ell n:=by omega
 have empty:All c n hn 0 a:=by intro i hi;omega
 obtain ⟨u,ticks,run,cost,up,out,low⟩:=UniformAxisCacheWholeLoop.remaining_low c n hn x (C.ell n-1) 0
  relation a selected input bankA empty clock ap boot.final_bound
 refine ⟨u,20+ticks,boot.executes run,?_,up,?_,?_⟩
 · have eq:C.ell n-1+1=C.ell n:=by omega
   rw [eq] at cost
   omega
 · exact ⟨out.input,out.bank,out.all,out.clock,
    out.savedNat.trans savedNat,out.savedScalar.trans savedScalar,out.natEnd,out.scalarEnd,
    out.outputs.trans outputs,out.roots.trans roots⟩
 · exact ⟨fun a ha=>(low.nat a ha).trans (congrFun nh a),
    fun a ha=>(low.scalar a ha).trans (congrFun sh a)⟩

end
end ExactFourierCircuits.UniformAxisCacheWholeExecution
