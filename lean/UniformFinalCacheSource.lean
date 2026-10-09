import UniformFinalCacheSourceLoop
import UniformCacheLowProtected
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCacheSource
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheLoopState UniformAxisCachePreparationRetention
noncomputable section
/-- Any genuine execution of the unchanged4654 controller produces6904 from
the actual seed Header. The boot and every remaining axis execute and are charged. -/
theorem execution_source (c:A.Constants) (n:ℕ) (hn:0<n) (x:Fin n→ℂ) (s u:State) (ticks:ℕ)
 (core:Core n x s) (slab:s.natReg 6020=A.slab c n)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=0) (wb:WordBound (A.envelope c n) s)
 (run:BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u):
 u.natReg 6904=Seed.directoryBase n:=by
 have fit:=UniformAxisCacheWholePrefix.code_fits c n
 obtain ⟨a,boot,ap,selected,input,bankA,clock,_,_,_,_,_,_,_⟩:=
  UniformAxisCacheBootInputs.execution c n hn UniformAxisCacheWholeProgram.program 0
   UniformAxisCacheWholeProgram.resetCode_at UniformAxisCacheWholeProgram.startupCode_at
   UniformAxisCacheWholeProgram.saveCode_at (by omega) x s core slab bank pc wb
 have positive:0<C.ell n:=by change 0<UniformWorkingLength.axisCount n+1;omega
 have relation:0+(C.ell n-1)+1=C.ell n:=by omega
 have empty:All c n hn 0 a:=by intro i hi;omega
 obtain ⟨v,t,tail,_,_,_,source⟩:=UniformFinalCacheSourceLoop.remaining_source c n hn x (C.ell n-1) 0
  relation a selected input bankA empty clock ap boot.final_bound
 have actual:=boot.executes tail
 have same:=(actual.executes.deterministic run.executes).2
 subst u
 exact source
end
end ExactFourierCircuits.UniformFinalCacheSource
