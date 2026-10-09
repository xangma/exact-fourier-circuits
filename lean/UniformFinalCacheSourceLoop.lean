import UniformAxisCacheWholeLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCacheSourceLoop
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheLoopState UniformAxisCacheWholeLoop
noncomputable section
/-- The unchanged actual all-axis loop retains its physically installed source
pointer. The terminal actual axis returns the genuine startup Control. -/
theorem remaining_source (c:A.Constants) (n:ℕ) (hn:0<n) (x:Fin n→ ℂ) (fuel j:ℕ)
 (last:j+fuel+1=C.ell n) (s:State)
 (selected:Selected c n j s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s) (all:All c n hn j s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks≤ (fuel+1)*maxBudget c n+1∧u.pc=4653∧Final c n hn x s u∧u.natReg 6904=Seed.directoryBase n:=by
 induction fuel generalizing j s with
 | zero=>
   let index:Fin (C.ell n):=⟨j,by omega⟩
   have lastIndex:index.val+1=C.ell n:=by simpa only [index,Nat.add_zero] using last
   obtain ⟨u,ticks,run,cost,up,out⟩:=axis_tail c n hn index x s selected input bank all clock pc wb
   have noMore:¬index.val+1<C.ell n:=by omega
   have haltPC:u.pc=4653:=by simpa only [ite_eq_right noMore] using up
   have halted:BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) u 1 u:=
    .halt run.final_bound (by rw [step,haltPC,UniformAxisCacheWholeProgram.halt_at])
   have source:=out.control.source
   have ends:=UniformAxisCacheFinalEnds.registers c n index lastIndex u out.allocation
   refine ⟨u,ticks+1,run.executes halted,?_,haltPC,⟨out.input,out.bank,?_,?_,
    out.savedNat,out.savedScalar,ends.1,ends.2,out.outputs,out.roots⟩,source⟩
   · simp only [Nat.zero_add,Nat.one_mul]
     omega
   · simpa only [lastIndex] using out.all
   · rw [out.clock,lastIndex]
     exact UniformFourierClockBounds.prefix_eq_horizon n
 | succ fuel ih=>
   let index:Fin (C.ell n):=⟨j,by omega⟩
   have more:index.val+1<C.ell n:=by dsimp [index];omega
   obtain ⟨a,ta,first,cost,ap,out⟩:=axis_tail c n hn index x s selected input bank all clock pc wb
   have advancePC:a.pc=4644:=by simpa only [ite_eq_left more] using ap
   have fit:=UniformAxisCacheWholePrefix.code_fits c n
   obtain ⟨b,advance,bp,selectedB,inputB,bankB,clockB,savedNat,savedScalar,frame⟩:=
    UniformAxisCacheAdvanceInputs.execution c n hn index more UniformAxisCacheWholeProgram.program
     4644 20 UniformAxisCacheWholeProgram.advanceCode_at (by omega) (by omega) x a
     out.control out.input out.allocation out.bank advancePC first.final_bound
   have nextAll:All c n hn (j+1) b:=out.all.transport frame.natHeap frame.scalarHeap
   obtain ⟨u,ticks,lastRun,bound,up,final,source⟩:=ih (j+1) (by omega) b selectedB inputB bankB nextAll
    (clockB.trans out.clock) bp advance.final_bound
   refine ⟨u,ta+9+ticks,(first.trans advance).executes lastRun,?_,up,Final.rebase final
    (savedNat.trans out.savedNat) (savedScalar.trans out.savedScalar)
    (frame.outputs.trans out.outputs) (frame.roots.trans out.roots),source⟩
   · have arithmetic:(fuel+1+1)*maxBudget c n=(fuel+1)*maxBudget c n+maxBudget c n:=by rw [Nat.add_mul,Nat.one_mul]
     rw [arithmetic]
     omega

end
end ExactFourierCircuits.UniformFinalCacheSourceLoop
