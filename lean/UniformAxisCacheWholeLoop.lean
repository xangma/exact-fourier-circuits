import UniformAxisCacheLoopState
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheWholeLoop
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheLoopState
noncomputable section

structure Completed (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (x:Fin n→ ℂ) (s u:State):Prop where
 input:Inputs n x u
 control:Control n j.val u
 allocation:UniformAxisCacheAllocationMachine.Result (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u
 bank:UniformLocalRectangleWorkspaceHeaders.Bank n u
 all:All c n hn (j.val+1) u
 clock:u.natReg 5921=UniformFourierClockBounds.clockPrefix n (j.val+1)
 savedNat:u.natReg 6909=s.natReg 6909
 savedScalar:u.natReg 6910=s.natReg 6910
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma axis_tail (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (x:Fin n→ ℂ) (s:State)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s) (all:All c n hn j.val s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedRuns UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks+9≤ maxBudget c n∧u.pc=(if j.val+1<C.ell n then 4644 else 4653)∧
 Completed c n hn j x s u:=by
 have fit:=UniformAxisCacheWholePrefix.code_fits c n
 obtain ⟨a,ta,first,cost,ap,out⟩:=UniformAxisCacheAxisExecution.execution c n hn j x s
  selected input bank clock pc wb
 obtain ⟨u,last,up,_,control,nh,sh,sr,outputs,roots,regs⟩:=UniformAxisCacheTail.execution n j.val
  (A.envelope c n) 4642 UniformAxisCacheWholeProgram.program UniformAxisCacheWholeProgram.tailCode_at
  x a out.control j.isLt (by omega) ap first.final_bound
 refine ⟨u,ta+2,first.trans last,?_,up,?_⟩
 · have bound:=budget_le c n j
   omega
 · refine ⟨?_,control,?_,?_,(All.step all out).transport nh sh,
    (regs _ (by omega)).trans out.clock,(regs _ (by omega)).trans out.savedNat,
    (regs _ (by omega)).trans out.savedScalar,outputs.trans out.outputs,roots.trans out.roots⟩
   · exact UniformAxisCacheInputs.transport c n j.val hn x a u out.input
      ⟨sh,sr,outputs,roots⟩ (fun q _=>congrFun nh q) (fun q lo hi=>regs q (by omega))
   · exact allocation_transport out.allocation (fun q lo hi=>regs q (by omega))
   · intro i
     have hi:=i.isLt
     exact (regs _ (by omega)).trans (out.bank i)

lemma Final.rebase {c n hn x s a u} (h:Final c n hn x a u)
 (savedNat:a.natReg 6909=s.natReg 6909) (savedScalar:a.natReg 6910=s.natReg 6910)
 (outputs:a.outputs=s.outputs) (roots:a.rootOrders=s.rootOrders):Final c n hn x s u:=
 ⟨h.input,h.bank,h.all,h.clock,h.savedNat.trans savedNat,h.savedScalar.trans savedScalar,
 h.natEnd,h.scalarEnd,h.outputs.trans outputs,h.roots.trans roots⟩

/-- The actual branch and nine-step selector repeat the complete producer for
all remaining axes, then execute the final halt. -/
theorem remaining (c:A.Constants) (n:ℕ) (hn:0<n) (x:Fin n→ ℂ) (fuel j:ℕ)
 (last:j+fuel+1=C.ell n) (s:State)
 (selected:Selected c n j s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s) (all:All c n hn j s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks≤ (fuel+1)*maxBudget c n+1∧u.pc=4653∧Final c n hn x s u:=by
 induction fuel generalizing j s with
 | zero=>
   let index:Fin (C.ell n):=⟨j,by omega⟩
   have lastIndex:index.val+1=C.ell n:=by simpa only [index,Nat.add_zero] using last
   obtain ⟨u,ticks,run,cost,up,out⟩:=axis_tail c n hn index x s selected input bank all clock pc wb
   have noMore:¬index.val+1<C.ell n:=by omega
   have haltPC:u.pc=4653:=by simpa only [ite_eq_right noMore] using up
   have halted:BoundedExecution UniformAxisCacheWholeProgram.program n x (A.envelope c n) u 1 u:=
    .halt run.final_bound (by rw [step,haltPC,UniformAxisCacheWholeProgram.halt_at])
   have ends:=UniformAxisCacheFinalEnds.registers c n index lastIndex u out.allocation
   refine ⟨u,ticks+1,run.executes halted,?_,haltPC,out.input,out.bank,?_,?_,
    out.savedNat,out.savedScalar,ends.1,ends.2,out.outputs,out.roots⟩
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
   obtain ⟨u,ticks,lastRun,bound,up,final⟩:=ih (j+1) (by omega) b selectedB inputB bankB nextAll
    (clockB.trans out.clock) bp advance.final_bound
   refine ⟨u,ta+9+ticks,(first.trans advance).executes lastRun,?_,up,Final.rebase final
    (savedNat.trans out.savedNat) (savedScalar.trans out.savedScalar)
    (frame.outputs.trans out.outputs) (frame.roots.trans out.roots)⟩
   · have arithmetic:(fuel+1+1)*maxBudget c n=(fuel+1)*maxBudget c n+maxBudget c n:=by rw [Nat.add_mul,Nat.one_mul]
     rw [arithmetic]
     omega

end
end ExactFourierCircuits.UniformAxisCacheWholeLoop
