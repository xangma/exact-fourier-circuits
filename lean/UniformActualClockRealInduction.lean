import UniformGlobalFiniteClockInduction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockRealInduction
open UniformMachine UniformTensorMonomialMachine
noncomputable section
attribute [local irreducible] UniformActualGlobalClockProgram.program

/-- Internal chronological induction with a uniform real majorant. This keeps
actual counts integral while allowing the certified theta kernel estimate. -/
theorem segments {n B count:ℕ}(x:Fin n→ℂ)(I:ℕ→State→Prop)(cost:ℝ)
 (s:State)(initial:I 0 s)(wb:WordBound B s)
 (advance:∀j,j<count→∀v,I j v→WordBound B v→∃u ticks,
  BoundedRuns UniformActualGlobalClockProgram.program n x B v ticks u ∧
  (ticks:ℝ)≤cost ∧I (j+1) u):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks u ∧
 (ticks:ℝ)≤count*cost ∧I count u:=by
 have prefixes:∀k,k≤count→∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks u ∧
  (ticks:ℝ)≤k*cost ∧I k u:=by
  intro k bound
  induction k with
  | zero=>exact ⟨s,0,.refl wb,by simp,initial⟩
  | succ k ih=>
    obtain ⟨v,t,run,cheap,ready⟩:=ih (by omega)
    obtain ⟨u,dt,next,nextCheap,done⟩:=advance k (by omega) v ready run.final_bound
    refine ⟨u,t+dt,run.trans next,?_,done⟩
    push_cast
    nlinarith only[cheap,nextCheap]
 exact prefixes count (le_refl _)

/-- The real false branch and halt close the finite chronological run. -/
theorem clocks {n B H:ℕ}(x:Fin n→ℂ)(I:ℕ→State→Prop)(cost:ℝ)
 (s:State)(initial:I 0 s)(wb:WordBound B s)
 (code:UniformActualGlobalClockProgram.program.length≤B)
 (headers:∀j v,I j v→v.pc=5 ∧v.natReg 5920=j ∧v.natReg 5921=H)
 (advance:∀j,j<H→∀v,I j v→WordBound B v→∃u ticks,
  BoundedRuns UniformActualGlobalClockProgram.program n x B v ticks u ∧
  (ticks:ℝ)≤cost ∧I (j+1) u):
 ∃u ticks,BoundedExecution UniformActualGlobalClockProgram.program n x B s ticks
  (setPC u (UniformGlobalClockConductor.finalPC UniformFourierAxisPrepareMachine.program
   UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)) ∧
 (ticks:ℝ)≤H*cost+2 ∧I H u:=by
 obtain ⟨u,ticks,run,cheap,ready⟩:=segments x I cost s initial wb advance
 obtain ⟨pc,index,count⟩:=headers H u ready
 have stop:=UniformActualClockBoundaryExecution.halt_execution x u pc (by rw[index,count]) code run.final_bound
 refine ⟨u,ticks+2,run.executes stop,?_,ready⟩
 push_cast
 linarith only[cheap]
end
end ExactFourierCircuits.UniformActualClockRealInduction
