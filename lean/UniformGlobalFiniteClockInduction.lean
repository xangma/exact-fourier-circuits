import UniformActualClockBoundaryExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalFiniteClockInduction
open UniformMachine
open UniformTensorMonomialMachine (setPC)
open scoped BigOperators
noncomputable section
attribute [local irreducible] Nat.add UniformActualGlobalClockProgram.program

/-- Internal finite induction over genuine bounded segments of the one fixed
program. The step motive must be discharged by the actual preparation/consumer
proof; it is not a replacement instruction or a final algorithm witness. -/
theorem segments {n B count:ℕ} (x:Fin n→ℂ) (I:ℕ→State→Prop) (cost:ℕ→ℕ)
 (s:State) (initial:I 0 s) (wb:WordBound B s)
 (advance:∀j,j<count→∀v,I j v→WordBound B v→∃u ticks,
  BoundedRuns UniformActualGlobalClockProgram.program n x B v ticks u ∧ticks≤cost j ∧I (j+1) u):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks u ∧
 ticks≤∑j∈Finset.range count,cost j ∧I count u:=by
 have completedPrefix:∀k,k≤count→∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks u ∧
  ticks≤∑j∈Finset.range k,cost j ∧I k u:=by
  intro k bound
  induction k with
  | zero=>exact ⟨s,0,.refl wb,by simp,initial⟩
  | succ k ih=>
    obtain ⟨v,t,run,cheap,ready⟩:=ih (by omega)
    obtain ⟨u,dt,next,nextCheap,done⟩:=advance k (by omega) v ready run.final_bound
    refine ⟨u,t+dt,run.trans next,?_,done⟩
    rw[Finset.sum_range_succ]
    exact Nat.add_le_add cheap nextCheap
 exact completedPrefix count (le_refl _)

/-- The concrete all-axis terminal branch is charged after the internal finite
axis induction. Every segment still runs the actual fixed clock program. -/
theorem axes {n B ell:ℕ} (x:Fin n→ℂ) (I:ℕ→State→Prop) (cost:ℕ→ℕ)
 (s:State) (initial:I 0 s) (wb:WordBound B s)
 (code:UniformActualGlobalClockProgram.program.length≤B)
 (headers:∀j v,I j v→v.pc=10 ∧v.natReg 5922=j ∧v.natReg 5938=ell)
 (advance:∀j,j<ell→∀v,I j v→WordBound B v→∃u ticks,
  BoundedRuns UniformActualGlobalClockProgram.program n x B v ticks u ∧ticks≤cost j ∧I (j+1) u):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks (setPC u 756) ∧
 ticks≤(∑j∈Finset.range ell,cost j)+1 ∧I ell u:=by
 obtain ⟨u,ticks,run,cheap,ready⟩:=segments x I cost s initial wb advance
 obtain ⟨pc,index,count⟩:=headers ell u ready
 have branch:=UniformActualClockBoundaryExecution.kernel_branch x u pc (by rw[index,count]) code run.final_bound
 exact ⟨u,ticks+1,run.trans branch,Nat.add_le_add_right cheap 1,ready⟩

/-- The complete horizon closes with the actual false branch and actual halt.
Only the internal proved whole-tick motive remains to instantiate. -/
theorem clocks {n B horizon:ℕ} (x:Fin n→ℂ) (I:ℕ→State→Prop) (cost:ℕ→ℕ)
 (s:State) (initial:I 0 s) (wb:WordBound B s)
 (code:UniformActualGlobalClockProgram.program.length≤B)
 (headers:∀j v,I j v→v.pc=5 ∧v.natReg 5920=j ∧v.natReg 5921=horizon)
 (advance:∀j,j<horizon→∀v,I j v→WordBound B v→∃u ticks,
  BoundedRuns UniformActualGlobalClockProgram.program n x B v ticks u ∧ticks≤cost j ∧I (j+1) u):
 ∃u ticks,BoundedExecution UniformActualGlobalClockProgram.program n x B s ticks
  (setPC u (UniformGlobalClockConductor.finalPC UniformFourierAxisPrepareMachine.program
   UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)) ∧
 ticks≤(∑j∈Finset.range horizon,cost j)+2 ∧I horizon u:=by
 obtain ⟨u,ticks,run,cheap,ready⟩:=segments x I cost s initial wb advance
 obtain ⟨pc,index,count⟩:=headers horizon u ready
 have stop:=UniformActualClockBoundaryExecution.halt_execution x u pc (by rw[index,count]) code run.final_bound
 exact ⟨u,ticks+2,run.executes stop,Nat.add_le_add_right cheap 2,ready⟩
end
end ExactFourierCircuits.UniformGlobalFiniteClockInduction
