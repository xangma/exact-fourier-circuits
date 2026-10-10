import DFTModelSavingResidualNativeGroupBank

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine DFTModelSavingResidualSetup
open UniformRecursiveGroupLoop (Control Frame)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

/-- The real complete-W loop, strengthened with exact paired child Scalars. -/
theorem pair_loop
  (remaining k q m r n B reserve D V A i groups stack depth stackTop F : ℕ)
  (cost : ℕ → ℕ) (x : Fin n → ℂ) (I : ℂ) (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) (s s0 : State)
  (ih : PairSmallerBodies k n B reserve stack stackTop cost x I h) (smaller : q < k)
  (same : StateMatch s s0) (left : i+remaining=groups) (pc : s.pc=P.address .groupTest)
  (control : Control k q m r A D V F stack depth groups i s)
  (bank : PairBank q groups D i I h input input0 s s0)
  (partition : groups*(W*2^q)=V) (dataBase : 3 ≤ D) (dataEnd : D+V ≤ F)
  (stackRoom : stack+34*(depth+q+2) ≤ stackTop) (stackEnd : stackTop ≤ F)
  (room : F+reserve*(q+1)*2^q ≤ B) (square : (2^q)^2 ≤ B)
  (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) (code : P.program.length ≤ B) :
  ∃u u0 ticks,
    BoundedRuns P.program n x B s ticks u ∧
    BoundedRuns P.program n (fun _=>0) B s0 ticks u0 ∧
    StateMatch u u0 ∧ u.pc=P.address .inverseTest ∧
    Control k q m r A D V F stack depth groups groups u ∧
    PairBank q groups D groups I h input input0 u u0 ∧
    (∀j∈UniformRecursiveReturnStackMachine.fields,j ≠ 4125→u.natReg j=s.natReg j) ∧
    Frame D V F stack depth stackTop s u ∧ Frame D V F stack depth stackTop s0 u0 ∧
    UniformBinaryCStageMachine.Constants u ∧
    ticks ≤ remaining*(cost q+169)+1 ∧
    u.natReg 5300=(if remaining=0 then s.natReg 5300 else k) ∧
    u.natReg 5301=(if remaining=0 then s.natReg 5301 else r) := by
  induction remaining generalizing i s s0 with
  | zero=>
    have eq : i=groups := by omega
    subst i
    let u : State := {s with pc:=P.address .inverseTest}
    let u0 : State := {s0 with pc:=P.address .inverseTest}
    have branch := UniformRecursiveBatchGroupMachine.branch_execution P.program (P.address .groupTest)
      (P.address .call) (P.address .inverseTest) n B groups groups x s UniformRecursiveGroupExecution.group_branch
      pc control.index control.count bound (UniformRecursiveParentReturn.start_bound .call B code)
      (UniformRecursiveParentReturn.start_bound .inverseTest B code)
    have run : BoundedRuns P.program n x B s 1 u := by
      simpa only [lt_self_iff_false,ite_false] using branch
    obtain ⟨v0,zeroRun,matched⟩ := boundedRuns_match (y:=fun _=>0) run same
    have zeroBranch := UniformRecursiveBatchGroupMachine.branch_execution P.program (P.address .groupTest)
      (P.address .call) (P.address .inverseTest) n B groups groups (fun _=>0) s0 UniformRecursiveGroupExecution.group_branch
      (same.pc.trans pc) ((congrFun same.natReg 4125).trans control.index)
      ((congrFun same.natReg 4126).trans control.count) (same.wordBound bound)
      (UniformRecursiveParentReturn.start_bound .call B code)
      (UniformRecursiveParentReturn.start_bound .inverseTest B code)
    have zeroRun' : BoundedRuns P.program n (fun _=>0) B s0 1 u0 := by
      simpa only [lt_self_iff_false,ite_false] using zeroBranch
    have eq : v0=u0 := boundedRuns_unique zeroRun zeroRun'
    subst v0
    exact ⟨u,u0,1,run,zeroRun',matched,rfl,control.withPC _,bank.withPC _,fun _ _ _=>rfl,
      ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩,
      ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩,UniformRecursiveGroupLoop.constants_withPC constants _,
      by omega,rfl,rfl⟩
  | succ remaining induct=>
    have hi : i < groups := by omega
    obtain ⟨a,a0,steps,result,result0,matched,pair⟩ := pair_step n B k q m r D V A i groups F stack depth stackTop reserve
      cost x I h (input ⟨i,hi⟩) (input0 ⟨i,hi⟩) s s0 same ih smaller control pc partition hi
      (bank.actual.remaining ⟨i,hi⟩ (by rfl)) (bank.zero.remaining ⟨i,hi⟩ (by rfl))
      dataBase dataEnd stackRoom stackEnd room square constants bound code
    have nextBank := bank.advance hi partition dataEnd result result0 pair
    have frame := UniformRecursiveGroupLoop.frame_of_group partition hi result.scalar result.nat result.outputs result.roots
    have frame0 := UniformRecursiveGroupLoop.frame_of_group partition hi result0.scalar result0.nat result0.outputs result0.roots
    obtain ⟨u,u0,tailTicks,tailRun,tailRun0,last,up,uc,ub,kept,uf,uf0,us,timeTail,nativeBits,nativeRest⟩ :=
      induct (i+1) a a0 matched (by omega) result.pc result.control nextBank result.constants result.run.final_bound
    have keptAll : ∀j∈UniformRecursiveReturnStackMachine.fields,j ≠ 4125→u.natReg j=s.natReg j := by
      intro j hj ne
      exact (kept j hj ne).trans (by simpa only [ne,ite_false] using result.fields j hj)
    refine ⟨u,u0,steps+tailTicks,result.run.trans tailRun,result0.run.trans tailRun0,last,up,uc,ub,keptAll,
      frame.trans uf,frame0.trans uf0,us,?_,?_,?_⟩
    · have time := result.time
      rw [Nat.succ_mul]
      omega
    · simpa only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,ite_false] using
        nativeBits.trans (by split <;> simp_all [result.nativeBits])
    · simpa only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,ite_false] using
        nativeRest.trans (by split <;> simp_all [result.nativeRest])

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup
