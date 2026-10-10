import DFTModelSavingResidualNativeGroupStep

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine DFTModelSavingResidualSetup
open UniformRecursiveGroupLoop (Control)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

 theorem control_match {k q m r A D V F stack depth groups i : ℕ} {s s0 : State}
  (control : Control k q m r A D V F stack depth groups i s) (same : StateMatch s s0) :
  Control k q m r A D V F stack depth groups i s0 := by
  cases control
  constructor <;> rw [same.natReg] <;> assumption

/-- A genuine branch/call83, paired smaller child, and return76/reload9.
The paired value names the concrete returned Scalars of both source runs. -/
 theorem pair_step (n B k q m r D V A i groups F stack depth stackTop reserve : ℕ)
  (cost : ℕ → ℕ) (x : Fin n → ℂ) (I : ℂ) (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin W → Fin (2^q) → Scalar) (s s0 : State)
  (same : StateMatch s s0)
  (ih : PairSmallerBodies k n B reserve stack stackTop cost x I h) (smaller : q < k)
  (control : Control k q m r A D V F stack depth groups i s)
  (pc : s.pc=P.address .groupTest) (partition : groups*(W*2^q)=V) (hi : i < groups)
  (data : ∀ (j : Fin W) (t : Fin (2^q)),s.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)=some (input j t))
  (data0 : ∀ (j : Fin W) (t : Fin (2^q)),s0.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)=some (input0 j t))
  (dataBase : 3 ≤ D) (dataEnd : D+V ≤ F)
  (stackRoom : stack+34*(depth+q+2) ≤ stackTop) (stackEnd : stackTop ≤ F)
  (room : F+reserve*(q+1)*2^q ≤ B) (square : (2^q)^2 ≤ B)
  (constants : UniformBinaryCStageMachine.Constants s) (wb : WordBound B s) (code : P.program.length ≤ B) :
  ∃u u0 ticks,
    GroupResult n B k q m r D V A i groups F stack depth stackTop cost x input s u ticks ∧
    GroupResult n B k q m r D V A i groups F stack depth stackTop cost (fun _=>0) input0 s0 u0 ticks ∧
    StateMatch u u0 ∧
    ∀(j : Fin W)(t : Fin (2^q)),
      (h ((q,I),DFTModelRecursiveScalarSource.paired input input0)).val.look (j.val*2^q+t.val) Tagged.blank=
      encodePaired ((u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero)
        ((u0.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero) := by
  have fb : F ≤ B := by omega
  have localStack : stack+34*(depth+1) ≤ B := by nlinarith only [stackRoom,stackEnd,fb]
  obtain ⟨c,called⟩:=call n B k q m r D V A i groups F stack depth x s control pc partition hi wb code
    (dataEnd.trans fb) localStack
  obtain ⟨c0,called0⟩:=call n B k q m r D V A i groups F stack depth (fun _=>0) s0
    (control_match control same) (same.pc.trans pc) partition hi (same.wordBound wb) code (dataEnd.trans fb) localStack
  obtain ⟨c0',r0,matched⟩:=boundedRuns_match (y:=fun _=>0) called.run same
  have eq : c0'=c0 := boundedRuns_unique r0 called0.run
  subst c0'
  have partEnd : (i+1)*(W*2^q) ≤ V :=
    (Nat.mul_le_mul_right (W*2^q) (Nat.succ_le_of_lt hi)).trans_eq partition
  have addEnd : D+i*(W*2^q)+W*2^q ≤ F := by
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact (Nat.add_le_add_left partEnd D).trans dataEnd
  have childData : ∀(j : Fin W)(t : Fin (2^q)),c.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)=some (input j t) := by
    intro j t;rw [called.scalar];exact data j t
  have childData0 : ∀(j : Fin W)(t : Fin (2^q)),c0.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)=some (input0 j t) := by
    intro j t;rw [called0.scalar];exact data0 j t
  have con : UniformBinaryCStageMachine.Constants c := by
    simpa only [UniformBinaryCStageMachine.Constants,called.scalar] using constants
  obtain ⟨v,v0,ct,child,child0,_matchedChild,paired⟩:=ih q smaller (D+i*(W*2^q)) F (depth+1) input input0 c c0
    matched called.pc called.bits called.base called.size called.fresh called.stackReg called.depthReg childData childData0
    (by omega) (by omega) addEnd (by convert stackRoom using 1; omega) stackEnd code room square con called.run.final_bound
  obtain ⟨u,result,heap⟩:=resume_child n B k q m r D V A i groups F stack depth stackTop cost x input s c v ct
    control partition hi dataEnd stackRoom stackEnd wb code fb called child
  obtain ⟨u0,result0,heap0⟩:=resume_child n B k q m r D V A i groups F stack depth stackTop cost (fun _=>0) input0 s0 c0 v0 ct
    (control_match control same) partition hi dataEnd stackRoom stackEnd (same.wordBound wb) code fb called0 child0
  obtain ⟨u0',run0,last⟩:=boundedRuns_match (y:=fun _=>0) result.run same
  have eq : u0'=u0 := boundedRuns_unique run0 result0.run
  subst u0'
  refine ⟨u,u0,_,result,result0,last,?_⟩
  intro j t
  rw [heap,heap0]
  exact paired j t

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup
