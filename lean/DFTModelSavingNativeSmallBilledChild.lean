import DFTModelSavingNativeSmallBilling
import DFTModelSavingResidualNativeGroupData
import UniformRecursiveSmallBody

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeSmallBilledChild
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open DFTModelAffine DFTModelRecursiveScalarSource
open DFTModelSavingResidualNativeGroup
namespace P
export UniformRecursiveSavingProgram (program address threshold)
end P
noncomputable abbrev cost := UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
noncomputable section
attribute [local irreducible] P.program DFTModelSavingProgram.program

/-- The actual positive-depth base of the coupled source induction. The one
closed upstream child returns the exact pair of the two genuine RAM outputs. -/
theorem execution (n B k A F stack stackTop depth reserve : ℕ) (x : Fin n → ℂ)
    (input input0 : Fin W → Fin (2^k) → Scalar) (s s0 : State)
    (thresholdFit : P.threshold ≤ reserve) (stackFit : 34 ≤ reserve) (small : k < P.threshold)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 4120=k)
    (base : s.natReg 4121=A) (size : s.natReg 4122=2^k) (frontier : s.natReg 4123=F)
    (sp : s.natReg 4150=stack) (dp : s.natReg 4151=depth)
    (data : ∀i j,s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))
    (data0 : ∀i j,s0.scalarHeap (A+i.val*2^k+j.val)=some (input0 i j))
    (positive : 1 ≤ depth) (heapBase : 3 ≤ A) (arrayEnd : A+W*2^k ≤ F)
    (_stackRoom : stack+34*(depth+k+1) ≤ stackTop) (_stackTop : stackTop ≤ F)
    (code : P.program.length ≤ B) (room : F+reserve*(k+1)*2^k ≤ B) (_square : (2^k)^2 ≤ B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 ticks,
      ChildResult n B k A F stack stackTop depth cost x input s u ticks ∧
      ChildResult n B k A F stack stackTop depth cost (fun _=>0) input0 s0 u0 ticks ∧
      StateMatch u u0 ∧
      (∀(i : Fin W)(j : Fin (2^k)),
        (run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).val.look
          (i.val*2^k+j.val) Tagged.blank=
          encodePaired ((u.scalarHeap (A+i.val*2^k+j.val)).getD Scalar.zero)
            ((u0.scalarHeap (A+i.val*2^k+j.val)).getD Scalar.zero)) ∧
      (run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).work≤33*ticks := by
  have fb:F ≤ B:=by omega
  have literal:P.threshold ≤ B:=thresholdFit.trans (UniformRecursiveSmallBody.reserve_le room)
  have extent:A+W*2^k ≤ B:=arrayEnd.trans fb
  have countBound:W ≤ B:=by
    have h:=Nat.mul_le_mul_left W (show 1 ≤ 2^k from Nat.two_pow_pos k)
    simp only [Nat.mul_one] at h
    omega
  obtain ⟨u,u0,t,t0,actual,zero,matched,up,up0,out,out0,ef,ef0,fr,fr0,con,con0,ud,ud0,
    uf,uf0,root,child,compiled⟩:=DFTModelSavingNativeSmall.execution n B k A F depth x s s0
      input input0 same pc bits base size frontier dp small data data0 heapBase constants bound code
      literal countBound extent (UniformRecursiveSmallBody.stack_room stackFit room)
  have nonzero:depth≠0:=by omega
  rw [ite_eq_right nonzero] at actual zero up up0
  have stepsFit:4+UniformRecursiveSmallBase.baseTicks W k ≤ cost k:=
    UniformRecursiveSmallBody.ticks_fit _ k small
  have left:ChildResult n B k A F stack stackTop depth cost x input s u
      (4+UniformRecursiveSmallBase.baseTicks W k) := by
    refine ⟨actual,up,(child nonzero).1.trans sp,ud,?_,?_,?_,?_,con,
      fr.outputs.trans ef.outputs,fr.roots.trans ef.roots,stepsFit⟩
    · intro i j;rw [out i j];rfl
    · intro i j;rw [out i j]
      exact congrArg some (congrFun (UniformBinaryTensorCoordinates.applyAxes_tensor k (input i)) j)
    · intro z _ _;rw [fr.natHeap,ef.natHeap]
    · intro z _ away
      exact (fr.scalarHeap z away).trans (congrFun ef.scalarHeap z)
  have right:ChildResult n B k A F stack stackTop depth cost (fun _=>0) input0 s0 u0
      (4+UniformRecursiveSmallBase.baseTicks W k) := by
    refine ⟨zero,up0,(child nonzero).2.trans (by rw [same.natReg];exact sp),ud0,?_,?_,?_,?_,con0,
      fr0.outputs.trans ef0.outputs,fr0.roots.trans ef0.roots,stepsFit⟩
    · intro i j;rw [out0 i j];rfl
    · intro i j;rw [out0 i j]
      exact congrArg some (congrFun (UniformBinaryTensorCoordinates.applyAxes_tensor k (input0 i)) j)
    · intro z _ _;rw [fr0.natHeap,ef0.natHeap]
    · intro z _ away
      exact (fr0.scalarHeap z away).trans (congrFun ef0.scalarHeap z)
  refine ⟨u,u0,_,left,right,matched,?_,DFTModelSavingNativeSmallBilling.native_work input input0 small⟩
  intro i j
  rw [compiled,paired_lookup,out i j,out0 i j]
  rfl

end
end ExactFourierCircuits.DFTModelSavingNativeSmallBilledChild
