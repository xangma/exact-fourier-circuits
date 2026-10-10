import DFTModelSavingSelfCall
import DFTModelSavingBinarySemantics
import DFTModelSavingNativeControl
import UniformRecursiveSmallEntry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeSmall
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open UniformFixedNetworkShearChildMachine (Present)
namespace P
export UniformRecursiveSavingProgram (program address threshold)
end P
abbrev W := UniformRecursiveSelfCallMachine.W
noncomputable section
attribute [local irreducible] P.program DFTModelSavingProgram.program
  DFTModelSavingProgram.ordinary DFTModelSavingProgram.large

lemma constants_match {s s0 : State} (same : StateMatch s s0)
    (constants : UniformBinaryCStageMachine.Constants s) :
    UniformBinaryCStageMachine.Constants s0 := by
  constructor
  · obtain ⟨v,hv,hm⟩:=(same.scalarHeap 1).left constants.1
    rw [←hm.eq_of_prepared rfl] at hv
    exact hv
  · obtain ⟨v,hv,hm⟩:=(same.scalarHeap 2).left constants.2
    rw [←hm.eq_of_prepared rfl] at hv
    exact hv

/-- The closed compiler's finite base is the complete real saving-program
entry, allocation, binary batch and terminal branch. Both source executions
retain their actual returned Scalars, including dependency flags. -/
theorem execution (n B k A F depth : ℕ) (x : Fin n→ℂ) (s s0 : State)
    (f f0 : Fin W→Fin (2^k)→Scalar) (same : StateMatch s s0)
    (pc : s.pc=0) (bits : s.natReg 4120=k) (base : s.natReg 4121=A)
    (size : s.natReg 4122=2^k) (frontier : s.natReg 4123=F) (dp : s.natReg 4151=depth)
    (small : k<P.threshold) (data : Present A W (2^k) f s)
    (baseline : Present A W (2^k) f0 s0) (heapBase : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (code : P.program.length≤B) (thresholdBound : P.threshold≤B) (countBound : W≤B)
    (extent : A+W*2^k≤B) (stackEnd : F+34*(k+1)≤B) :
    ∃u u0 t t0,
      BoundedRuns P.program n x B s
        ((if depth=0 then 10 else 4)+UniformRecursiveSmallBase.baseTicks W k) u ∧
      BoundedRuns P.program n (fun _=>0) B s0
        ((if depth=0 then 10 else 4)+UniformRecursiveSmallBase.baseTicks W k) u0 ∧
      StateMatch u u0 ∧
      u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
      u0.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
      Present A W (2^k) (fun i=>UniformBinaryBatchCMachine.transformed k (f i)) u ∧
      Present A W (2^k) (fun i=>UniformBinaryBatchCMachine.transformed k (f0 i)) u0 ∧
      UniformRecursiveSavingExecution.EntryFrame s t ∧
      UniformRecursiveSavingExecution.EntryFrame s0 t0 ∧
      UniformRecursiveSmallBase.Frame A (W*2^k) t u ∧
      UniformRecursiveSmallBase.Frame A (W*2^k) t0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧UniformBinaryCStageMachine.Constants u0 ∧
      u.natReg 4151=depth ∧u0.natReg 4151=depth ∧
      u.natReg 4123=(if depth=0 then F+34*(k+1) else F) ∧
      u0.natReg 4123=(if depth=0 then F+34*(k+1) else F) ∧
      (depth=0→u.natReg 4150=F ∧u0.natReg 4150=F) ∧
      (depth≠0→u.natReg 4150=s.natReg 4150 ∧u0.natReg 4150=s0.natReg 4150) ∧
      (run DFTModelSavingProgram.program ((k,Complex.I),paired f f0)).val=
        paired (fun i=>UniformBinaryBatchCMachine.transformed k (f i))
          (fun i=>UniformBinaryBatchCMachine.transformed k (f0 i)) := by
  obtain ⟨u,t,actual,up,out,_,entry,frame,con,udp,uf,root,child⟩:=
    UniformRecursiveSmallEntry.execution n B k A F depth x s f pc bits base size frontier dp small
      data heapBase constants bound code thresholdBound countBound extent stackEnd
  obtain ⟨u0,t0,zero,up0,out0,_,entry0,frame0,con0,udp0,uf0,root0,child0⟩:=
    UniformRecursiveSmallEntry.execution n B k A F depth (fun _=>0) s0 f0
      (same.pc.trans pc) (by rw [same.natReg];exact bits)
      (by rw [same.natReg];exact base) (by rw [same.natReg];exact size)
      (by rw [same.natReg];exact frontier) (by rw [same.natReg];exact dp) small
      baseline heapBase (constants_match same constants) (same.wordBound bound)
      code thresholdBound countBound extent stackEnd
  refine ⟨u,u0,t,t0,actual,zero,DFTModelSavingNativeControl.paired_runs actual zero same,
    up,up0,out,out0,entry,entry0,frame,frame0,con,con0,udp,udp0,uf,uf0,
    (fun h=>⟨root h,root0 h⟩),(fun h=>⟨child h,child0 h⟩),?_⟩
  rw [DFTModelSavingSelfCall.recursive_value,ite_eq_left small]
  rw [DFTModelSavingProgram.ordinary]
  exact DFTModelSavingBinary.program_paired f f0

end
end ExactFourierCircuits.DFTModelSavingNativeSmall
