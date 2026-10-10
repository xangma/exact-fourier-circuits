import DFTModelSavingNativeBilledResidualTyped
import DFTModelSavingNativeBilledLeaf

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeBilledCore
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelSavingNativeBilledSequence
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch

theorem record_execution (n B T tapeEnd A F q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (ni : NoPadding i)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies (q*m+rest) n B reserve stack stackTop K K cost x I h)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q i).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (recordEnd : T+(Instruction.record q i).data.length≤F-6) (stackEnd : stackTop≤T)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 time g g0,StepResult n B T A F q rest stack depth stackTop K cost x I h i s s0 f f0 u u0 time g g0 := by
  by_cases leaf:DFTModelSavingNativeLeafTyped.Leaf i
  · obtain ⟨u,u0,g,g0,out⟩:=DFTModelSavingNativeBilledLeaf.execution n B T tapeEnd A F q rest stack depth stackTop reserve K
      cost x I h i leaf cap s s0 f f0 same pc parent metadata live printed data data0 geometry recordEnd constants bound
    exact ⟨u,u0,_,g,g0,out⟩
  · cases i with
    | initial=>exact False.elim (leaf trivial)
    | boundary a=>exact False.elim (leaf trivial)
    | translation=>exact False.elim (leaf trivial)
    | exchange=>exact False.elim (leaf trivial)
    | padding=>exact False.elim ni
    | «macro» a v=>
      cases v with
      | edge old new role edge=>
        exact DFTModelSavingNativeBilledResidualTyped.execution n B T tapeEnd A F q rest stack depth stackTop reserve K
          cost x I h a role edge s s0 f f0 childIH ((DFTModelSavingCost.factor_direction rest geometry.remainder).trans cap) same pc parent metadata live printed data data0 geometry recordEnd stackEnd constants bound
      | shear d src ne c hc=>exact False.elim (leaf trivial)

/-- The whole real nonpadding record family is chronological. Its sole
recursive premise is actual strictly smaller execution of this SAME program;
no per-record action or output is supplied. -/
theorem run_records (n B tapeEnd A F q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort) (is : List TypedInstruction)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies (q*m+rest) n B reserve stack stackTop K K cost x I h)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (noPadding : ∀i∈is,NoPadding i) (mainEnd : tapeEnd≤F-6) :
    ∀(T : ℕ)(s s0 : State)(f f0 : Fin W→Fin (2^(q*m+rest))→Scalar),
      StateMatch s s0→s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
      s.natHeap (F-1)=some tapeEnd→PrintedRecords T (is.map (Instruction.record q)) s→
      Present A W (2^(q*m+rest)) f s→Present A W (2^(q*m+rest)) f0 s0→
      T+(serialize (is.map (Instruction.record q))).length≤tapeEnd→stackTop≤T→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 time g g0,SequenceResult n B T A F q rest stack depth stackTop K cost x I h is s s0 f f0 u u0 time g g0 :=
  DFTModelSavingNativeBilledSequence.run_records n B tapeEnd A F q rest stack depth stackTop reserve K cost x I h is geometry mainEnd
    (fun i hi T s s0 f f0 same pc parent metadata live printed data data0 endBound stackEnd constants bound=>
      record_execution n B T tapeEnd A F q rest stack depth stackTop reserve K cost x I h i (noPadding i hi) cap s s0 f f0
        childIH same pc parent metadata live printed data data0 geometry endBound stackEnd constants bound)

end
end ExactFourierCircuits.DFTModelSavingNativeBilledCore
