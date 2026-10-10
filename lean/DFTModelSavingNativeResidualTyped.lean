import DFTModelSavingNativeResidualExecution
import DFTModelSavingNativeSequence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeResidualTyped
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open DFTModelSavingNativeSequence
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch

lemma values {R V : ℕ} (i : Fin R) (f g : Fin R→Fin V→Scalar)
    (other : ∀j,j≠i→∀z,g j z=f j z) :
    g=UniformRecursiveResidualRoleSemantics.replaceRole i (g i) f := by
  funext j z
  by_cases eq:j=i
  · subst j;simp only [UniformRecursiveResidualRoleSemantics.replaceRole,ite_true]
  · simpa only [UniformRecursiveResidualRoleSemantics.replaceRole,ite_eq_right eq] using other j eq z

lemma outside {R V A F : ℕ} (i : Fin R) (s u : State)
    (fr : ∀z,z<F→(z<A+i.val*V∨A+(i.val+1)*V≤z)→u.scalarHeap z=s.scalarHeap z) :
    ∀z,z<F→(z<A∨A+R*V≤z)→u.scalarHeap z=s.scalarHeap z := by
  intro z hz away
  apply fr z hz
  have bound: (i.val+1)*V≤R*V:=Nat.mul_le_mul_right V (Nat.succ_le_iff.mpr i.isLt)
  rcases away with h|h
  · left;omega
  · right;omega

/-- The actual residual macro joins the chronological typed step without
choosing an ordinary tag fold. The returned source Scalars determine tags. -/
theorem execution (n B T tapeEnd A F q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (handler : Handler ChildPort)
    (a : Invocation) {old new : FramedScheduleWords.Label seedWidth}
    (role : Fin (fixedBlock a).width) (edge : FramedScheduleWords.NestedEdge old new)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*m+rest) n B reserve stack stackTop cost x I handler)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q (.macro a (.edge old new role edge))).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (recordEnd : T+(Instruction.record q (.macro a (.edge old new role edge))).data.length≤F-6)
    (stackEnd : stackTop≤T) (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 time g g0,StepResult n B T A F q rest stack depth stackTop cost x I handler
      (.macro a (.edge old new role edge)) s s0 f f0 u u0 time g g0 := by
  let emb:Fin (fixedBlock a).width↪Fin W:=
    (fixedBlock a).embedding.trans UniformRecursiveResidualRoleSemantics.roleMap
  have recordEq : macroRecord q emb (.edge old new role edge)=
      Instruction.record q (.macro a (.edge old new role edge)) :=
    UniformRecursiveResidualRoleSemantics.padded_record q a role edge
  have bank:Printed T (macroRecord q emb (.edge old new role edge)).data s:=by rw [recordEq];exact printed
  have limit:T+(macroRecord q emb (.edge old new role edge)).data.length≤F-6:=by rw [recordEq];exact recordEnd
  let raw:=DFTModelCacheRecords.dataTape (macroRecord q emb (.edge old new role edge)).data
  obtain ⟨u,u0,time,g,g0,res⟩:=DFTModelSavingNativeResidual.execution
    n B T tapeEnd (fixedBlock a).width W A F q (m-1) rest stack depth stackTop reserve cost x emb role edge
    s s0 f f0 I handler childIH same geometry.smaller pc parent metadata live bank data data0
    geometry.positive (by norm_num [m,ExplicitSeedBudget.m]) geometry.remainder geometry.batchFit
    limit geometry.width geometry.arrayEnd geometry.poolEnd geometry.square geometry.low geometry.base
    geometry.stackRoom stackEnd geometry.childRoom constants bound geometry.code raw
    (DFTModelSavingDirection.dataTape_source _)
  have out:arrayValues q rest g=(semantic q rest (.macro a (.edge old new role edge))).mulVec (arrayValues q rest f) := by
    rw [values (emb role) f g res.other]
    exact UniformRecursiveResidualRoleSemantics.edge_values q rest a role edge f (g (emb role)) res.values
  have out0:arrayValues q rest g0=(semantic q rest (.macro a (.edge old new role edge))).mulVec (arrayValues q rest f0) := by
    rw [values (emb role) f0 g0 res.zeroOther]
    exact UniformRecursiveResidualRoleSemantics.edge_values q rest a role edge f0 (g0 (emb role)) res.zeroValues
  have code : DFTModelSavingChronology.recordStep W rest handler
      (Instruction.record q (.macro a (.edge old new role edge))) ((q*m+rest,I),paired f f0)=
      ((q*m+rest,I),paired g g0) := by
    unfold DFTModelSavingChronology.recordStep
    rw [←recordEq,DFTModelSavingRecords.dispatch,DFTModelSavingControl.code_ifz_value]
    change (if raw.look 0 0=0 then _ else _)=_
    have opcode:raw.look 0 0=0:=
      (DFTModelSavingDirection.dataTape_source (macroRecord q emb (.edge old new role edge))).header ⟨0,by decide⟩
    rw [ite_eq_left opcode]
    exact res.value
  refine ⟨u,u0,time,g,g0,res.run,res.zeroRun,res.matched,res.pc,res.matched.pc.trans res.pc,?_,?_,
    res.present,res.zeroPresent,out,out0,⟨res.nat,outside (emb role) s u res.scalar,res.roots,res.outputs⟩,
    ⟨res.zeroNat,outside (emb role) s0 u0 res.zeroScalar,res.zeroRoots,res.zeroOutputs⟩,
    res.constants,res.zeroConstants,?_,code⟩
  · have h:=res.parent
    change Parent (q*m+rest) q A F (T+(macroRecord q emb (.edge old new role edge)).data.length) rest stack depth u at h
    have len:=congrArg (fun r:Record=>r.data.length) recordEq
    rw [len] at h
    exact h
  · have h:=res.zeroParent
    change Parent (q*m+rest) q A F (T+(macroRecord q emb (.edge old new role edge)).data.length) rest stack depth u0 at h
    have len:=congrArg (fun r:Record=>r.data.length) recordEq
    rw [len] at h
    exact h
  · change time≤edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
      (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q (.macro a (.edge old new role edge)))) cost+53
    have h:=res.time
    change time≤edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
      (UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))) cost+53 at h
    have head:=congrArg UniformFixedNetworkOpcodeMachine.headCost recordEq
    rw [head] at h
    exact h

end
end ExactFourierCircuits.DFTModelSavingNativeResidualTyped
