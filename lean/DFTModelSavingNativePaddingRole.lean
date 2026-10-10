import DFTModelSavingNativePaddingRoleData
import DFTModelSavingNativePaddingUnitSource
import DFTModelSavingNativeDirectionLoop

set_option autoImplicit false

/-! Paper E (adc7f), §2.6, Theorem 2.6: one actual padding role, using the
same complete-W recursive child program and its exact returned Scalar tags. -/
namespace ExactFourierCircuits.DFTModelSavingNativePaddingRole
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
open UniformRecursivePaddingArrays (values applyRole lowMatrix)
open DFTModelSavingNativePaddingBoot (macRecord)
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit

theorem execution (n B U R A F q w r stack depth stackTop reserve saved last prior : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (role : Fin R) (s s0 : State)
    (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) (I : ℂ)
    (handler : Handler DFTModelSavingRecords.Port)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies
      (q*(w+1)+r) n B reserve stack stackTop cost x I handler)
    (same : StateMatch s s0) (smaller : q<q*(w+1)+r)
    (pc : s.pc=P.address .paddingPatch)
    (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (metadata : Metadata F U saved role.val last s) (dest : s.natReg 4175=role.val)
    (printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (present0 : Present A R (2^(q*(w+1)+r)) f0 s0)
    (qp : 1≤q) (m2 : 2≤w+1) (rp : r<w+1) (fits : ExplicitSeedBudget.roleBits≤q*w+r)
    (unitEnd : U+(record w).data.length≤F-6) (widthBound : (w+1)+1≤B)
    (arrayEnd : A+R*2^(q*(w+1)+r)≤F) (poolEnd : F+5*2^(q*(w+1)+r)≤B)
    (square : (2^(q*(w+1)+r))^2≤B) (low : 6≤F) (dataBase : 3≤A)
    (stackRoom : stack+34*(depth+q+2) ≤ stackTop) (recordAbove : stackTop ≤ U)
    (room : F+5*2^(q*(w+1)+r)+reserve*(q+1)*2^q≤B) (roleBound : role.val+1≤B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (code : P.program.length≤B) (widthActual : w+1=ExplicitSeedBudget.m) :
    ∃u u0 ticks,∃g g0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar,
      Result n B U R A F q w r stack depth stackTop saved last cost x role I handler s s0 u u0 ticks f f0 g g0 := by
  let edge:=UniformRecursivePaddingUnitEdge.unitEdge (w+1)
  let emb:=Function.Embedding.refl (Fin R)
  let raw:=(run DFTModelCacheRecords.unit (q,role.val)).val
  have mac : macRecord q w R role=UniformRecursivePaddingControl.patchRecord (record w) q role.val :=
    UniformRecursivePaddingUnitEdge.macro_unit q (w+1) emb role
  have recEnd : U+(macRecord q w R role).data.length≤F := by
    rw [mac,UniformRecursivePaddingControl.patch_length_same];omega
  obtain ⟨b,b0,boot⟩:=DFTModelSavingNativePaddingBoot.paired
    n B U R A F q w r stack depth saved last prior x role s s0 f f0 same pc parent metadata dest printed
      present present0 unitEnd low (by omega) widthBound constants bound code
  have visit : UniformRecursiveResidualDirectionLoop.Visit edge.dimension 0 (List.finRange edge.dimension) := by
    rw [←UniformRecursiveResidualDirectionLoop.indices_all]
    exact UniformRecursiveResidualDirectionLoop.indices_visit edge.dimension 0 edge.dimension (by omega)
  obtain ⟨c,c0,dt,g,g0,directions⟩:=DFTModelSavingNativeDirection.paired_loop
    n B U R R A F q w r stack depth stackTop reserve cost x emb role edge 0 (List.finRange edge.dimension)
      visit b b0 f f0 I handler childIH boot.matched smaller boot.pc boot.control boot.zeroControl boot.printed
      boot.present boot.zeroPresent qp m2 rp fits recEnd widthBound arrayEnd poolEnd square (by omega)
      dataBase stackRoom (by omega) recordAbove room boot.constants boot.run.final_bound code raw
      (DFTModelSavingNativePaddingUnitSource.source q w R role widthActual)
  have pcParent:=Parent.of_control directions.control
  have pcParent0:=Parent.of_control directions.zeroControl
  have metaC:=UniformRecursivePaddingRole.metadata_loop boot.metadata directions.nat unitEnd low recordAbove
  have metaC0:=UniformRecursivePaddingRole.metadata_loop boot.zeroMetadata directions.zeroNat unitEnd low recordAbove
  have printC : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q role.val).data c :=
    UniformRecursivePaddingRole.printed_loop (by simpa only [mac] using boot.printed)
      directions.nat unitEnd low recordAbove
  obtain ⟨d,edgeDone,dp,_,dnh,df⟩:=UniformRecursiveResidualControlJoin.edge_done_finish
    n B F 1 x c directions.pc pcParent.one pcParent.frontier metaC.mode directions.run.final_bound code
  obtain ⟨d0,edgeDone0,dp0,_,dnh0,df0⟩:=UniformRecursiveResidualControlJoin.edge_done_finish
    n B F 1 (fun _=>0) c0 (directions.matched.pc.trans directions.pc) pcParent0.one pcParent0.frontier
      metaC0.mode directions.zeroRun.final_bound code
  have pd:=pcParent.residual df
  have pd0:=pcParent0.residual df0
  have md:=metaC.transport (fun z _=>congrFun dnh z)
  have md0:=metaC0.transport (fun z _=>congrFun dnh0 z)
  have dpc : d.pc=P.address .paddingNext := by simpa only [Nat.lt_irrefl,ite_false] using dp
  have dpc0 : d0.pc=P.address .paddingNext := by simpa only [Nat.lt_irrefl,ite_false] using dp0
  obtain ⟨u,advance,up,pu,mu,af⟩:=DFTModelSavingNativePaddingControl.next
    n B (q*(w+1)+r) q A F r stack depth U saved role.val last x d dpc pd md low edgeDone.final_bound code roleBound
  obtain ⟨u0,advance0,up0,pu0,mu0,af0⟩:=DFTModelSavingNativePaddingControl.next
    n B (q*(w+1)+r) q A F r stack depth U saved role.val last (fun _=>0) d0 dpc0 pd0 md0 low
      edgeDone0.final_bound code roleBound
  have run:BoundedRuns P.program n x B s (47+dt+4+6) u :=
    ((boot.run.trans directions.run).trans edgeDone).trans advance
  have run0:BoundedRuns P.program n (fun _=>0) B s0 (47+dt+4+6) u0 :=
    ((boot.zeroRun.trans directions.zeroRun).trans edgeDone0).trans advance0
  have printU : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q role.val).data u := by
    intro j hj
    have length : (UniformRecursivePaddingControl.patchRecord (record w) q role.val).data.length=
        (record w).data.length := UniformRecursivePaddingControl.patch_length_same _ _ _
    have neq : U+j≠F-4 := by rw [length] at hj;omega
    rw [af.natHeap _ (by simpa only [List.mem_singleton] using neq),dnh]
    exact printC j hj
  have cu : UniformBinaryCStageMachine.Constants u := by
    have cc:=directions.constants
    unfold UniformBinaryCStageMachine.Constants at cc ⊢
    rw [af.scalarHeap,df.scalarHeap];exact cc
  have cu0 : UniformBinaryCStageMachine.Constants u0 := by
    have cc:=directions.zeroConstants
    unfold UniformBinaryCStageMachine.Constants at cc ⊢
    rw [af0.scalarHeap,df0.scalarHeap];exact cc
  refine ⟨u,u0,47+dt+4+6,g,g0,run,run0,DFTModelSavingNativeControl.paired_runs run run0 same,
    up,pu,pu0,mu,mu0,printU,?_,?_,?_,?_,?_,?_,cu,cu0,
    af.roots.trans (df.roots.trans (directions.roots.trans boot.roots)),
    af0.roots.trans (df0.roots.trans (directions.zeroRoots.trans boot.zeroRoots)),
    af.outputs.trans (df.outputs.trans (directions.outputs.trans boot.outputs)),
    af0.outputs.trans (df0.outputs.trans (directions.zeroOutputs.trans boot.zeroOutputs)),?_,?_,?_,?_⟩
  · intro i z;rw [af.scalarHeap,df.scalarHeap];exact directions.present i z
  · intro i z;rw [af0.scalarHeap,df0.scalarHeap];exact directions.zeroPresent i z
  · intro z hz away a b e
    rw [af.natHeap _ (by simpa only [List.mem_singleton] using e),dnh,directions.nat z hz away]
    exact boot.nat z a b
  · intro z hz away a b e
    rw [af0.natHeap _ (by simpa only [List.mem_singleton] using e),dnh0,directions.zeroNat z hz away]
    exact boot.zeroNat z a b
  · intro z hz away;rw [af.scalarHeap,df.scalarHeap,directions.scalar z hz away,boot.scalar]
  · intro z hz away;rw [af0.scalarHeap,df0.scalarHeap,directions.zeroScalar z hz away,boot.zeroScalar]
  · have time:=directions.time
    simp only [List.length_finRange,edge,UniformRecursivePaddingUnitEdge.dimension] at time
    have head : UniformFixedNetworkOpcodeMachine.headCost (macRecord q w R role)=32 := by rw [mac];rfl
    change dt≤(w+1)*UniformRecursiveResidualDirectionLoop.directionCost q w r
      (UniformFixedNetworkOpcodeMachine.headCost (macRecord q w R role)) cost+1 at time
    rw [head] at time
    unfold roleCost
    omega
  · exact (DFTModelSavingNativePaddingUnitSource.value q w r R role widthActual handler
      ((q*(w+1)+r,I),DFTModelRecursiveScalarSource.paired f f0)).trans directions.value
  · funext i z
    by_cases eq:i=role
    · subst i
      simp only [values,applyRole,Function.update_self]
      exact (directions.values z).trans (congrFun
        (UniformRecursivePaddingUnitEdge.action_unit q w r (fun y=>(f role y).value)) z)
    · simp only [values,applyRole,Function.update_of_ne eq]
      exact congrArg Scalar.value (directions.other i eq z)
  · funext i z
    by_cases eq:i=role
    · subst i
      simp only [values,applyRole,Function.update_self]
      exact (directions.zeroValues z).trans (congrFun
        (UniformRecursivePaddingUnitEdge.action_unit q w r (fun y=>(f0 role y).value)) z)
    · simp only [values,applyRole,Function.update_of_ne eq]
      exact congrArg Scalar.value (directions.zeroOther i eq z)

end
end ExactFourierCircuits.DFTModelSavingNativePaddingRole
