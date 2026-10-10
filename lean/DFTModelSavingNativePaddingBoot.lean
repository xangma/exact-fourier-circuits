import DFTModelSavingNativePaddingPatch
import DFTModelSavingNativeEntry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingBoot
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record)
open DFTModelSavingNativePaddingControl (parent_match metadata_match printed_match)
noncomputable section

def macRecord (q w R : ℕ) (role : Fin R) :=
  macroRecord q (Function.Embedding.refl (Fin R))
    (.edge _ _ role (UniformRecursivePaddingUnitEdge.unitEdge (w+1)))

structure Result (n B U R A F q w r stack depth saved last : ℕ)
    (x : Fin n→ℂ) (role : Fin R) (s s0 u u0 : State)
    (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) : Prop where
  run : BoundedRuns P.program n x B s 47 u
  zeroRun : BoundedRuns P.program n (fun _=>0) B s0 47 u0
  matched : StateMatch u u0
  pc : u.pc=P.address .directionTest
  control : UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F U r stack depth 0 (w+1)
    (U+(macRecord q w R role).data.length) (macRecord q w R role).inverse u
  zeroControl : UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F U r stack depth 0 (w+1)
    (U+(macRecord q w R role).data.length) (macRecord q w R role).inverse u0
  metadata : Metadata F U saved role.val last u
  zeroMetadata : Metadata F U saved role.val last u0
  printed : Printed U (macRecord q w R role).data u
  present : Present A R (2^(q*(w+1)+r)) f u
  zeroPresent : Present A R (2^(q*(w+1)+r)) f0 u0
  nat : ∀z,z≠U+1→z≠U+3→u.natHeap z=s.natHeap z
  zeroNat : ∀z,z≠U+1→z≠U+3→u0.natHeap z=s0.natHeap z
  scalar : u.scalarHeap=s.scalarHeap
  zeroScalar : u0.scalarHeap=s0.scalarHeap
  constants : UniformBinaryCStageMachine.Constants u
  zeroConstants : UniformBinaryCStageMachine.Constants u0
  roots : u.rootOrders=s.rootOrders
  zeroRoots : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  zeroOutputs : u0.outputs=s0.outputs

theorem single (n B U R A F q w r stack depth saved last prior : ℕ)
    (x : Fin n→ℂ) (role : Fin R) (s : State)
    (f : Fin R→Fin (2^(q*(w+1)+r))→Scalar)
    (pc : s.pc=P.address .paddingPatch)
    (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (metadata : Metadata F U saved role.val last s) (dest : s.natReg 4175=role.val)
    (printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (unitEnd : U+(record w).data.length≤F-6) (low : 6≤F)
    (extent : U+(record w).data.length≤B) (width : (w+1)+1≤B)
    (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u, BoundedRuns P.program n x B s 47 u ∧ u.pc=P.address .directionTest ∧
      UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F U r stack depth 0 (w+1)
        (U+(macRecord q w R role).data.length) (macRecord q w R role).inverse u ∧
      Metadata F U saved role.val last u ∧ Printed U (macRecord q w R role).data u ∧
      Present A R (2^(q*(w+1)+r)) f u ∧
      (∀z,z≠U+1→z≠U+3→u.natHeap z=s.natHeap z) ∧ u.scalarHeap=s.scalarHeap ∧
      UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs := by
  let old:=UniformRecursivePaddingControl.patchRecord (record w) q prior
  have mac : macRecord q w R role=UniformRecursivePaddingControl.patchRecord (record w) q role.val :=
    UniformRecursivePaddingUnitEdge.macro_unit q (w+1) (Function.Embedding.refl _) role
  have patched : UniformRecursivePaddingControl.patchRecord old q role.val=macRecord q w R role := by
    rw [UniformRecursivePaddingControl.patch_twice,←mac]
  have fg:=UniformRecursivePaddingControl.patch_good (record w) q prior
    (UniformRecursivePaddingControl.binaryUnit_good (w+1))
  have oe : U+old.data.length≤B := by rw [UniformRecursivePaddingControl.patch_length_same];exact extent
  have ou : U+old.data.length≤F-6 := by rw [UniformRecursivePaddingControl.patch_length_same];exact unitEnd
  obtain ⟨a,patch,ap,pa,ma,fields,bank,_,finish,pf⟩:=DFTModelSavingNativePaddingPatch.execution
    n B (q*(w+1)+r) q A F r stack depth U saved role.val last old x s pc parent metadata dest printed fg
      ou low oe width bound code
  have bankA : Printed U (macRecord q w R role).data a := by simpa only [patched] using bank
  have dim : a.natReg 2857=w+1 := fields.dimension
  have inv : a.natReg 2856=0 := fields.inverse
  have finishA : a.natReg 2865=U+(macRecord q w R role).data.length := by
    rw [mac,UniformRecursivePaddingControl.patch_length_same]
    simpa only [old,UniformRecursivePaddingControl.patch_length_same] using finish
  obtain ⟨u,init,up,idx,dimension,ending,inverse,heap,ifr⟩:=UniformRecursiveResidualControl.init_execution
    n B F (w+1) (U+(macRecord q w R role).data.length) 0 x a ap pa.one dim finishA inv patch.final_bound code
  have pu:=pa.residual ifr
  have cursor : u.natReg 2850=U :=
    (UniformRecursivePaddingFragments.residual_init_cursor n B F (w+1) (U+(macRecord q w R role).data.length)
      0 x a u ap pa.one dim finishA inv patch.final_bound code init).trans fields.cursor
  have control : UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F U r stack depth 0 (w+1)
      (U+(macRecord q w R role).data.length) (macRecord q w R role).inverse u :=
    ⟨cursor,pu.nativeBase,pu.original,pu.bits,pu.volume,pu.frontier,pu.rest,pu.stack,pu.depth,pu.one,
      idx,dimension,ending,inverse,pu.nativeBits,pu.nativeRest,pu.table,pu.columns,pu.width⟩
  have sh : u.scalarHeap=s.scalarHeap := ifr.scalarHeap.trans pf.scalarHeap
  have cu : UniformBinaryCStageMachine.Constants u := by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [sh];exact constants
  refine ⟨u,?_,up,control,ma.transport (fun z _=>congrFun heap z),?_,?_,?_,sh,cu,
    ifr.roots.trans pf.roots,ifr.outputs.trans pf.outputs⟩
  · simpa only [old,UniformRecursivePaddingControl.patch_headCost,UniformRecursivePaddingRole.record_cost]
      using patch.trans init
  · intro j hj;rw [heap];exact bankA j hj
  · intro i z;rw [sh];exact present i z
  · intro z a b;rw [heap];exact pf.natHeap z (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨a,b⟩)

theorem paired (n B U R A F q w r stack depth saved last prior : ℕ)
    (x : Fin n→ℂ) (role : Fin R) (s s0 : State)
    (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) (same : StateMatch s s0)
    (pc : s.pc=P.address .paddingPatch)
    (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (metadata : Metadata F U saved role.val last s) (dest : s.natReg 4175=role.val)
    (printed : Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (present0 : Present A R (2^(q*(w+1)+r)) f0 s0)
    (unitEnd : U+(record w).data.length≤F-6) (low : 6≤F)
    (extent : U+(record w).data.length≤B) (width : (w+1)+1≤B)
    (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u u0, Result n B U R A F q w r stack depth saved last x role s s0 u u0 f f0 := by
  obtain ⟨u,run,up,control,mu,bank,data,nh,sh,cu,roots,outputs⟩:=single
    n B U R A F q w r stack depth saved last prior x role s f pc parent metadata dest printed present
      unitEnd low extent width constants bound code
  obtain ⟨u0,run0,up0,control0,mu0,bank0,data0,nh0,sh0,cu0,roots0,outputs0⟩:=single
    n B U R A F q w r stack depth saved last prior (fun _=>0) role s0 f0 (same.pc.trans pc)
      (parent_match same parent) (metadata_match same metadata) (by rw [same.natReg];exact dest)
      (printed_match same printed) present0 unitEnd low extent width
      (DFTModelSavingNativeEntry.constants_match same constants) (same.wordBound bound) code
  exact ⟨u,u0,run,run0,DFTModelSavingNativeControl.paired_runs run run0 same,up,control,control0,
    mu,mu0,bank,data,data0,nh,nh0,sh,sh0,cu,cu0,roots,roots0,outputs,outputs0⟩

end
end ExactFourierCircuits.DFTModelSavingNativePaddingBoot
