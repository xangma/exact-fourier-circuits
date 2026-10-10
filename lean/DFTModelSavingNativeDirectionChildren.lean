import DFTModelSavingNativeDirectionPairBoot
import DFTModelSavingResidualNativeGroupSlice
import UniformRecursiveResidualChildren

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
namespace FV
export UniformRecursiveResidualFiberValues (input representative representative_value)
end FV
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

structure ChildrenResult (n B T nRoles R A F q w r stack depth stackTop : ℕ) (cost:ℕ→ℕ) (x:Fin n→ℂ)
 (emb:Fin nRoles↪Fin R) {old new:Label (w+1)} (role:Fin nRoles)
 (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar) (p:Fin (w+1)) (hp:edgeVectors edge j p=1)
 (fits:ExplicitSeedBudget.roleBits≤q*w+r) (s u:State) (ticks:ℕ) : Prop where
 run : BoundedRuns P.program n x B s ticks u
 pc : u.pc=P.address .inverseTest
 control : UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
    (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
    (BG.groupCount q w r) (BG.groupCount q w r) u
 bank : UniformRecursiveGroupLoop.Bank q (BG.groupCount q w r) (F+4*2^(q*(w+1)+r))
    (BG.groupCount q w r) (FV.input q w r fits (edgeVectors edge j) p hp X) u
 permutation : (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
    ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val))
 entries : UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u
 nat : (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z)
 scalar : (∀z,z < F→u.scalarHeap z=s.scalarHeap z)
 source : u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r)
 permPointer : u.natReg 4067=F+2*2^(q*(w+1)+r)
 xorPointer : u.natReg 4068=F+3*2^(q*(w+1)+r)
 directionPointer : u.natReg 4062=T+8+j.val*(w+1)
 direction : UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u
 cursor : u.natReg 2850=T
 frontier : u.natReg 4123=F
 index : u.natReg 4134=j.val
 finish : u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length
 inverse : u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse
 dimension : u.natReg 4132=edge.dimension
 constants : UniformBinaryCStageMachine.Constants u
 roots : u.rootOrders=s.rootOrders
 outputs : u.outputs=s.outputs
 time : ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
    UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16+
    BG.groupCount q w r*(cost q+169)+1
 nativeBits : u.natReg 5300=q*(w+1)+r
 nativeRest : u.natReg 5301=r
 table : u.natReg 3389=s.natReg 3389
 first : ∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0

/-- Retain the whole original native child-loop footprint and metadata when
composing a first-pivot boot with a completed physical loop. -/
theorem children_of_loop (n B T nRoles R A F q w r stack depth stackTop : ℕ)
 (cost:ℕ→ℕ) (x:Fin n→ℂ) (s:State) (emb:Fin nRoles↪Fin R) {old new:Label (w+1)}
 (role:Fin nRoles) (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar) (p:Fin (w+1)) (hp:edgeVectors edge j p=1)
 (fits:ExplicitSeedBudget.roleBits≤q*w+r) (a u:State) (gt steps:ℕ)
 (br:BootResult n B T nRoles R A F q w r stack depth x emb role edge j X p hp s a gt)
 (run:BoundedRuns P.program n x B a steps u) (up:u.pc=P.address .inverseTest)
 (control:UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
  (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
  (BG.groupCount q w r) (BG.groupCount q w r) u)
 (bank:UniformRecursiveGroupLoop.Bank q (BG.groupCount q w r) (F+4*2^(q*(w+1)+r))
  (BG.groupCount q w r) (FV.input q w r fits (edgeVectors edge j) p hp X) u)
 (kept:∀z∈UniformRecursiveReturnStackMachine.fields,z≠4125→u.natReg z=a.natReg z)
 (frame:UniformRecursiveGroupLoop.Frame (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r))
  (F+5*2^(q*(w+1)+r)) stack depth stackTop a u)
 (cu:UniformBinaryCStageMachine.Constants u) (time:steps≤BG.groupCount q w r*(cost q+169)+1)
 (nativeBits:u.natReg 5300=q*(w+1)+r) (nativeRest:u.natReg 5301=r)
 (cursor:s.natReg 2850=T) (frontier:s.natReg 4123=F) (index:s.natReg 4134=j.val)
 (m2:2≤w+1) (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length≤F)
 (_stackEnd:stackTop≤F) (recordAbove:stackTop≤T) :
 ChildrenResult n B T nRoles R A F q w r stack depth stackTop cost x emb role edge j X p hp fits s u (gt+steps) := by
 rcases br with ⟨gr,gpc,gc,gdata,goutside,gperm,gentries,gnat,gdst,gpermptr,gxorptr,gkeep,
  gend,ginv,gdim,gro,gout,gdir,gsource,gtime,first⟩
 have reg(z:ℕ)(hz:z∈UniformRecursiveReturnStackMachine.fields)(ne:z≠4125):u.natReg z=a.natReg z:=kept z hz ne
 have physical:∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val):=by
  intro z
  rw [frame.nat _ (by have h:=z.isLt;omega) (Or.inr (by omega))]
  exact gperm z
 have smallTable:2^q*2^q ≤ 2^(q*(w+1)+r):=UniformRecursiveResidualGatherRecordMachine.table_fits q (w+1) r m2
 have entries:UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u:=by
  intro z hz
  rw [frame.nat _ (by omega) (Or.inr (by omega))]
  exact gentries z hz
 have source:UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u:=by
  intro z
  have dirEnd:=UniformRecursiveResidualGatherRecordMachine.direction_end T edge.dimension (w+1) j.val F j.isLt
   (by simpa only [UniformFixedNetworkScheduleMachine.Record.data_length,macroRecord,UniformFixedNetworkScheduleMachine.edgeBits_length,Nat.add_assoc] using recordEnd)
  rw [frame.nat _ (by have h:=z.isLt;omega) (Or.inr (by omega))]
  exact gsource z
 refine ⟨gr.trans run,up,control,bank,physical,entries,?_,?_,
  (reg _ (by decide) (by omega)).trans gdst,(reg _ (by decide) (by omega)).trans gpermptr,
  (reg _ (by decide) (by omega)).trans gxorptr,(reg _ (by decide) (by omega)).trans gdir,source,
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans cursor),
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans frontier),
  (reg _ (by decide) (by omega)).trans ((gkeep _ (by decide)).trans index),
  (reg _ (by decide) (by omega)).trans gend,(reg _ (by decide) (by omega)).trans ginv,
  (reg _ (by decide) (by omega)).trans gdim,cu,frame.roots.trans gro,frame.outputs.trans gout,?_,nativeBits,nativeRest,?_,first⟩
 · intro z hz away;exact (frame.nat z (by omega) away).trans (gnat z hz)
 · intro z hz;exact (frame.scalar z (by omega) (Or.inl (by omega))).trans (goutside z (Or.inl (by omega)))
 · omega
 · exact (reg _ (by decide) (by omega)).trans (gkeep _ (by decide))
end
end ExactFourierCircuits.DFTModelSavingNativeDirection
