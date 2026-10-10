import DFTModelSavingNativeDirectionGather
import DFTModelSavingNativePivotBoot

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
open UniformNatBlockMachine (applyBlock Op BlockAt)
open UniformRecursiveResidualBoot (boot_kept boot_pc)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
namespace BG
export UniformRecursiveBatchGroupMachine (bootGroups groupCount W initialize_execution)
end BG
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

structure BootResult (n B T nRoles R A F q w r stack depth : ℕ) (x : Fin n→ℂ)
 (emb : Fin nRoles↪Fin R) {old new : Label (w+1)} (role : Fin nRoles)
 (edge : NestedEdge old new) (j : Fin edge.dimension)
 (X : Fin (2^(q*(w+1)+r))→Scalar) (p : Fin (w+1)) (hp : edgeVectors edge j p=1)
 (s u : State) (ticks : ℕ) : Prop where
 run : BoundedRuns P.program n x B s ticks u
 pc : u.pc=P.address .groupTest
 control : UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
    (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
    (BG.groupCount q w r) 0 u
 data : (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
    some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t))))
 outside : (∀z,z < F+4*2^(q*(w+1)+r)∨F+5*2^(q*(w+1)+r) ≤ z→u.scalarHeap z=s.scalarHeap z)
 permutation : (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
    ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val))
 entries : UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u
 nat : (∀z,z < F→u.natHeap z=s.natHeap z)
 source : u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r)
 permPointer : u.natReg 4067=F+2*2^(q*(w+1)+r)
 xorPointer : u.natReg 4068=F+3*2^(q*(w+1)+r)
 kept : (∀z,z∈UniformRecursiveResidualGatherFrame.keptRegisters→u.natReg z=s.natReg z)
 finish : u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length
 inverse : u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse
 dimension : u.natReg 4132=edge.dimension
 roots : u.rootOrders=s.rootOrders
 outputs : u.outputs=s.outputs
 directionPointer : u.natReg 4062=T+8+j.val*(w+1)
 direction : UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u
 time : ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
    UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16
 first : (∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0)

private lemma placed_reset (s:State) (start:ℕ) (pc:s.pc=start) : placed start {s with pc:=0}=s := by
 change {s with pc:=start}=s
 rw [←pc]

/-- Append the real five group-header operations to the already produced
standalone gather, retaining its chosen physical pivot and exact Scalars. -/
theorem boot_of_gather (n B T nRoles R A F q w r stack depth : ℕ)
 (x : Fin n→ℂ) (s : State) (emb : Fin nRoles↪Fin R) {old new : Label (w+1)}
 (role : Fin nRoles) (edge : NestedEdge old new) (j : Fin edge.dimension)
 (X : Fin (2^(q*(w+1)+r))→Scalar) (p : Fin (w+1)) (hp : edgeVectors edge j p=1)
 (a : State) (gt : ℕ)
 (g : GatherResult n B T nRoles R A F q w r x emb role edge j X p hp {s with pc:=0} a gt)
 (pc : s.pc=P.address .gather) (base:s.natReg 3300=A) (original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r) (volume:s.natReg 4122=2^(q*(w+1)+r))
 (rest:s.natReg 4127=r) (st:s.natReg 4150=stack) (dp:s.natReg 4151=depth) (one:s.natReg 4153=1)
 (fits:ExplicitSeedBudget.roleBits≤q*w+r) (code:P.program.length≤B)
 (poolEnd:F+5*2^(q*(w+1)+r)≤B) :
 ∃u,BootResult n B T nRoles R A F q w r stack depth x emb role edge j X p hp s u (gt+5) := by
 let localState:State:={s with pc:=0}
 rcases g with ⟨gr,gtime,gpc,gdata,goutside,gperm,gsize,gvol,gq,gdst,gbase,gfresh,gro,gout,
  gentries,gnat,gwidth,gpermptr,gxorptr,gkeep,gend,ginv,gdim,gone,gdir,gsource,first⟩
 have gatherExtent:P.address .gather+366≤B:=UniformRecursiveParentReturn.code_bound .gather 366 B rfl code
 have moved:=UniformBoundedAssembly.boundedExecution_placed UniformRecursiveSavingProgram.gather_code
  (by simpa only [UniformRecursiveResidualGatherRecordMachine.program_length] using gatherExtent)
  (UniformRecursiveParentReturn.start_bound .bootGroups B code) gr
 have entry:placed (P.address .gather) localState=s:=placed_reset s _ pc
 rw [entry] at moved
 let arrived:State:={a with pc:=P.address .bootGroups}
 have bootRun:=BG.initialize_execution P.program (P.address .bootGroups) n B q w r (F+4*2^(q*(w+1)+r))
  x arrived UniformRecursiveResidualBoot.boot_code rfl gsize gvol gone fits moved.final_bound
  (UniformRecursiveParentReturn.code_bound .bootGroups 5 B rfl code) (by omega)
 let u:=applyBlock BG.bootGroups arrived
 have kept(z:ℕ)(hz:z∈UniformRecursiveResidualGatherFrame.keptRegisters):u.natReg z=s.natReg z:=by
  have safe:z≠4164∧z≠4165∧z≠4126∧z≠4125∧z≠4124:=by
   simp only [UniformRecursiveResidualGatherFrame.keptRegisters,List.mem_cons,List.not_mem_nil,or_false] at hz
   omega
  exact (boot_kept arrived z safe).trans (gkeep z hz)
 have unchanged(z:ℕ)(safe:z≠4164∧z≠4165∧z≠4126∧z≠4125∧z≠4124):u.natReg z=a.natReg z:=boot_kept arrived z safe
 have control:UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
  (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth (BG.groupCount q w r) 0 u:=by
  refine ⟨bootRun.2.2.1,bootRun.2.1,(unchanged _ (by omega)).trans gq,(unchanged _ (by omega)).trans gsize,
   bootRun.2.2.2.1,(unchanged _ (by omega)).trans gbase,(unchanged _ (by omega)).trans gfresh,
   (kept _ (by decide)).trans st,(kept _ (by decide)).trans dp,(kept _ (by decide)).trans one,
   (kept _ (by decide)).trans bits,(kept _ (by decide)).trans rest,(kept _ (by decide)).trans original,
   (kept _ (by decide)).trans volume,(unchanged _ (by omega)).trans gwidth,(kept _ (by decide)).trans base⟩
 refine ⟨u,⟨moved.trans bootRun.1,?_,control,gdata,goutside,gperm,gentries,gnat,
  (unchanged _ (by omega)).trans gdst,(unchanged _ (by omega)).trans gpermptr,
  (unchanged _ (by omega)).trans gxorptr,kept,(unchanged _ (by omega)).trans gend,
  (unchanged _ (by omega)).trans ginv,(unchanged _ (by omega)).trans gdim,gro,gout,
  (unchanged _ (by omega)).trans gdir,gsource,?_,first⟩⟩
 · exact (boot_pc arrived).trans UniformRecursiveAdjacent.boot_after
 · omega

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
