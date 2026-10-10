import UniformRecursiveResidualBoot
import DFTModelSavingNativePivotRecordFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualBoot
open UniformMachine UniformAssembly BinaryFrames
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
open UniformNatBlockMachine (applyBlock Op BlockAt)
noncomputable section

/-- Same actual bytecode and original execution contract, retaining the least nonzero pivot fact. -/
theorem generic_execution_first (main:Program)(start boot test n B T nRoles R A F q w r stack depth:ℕ)
 (x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}(role:Fin nRoles)
 (edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (gcode:CodeAt UniformRecursiveResidualGatherRecordMachine.program main start boot)
 (bcode:BlockAt BG.bootGroups main boot)(after:boot+5=test)
 (pc:s.pc=start)(cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val)(base:s.natReg 3300=A)(original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r)(volume:s.natReg 4122=2^(q*(w+1)+r))
 (frontier:s.natReg 4123=F)(rest:s.natReg 4127=r)
 (st:s.natReg 4150=stack)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (bound:WordBound B s)(code:start+366 ≤ B)(bextent:boot+5 ≤ B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B):
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 BoundedRuns main n x B s ticks u ∧ u.pc=test ∧
 UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
  (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
  (BG.groupCount q w r) 0 u ∧
 (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t)))) ∧
 (∀z,z < F+4*2^(q*(w+1)+r)∨F+5*2^(q*(w+1)+r) ≤ z→u.scalarHeap z=s.scalarHeap z) ∧
 (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val)) ∧
 UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u ∧
 (∀z,z < F→u.natHeap z=s.natHeap z) ∧
 u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r) ∧
 u.natReg 4067=F+2*2^(q*(w+1)+r) ∧ u.natReg 4068=F+3*2^(q*(w+1)+r) ∧
 (∀z,z∈UniformRecursiveResidualGatherFrame.keptRegisters→u.natReg z=s.natReg z) ∧
 u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length ∧
 u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse ∧ u.natReg 4132=edge.dimension ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 u.natReg 4062=T+8+j.val*(w+1) ∧
 UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u ∧
 ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16 ∧
 (∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0):=by
 let localState:State:={s with pc:=0}
 have lb:=changePC_bound B s 0 bound (by omega)
 obtain ⟨p,hp,a,gt,gr,gtime,gpc,gdata,goutside,gperm,gsize,gvol,gq,gdst,gbase,gfresh,gro,gout,
  gentries,gnat,gwidth,gpermptr,gxorptr,gkeep,gend,ginv,gdim,gone,gdir,gsource,first⟩:=
  UniformRecursiveResidualGatherFrame.execution_frame_first n B T nRoles R A F q w r x localState emb role edge j X
   rfl cursor printed index base volume frontier rest data qp m2 rp lb (by omega) recordEnd widthBound arrayEnd poolEnd square
 have moved:=UniformBoundedAssembly.boundedExecution_placed gcode
  (by simpa only [UniformRecursiveResidualGatherRecordMachine.program_length] using code) (by omega) gr
 have entry:placed start localState=s:=by
  change {s with pc:=start}=s
  rw [←pc]
 rw [entry] at moved
 let arrived:State:={a with pc:=boot}
 have bootRun:=BG.initialize_execution main boot n B q w r (F+4*2^(q*(w+1)+r)) x arrived bcode rfl gsize gvol gone fits
  moved.final_bound bextent (by omega)
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
 refine ⟨p,hp,u,gt+5,moved.trans bootRun.1,?_,control,gdata,goutside,gperm,gentries,gnat,
  (unchanged _ (by omega)).trans gdst,(unchanged _ (by omega)).trans gpermptr,
  (unchanged _ (by omega)).trans gxorptr,kept,(unchanged _ (by omega)).trans gend,
  (unchanged _ (by omega)).trans ginv,(unchanged _ (by omega)).trans gdim,gro,gout,(unchanged _ (by omega)).trans gdir,gsource,?_,first⟩
 · exact (boot_pc arrived).trans after
 · omega

theorem execution_first (n B T nRoles R A F q w r stack depth:ℕ)
 (x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}(role:Fin nRoles)
 (edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=P.address .gather)(cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val)(base:s.natReg 3300=A)(original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r)(volume:s.natReg 4122=2^(q*(w+1)+r))
 (frontier:s.natReg 4123=F)(rest:s.natReg 4127=r)
 (st:s.natReg 4150=stack)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (bound:WordBound B s)(code:P.program.length ≤ B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B):
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .groupTest ∧
 UniformRecursiveGroupLoop.Control (q*(w+1)+r) q (w+1) r A
  (F+4*2^(q*(w+1)+r)) (2^(q*(w+1)+r)) (F+5*2^(q*(w+1)+r)) stack depth
  (BG.groupCount q w r) 0 u ∧
 (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t)))) ∧
 (∀z,z < F+4*2^(q*(w+1)+r)∨F+5*2^(q*(w+1)+r) ≤ z→u.scalarHeap z=s.scalarHeap z) ∧
 (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val)) ∧
 UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u ∧
 (∀z,z < F→u.natHeap z=s.natHeap z) ∧
 u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r) ∧
 u.natReg 4067=F+2*2^(q*(w+1)+r) ∧ u.natReg 4068=F+3*2^(q*(w+1)+r) ∧
 (∀z,z∈UniformRecursiveResidualGatherFrame.keptRegisters→u.natReg z=s.natReg z) ∧
 u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length ∧
 u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse ∧ u.natReg 4132=edge.dimension ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 u.natReg 4062=T+8+j.val*(w+1) ∧
 UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u ∧
 ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+16 ∧
 (∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0):=by
 exact generic_execution_first P.program (P.address .gather) (P.address .bootGroups) (P.address .groupTest)
  n B T nRoles R A F q w r stack depth x s emb role edge j X UniformRecursiveSavingProgram.gather_code
  boot_code UniformRecursiveAdjacent.boot_after pc cursor printed index base original bits volume frontier rest st dp one
  data qp m2 rp fits bound (UniformRecursiveParentReturn.code_bound .gather 366 B rfl code)
  (UniformRecursiveParentReturn.code_bound .bootGroups 5 B rfl code) recordEnd widthBound arrayEnd poolEnd square

end
end ExactFourierCircuits.UniformRecursiveResidualBoot
