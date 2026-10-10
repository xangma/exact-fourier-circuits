import UniformRecursiveResidualGatherFrame
import DFTModelSavingNativePivotGatherFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualGatherFrame
open UniformMachine UniformAssembly BinaryFrames
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
open UniformRecursiveResidualGatherRecordMachine
noncomputable section

/-- Same actual bytecode and original execution contract, retaining the least nonzero pivot fact. -/
theorem execution_frame_first (n B T nRoles R A F q w r:ℕ) (x:Fin n→ℂ) (s:State)
 (emb:Fin nRoles↪Fin R) {old new:Label (w+1)} (role:Fin nRoles)
 (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=0) (cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val) (base:s.natReg 3300=A)
 (volume:s.natReg 4122=2^(q*(w+1)+r)) (frontier:s.natReg 4123=F) (rest:s.natReg 4127=r)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1  ≤  q) (m2:2  ≤  w+1) (rp:r  <  w+1)
 (bound:WordBound B s) (code:366  ≤  B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length  ≤  F)
 (widthBound:(w+1)+1  ≤  B) (arrayEnd:A+R*2^(q*(w+1)+r)  ≤  F)
 (poolEnd:F+5*2^(q*(w+1)+r)  ≤  B) (square:(2^(q*(w+1)+r))^2  ≤  B) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 BoundedExecution program n x B s ticks u  ∧
 ticks  ≤  UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+11  ∧  u.pc=365  ∧
 (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t))))  ∧
 (∀z,z  <  F+4*2^(q*(w+1)+r) ∨ F+5*2^(q*(w+1)+r)  ≤  z→u.scalarHeap z=s.scalarHeap z)  ∧
 (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val))  ∧
 u.natReg 4015=2^q  ∧  u.natReg 4023=2^(q*(w+1)+r)  ∧
 u.natReg 4060=q  ∧  u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r)  ∧
 u.natReg 4091=F+4*2^(q*(w+1)+r)  ∧  u.natReg 4133=F+5*2^(q*(w+1)+r)  ∧
 u.rootOrders=s.rootOrders  ∧  u.outputs=s.outputs ∧
 UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u ∧
 (∀z,z < F→u.natHeap z=s.natHeap z) ∧
 u.natReg 4061=w+1 ∧ u.natReg 4067=F+2*2^(q*(w+1)+r) ∧ u.natReg 4068=F+3*2^(q*(w+1)+r) ∧
 (∀z,z∈keptRegisters→u.natReg z=s.natReg z) ∧
 u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length ∧
 u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse ∧ u.natReg 4132=edge.dimension ∧ u.natReg 4069=1 ∧
 u.natReg 4062=T+8+j.val*(w+1) ∧
 UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u ∧
 (∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0) := by
 let record:=macroRecord q emb (.edge old new role edge)
 have good:UniformFixedNetworkOpcodeMachine.WellFormed record:=by
  constructor
  · change 0  <  7;omega
  · simp [record,macroRecord,UniformFixedNetworkOpcodeMachine.bodyLength,UniformFixedNetworkScheduleMachine.edgeBits_length]
 obtain ⟨read,rr,rpc,input,aa,dd,rem,fresh,nextptr,inv,dim,rnh,rsh,rsr,ro,rro⟩:=
  UniformRecursiveResidualRecordPreparation.execution n B T R A (2^(q*(w+1)+r)) F q (w+1) r edge.dimension (emb role).val j.val x s record
   rfl rfl rfl rfl rfl pc cursor printed good index j.isLt (emb role).isLt base volume frontier rest bound (by omega) recordEnd widthBound
   (arrayEnd.trans (by omega)) poolEnd
 have reader:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 70  ≤  B;omega) (by omega) rr
 have zero:placed 0 s=s:=by simp [placed]
 rw [zero] at reader
 let child:State:={read with pc:=0}
 have cb:=changePC_bound B read 0 rr.final_bound (by omega)
 have gi:UniformResidualPermutationPreparation.Inputs q (w+1) (T+8+j.val*(w+1)) F
  (F+2^(q*(w+1)+r)) (F+2*2^(q*(w+1)+r)) (F+3*2^(q*(w+1)+r)) child:=
  ⟨⟨input.descriptor.columns,input.descriptor.width,input.descriptor.direction,input.descriptor.images⟩,input.stack,input.output,input.table⟩
 have dsource:=UniformRecursiveResidualRecordPreparation.edge_direction q T emb role edge j s printed
 have physical:UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) child:=by
  intro i
  change read.natHeap _=some _
  rw [rnh]
  exact dsource.1 i
 have datapresent:∀z,z  <  2^(q*(w+1)+r)→∃a,child.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z)=some a:=by
  intro z hz
  exact ⟨X ⟨z,hz⟩,by change read.scalarHeap _=some _;rw [rsh];exact data ⟨z,hz⟩⟩
 have dEnd:=data_end A R (2^(q*(w+1)+r)) (emb role).val F (emb role).isLt arrayEnd
 have recEnd:T+8+edge.dimension*(w+1)  ≤  F:=by
  simpa only [UniformFixedNetworkScheduleMachine.Record.data_length,macroRecord,UniformFixedNetworkScheduleMachine.edgeBits_length,Nat.add_assoc] using recordEnd
 have dirEnd:=direction_end T edge.dimension (w+1) j.val F j.isLt recEnd
 have twice:=Nat.mul_le_pow (by omega:2≠1) (q*(w+1)+r)
 have kb:q*(w+1)+r  ≤  2^(q*(w+1)+r):=by omega
 have tableCap:=table_fits q (w+1) r m2
 have padded:=native_padded q (w+1) r B qp rp square
 obtain ⟨p,hp,gathered,gt,gr,gcost,gp,gvals,goutside,gaddresses,gro,go,gsz,gcount,gone,gnr,gptr,gentries,gnatOutside,gwidth,goutput,gtable,first⟩:=
  UniformResidualGeneralGatherFrame.execution_frame_first n B q w r (T+8+j.val*(w+1)) F
   (F+2^(q*(w+1)+r)) (F+2*2^(q*(w+1)+r)) (F+3*2^(q*(w+1)+r))
   (A+(emb role).val*2^(q*(w+1)+r)) (F+4*2^(q*(w+1)+r)) (edgeVectors edge j) x child rfl gi rem qp dsource.2 physical aa dd datapresent
   (Or.inl (by omega)) cb (by omega) dirEnd (by omega) (by omega) (by omega) (by omega) padded (by omega) (by omega)
 have gather:=UniformBoundedAssembly.boundedExecution_placed gather_code (by rw [UniformResidualGeneralGatherPreparation.program_length];omega) (by omega) gr
 have same:placed 70 child={read with pc:=70}:=rfl
 rw [same] at gather
 let u:State:={gathered with pc:=365}
 have stop:BoundedExecution program n x B u 1 u:=.halt gather.final_bound (by simp [step,u,halt_at])
 have keptq:gathered.natReg 4060=child.natReg 4060:=UniformRecursiveRegisterFrames.boundedExecution_keep
  gather_preserves_q gr
 have qval:child.natReg 4060=q:=input.descriptor.columns
 have kept(i:ℕ)(hi:((i  <  3350 ∨ 3446  <  i) ∧ (i  <  4000 ∨ 4081  <  i) ∧ (i  <  4101 ∨ 4104  <  i))):gathered.natReg i=read.natReg i:=gnr i hi
 refine ⟨p,hp,u,UniformFixedNetworkOpcodeMachine.headCost record+18+gt+1,?_,?_,rfl,?_,?_,gaddresses,gsz,gcount,keptq.trans qval,
  (kept _ (by omega)).trans aa,(kept _ (by omega)).trans dd,(kept _ (by omega)).trans fresh,gro.trans rro,go.trans ro,gentries,?_,gwidth,goutput,gtable,?_,?_,?_,?_,gone,?_,?_,first⟩
 · exact (reader.trans gather).executes stop
 · dsimp only [record];omega
 · intro b t
   have val:=gvals (UniformResidualExtendedPermutation.flat q w r (b,t))
   rw [UniformResidualExtendedPermutation.fibers_flat] at val
   have heap:child.scalarHeap=s.scalarHeap:=rsh
   rw [heap] at val
   simpa only [u,UniformResidualExtendedPermutation.flat_value,Nat.add_assoc] using val.trans
    (data (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t)))
 · intro z hz
   exact (goutside z (by unfold UniformResidualArrayCopyMachine.Outside at goutside;omega)).trans (congrFun rsh z)
 · intro z hz
   exact (gnatOutside z (Or.inl hz)).trans (congrFun rnh z)
 · intro z hz
   have readKeep:read.natReg z=s.natReg z:=UniformRecursiveRegisterFrames.boundedExecution_keep (reader_avoids z hz) rr
   by_cases eq:z=3389
   · subst z
     exact (UniformRecursiveRegisterFrames.boundedExecution_keep gather_preserves_table gr).trans readKeep
   have gsafe:((z  <  3350 ∨ 3446  <  z) ∧ (z  <  4000 ∨ 4081  <  z) ∧ (z  <  4101 ∨ 4104  <  z)):=by
    simp only [keptRegisters,List.mem_cons,List.not_mem_nil,or_false] at hz
    omega
   exact (gnr z gsafe).trans readKeep

 · exact (kept 4130 (by omega)).trans nextptr
 · exact (kept 4131 (by omega)).trans inv
 · exact (kept 4132 (by omega)).trans dim
 · exact (UniformRecursiveRegisterFrames.boundedExecution_keep gather_preserves_direction gr).trans input.descriptor.direction
 · intro i
   exact (gnatOutside _ (Or.inl (by have hi:=i.isLt;omega))).trans
    ((congrFun rnh _).trans (dsource.1 i))

end
end ExactFourierCircuits.UniformRecursiveResidualGatherFrame
