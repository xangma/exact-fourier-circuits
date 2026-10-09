import UniformRecursiveResidualRecordPreparation
import UniformRecursiveRegisterFrames
import UniformResidualExtendedPermutation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualGatherRecordMachine
open UniformMachine UniformAssembly BinaryFrames
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
noncomputable section

def program : Program := UniformRecursiveResidualRecordPreparation.program.map (relocate 0 70)++
 UniformResidualGeneralGatherPreparation.program.map (relocate 70 365)++[.halt]
lemma program_length : program.length=366:=by
 simp only [program,List.length_append,List.length_map,UniformRecursiveResidualRecordPreparation.program_length,
  UniformResidualGeneralGatherPreparation.program_length,List.length_cons,List.length_nil]
lemma reader_code : CodeAt UniformRecursiveResidualRecordPreparation.program program 0 70:=by
 have h:=embed_code [] UniformRecursiveResidualRecordPreparation.program
  (UniformResidualGeneralGatherPreparation.program.map (relocate 70 365)++[.halt]) 70
 simpa only [embed,List.length_nil,List.nil_append,program,List.append_assoc] using h
lemma gather_code : CodeAt UniformResidualGeneralGatherPreparation.program program 70 365:=by
 let h:=UniformRecursiveResidualRecordPreparation.program.map (relocate 0 70)
 have len:h.length=70:=by simp only [h,List.length_map,UniformRecursiveResidualRecordPreparation.program_length]
 have code:=embed_code h UniformResidualGeneralGatherPreparation.program [.halt] 365
 unfold embed at code
 rw [len] at code
 simpa only [h,program,List.append_assoc] using code
lemma halt_at : program[365]?=some .halt:=by
 have len:(UniformRecursiveResidualRecordPreparation.program.map (relocate 0 70)++
 UniformResidualGeneralGatherPreparation.program.map (relocate 70 365)).length=365:=by
  simp only [List.length_append,List.length_map,UniformRecursiveResidualRecordPreparation.program_length,
   UniformResidualGeneralGatherPreparation.program_length]
 rw [program,List.getElem?_append_right (by omega),len];rfl

lemma table_fits (q m r:ℕ) (m2:2 ≤ m) : 2^q*2^q ≤ 2^(q*m+r):=by
 rw [←Nat.pow_add]
 have h:=Nat.mul_le_mul_left q m2
 apply Nat.pow_le_pow_right (by omega)
 omega
lemma native_padded (q m r B:ℕ) (qp:1 ≤ q) (rp:r < m) (square:(2^(q*m+r))^2 ≤ B) :
 2^(q*(m+r)) ≤ B:=by
 have h:=(UniformResidualExtendedPermutation.padded_bits q m r qp rp).2
 have powers:=Nat.pow_le_pow_right (by omega:1 ≤ 2) h
 have same:2^(2*(q*m+r))=(2^(q*m+r))^2:=by rw [mul_comm 2, Nat.pow_mul]
 exact (powers.trans_eq same).trans square
lemma data_end (A R V d F:ℕ) (hd:d < R) (endptr:A+R*V ≤ F) : A+d*V+V ≤ F:=by
 have h:=Nat.mul_le_mul_right V (by omega:d+1 ≤ R)
 rw [Nat.add_mul,Nat.one_mul] at h
 omega
lemma direction_end (T dimension m j F:ℕ) (hj:j < dimension) (endptr:T+8+dimension*m ≤ F) : T+8+j*m+m ≤ F:=by
 have h:=Nat.mul_le_mul_right m (by omega:j+1 ≤ dimension)
 rw [Nat.add_mul,Nat.one_mul] at h
 omega

lemma gather_preserves_q : ∀i∈UniformResidualGeneralGatherPreparation.program,UniformRecursiveRegisterFrames.Avoids 4060 i:=by
 have descriptor:∀i∈UniformResidualDescriptorBankMachine.program,UniformRecursiveRegisterFrames.Avoids 4060 i:=by
  intro i hi
  have safe:=UniformResidualDescriptorBankMachine.program_safe i hi
  cases i <;> simp_all [UniformResidualDescriptorBankMachine.Safe,UniformRecursiveRegisterFrames.Avoids] <;> omega
 simp only [UniformResidualGeneralGatherPreparation.program,UniformResidualGeneralPreparation.program,
  UniformResidualPermutationPreparation.program,UniformRecursiveRegisterFrames.append_iff,UniformRecursiveRegisterFrames.relocated_iff]
 repeat' constructor
 all_goals first
  | exact descriptor
  | exact UniformRecursiveRegisterFrames.code_of_all _ _ (by decide)

/-- A real printed macro is read, its selected residual vector is read from
that very body, and all native gather addresses/data are produced. There is
no supplied descriptor, basis/permutation/xor table or gathered child bank. -/
theorem execution (n B T nRoles R A F q w r:ℕ) (x:Fin n→ℂ) (s:State)
 (emb:Fin nRoles↪Fin R) {old new:Label (w+1)} (role:Fin nRoles)
 (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=0) (cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val) (base:s.natReg 3300=A)
 (volume:s.natReg 4122=2^(q*(w+1)+r)) (frontier:s.natReg 4123=F) (rest:s.natReg 4127=r)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q) (m2:2 ≤ w+1) (rp:r < w+1)
 (bound:WordBound B s) (code:366 ≤ B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B) (arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B) (square:(2^(q*(w+1)+r))^2 ≤ B) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 BoundedExecution program n x B s ticks u  ∧ 
 ticks ≤ UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+11  ∧  u.pc=365  ∧ 
 (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t))))  ∧ 
 (∀z,z < F+4*2^(q*(w+1)+r) ∨ F+5*2^(q*(w+1)+r) ≤ z→u.scalarHeap z=s.scalarHeap z)  ∧ 
 (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val))  ∧ 
 u.natReg 4015=2^q  ∧  u.natReg 4023=2^(q*(w+1)+r)  ∧ 
 u.natReg 4060=q  ∧  u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r)  ∧ 
 u.natReg 4091=F+4*2^(q*(w+1)+r)  ∧  u.natReg 4133=F+5*2^(q*(w+1)+r)  ∧ 
 u.rootOrders=s.rootOrders  ∧  u.outputs=s.outputs := by
 let record:=macroRecord q emb (.edge old new role edge)
 have good:UniformFixedNetworkOpcodeMachine.WellFormed record:=by
  constructor
  · change 0 < 7;omega
  · simp [record,macroRecord,UniformFixedNetworkOpcodeMachine.bodyLength,UniformFixedNetworkScheduleMachine.edgeBits_length]
 obtain ⟨read,rr,rpc,input,aa,dd,rem,fresh,nextptr,inv,dim,rnh,rsh,rsr,ro,rro⟩:=
  UniformRecursiveResidualRecordPreparation.execution n B T R A (2^(q*(w+1)+r)) F q (w+1) r edge.dimension (emb role).val j.val x s record
   rfl rfl rfl rfl rfl pc cursor printed good index j.isLt (emb role).isLt base volume frontier rest bound (by omega) recordEnd widthBound
   (arrayEnd.trans (by omega)) poolEnd
 have reader:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 70 ≤ B;omega) (by omega) rr
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
 have datapresent:∀z,z < 2^(q*(w+1)+r)→∃a,child.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z)=some a:=by
  intro z hz
  exact ⟨X ⟨z,hz⟩,by change read.scalarHeap _=some _;rw [rsh];exact data ⟨z,hz⟩⟩
 have dEnd:=data_end A R (2^(q*(w+1)+r)) (emb role).val F (emb role).isLt arrayEnd
 have recEnd:T+8+edge.dimension*(w+1) ≤ F:=by
  simpa only [UniformFixedNetworkScheduleMachine.Record.data_length,macroRecord,UniformFixedNetworkScheduleMachine.edgeBits_length,Nat.add_assoc] using recordEnd
 have dirEnd:=direction_end T edge.dimension (w+1) j.val F j.isLt recEnd
 have twice:=Nat.mul_le_pow (by omega:2≠1) (q*(w+1)+r)
 have kb:q*(w+1)+r ≤ 2^(q*(w+1)+r):=by omega
 have tableCap:=table_fits q (w+1) r m2
 have padded:=native_padded q (w+1) r B qp rp square
 obtain ⟨p,hp,gathered,gt,gr,gcost,gp,gvals,goutside,gaddresses,gro,go,gsz,gcount,gone,gnr,gptr⟩:=
  UniformResidualGeneralGatherPreparation.execution n B q w r (T+8+j.val*(w+1)) F
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
 have kept(i:ℕ)(hi:((i < 3350 ∨ 3446 < i) ∧ (i < 4000 ∨ 4081 < i) ∧ (i < 4101 ∨ 4104 < i))):gathered.natReg i=read.natReg i:=gnr i hi
 refine ⟨p,hp,u,UniformFixedNetworkOpcodeMachine.headCost record+18+gt+1,?_,?_,rfl,?_,?_,gaddresses,gsz,gcount,keptq.trans qval,
  (kept _ (by omega)).trans aa,(kept _ (by omega)).trans dd,(kept _ (by omega)).trans fresh,gro.trans rro,go.trans ro⟩
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
end
end ExactFourierCircuits.UniformRecursiveResidualGatherRecordMachine
