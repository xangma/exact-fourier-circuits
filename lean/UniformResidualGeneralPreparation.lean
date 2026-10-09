import UniformResidualImagePreparation
import UniformResidualSpectatorBankMachine
import UniformResidualSpectators
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualGeneralPreparation
open UniformMachine UniformAssembly BinaryFrames UniformBinaryXorCoordinates
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def program : Program := UniformResidualPermutationPreparation.program.map (relocate 0 188)++
 UniformResidualSpectatorBankMachine.program.map (relocate 188 201)++
 UniformResidualFiberAddressMachine.program.map (relocate 201 272)++[.halt]
theorem program_length : program.length=273 := by simp only [program,List.length_append,List.length_map,
 UniformResidualPermutationPreparation.program_length,UniformResidualSpectatorBankMachine.program_length,
 UniformResidualFiberAddressMachine.program_length,List.length_cons,List.length_nil]
theorem preparation_code : CodeAt UniformResidualPermutationPreparation.program program 0 188 := by
 have h:=embed_code [] UniformResidualPermutationPreparation.program
  (UniformResidualSpectatorBankMachine.program.map (relocate 188 201)++UniformResidualFiberAddressMachine.program.map (relocate 201 272)++[.halt]) 188
 simpa only [embed,List.length_nil,List.nil_append,program,List.append_assoc] using h
theorem spectator_code : CodeAt UniformResidualSpectatorBankMachine.program program 188 201 := by
 let head:=UniformResidualPermutationPreparation.program.map (relocate 0 188)
 have len:head.length=188:=by simp only [head,List.length_map,UniformResidualPermutationPreparation.program_length]
 have h:=embed_code head UniformResidualSpectatorBankMachine.program
  (UniformResidualFiberAddressMachine.program.map (relocate 201 272)++[.halt]) 201
 unfold embed at h;rw [len] at h
 simpa only [head,program,List.append_assoc] using h
theorem dfs_code : CodeAt UniformResidualFiberAddressMachine.program program 201 272 := by
 let head:=UniformResidualPermutationPreparation.program.map (relocate 0 188)++UniformResidualSpectatorBankMachine.program.map (relocate 188 201)
 have len:head.length=201:=by simp only [head,List.length_append,List.length_map,
  UniformResidualPermutationPreparation.program_length,UniformResidualSpectatorBankMachine.program_length]
 have h:=embed_code head UniformResidualFiberAddressMachine.program [.halt] 272
 unfold embed at h;rw [len] at h
 simpa only [head,program,List.append_assoc] using h
theorem halt_at : program[272]?=some .halt:=by
 let pre:=UniformResidualPermutationPreparation.program.map (relocate 0 188)++
  UniformResidualSpectatorBankMachine.program.map (relocate 188 201)++
  UniformResidualFiberAddressMachine.program.map (relocate 201 272)
 have plen:pre.length=272:=by simp only [pre,List.length_append,List.length_map,
  UniformResidualPermutationPreparation.program_length,UniformResidualSpectatorBankMachine.program_length,
  UniformResidualFiberAddressMachine.program_length]
 have eq:program=pre++[.halt]:=by simp only [program,pre,List.append_assoc]
 rw [eq,List.getElem?_append_right (by omega)]
 simp [plen]

def image (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (i:ℕ) : ℕ :=
 if hi:i< k+r then (UniformResidualSpectators.extend k r F (encode (unit ⟨i,hi⟩))).val else 0
lemma low_image (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (i:ℕ) (hi:i< k) :
 image k r F i=(F (encode (unit (⟨i,hi⟩:Fin k)))).val := by
 have big:i< k+r:=by omega
 simp only [image,dite_eq_left big]
 have eq:encode (unit (⟨i,big⟩:Fin (k+r)))=
  (⟨(encode (unit (⟨i,hi⟩:Fin k))).val,(encode (unit (⟨i,hi⟩:Fin k))).isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩:Fin (2^(k+r))):=by
  apply Fin.ext;simp [UniformResidualPermutation.encode_unit]
 rw [eq,UniformResidualSpectators.extend_low]
lemma high_image (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0) (i:ℕ) (lo:k≤ i) (hi:i< k+r) :
 image k r F i=2^i:=by
 let j:Fin r:=⟨i-k,by omega⟩
 have eq:k+j.val=i:=by simp [j];omega
 simp only [image,dite_eq_left hi]
 have units:encode (unit (⟨i,hi⟩:Fin (k+r)))=encode (unit (⟨k+j.val,by omega⟩:Fin (k+r))):=by congr 2;apply Fin.ext;exact eq.symm
 rw [units,UniformResidualSpectators.extend_high_unit k r F zero j,eq]
lemma address_eq (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0)
 (add:∀a b,F (xorIndex a b)=xorIndex (F a) (F b)) (j:Fin (2^(k+r))) :
 UniformResidualFiberTraversal.address (image k r F) (k+r) 0 j.val=(UniformResidualSpectators.extend k r F j).val:=by
 have h:=UniformResidualPermutation.address_of_xor_equiv (UniformResidualSpectators.extend k r F)
  (UniformResidualSpectators.extend_zero k r F zero) (UniformResidualSpectators.extend_xor k r F add)
  (image k r F) (by intro i;simp [image,i.isLt]) (k+r) 0 j.val (by omega) j.isLt
 simpa using h

def runtimeBound (q m r:ℕ) := UniformResidualPermutationPreparation.runtimeBound q m+(7*r+7)+
 (UniformResidualFiberAddressMachine.treeCost (m+r) (q*m+r)+9)+1

def RegFrame (s u:State) : Prop := ∀i,((i< 3350 ∨ 3446< i) ∧ (i< 4000 ∨ 4069< i) ∧ (i< 4101 ∨ 4104< i))→ u.natReg i=s.natReg i

/-- One native traversal includes all r spectator bits. The child arrays have
q innermost coordinates; no spectator is dropped or separately padded. -/
theorem execution (n B q w r U images stack output table:ℕ) (v:Vec (Fin (w+1))) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=0) (input:UniformResidualPermutationPreparation.Inputs q (w+1) U images stack output table s)
 (rest:s.natReg 4100=r) (qp:1≤ q) (nonzero:v≠0) (source:UniformRepeatedMaskMachine.Source U v s)
 (bound:WordBound B s) (code:273≤ B) (sourceEnd:U+(w+1)≤ images)
 (imagesBefore:images+(q*(w+1)+r)≤ stack) (stackBefore:stack+2*(q*(w+1)+r)≤ output)
 (outputBefore:output+2^(q*(w+1)+r)≤ table) (tableBound:table+2^q*2^q≤ B)
 (paddedVolume:2^(q*((w+1)+r))≤ B) :
 ∃p:Fin (w+1),∃hp:v p=1,∃u ticks,BoundedExecution program n x B s ticks u ∧
 ticks≤ runtimeBound q (w+1) r ∧
 u.pc=272 ∧ u.natReg 4023=2^(q*(w+1)+r) ∧
 (∀j:Fin (2^(q*(w+1)+r)),u.natHeap (output+j.val)=some
  ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp) j).val)) ∧
 UniformRepeatedMaskMachine.Source U v u ∧ UniformXorTableMachine.Entries q table (2^q*2^q) u ∧
 (∀z,z< images ∨ table+2^q*2^q≤ z→ u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 u.natReg 4069=1 ∧ u.natReg 4067=output ∧ RegFrame s u ∧ u.natReg 4015=2^q := by
 have tableB:table≤ B:=(Nat.le_add_right table _).trans tableBound
 have volume:2^(q*(w+1)+r)≤ B:=(Nat.le_add_left _ output).trans (outputBefore.trans tableB)
 have outputB:output≤ B:=(Nat.le_add_right output _).trans (outputBefore.trans tableB)
 have stackB:stack≤ B:=(Nat.le_add_right stack _).trans (stackBefore.trans outputB)
 have oldVol:2^(q*(w+1))≤ 2^(q*(w+1)+r):=Nat.pow_le_pow_right (by omega) (by omega)
 obtain ⟨p,hp,prepared,pt,pr,pcost,pp,_,count,one,pointer,addresses,entries,retained,oldImages,outside,sh,sr,ou,ro,nr,header⟩:=
  UniformResidualPermutationPreparation.execution_images n B q w U images stack output table v x s pc input qp nonzero source
   bound (by omega) sourceEnd (by omega) (by omega) (by have h:=Nat.add_le_add_left oldVol output;exact h.trans outputBefore) tableBound
 have prep:=UniformBoundedAssembly.boundedExecution_placed preparation_code (by rw [UniformResidualPermutationPreparation.program_length];omega) (by omega) pr
 have same:placed 0 s=s:=by simp only [placed,Nat.zero_add]
 rw [same] at prep
 let appendChild:State:={prepared with pc:=0}
 have appendBound:=changePC_bound B prepared 0 pr.final_bound (by omega)
 have restNow:appendChild.natReg 4100=r:=(nr _ (by omega)).trans rest
 have newWidth:(w+1)+r≤ B:=by
  have le:(w+1)+r≤ q*(w+1)+r:=by nlinarith
  have lv:q*(w+1)+r≤ 2^(q*(w+1)+r):=Nat.le_of_lt Nat.lt_two_pow_self
  exact le.trans (lv.trans volume)
 obtain ⟨extended,er,ep,ek,ew,newImages,ef,esh,esr,eo,ero,enr⟩:=
  UniformResidualSpectatorBankMachine.execution n B (q*(w+1)) r (w+1) images x appendChild rfl restNow
   header.bits header.images one count header.width appendBound (by omega) (by simpa only [Nat.add_assoc] using imagesBefore.trans stackB) volume newWidth
 have appended:=UniformBoundedAssembly.boundedExecution_placed spectator_code (by change 201≤ B;omega) (by omega) er
 have ae:placed 188 appendChild={prepared with pc:=188}:=rfl
 rw [ae] at appended
 let dfsChild:State:={extended with pc:=0}
 have db:=changePC_bound B extended 0 er.final_bound (by omega)
 have keep (i:ℕ) (hi:i< 4101 ∨ 4104< i) (h8:i≠4008) (h14:i≠4014):extended.natReg i=prepared.natReg i:=enr i hi h8 h14
 have args:UniformResidualFiberTraversal.Inputs (q*(w+1)+r) q ((w+1)+r) images stack output table dfsChild:=
  ⟨ek,(keep _ (by omega) (by omega) (by omega)).trans header.images,
   (keep _ (by omega) (by omega) (by omega)).trans header.stack,
   (keep _ (by omega) (by omega) (by omega)).trans header.output,
   (keep _ (by omega) (by omega) (by omega)).trans header.table,ew,
   (keep _ (by omega) (by omega) (by omega)).trans header.size⟩
 let F:=UniformResidualPermutation.permutation q w v p hp
 have zero:F 0=0:=UniformResidualPermutation.permutation_zero q w v p hp
 have imageBank:∀i,i< q*(w+1)+r→ dfsChild.natHeap (images+i)=some (image (q*(w+1)) r F i):=by
  intro i hi
  by_cases low:i< q*(w+1)
  · have eh:=ef (images+i) (by left;omega)
    rw [eh,oldImages i low,UniformResidualPermutation.image,dite_eq_left low,low_image _ _ _ _ low]
  · have jlt:i-q*(w+1)< r:=by omega
    have written:=newImages (⟨i-q*(w+1),jlt⟩:Fin r)
    have value:q*(w+1)+(i-q*(w+1))=i:=by omega
    simpa [Nat.add_assoc,value,high_image _ _ _ zero i (by omega) hi] using written
 have nativeWithin:q*(w+1)+r≤ q*((w+1)+r):=by nlinarith
 have small:∀i,i< q*(w+1)+r→ image (q*(w+1)) r F i< 2^(q*((w+1)+r)):=by
  intro i hi
  simp only [image,dite_eq_left hi]
  exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by omega) nativeWithin)
 have entriesNow:UniformXorTableMachine.Entries q table (2^q*2^q) dfsChild:=by
  intro i hi
  exact (ef (table+i) (by right;omega)).trans (entries i hi)
 obtain ⟨addressed,ar,ap,actualCount,written,af,ash,asr,ao,aro,actualHeader⟩:=
  UniformResidualFiberTraversal.execution_headers n B (q*(w+1)+r) q ((w+1)+r) images stack output table
   (image (q*(w+1)) r F) x dfsChild rfl args db (by omega) imagesBefore stackBefore outputBefore tableBound paddedVolume imageBank small entriesNow
 have df:=UniformResidualFiberTraversal.execution_frame ar.executes
 have placedDFS:=UniformBoundedAssembly.boundedExecution_placed dfs_code (by change 272≤ B;omega) (by omega) ar
 have deq:placed 201 dfsChild={extended with pc:=201}:=rfl
 rw [deq] at placedDFS
 let u:State:={addressed with pc:=272}
 have finish:BoundedExecution program n x B u 1 u:=.halt placedDFS.final_bound (by simp [step,u,halt_at])
 refine ⟨p,hp,u,pt+(7*r+7)+(UniformResidualFiberAddressMachine.treeCost ((w+1)+r) (q*(w+1)+r)+9)+1,
  by simpa only [Nat.add_assoc] using (prep.trans (appended.trans placedDFS)).executes finish,by unfold runtimeBound;omega,rfl,actualCount,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · intro j
   have val:=written j.val j.isLt
   rwa [address_eq _ _ F zero (UniformResidualPermutation.permutation_xor q w v p hp) j] at val
 · intro i
   exact (af (U+i.val) (by left;have h:=i.isLt;omega) (by left;have h:=i.isLt;omega)).trans
    ((ef (U+i.val) (by left;have h:=i.isLt;omega)).trans (retained i))
 · intro i hi
   exact (af (table+i) (by right;omega) (by right;omega)).trans (entriesNow i hi)
 · intro z hz
   exact (af z (by rcases hz with h|h <;> omega) (by rcases hz with h|h <;> omega)).trans
    ((ef z (by rcases hz with h|h <;> omega)).trans (outside z hz))
 · exact ash.trans (esh.trans sh)
 · exact asr.trans (esr.trans sr)
 · exact ao.trans (eo.trans ou)
 · exact aro.trans (ero.trans ro)
 · exact (df.natReg 4069 (by omega)).trans ((keep _ (by omega) (by omega) (by omega)).trans one)
 · exact (df.natReg 4067 (by omega)).trans ((keep _ (by omega) (by omega) (by omega)).trans pointer)
 · intro i hi
   exact (df.natReg i (by omega)).trans ((keep i hi.2.2 (by omega) (by omega)).trans (nr i ⟨hi.1,hi.2.1⟩))

 · exact actualHeader.size

/-- The literal permutation preparation has a linear array budget even with
all remainder bits in the same traversal. Width m is the fixed seed width. -/
theorem runtime_linear (q m r:ℕ) (qp:1≤ q) (mp:3≤ m) (rp:r< m) :
 runtimeBound q m r≤ (58*m+268)*2^(q*m+r) := by
 have old:=UniformResidualPermutationPreparation.runtime_linear q m qp mp
 have le:2^(q*m)≤ 2^(q*m+r):=Nat.pow_le_pow_right (by omega) (by omega)
 have old':UniformResidualPermutationPreparation.runtimeBound q m≤ (17*m+184)*2^(q*m+r):=
  old.trans (Nat.mul_le_mul_left _ le)
 have vc:1≤ 2^(q*m+r):=Nat.two_pow_pos _
 have tree:=UniformResidualFiberAddressMachine.treeCost_balance (m+r) (q*m+r)
 have width:m+r≤ 2*m:=by omega
 unfold runtimeBound
 nlinarith

end
end ExactFourierCircuits.UniformResidualGeneralPreparation
