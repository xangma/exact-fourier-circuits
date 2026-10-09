import DFTModelCRTMetadataProgram
import DFTModelCRTSelected
import UniformWorkingCompletion

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTMetadata
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformCRTTraversalCycle UniformWorkingLength
open scoped BigOperators
noncomputable section

def selectedInput (n : ℕ) : Input.T :=
  (UniformWorkingLength.axisCount n,(len n,(binaryFactor n,⟨UniformWorkingLength.axisCount n,fun i => oddPrime i.val⟩)))

/-- The exact produced source ABI, with no coefficient or CRT table premise. -/
def Represents (n : ℕ) (s : UniformMachine.State) (x : Input.T) : Prop :=
  x.1=s.natReg 10 ∧ x.2.1=s.natReg 17 ∧ x.2.2.1=s.natReg 18 ∧
    x.2.2.2.len=s.natReg 10 ∧
    ∀j : Fin (UniformWorkingLength.axisCount n),s.natHeap j.val=some (x.2.2.2.look j.val 0)

theorem selected_represents {n : ℕ} {s : UniformMachine.State}
    (ready : UniformWorkingCompletion.PreparedState n s) : Represents n s (selectedInput n) := by
  rcases ready with ⟨⟨_,count,_,primes,_⟩,_,binary,volume⟩
  refine ⟨count.symm,volume.symm,binary.symm,count.symm,?_⟩
  intro i
  simpa [selectedInput,Tape.look,i.isLt] using primes i.val i.isLt

theorem selected_radix (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n+1)) :
    radixValue (selectedInput n) i.val=radices n i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [radixValue,selectedInput,UniformSelectedCRT.radices]
  · simp [radixValue,selectedInput,UniformSelectedCRT.radices,Tape.look,j.isLt]

theorem selected_cell {n : ℕ} (hn : 0<n) (i : Fin (UniformWorkingLength.axisCount n+1)) :
    (run cell (selectedInput n,i.val)).val=
      (radices n i,(alphaWeights n i,betaWeights n i)) := by
  rw [cell_value,selected_radix]
  change (radices n i,((len n/radices n i)*
    (run inverse (len n/radices n i,radices n i)).val,len n/radices n i))=_
  have co : len n/radices n i=UniformCRT.cofactor (radices n) i := by
    rw [UniformCRT.cofactor_eq_div _ _ (UniformSelectedCRT.radix_pos n i),
      UniformSelectedCRT.radices_product]
  rw [co,inverse_value _ _
    (by have h : 2≤radices n i := UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i;omega)
    (UniformCRT.cofactor_coprime (radices n) (UniformSelectedCRT.radices_pairwise n) i)]
  rfl

theorem selected_metadata {n : ℕ} (hn : 0<n) :
    (run metadata (selectedInput n)).val=DFTModelCRT.selectedRows n := by
  rw [metadata_value]
  change (⟨UniformWorkingLength.axisCount n+1,fun i => (Code.run cell () (selectedInput n,i.val)).val⟩ : Tape (ℕ×(ℕ×ℕ)))=⟨UniformWorkingLength.axisCount n+1,_⟩
  congr 1
  funext i
  exact selected_cell hn i

theorem list_sum_le_twice_prod (rs : List ℕ) (two : ∀q∈rs,2≤q) : rs.sum≤2*rs.prod := by
  induction rs with
  | nil => simp
  | cons q rs ih =>
      have tq : 2≤q := two q (by simp)
      have tail : ∀r∈rs,2≤r := fun r hr => two r (List.mem_cons_of_mem q hr)
      have p : 1≤rs.prod := Nat.succ_le_of_lt (List.prod_pos (fun r hr => by have:=tail r hr;omega))
      have h := ih tail
      have first := Nat.mul_le_mul_left q p
      have second := Nat.mul_le_mul_right rs.prod tq
      simp only [Nat.mul_one] at first
      simp only [List.sum_cons,List.prod_cons]
      omega

theorem selected_radix_sum {n : ℕ} (hn : 0<n) :
    (∑i ∈ Finset.range (UniformWorkingLength.axisCount n+1),radixValue (selectedInput n) i)≤2*len n := by
  have h := list_sum_le_twice_prod (List.ofFn (radices n)) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i)
  have eq : (∑i ∈ Finset.range (UniformWorkingLength.axisCount n+1),radixValue (selectedInput n) i)=∑i,radices n i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact selected_radix n i
  rw [eq]
  simpa only [List.sum_ofFn,List.prod_ofFn,UniformSelectedCRT.radices_product] using h

theorem selected_count_le {n : ℕ} (hn : 0<n) : UniformWorkingLength.axisCount n+1≤len n := by
  have h := DFTModelCRT.prefix_axes_le _ _ (DFTModelCRT.selected_rows_two hn)
  rw [DFTModelCRT.selected_length] at h
  change UniformWorkingLength.axisCount n+1+1≤len n at h
  omega

theorem selected_work {n : ℕ} (hn : 0<n) :
    (run metadata (selectedInput n)).work≤200*(len n+1) := by
  have cost := metadata_work (selectedInput n)
  have sum := selected_radix_sum hn
  have count := selected_count_le hn
  change (run metadata (selectedInput n)).work≤
    78*(UniformWorkingLength.axisCount n+1)+46*(∑i ∈ Finset.range (UniformWorkingLength.axisCount n+1),radixValue (selectedInput n) i)+8 at cost
  omega

theorem selected_peak {n : ℕ} (hn : 0<n) :
    (run metadata (selectedInput n)).peak≤(len n+1)^2 := by
  have count := selected_count_le hn
  have positive : 0<len n := by
    have h : 2*n≤len n := UniformWorkingLength.workingLength_lower n
    omega
  apply metadata_peak _ _ positive rfl count
  intro i hi
  rw [selected_radix n ⟨i,hi⟩]
  have p : 0<UniformCRT.cofactor (radices n) ⟨i,hi⟩ :=
    Finset.prod_pos (fun j _ => UniformSelectedCRT.radix_pos n j)
  have h := UniformCRT.cofactor_mul (radices n) ⟨i,hi⟩
  rw [UniformSelectedCRT.radices_product] at h
  change UniformCRT.cofactor (radices n) ⟨i,hi⟩*radices n ⟨i,hi⟩=len n at h
  nlinarith

end
end ExactFourierCircuits.DFTModelCRTMetadata
