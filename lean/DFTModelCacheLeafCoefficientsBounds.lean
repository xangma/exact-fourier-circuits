import DFTModelCacheLeafCoefficientsCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTransposeDescriptorMachine
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelCacheForest.prepareInverseH
  DFTModelCacheDirectLeaf.orientations banks annotate body setup

theorem banks_work (r : ℕ) (omega : ℂ) :
    (run banks (r,omega)).work≤160*(r+1)^2+7 := by
  rw [banks_run]
  have a:=DFTModelCacheForest.prepareInverseH_work r omega
  have b:=DFTModelCacheForest.prepareInverseH_work r omega⁻¹
  change _+_+7≤_
  omega

theorem banks_peak (r : ℕ) (omega : ℂ) : (run banks (r,omega)).peak≤r := by
  rw [banks_run]
  exact max_le (DFTModelCacheForest.prepareInverseH_peak _ _)
    (DFTModelCacheForest.prepareInverseH_peak _ _)

theorem body_work (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run body (input,((h,hc),(f,t)))).work=57+67*(f.len+t.len) := by
  rw [body_run]
  change (run annotate _).work+(run annotate _).work+1+44=_
  rw [annotate_work,annotate_work]
  omega

theorem body_peak (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) (B : ℕ)
    (hf : (run annotate ((input.2.2.2,(h,hc)),f)).peak≤B)
    (ht : (run annotate ((input.2.2.2,(h,hc)),t)).peak≤B) :
    (run body (input,((h,hc),(f,t)))).peak≤B := by
  rw [body_run]
  exact max_le (max_le hf (max_le ht (Nat.zero_le _))) (Nat.zero_le _)

theorem encoded_length (qs : List Record) : (encoded qs).len=qs.length := by
  simp [encoded,DFTModelCacheTraversal.ofList]

theorem encoded_index (r K : ℕ) (qs : List Record)
    (range : ∀q∈qs,UniformDirectLeafCacheSource.InRange r K q)
    (i : ℕ) (hi : i<(encoded qs).len) :
    ((encoded qs).look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K<r := by
  have hi' : i<qs.length := by simpa only [encoded_length] using hi
  rw [Tape.look_of_lt _ _ hi]
  simp only [encoded,DFTModelCacheTraversal.ofList,List.getElem_map]
  change (DFTModelCacheDirectLeaf.encode qs[i]).2.2.2-K<r
  have rng:=range qs[i] (List.getElem_mem hi')
  change qs[i].coefficient-K<r
  rcases rng with ⟨_,_,lo,up⟩
  omega

def workBudget (r v : ℕ) : ℕ :=160*(r+1)^2+1000*(v+1)^3+134*(v+1)^2+72
def peakBudget (r v o K : ℕ) : ℕ :=r+o+K+2*(v+1)^2

theorem program_work (r v o K : ℕ) (omega : ℂ) :
    (run program ((r,omega),(v,(o,K)))).work≤workBudget r v := by
  change (run setup _).work+(run body (run setup _).val).work+1≤_
  rw [setup_run]
  change (run banks (r,omega)).work+
    (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).work+7+
    (run body ((((r,omega),(v,(o,K))),((run banks (r,omega)).val,
      (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).val)))).work+1≤_
  rw [DFTModelCacheDirectLeaf.orientations_value]
  rw [body_work]
  have bl:=banks_work r omega
  have ow:=DFTModelCacheDirectLeaf.orientations_work v o K
  have len: (leafRecords v o K).length≤(v+1)^2 := by
    simpa [←DFTModelCacheDirectLeaf.records_native] using
      DFTModelCacheDirectLeaf.records_length_bound v o K
  simp only [DFTModelCacheTraversal.ofList,List.length_map,List.length_reverse]
  unfold workBudget
  omega

theorem program_peak (r v o K : ℕ) (omega : ℂ) (extent : o+v≤r) :
    (run program ((r,omega),(v,(o,K)))).peak≤peakBudget r v o K := by
  change max (max (run setup _).peak (run body (run setup _).val).peak) 0≤_
  apply max_le (max_le ?_ ?_) (Nat.zero_le _)
  · rw [setup_run]
    exact max_le ((banks_peak r omega).trans (by unfold peakBudget;omega))
      ((DFTModelCacheDirectLeaf.orientations_peak v o K).trans (by unfold peakBudget;omega))
  · rw [setup_run]
    change (run body ((((r,omega),(v,(o,K))),((run banks (r,omega)).val,
      (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).val)))).peak≤_
    rw [DFTModelCacheDirectLeaf.orientations_value]
    apply body_peak
    all_goals apply annotate_peak
    · change (encoded (leafRecords v o K)).len≤_
      rw [encoded_length]
      have len:=DFTModelCacheDirectLeaf.records_length_bound v o K
      rw [DFTModelCacheDirectLeaf.records_native] at len
      unfold peakBudget
      omega
    · intro i hi
      change ((encoded (leafRecords v o K)).look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K≤_
      have ix:=encoded_index r K (leafRecords v o K)
        (fun q h=>(UniformDirectLeafCacheChronology.leaf_valid v o K r extent q h).1) i hi
      exact (Nat.le_of_lt ix).trans (by unfold peakBudget;omega)
    · change (encoded ((leafRecords v o K).reverse.map Record.transpose)).len≤_
      rw [encoded_length,List.length_map,List.length_reverse]
      have len:=DFTModelCacheDirectLeaf.records_length_bound v o K
      rw [DFTModelCacheDirectLeaf.records_native] at len
      unfold peakBudget
      omega
    · intro i hi
      change ((encoded ((leafRecords v o K).reverse.map Record.transpose)).look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K≤_
      have ix:=encoded_index r K ((leafRecords v o K).reverse.map Record.transpose) (fun q h=>by
        obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
        have good:=UniformDirectLeafCacheChronology.leaf_valid v o K r extent p (List.mem_reverse.mp hp)
        exact (UniformDirectLeafCacheChronology.transpose_valid r K p good.1 good.2).1) i hi
      exact (Nat.le_of_lt ix).trans (by unfold peakBudget;omega)

theorem specification {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) (v o K : ℕ) (extent : o+v≤r) :
    (run program ((r,omega),(v,(o,K)))).val=values r v o K omega ∧
    (run program ((r,omega),(v,(o,K)))).valid ∧
    (run program ((r,omega),(v,(o,K)))).work≤workBudget r v ∧
    (run program ((r,omega),(v,(o,K)))).peak≤peakBudget r v o K :=
  ⟨program_value _ _ _ _ _ extent,program_valid hr primitive _ _ _,
    program_work _ _ _ _ _,program_peak _ _ _ _ _ extent⟩

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients
