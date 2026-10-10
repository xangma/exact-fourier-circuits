import DFTModelCacheLeafCoefficientsForest

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients.Forest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTransposeDescriptorMachine
open scoped BigOperators
noncomputable section
attribute [local irreducible] banks body annotate DFTModelCacheDirectLeaf.forest setup finish cell Bill.tab

theorem forest_look (v o K i : ℕ) (hi : i<(DFTModelCacheDirectLeaf.visits v o).length) :
    (run DFTModelCacheDirectLeaf.forest (v,(o,K))).val.2.look i DFTModelCacheDirectLeaf.Orientations.blank=
      DFTModelCacheDirectLeaf.leafValue K (DFTModelCacheDirectLeaf.visits v o)[i] := by
  rw [DFTModelCacheDirectLeaf.forest_value]
  have h : i<(DFTModelCacheTraversal.ofList
      ((DFTModelCacheDirectLeaf.visits v o).map (DFTModelCacheDirectLeaf.leafValue K))).len := by
    simpa [DFTModelCacheTraversal.ofList] using hi
  change (DFTModelCacheTraversal.ofList _).look i _=_
  rw [Tape.look_of_lt _ _ h]
  simp only [DFTModelCacheTraversal.ofList,List.getElem_map]

theorem visits_bound (v o : ℕ) : (DFTModelCacheDirectLeaf.visits v o).length≤2*v+1 := by
  have h:=(DFTModelCacheTraversal.program_lengths v o).1
  rw [DFTModelCacheTraversal.program_value] at h
  simpa [DFTModelCacheTraversal.ofList,DFTModelCacheDirectLeaf.visits] using h

theorem leaf_lengths (K : ℕ) (q : UniformLocalCacheTreeMachine.Visit) :
    (DFTModelCacheDirectLeaf.leafValue K q).1.len≤(q.task.width+1)^2 ∧
    (DFTModelCacheDirectLeaf.leafValue K q).2.len≤(q.task.width+1)^2 := by
  by_cases h : DFTModelCacheDirectLeaf.leaf q
  · simp only [DFTModelCacheDirectLeaf.leafValue,h,ite_true]
    have len:=DFTModelCacheDirectLeaf.records_length_bound q.task.width q.task.offset K
    rw [DFTModelCacheDirectLeaf.records_native] at len
    simpa [DFTModelCacheTraversal.ofList] using And.intro len len
  · simp [DFTModelCacheDirectLeaf.leafValue,h,DFTModelCacheTraversal.ofList]

theorem cell_work (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) (i : ℕ) :
    (run cell ((input,((h,hc),f)),i)).work=
      83+67*((f.2.look i DFTModelCacheDirectLeaf.Orientations.blank).1.len+
        (f.2.look i DFTModelCacheDirectLeaf.Orientations.blank).2.len) := by
  rw [cell_run,body_work]
  change 57+67*(_+_)+26=_
  omega

theorem finish_work (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) :
    (run finish (input,((h,hc),f))).work=18+4*f.2.len+
      ∑i∈Finset.range f.2.len,(run cell ((input,((h,hc),f)),i)).work := by
  rw [finish_run]
  change (Bill.tab _ _ _).work+1+15=_
  rw [ModelEquivalenceInterpreter.tab_work]
  omega

theorem finish_peak (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) (B : ℕ) (count : f.2.len≤B)
    (cells : ∀i,i<f.2.len→(run cell ((input,((h,hc),f)),i)).peak≤B) :
    (run finish (input,((h,hc),f))).peak≤B := by
  rw [finish_run]
  change max (max (Bill.tab _ _ _).peak 0) f.2.len≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (max_le count ?_) (Nat.zero_le _)) count
  apply Finset.sup_le
  intro i hi
  exact cells i (Finset.mem_range.mp hi)

def workBudget (r v : ℕ) : ℕ :=160*(r+1)^2+DFTModelCacheDirectLeaf.forestWorkBudget v+
  (2*v+1)*(87+134*(v+1)^2)+33

theorem program_work (r v o K : ℕ) (omega : ℂ) :
    (run program ((r,omega),(v,(o,K)))).work≤workBudget r v := by
  let f:=(run DFTModelCacheDirectLeaf.forest (v,(o,K))).val
  let h:=(run banks (r,omega)).val
  have length : f.2.len=(DFTModelCacheDirectLeaf.visits v o).length :=
    (DFTModelCacheDirectLeaf.forest_lengths v o K).2.2
  have count : f.2.len≤2*v+1 := length.trans_le (visits_bound v o)
  have cw : ∀i∈Finset.range f.2.len,
      (run cell ((((r,omega),(v,(o,K))),(h,f)),i)).work≤83+134*(v+1)^2 := by
    intro i hi
    have hi' : i<(DFTModelCacheDirectLeaf.visits v o).length :=
      (Finset.mem_range.mp hi).trans_eq length
    rw [cell_work,forest_look v o K i hi']
    have ls:=leaf_lengths K (DFTModelCacheDirectLeaf.visits v o)[i]
    have width:=(DFTModelCacheDirectLeaf.visit_bounds v o
      (DFTModelCacheDirectLeaf.visits v o)[i] (List.getElem_mem hi')).1
    have power:=Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2
    omega
  have sum:=Finset.sum_le_sum cw
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  have bw:=banks_work r omega
  have fw:=DFTModelCacheDirectLeaf.forest_work v o K
  have scaled:=Nat.mul_le_mul_right (87+134*(v+1)^2) count
  change (run setup _).work+(run finish (run setup _).val).work+1≤_
  rw [setup_run]
  change (run banks (r,omega)).work+(run DFTModelCacheDirectLeaf.forest (v,(o,K))).work+7+
    (run finish ((((r,omega),(v,(o,K))),(h,f)))).work+1≤_
  rw [finish_work]
  unfold workBudget
  nlinarith

/-- Generic immutable-bank annotation bound, used only after native range checking. -/
theorem body_native_peak (input : Input.T) (h hc : Tape ℂ)
    (r B : ℕ) (qs ts : List Record) (rfit : r≤B)
    (rangeQ : ∀q∈qs,UniformDirectLeafCacheSource.InRange r input.2.2.2 q)
    (rangeT : ∀q∈ts,UniformDirectLeafCacheSource.InRange r input.2.2.2 q)
    (lenQ : qs.length≤B) (lenT : ts.length≤B) :
    (run body (input,((h,hc),(encoded qs,encoded ts)))).peak≤B := by
  apply body_peak
  · apply annotate_peak
    · simpa only [encoded_length] using lenQ
    · intro i hi
      exact ((encoded_index r _ qs rangeQ i hi).le).trans rfit
  · apply annotate_peak
    · simpa only [encoded_length] using lenT
    · intro i hi
      exact ((encoded_index r _ ts rangeT i hi).le).trans rfit

def peakBudget (r v o K : ℕ) : ℕ :=
  max (DFTModelCacheDirectLeaf.forestPeakBudget v o K) (r+2*v+1+2*(v+1)^2)

theorem program_peak (r v o K : ℕ) (omega : ℂ) (extent : o+v≤r) :
    (run program ((r,omega),(v,(o,K)))).peak≤peakBudget r v o K := by
  let f:=(run DFTModelCacheDirectLeaf.forest (v,(o,K))).val
  let h:=(run banks (r,omega)).val
  let B:=peakBudget r v o K
  have length : f.2.len=(DFTModelCacheDirectLeaf.visits v o).length :=
    (DFTModelCacheDirectLeaf.forest_lengths v o K).2.2
  have rfit : r≤B := (show r≤r+2*v+1+2*(v+1)^2 by omega).trans (le_max_right _ _)
  have count : f.2.len≤B :=
    (length.trans_le (visits_bound v o)).trans ((by omega : 2*v+1≤r+2*v+1+2*(v+1)^2).trans (le_max_right _ _))
  have cells : ∀i,i<f.2.len→(run cell ((((r,omega),(v,(o,K))),(h,f)),i)).peak≤B := by
    intro i hi
    have hi' : i<(DFTModelCacheDirectLeaf.visits v o).length := hi.trans_eq length
    rw [cell_run,forest_look v o K i hi']
    let q:=(DFTModelCacheDirectLeaf.visits v o)[i]
    have bounds:=DFTModelCacheDirectLeaf.visit_bounds v o q (List.getElem_mem hi')
    have qe : q.task.offset+q.task.width≤r := bounds.2.trans extent
    change (run body ((((r,omega),(v,(o,K))),(h,DFTModelCacheDirectLeaf.leafValue K q)))).peak≤B
    by_cases leaf : DFTModelCacheDirectLeaf.leaf q
    · simp only [DFTModelCacheDirectLeaf.leafValue,leaf,ite_true]
      apply body_native_peak _ _ _ r _ _ _ rfit
      · exact fun p hp=>(UniformDirectLeafCacheChronology.leaf_valid _ _ _ _ qe p hp).1
      · intro p hp
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
        have good:=UniformDirectLeafCacheChronology.leaf_valid _ _ _ _ qe a (List.mem_reverse.mp ha)
        exact (UniformDirectLeafCacheChronology.transpose_valid r K a good.1 good.2).1
      all_goals
        have len:=DFTModelCacheDirectLeaf.records_length_bound q.task.width q.task.offset K
        rw [DFTModelCacheDirectLeaf.records_native] at len
        have power:=Nat.pow_le_pow_left (Nat.add_le_add_right bounds.1 1) 2
        have fit : (v+1)^2≤B := (show (v+1)^2≤r+2*v+1+2*(v+1)^2 by omega).trans (le_max_right _ _)
        simpa only [List.length_map,List.length_reverse] using len.trans (power.trans fit)
    · simp only [DFTModelCacheDirectLeaf.leafValue,leaf,ite_false]
      apply body_native_peak _ _ _ r _ [] [] rfit
      all_goals simp
  change max (max (run setup _).peak (run finish (run setup _).val).peak) 0≤B
  refine max_le (max_le ?_ ?_) (Nat.zero_le _)
  · rw [setup_run]
    exact max_le ((banks_peak r omega).trans rfit)
      ((DFTModelCacheDirectLeaf.forest_peak v o K).trans (le_max_left _ _))
  · rw [setup_run]
    exact finish_peak _ _ _ _ _ count cells

theorem specification {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) (v o K : ℕ) (extent : o+v≤r) :
    (run program ((r,omega),(v,(o,K)))).valid ∧
    (run program ((r,omega),(v,(o,K)))).work≤workBudget r v ∧
    (run program ((r,omega),(v,(o,K)))).peak≤peakBudget r v o K :=
  ⟨program_valid hr primitive _ _ _,program_work _ _ _ _ _,program_peak _ _ _ _ _ extent⟩

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients.Forest
