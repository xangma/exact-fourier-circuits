import DFTModelCacheDirectChronologyProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDirectLeaf
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology
open scoped BigOperators
noncomputable section

def values (v o t K : ℕ) : Tape Event.T :=
  DFTModelCacheTraversal.ofList ((leafRecords v o K).map (event v o t))

theorem annotate_value (v o t K : ℕ) (qs : List Record) :
    (run annotate ((v,(o,(t,K))),DFTModelCacheTraversal.ofList (qs.map encode))).val=
      DFTModelCacheTraversal.ofList (qs.map (event v o t)) := by
  rw [annotate_run]
  change (Bill.tab _ Event.blank _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply DFTModelCacheTraversal.tape_ext _ _ Event.blank
    (by simp [DFTModelCacheTraversal.ofList,Tape.tab])
  intro j hj
  have hj' : j<qs.length := by simpa [DFTModelCacheTraversal.ofList,Tape.tab] using hj
  rw [Tape.look_of_lt _ _ hj]
  change (run cell (((v,(o,(t,K))),DFTModelCacheTraversal.ofList (qs.map encode)),j)).val=_
  rw [cell_run]
  change (run stamp ((v,(o,(t,K))),_)).val=_
  have hx : j<(qs.map encode).length := by simpa using hj'
  have hy : j<(qs.map (event v o t)).length := by simpa using hj'
  simp only [DFTModelCacheTraversal.ofList]
  rw [Tape.look_of_lt _ _ hx,Tape.look_of_lt _ _ hy]
  simp only [List.getElem_map]
  exact stamp_value v o t K qs[j]

theorem annotate_valid (v o t K : ℕ) (qs : List Record) :
    (run annotate ((v,(o,(t,K))),DFTModelCacheTraversal.ofList (qs.map encode))).valid := by
  rw [annotate_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j hj
  rw [cell_run]
  have hx : j<(qs.map encode).length := hj
  change (run stamp ((v,(o,(t,K))),_)).valid
  simp only [DFTModelCacheTraversal.ofList]
  rw [Tape.look_of_lt _ _ hx]
  dsimp only
  rw [List.getElem_map]
  exact stamp_valid _ _ _ _ _

theorem program_value (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).val=values v o t K := by
  rw [program_run]
  change (run annotate ((v,(o,(t,K))),(run forward (v,(o,K))).val)).val=_
  rw [forward_value,annotate_value]
  rfl

theorem program_valid (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).valid := by
  rw [program_run]
  change (run forward (v,(o,K))).valid ∧
    (run annotate ((v,(o,(t,K))),(run forward (v,(o,K))).val)).valid
  constructor
  · exact forward_valid _ _ _
  · rw [forward_value]
    exact annotate_valid _ _ _ _ _

/-- The charged output stores precisely the native prefix clock and native kind,
with the original record and coefficient address unchanged. -/
theorem program_chronology (v o t K j : ℕ) (hj:j<(leafRecords v o K).length) :
    ((run program (v,(o,(t,K)))).val.look j Event.blank)=
      (starts t (leafRecords v o K) j,
        (cacheKind (leafRecords v o K)[j],encode (leafRecords v o K)[j])) := by
  rw [program_value]
  have h : j<((leafRecords v o K).map (event v o t)).length := by simpa using hj
  simp only [values,DFTModelCacheTraversal.ofList]
  rw [Tape.look_of_lt _ _ h]
  dsimp only
  rw [List.getElem_map]
  unfold event
  rw [native_timestamp v o K t j hj]

theorem program_length (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).val.len=v+v*(v-1)/2 := by
  rw [program_value]
  simp [values,DFTModelCacheTraversal.ofList,leafRecords_length]

theorem width_zero (o t K : ℕ) :
    (run program (0,(o,(t,K)))).val=DFTModelCacheTraversal.ofList [] := by
  rw [program_value]
  change DFTModelCacheTraversal.ofList ((leafRecords 0 o K).map _)=_
  rw [←records_native]
  rfl

theorem width_one (o t K : ℕ) :
    (run program (1,(o,(t,K)))).val=
      DFTModelCacheTraversal.ofList [(t,(1,encode ⟨0,o,o,K⟩))] := by
  rw [program_value]
  change DFTModelCacheTraversal.ofList ((leafRecords 1 o K).map _)=_
  rw [←records_native]
  simp [records,rowRecords,event,timestamp,rowOffset,cacheKind]

theorem clock_end (v o t K : ℕ) :
    t+elapsed (leafRecords v o K)=t+v+14*v*(v-1) := by
  rw [leaf_elapsed]
  omega

end
end ExactFourierCircuits.DFTModelCacheDirectChronology
