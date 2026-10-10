import DFTModelCacheRecords

set_option autoImplicit false

/-! The actual unit-frame record is freshly printed from runtime (q,role).
Paper E (adc7f), §2.6, Theorem 2.6, pp. 11–12. All fixed identity-direction
words are integer literals in the finite syntax; no unit table is an input. -/
namespace ExactFourierCircuits.DFTModelCacheRecords
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheLiteral
open UniformFixedNetworkScheduleMachine (Record)
noncomputable section

def roleWords (r : Record) : List (Prog false (p w w) w) :=
  [.atom (.lit r.opcode),.atom .fst,.atom (.lit r.width),
   .atom .snd,.atom (.lit r.source),.atom (.lit r.inverse),
   .atom (.lit r.dimension),.atom (.lit r.scalar)] ++
    r.directions.map (fun v=>.atom (.lit v))

def roleRecord (r : Record) : Prog false (p w w) (Ty.a w) :=
  materialize (.atom (.lit 0)) (roleWords r)

def withRole (q role : ℕ) (r : Record) : Record := {r with columns:=q,dest:=role}

theorem roleWords_length (r : Record) : (roleWords r).length=r.data.length := by
  simp [roleWords,Record.data,Record.header]

theorem roleWords_values (r : Record) (q role : ℕ) :
    (roleWords r).map (fun f=>(run f (q,role)).val)=(withRole q role r).data := by
  simp [roleWords,Record.data,Record.header,withRole,
    atom_run,Atom.run,Bill.one,Bill.word,List.map_map,Function.comp_def]

theorem roleWords_work (r : Record) (q role : ℕ) :
    ((roleWords r).map (fun f=>(run f (q,role)).work)).sum=r.data.length := by
  simp [roleWords,Record.data,Record.header,atom_run,Atom.run,Bill.one,Bill.word,
    List.map_map,Function.comp_def,List.sum_replicate]
  omega

theorem roleWords_valid (r : Record) (q role : ℕ) :
    ∀f∈roleWords r,(run f (q,role)).valid := by
  intro f hf
  simp only [roleWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
    trivial

theorem roleWords_peak (r : Record) (q role B : ℕ)
    (hl : ∀v∈r.data,v≤B) : ∀f∈roleWords r,(run f (q,role)).peak≤B := by
  intro f hf
  simp only [roleWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change r.opcode≤B;exact hl _ (by simp [Record.data,Record.header])
    · exact Nat.zero_le _
    · change r.width≤B;exact hl _ (by simp [Record.data,Record.header])
    · exact Nat.zero_le _
    · change r.source≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.inverse≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.dimension≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.scalar≤B;exact hl _ (by simp [Record.data,Record.header])
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
    exact hl v (by simp [Record.data,hv])

theorem roleRecord_value (r : Record) (q role : ℕ) :
    (run (roleRecord r) (q,role)).val=dataTape (withRole q role r).data := by
  rw [roleRecord,materialize_value]
  have hw:=roleWords_values r q role
  have hlen:=roleWords_length r
  unfold dataTape
  have len : (withRole q role r).data.length=r.data.length := by
    simp [withRole,Record.data,Record.header]
  rw [len,←hlen]
  apply tab_ext
  intro j _
  have hm : ((roleWords r).map (fun f=>(run f (q,role)).val))[j]?=
      Option.map (fun f=>(run f (q,role)).val) ((roleWords r)[j]?) := List.getElem?_map
  rw [hw] at hm
  cases h:(roleWords r)[j]? <;> simp [h,hm,atom_run,Atom.run,Bill.word]

theorem roleRecord_valid (r : Record) (q role : ℕ) :
    (run (roleRecord r) (q,role)).valid :=
  materialize_valid _ _ _ (by trivial) (roleWords_valid r q role)

theorem roleRecord_work (r : Record) (q role : ℕ) :
    (run (roleRecord r) (q,role)).work≤recordCost r := by
  have h:=materialize_work (.atom (.lit 0)) (roleWords r) (q,role)
  rw [roleWords_length,roleWords_work] at h
  change (run (roleRecord r) (q,role)).work≤_ at h
  simp only [atom_run,Atom.run,Bill.word] at h
  dsimp [recordCost]
  nlinarith

theorem roleRecord_peak (r : Record) (q role B : ℕ)
    (h1 : 1≤B) (hlen : r.data.length≤B) (hl : ∀v∈r.data,v≤B) :
    (run (roleRecord r) (q,role)).peak≤B :=
  materialize_peak _ _ _ B (by simpa [roleWords_length]) h1 (Nat.zero_le _)
    (roleWords_peak r q role B hl)

def unit : Prog false (p w w) (Ty.a w) := roleRecord UniformRecursiveSavingProgram.unitRecord

theorem unit_value (q role : ℕ) : (run unit (q,role)).val=
    dataTape (withRole q role UniformRecursiveSavingProgram.unitRecord).data :=
  roleRecord_value _ q role
theorem unit_valid (q role : ℕ) : (run unit (q,role)).valid := roleRecord_valid _ q role
theorem unit_work (q role : ℕ) : (run unit (q,role)).work≤
    recordCost UniformRecursiveSavingProgram.unitRecord := roleRecord_work _ q role

def unitPeak : ℕ := max 1 (max UniformRecursiveSavingProgram.unitRecord.data.length
  (UniformFixedNetworkScheduleMachine.literalCap UniformRecursiveSavingProgram.unitRecord.data))

theorem unit_peak (q role : ℕ) : (run unit (q,role)).peak≤unitPeak := by
  apply roleRecord_peak _ _ _ _ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))
  intro v hv
  exact le_trans (UniformFixedNetworkScheduleMachine.member_le_cap _ _ hv)
    (le_trans (le_max_right _ _) (le_max_right _ _))

theorem unit_specification (q role : ℕ) :
    (run unit (q,role)).val=dataTape (withRole q role UniformRecursiveSavingProgram.unitRecord).data ∧
    (run unit (q,role)).valid ∧ (run unit (q,role)).work≤recordCost UniformRecursiveSavingProgram.unitRecord ∧
    (run unit (q,role)).peak≤unitPeak :=
  ⟨unit_value q role,unit_valid q role,unit_work q role,unit_peak q role⟩

end
end ExactFourierCircuits.DFTModelCacheRecords
