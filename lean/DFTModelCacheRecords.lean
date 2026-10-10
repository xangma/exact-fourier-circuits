import DFTModelCacheLiteral
import UniformRecursiveSavingProgram

set_option autoImplicit false

/-! A single fixed typed program prints the saving seed's nested record tapes.
Only the runtime columns are patched; neither the record array nor its entries
are supplied by the caller. The finite literal payload remains symbolic. -/
/- Paper E (adc7f), §2.6, Theorem 2.6, pp. 11–12: preparation of the fixed
recursive seed and unit records is charged before the recursive saving calls. -/
namespace ExactFourierCircuits.DFTModelCacheRecords
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheLiteral
open UniformFixedNetworkScheduleMachine (Record)
noncomputable section

def words (r : Record) : List (Prog false w w) :=
  [.atom (.lit r.opcode),.atom .id,.atom (.lit r.width),
   .atom (.lit r.dest),.atom (.lit r.source),.atom (.lit r.inverse),
   .atom (.lit r.dimension),.atom (.lit r.scalar)] ++
    r.directions.map (fun v=>.atom (.lit v))

def record (r : Record) : Prog false w (Ty.a w) :=
  materialize (.atom (.lit 0)) (words r)

def blank : Record := ⟨0,0,0,0,0,0,0,0,[]⟩

def records (rs : List Record) : Prog false w (Ty.a (Ty.a w)) :=
  materialize (record blank) (rs.map record)

def dataTape (vs : List ℕ) : Tape ℕ := Tape.tab vs.length (fun j=>(vs[j]?).getD 0)
def recordTape (rs : List Record) : Tape (Tape ℕ) :=
  Tape.tab rs.length (fun j=>dataTape ((rs[j]?).getD blank).data)

def recordCost (r : Record) : ℕ := 4+r.data.length*(13*r.data.length+7)
def recordsCost (rs : List Record) : ℕ :=
  4+rs.length*(12*rs.length+(rs.map recordCost).sum+recordCost blank+6)

def recordsPeak (rs : List Record) : ℕ :=
  max 8 (max rs.length (max (UniformFixedNetworkScheduleMachine.literalCap
    (UniformFixedNetworkScheduleMachine.serialize rs))
      (UniformFixedNetworkScheduleMachine.literalCap (rs.map (fun r=>r.data.length)))))

theorem words_length (r : Record) : (words r).length=r.data.length := by
  simp [words,Record.data,Record.header]

theorem words_values (r : Record) (q : ℕ) :
    (words r).map (fun f=>(run f q).val)=(r.withColumns q).data := by
  simp [words,Record.data,Record.header,Record.withColumns,
    atom_run,Atom.run,Bill.one,Bill.word,List.map_map,Function.comp_def]

theorem words_work (r : Record) (q : ℕ) :
    ((words r).map (fun f=>(run f q).work)).sum=r.data.length := by
  simp [words,Record.data,Record.header,atom_run,Atom.run,Bill.one,Bill.word,
    List.map_map,Function.comp_def,List.sum_replicate]
  omega

theorem words_valid (r : Record) (q : ℕ) : ∀f∈words r,(run f q).valid := by
  intro f hf
  simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
    trivial

theorem words_peak (r : Record) (q B : ℕ) (_hq : q≤B)
    (hl : ∀v∈r.data,v≤B) : ∀f∈words r,(run f q).peak≤B := by
  intro f hf
  simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with h|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change r.opcode≤B;exact hl _ (by simp [Record.data,Record.header])
    · exact Nat.zero_le _
    · change r.width≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.dest≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.source≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.inverse≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.dimension≤B;exact hl _ (by simp [Record.data,Record.header])
    · change r.scalar≤B;exact hl _ (by simp [Record.data,Record.header])
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
    exact hl v (by simp [Record.data,hv])

theorem record_value (r : Record) (q : ℕ) :
    (run (record r) q).val=dataTape (r.withColumns q).data := by
  rw [record,materialize_value]
  have hw:=words_values r q
  have hlen:=words_length r
  unfold dataTape
  rw [UniformFixedNetworkLiteralDecoderMachine.data_columns_length,←hlen]
  apply tab_ext
  intro j _
  have hm : ((words r).map (fun f=>(run f q).val))[j]?=
      Option.map (fun f=>(run f q).val) ((words r)[j]?) := List.getElem?_map
  rw [hw] at hm
  cases h:(words r)[j]? <;> simp [h,hm,atom_run,Atom.run,Bill.word]

theorem record_valid (r : Record) (q : ℕ) : (run (record r) q).valid :=
  materialize_valid _ _ _ (by trivial) (words_valid r q)

theorem record_work (r : Record) (q : ℕ) :
    (run (record r) q).work≤recordCost r := by
  have h:=materialize_work (.atom (.lit 0)) (words r) q
  rw [words_length,words_work] at h
  change (run (record r) q).work≤_ at h
  simp only [atom_run,Atom.run,Bill.word] at h
  dsimp [recordCost]
  nlinarith

theorem record_peak (r : Record) (q B : ℕ) (hq : q≤B)
    (h1 : 1≤B) (hlen : r.data.length≤B) (hl : ∀v∈r.data,v≤B) :
    (run (record r) q).peak≤B :=
  materialize_peak _ _ _ B (by simpa [words_length]) h1 (Nat.zero_le _)
    (words_peak r q B hq hl)

theorem records_value (rs : List Record) (q : ℕ) :
    (run (records rs) q).val=recordTape (rs.map (Record.withColumns q)) := by
  rw [records,materialize_value]
  simp only [List.length_map,recordTape]
  apply tab_ext
  intro j hj
  simp only [List.getElem?_map]
  cases h:rs[j]? with
  | none => have hn:=List.getElem?_eq_none_iff.mp h;omega
  | some r => simp [record_value]

theorem records_valid (rs : List Record) (q : ℕ) : (run (records rs) q).valid := by
  apply materialize_valid _ _ _ (record_valid blank q)
  intro f hf
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hf
  exact record_valid r q

theorem records_work (rs : List Record) (q : ℕ) :
    (run (records rs) q).work≤recordsCost rs := by
  have h:=materialize_work (record blank) (rs.map record) q
  simp only [List.length_map,List.map_map,Function.comp_def] at h
  have hs : (rs.map (fun r=>(run (record r) q).work)).sum≤(rs.map recordCost).sum :=
    List.sum_le_sum (fun r _=>record_work r q)
  have hd:=record_work blank q
  dsimp [records,recordsCost]
  nlinarith

theorem records_peak (rs : List Record) (q B : ℕ) (hq : q≤B) (h1 : 8≤B)
    (hlen : rs.length≤B) (hlens : ∀r∈rs,r.data.length≤B)
    (hl : ∀r∈rs,∀v∈r.data,v≤B) : (run (records rs) q).peak≤B := by
  apply materialize_peak _ _ _ B (by simpa) (by omega)
    (record_peak blank q B hq (by omega) (by simpa [blank,Record.data,Record.header])
      (by simp [blank,Record.data,Record.header]))
  intro f hf
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hf
  exact record_peak r q B hq (by omega) (hlens r hr) (hl r hr)

def seed : Prog false w (Ty.a (Ty.a w)) := records UniformFixedNetworkScheduleMachine.baseSchedule

theorem seed_value (q : ℕ) : (run seed q).val=
    recordTape (UniformFixedNetworkScheduleMachine.scheduleRecords q) :=
  records_value _ q
theorem seed_valid (q : ℕ) : (run seed q).valid := records_valid _ q
theorem seed_work (q : ℕ) : (run seed q).work≤
    recordsCost UniformFixedNetworkScheduleMachine.baseSchedule := records_work _ q

theorem records_peak_fixed (rs : List Record) (q : ℕ) :
    (run (records rs) q).peak≤q+recordsPeak rs := by
  apply records_peak rs q (q+recordsPeak rs) (Nat.le_add_right _ _)
  · exact le_trans (le_max_left _ _) (Nat.le_add_left _ _)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_add_left _ _)
  · intro r hr
    have h:=UniformFixedNetworkScheduleMachine.member_le_cap _ _
      (List.mem_map.mpr ⟨r,hr,rfl⟩ : r.data.length∈rs.map (fun r=>r.data.length))
    exact le_trans h (le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) (Nat.le_add_left _ _))
  · intro r hr v hv
    have h:=UniformFixedNetworkScheduleMachine.member_le_cap _ _
      (UniformFixedNetworkScheduleMachine.serialize_mem.mpr ⟨r,hr,hv⟩)
    exact le_trans h (le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) (Nat.le_add_left _ _))

theorem seed_peak (q : ℕ) : (run seed q).peak≤
    q+recordsPeak UniformFixedNetworkScheduleMachine.baseSchedule := records_peak_fixed _ q

theorem seed_specification (q : ℕ) :
    (run seed q).val=recordTape (UniformFixedNetworkScheduleMachine.scheduleRecords q) ∧
    (run seed q).valid ∧ (run seed q).work≤recordsCost UniformFixedNetworkScheduleMachine.baseSchedule ∧
    (run seed q).peak≤q+recordsPeak UniformFixedNetworkScheduleMachine.baseSchedule :=
  ⟨seed_value q,seed_valid q,seed_work q,seed_peak q⟩

end
end ExactFourierCircuits.DFTModelCacheRecords
