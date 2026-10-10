import DFTModelSavingY

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
open UniformNativeYRecordMachine (Direction record body)
open UniformFixedNetworkScheduleMachine (Printed Record bitWords)
noncomputable section

/-- Exactly the original record bytes, indexed relative to its first cell. -/
def RecordSource {R m : ℕ} (q : ℕ) (ds : List (Direction R m)) (raw : Tape ℕ) : Prop :=
  ∀ j (hj : j<(record q m ds).data.length),raw.look j 0=(record q m ds).data[j]'hj

theorem RecordSource.headers {R m q : ℕ} {ds : List (Direction R m)} {raw : Tape ℕ}
    (h : RecordSource q ds raw) :
    raw.look 1 0=q ∧ raw.look 2 0=m ∧ raw.look 6 0=ds.length := by
  have a:=h 1 (by rw [UniformNativeYRecordMachine.record_length];omega)
  have b:=h 2 (by rw [UniformNativeYRecordMachine.record_length];omega)
  have c:=h 6 (by rw [UniformNativeYRecordMachine.record_length];omega)
  simpa only [record,Record.data,Record.header,List.getElem_append,
    List.getElem_cons_succ,List.getElem_cons_zero] using ⟨a,b,c⟩

theorem ordinal_bound {m i j count : ℕ} (hi : i<count) (hj : j < m + 1) :
    (m+1)*i+j<(m+1)*count := by
  have h:=Nat.mul_le_mul_left (m+1) (Nat.succ_le_iff.mpr hi)
  simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one] at h
  omega

theorem body_get {R m : ℕ} (ds : List (Direction R m)) (i j : ℕ)
    (hi : i<ds.length) (hj : j < m + 1) :
    (UniformNativeYRecordMachine.body ds).getD ((m+1)*i+j) 0=
      (ds[i]'hi).data.getD j 0 := by
  induction ds generalizing i with
  | nil => simp at hi
  | cons d ds ih =>
    cases i with
    | zero =>
      simp only [UniformNativeYRecordMachine.body,List.map_cons,List.flatten_cons,
        Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero,List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show j<d.data.length by rw [Direction.data_length];exact hj)]
    | succ i =>
      have hil : i<ds.length := by simpa using hi
      have after : d.data.length≤(m+1)*(i+1)+j := by
        rw [Direction.data_length,Nat.mul_add,Nat.mul_one];omega
      have sub : (m+1)*(i+1)+j-d.data.length=(m+1)*i+j := by
        rw [Direction.data_length,Nat.mul_add,Nat.mul_one];omega
      simpa only [UniformNativeYRecordMachine.body,List.map_cons,List.flatten_cons,
        List.getD_eq_getElem?_getD,List.getElem?_append_right after,sub,
        List.getElem_cons_succ] using ih i hil

theorem RecordSource.row {R m q : ℕ} {ds : List (Direction R m)} {raw : Tape ℕ}
    (h : RecordSource q ds raw) (i : ℕ) (hi : i<ds.length) (j : ℕ) (hj : j < m + 1) :
    raw.look (8+(m+1)*i+j) 0=(ds[i]'hi).data.getD j 0 := by
  have small:=ordinal_bound hi hj
  have valid : 8+(m+1)*i+j<(record q m ds).data.length := by
    rw [UniformNativeYRecordMachine.record_length];omega
  have cell:=h (8+(m+1)*i+j) valid
  have gd : (record q m ds).data.getD (8+(m+1)*i+j) 0=
      (record q m ds).data[8+(m+1)*i+j]'valid := by simp [List.getD_eq_getElem?_getD,valid]
  rw [←gd] at cell
  have after : (record q m ds).header.length≤8+(m+1)*i+j := by
    rw [Record.header_length];omega
  have sub : 8+(m+1)*i+j-(record q m ds).header.length=(m+1)*i+j := by
    rw [Record.header_length];omega
  change raw.look (8+(m+1)*i+j) 0=
    ((record q m ds).header++(record q m ds).directions).getD (8+(m+1)*i+j) 0 at cell
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right after,sub,
    ←List.getD_eq_getElem?_getD] at cell
  exact cell.trans (body_get ds i j hi hj)

theorem RecordSource.direction {R m q : ℕ} {ds : List (Direction R m)} {raw : Tape ℕ}
    (h : RecordSource q ds raw) (i : ℕ) (hi : i<ds.length) :
    raw.look (8+(m+1)*i) 0=(ds[i]'hi).role.val ∧
    ∀ j:Fin m,raw.look (8+(m+1)*i+1+j.val) 0=((ds[i]'hi).vector j).val := by
  constructor
  · simpa only [Nat.add_zero,Direction.data,List.getD_cons_zero] using h.row i hi 0 (by omega)
  · intro j
    have cell:=h.row i hi (j.val+1) (by omega)
    simpa [Direction.data,bitWords,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cell

theorem RecordSource.of_printed {R m : ℕ} (q P : ℕ) (ds : List (Direction R m))
    (raw : Tape ℕ) (s : State) (bank : Printed P (record q m ds).data s)
    (copied : ∀ j,j<(record q m ds).data.length →
      ∀ z,s.natHeap (P+j)=some z → raw.look j 0=z) : RecordSource q ds raw := by
  intro j hj
  exact copied j hj _ (bank j hj)

end
end ExactFourierCircuits.DFTModelSavingY
