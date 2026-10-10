import DFTModelCacheUnit
import DFTModelSavingYData

set_option autoImplicit false

/-! Factual byte projections of the actual residual and unit-frame records. -/
namespace ExactFourierCircuits.DFTModelSavingDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetworkScheduleMachine
open BinaryFrames FramedScheduleWords UniformFixedNetwork
noncomputable section

def RawSource (r : Record) (raw : Tape ℕ) : Prop :=
  ∀ j (hj : j<r.data.length),raw.look j 0=r.data[j]'hj

theorem RawSource.of_printed (P : ℕ) (r : Record) (raw : Tape ℕ) (s : State)
    (bank : Printed P r.data s)
    (copied : ∀ j,j<r.data.length → ∀ z,s.natHeap (P+j)=some z → raw.look j 0=z) : RawSource r raw := by
  intro j hj
  exact copied j hj _ (bank j hj)

theorem RawSource.header {r : Record} {raw : Tape ℕ} (h : RawSource r raw) (i : Fin 8) :
    raw.look i.val 0=r.header[i.val]'(by rw [Record.header_length];exact i.isLt) := by
  have small : i.val<r.header.length := by rw [Record.header_length];exact i.isLt
  have cell:=h i.val (by rw [Record.data_length];omega)
  simpa only [Record.data,List.getElem_append_left small] using cell

theorem RawSource.body {r : Record} {raw : Tape ℕ} (h : RawSource r raw)
    (i : ℕ) (hi : i<r.directions.length) : raw.look (8+i) 0=r.directions[i]'hi := by
  have valid : 8+i<r.data.length := by rw [Record.data_length];omega
  have cell:=h (8+i) valid
  have copied:=List.getElem_eq_getD (l:=r.data) (i:=8+i) (h:=valid) 0
  rw [copied] at cell
  change raw.look (8+i) 0=(r.header++r.directions).getD (8+i) 0 at cell
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right
    (show r.header.length≤8+i by rw [Record.header_length];omega),Record.header_length,
    show 8+i-8=i by omega,←List.getD_eq_getElem?_getD] at cell
  exact cell.trans (List.getElem_eq_getD (l:=r.directions) (i:=i) (h:=hi) 0).symm

theorem macro_headers {R S m : ℕ} (q : ℕ) (e : Fin R ↪ Fin S)
    {old new : Label m} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q e (.edge old new role edge)) raw) :
    raw.look 1 0=q ∧ raw.look 2 0=m ∧ raw.look 3 0=(e role).val ∧
    raw.look 5 0=(if edgeInverse edge then 1 else 0) ∧ raw.look 6 0=edge.dimension := by
  have h1:=source.header ⟨1,by decide⟩
  have h2:=source.header ⟨2,by decide⟩
  have h3:=source.header ⟨3,by decide⟩
  have h5:=source.header ⟨5,by decide⟩
  have h6:=source.header ⟨6,by decide⟩
  exact ⟨h1,h2,h3,h5,h6⟩

theorem macro_bits {R S m : ℕ} (q : ℕ) (e : Fin R ↪ Fin S)
    {old new : Label m} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q e (.edge old new role edge)) raw)
    (i : Fin edge.dimension) (j : Fin m) :
    raw.look (8+m*i.val+j.val) 0=(edgeVectors edge i j).val := by
  have small : m*i.val+j.val<edge.dimension*m := by
    have h:=Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr i.isLt)
    simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at h
    nlinarith only [h,j.isLt]
  have cell:=source.body (m*i.val+j.val) (by
    change m*i.val+j.val<(edgeBits edge).length
    rw [edgeBits_length]
    exact small)
  have eq : (finProdFinEquiv (i,j)).val=m*i.val+j.val := by
    simp [finProdFinEquiv,Nat.add_comm]
  have actual:=edgeBits_coordinate edge i j
  have valid : m*i.val+j.val<(edgeBits edge).length := by rw [edgeBits_length];exact small
  have gd:=List.getElem_eq_getD (l:=edgeBits edge) (i:=m*i.val+j.val) (h:=valid) 0
  change raw.look (8+(m*i.val+j.val)) 0=(edgeBits edge)[m*i.val+j.val]'valid at cell
  rw [gd] at cell
  rw [List.getElem_eq_getD 0,eq] at actual
  exact (by simpa only [Nat.add_assoc] using cell.trans actual)

theorem dataTape_source (r : Record) : RawSource r (DFTModelCacheRecords.dataTape r.data) := by
  intro j hj
  simp [DFTModelCacheRecords.dataTape,Tape.look,Tape.tab,hj]

end
end ExactFourierCircuits.DFTModelSavingDirection
