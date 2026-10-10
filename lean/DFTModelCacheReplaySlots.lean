import DFTModelCacheCalendarDuration
import UniformReplaySlotIndex

set_option autoImplicit false

/-! Paper E, §3.1–3.5 (pp.13–18), six-phase replay chronology.
This is the integer-only phase printer in the upstream typed RAM. It retains
empty colors and reverses both depth and color in inverse phases. Scalar
coefficients, matching partitions and physical cache allocation are separate. -/
namespace ExactFourierCircuits.DFTModelCacheReplaySlots
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheChronology
open UniformLocalReplaySlotMachine (bit levelCount decodedSlot slots)
open DFTModelCacheTraversal (ofList)
open scoped BigOperators
noncomputable section

abbrev Slot5 : Ty := p w (p w (p w (p w w)))
def encode (s : Slot) : Slot5.T :=
  (bit s.broadcast,(bit s.enabled,(bit s.inverse,(s.depth,s.color))))
abbrev CellInput : Ty := p w w
def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def levels (b : Bool) : Prog false w w :=
  if b then .atom (.lit 1) else nat .add (.atom .id) (.atom (.lit 1))
def count (b : Bool) : Prog false w w := nat .mul (levels b) (.atom (.lit 11))
def depth (b i : Bool) : Prog false CellInput w :=
  if b then .atom (.lit 0) else
    if i then nat .sub (.atom .fst) (nat .div (.atom .snd) (.atom (.lit 11)))
    else nat .div (.atom .snd) (.atom (.lit 11))
def color (i : Bool) : Prog false CellInput w :=
  if i then nat .sub (.atom (.lit 10)) (nat .mod (.atom .snd) (.atom (.lit 11)))
  else nat .mod (.atom .snd) (.atom (.lit 11))
def cell (b e i : Bool) : Prog false CellInput Slot5 :=
  .fork (.atom (.lit (bit b))) (.fork (.atom (.lit (bit e)))
    (.fork (.atom (.lit (bit i))) (.fork (depth b i) (color i))))
def phase (b e i : Bool) : Prog false w (Ty.a Slot5) := .tab (count b) (cell b e i)

theorem count_value (H : ℕ) (b : Bool) : (run (count b) H).val=levelCount H b*11 := by
  cases b <;> rfl
theorem count_valid (H : ℕ) (b : Bool) : (run (count b) H).valid := by
  cases b <;> trivial
theorem count_work (H : ℕ) (b : Bool) : (run (count b) H).work≤9 := by
  cases b <;> simp [count,levels,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
theorem count_peak (H : ℕ) (b : Bool) : (run (count b) H).peak≤11*(H+1) := by
  cases b <;> simp [count,levels,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,Nat.mul_comm]

theorem cell_value (H j : ℕ) (b e i : Bool) :
    (run (cell b e i) (H,j)).val=encode (decodedSlot H b e i (j/11) (j%11)) := by
  cases b <;> cases e <;> cases i <;> rfl
theorem cell_valid (H j : ℕ) (b e i : Bool) : (run (cell b e i) (H,j)).valid := by
  cases b <;> cases e <;> cases i <;> trivial
theorem cell_work (H j : ℕ) (b e i : Bool) : (run (cell b e i) (H,j)).work≤60 := by
  cases b <;> cases e <;> cases i <;>
    simp [cell,depth,color,nat,bit,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
theorem cell_peak (H j : ℕ) (b e i : Bool) (hj:j<levelCount H b*11) :
    (run (cell b e i) (H,j)).peak≤H+11 := by
  have hm:=Nat.mod_lt j (by omega : 0<11)
  cases b <;> cases e <;> cases i <;>
    simp only [levelCount,Bool.false_eq_true,ite_false,ite_true] at hj <;>
    simp [cell,depth,color,nat,bit,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay] <;> omega

theorem phase_value (H : ℕ) (b e i : Bool) :
    (run (phase b e i) H).val=ofList ((slots H b e i).map encode) := by
  change (Bill.tab (run (count b) H).val Slot5.blank
    (fun j=>run (cell b e i) (H,j))).val=_
  rw [count_value,ModelEquivalenceInterpreter.tab_value,
    UniformReplaySlotIndex.slots_ofFn,List.map_ofFn]
  change (Tape.tab (levelCount H b*11) (fun j=>(run (cell b e i) (H,j)).val))=
    DFTModelCacheDescriptor.listTape (List.ofFn (fun j : Fin (levelCount H b*11)=>
      encode (decodedSlot H b e i (j.val/11) (j.val%11))))
  rw [DFTModelCacheDescriptor.listTape_ofFn]
  unfold Tape.tab
  congr 1
  funext j
  exact cell_value H j.val b e i

theorem phase_valid (H : ℕ) (b e i : Bool) : (run (phase b e i) H).valid := by
  change (run (count b) H).valid ∧ (Bill.tab (run (count b) H).val Slot5.blank
    (fun j=>run (cell b e i) (H,j))).valid
  exact ⟨count_valid H b,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _=>cell_valid H j b e i)⟩

theorem phase_work (H : ℕ) (b e i : Bool) :
    (run (phase b e i) H).work≤704*(H+1)+12 := by
  change (run (count b) H).work+(Bill.tab (run (count b) H).val Slot5.blank
    (fun j=>run (cell b e i) (H,j))).work+1≤_
  rw [count_value,ModelEquivalenceInterpreter.tab_work]
  have hc:=count_work H b
  have bound:(∑j∈Finset.range (levelCount H b*11),(run (cell b e i) (H,j)).work)≤
      60*(levelCount H b*11) := by
    calc
      _≤∑_j∈Finset.range (levelCount H b*11),60 :=
        Finset.sum_le_sum (fun j _=>cell_work H j b e i)
      _=_:=by simp [Nat.mul_comm]
  have hl:levelCount H b≤H+1 := by cases b <;> simp [levelCount]
  omega

theorem phase_peak (H : ℕ) (b e i : Bool) :
    (run (phase b e i) H).peak≤11*(H+1) := by
  change max (max (run (count b) H).peak
    (Bill.tab (run (count b) H).val Slot5.blank
      (fun j=>run (cell b e i) (H,j))).peak) 0≤_
  rw [count_value,ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,max_le_iff]
  refine ⟨count_peak H b,?_,?_⟩
  · have hl:levelCount H b≤H+1 := by cases b <;> simp [levelCount]
    omega
  · apply Finset.sup_le
    intro j hj
    exact (cell_peak H j b e i (Finset.mem_range.mp hj)).trans (by omega)

end
end ExactFourierCircuits.DFTModelCacheReplaySlots
