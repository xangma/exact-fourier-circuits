import DFTModelCacheReplaySlots

set_option autoImplicit false

/-! Rectangle macro refinement: every replay slot occupies exactly 28 native
ticks, including empty matching colors. Calendar macro tags are not native ABI
kinds: every event emitted here has native kind0 (one shear word). -/
namespace ExactFourierCircuits.DFTModelCacheReplaySlots
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheCalendar (Row7)
open scoped BigOperators
noncomputable section

abbrev TimingInput : Ty := p w (p Row7 (Ty.a Slot5))
abbrev TimingCellInput : Ty := p TimingInput w
abbrev Event : Ty := p w (p w (p Row7 Slot5))
def timingCount : Prog false TimingInput w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .len))
def timingStart : Prog false TimingCellInput w := .comp (.atom .fst) (.atom .fst)
def timingRow : Prog false TimingCellInput Row7 :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def timingSlots : Prog false TimingCellInput (Ty.a Slot5) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def timingSlot : Prog false TimingCellInput Slot5 :=
  .comp (.fork timingSlots (.atom .snd)) (.atom .look)
def timingCell : Prog false TimingCellInput Event :=
  .fork (nat .add timingStart (nat .mul (.atom (.lit 28)) (.atom .snd)))
    (.fork (.atom (.lit 0)) (.fork timingRow timingSlot))
def annotate : Prog false TimingInput (Ty.a Event) := .tab timingCount timingCell

theorem timingCount_run (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    run timingCount (start,(row,ss))=⟨ss.len,5,ss.len,True⟩ := by
  simp [timingCount,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem annotate_run (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    run annotate (start,(row,ss))=
      (Bill.tab ss.len Event.blank (fun j=>run timingCell ((start,(row,ss)),j))).pay 6 ss.len := by
  change ((run timingCount (start,(row,ss))).pass (fun n=>Bill.tab n Event.blank
    (fun j=>run timingCell ((start,(row,ss)),j)))).pay 1 0=_
  rw [timingCount_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem timingCell_value (start j : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run timingCell ((start,(row,ss)),j)).val=
      (start+28*j,(0,(row,ss.look j Slot5.blank))) := rfl
theorem timingCell_valid (start j : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run timingCell ((start,(row,ss)),j)).valid := by trivial
theorem timingCell_work (start j : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run timingCell ((start,(row,ss)),j)).work=29 := by
  simp [timingCell,timingStart,timingRow,timingSlot,timingSlots,nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
theorem timingCell_peak (start j : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run timingCell ((start,(row,ss)),j)).peak ≤ start+28*j+28 := by
  simp [timingCell,timingStart,timingRow,timingSlot,timingSlots,nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem annotate_value (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run annotate (start,(row,ss))).val=Tape.tab ss.len
      (fun j=>(start+28*j,(0,(row,ss.look j Slot5.blank)))) := by
  change (Bill.tab ss.len Event.blank
    (fun j=>run timingCell ((start,(row,ss)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl
theorem annotate_valid (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run annotate (start,(row,ss))).valid := by
  rw [annotate_run]
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _=>timingCell_valid start j row ss)
theorem annotate_work (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run annotate (start,(row,ss))).work=33*ss.len+8 := by
  rw [annotate_run]
  change (Bill.tab ss.len Event.blank
    (fun j=>run timingCell ((start,(row,ss)),j))).work+6=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have point : (fun j=>(run timingCell ((start,(row,ss)),j)).work)=fun _=>29 := by
    funext j
    exact timingCell_work start j row ss
  rw [point]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega
theorem annotate_peak (start : ℕ) (row : Row7.T) (ss : Tape Slot5.T) :
    (run annotate (start,(row,ss))).peak ≤ start+29*ss.len+28 := by
  rw [annotate_run]
  change max (Bill.tab ss.len Event.blank
    (fun j=>run timingCell ((start,(row,ss)),j))).peak ss.len≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  apply max_le
  · apply max_le (by omega)
    apply Finset.sup_le
    intro j hj
    exact (timingCell_peak start j row ss).trans (by
      have:=Finset.mem_range.mp hj
      omega)
  · omega

end
end ExactFourierCircuits.DFTModelCacheReplaySlots
