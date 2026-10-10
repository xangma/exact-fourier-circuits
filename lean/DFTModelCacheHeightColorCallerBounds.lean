import DFTModelCacheHeightColorCallerCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightColorCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheHeight (Words words_mono)
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheHeightRaw.program
 DFTModelCacheHeight.program DFTModelCacheColorRebaseSelected.program
 DFTModelCacheColorSelection.program

def rowWordBound (B:ℕ) : ℕ := (2*B+2)^DFTModelCacheHeight.degree DFTModelCacheHeight.row+2*B+2

theorem height_output_words (x:DFTModelCacheHeight.Input.T) (B:ℕ) (five:5≤B)
 (words:Words DFTModelCacheHeight.Input B x) :
 Words (Ty.a DFTModelCacheHeight.Row) (rowWordBound B) (run DFTModelCacheHeight.program x).val := by
 let M:=2*B+2
 have larger:B≤M:=by dsimp [M];omega
 have slots:DFTModelCacheHeight.slotCount x≤M:=
  (DFTModelCacheHeight.slotCount_bound x B words).trans (by dsimp [M];omega)
 have input:Words DFTModelCacheHeight.Input M x:=words_mono _ larger _ words
 rw [DFTModelCacheHeight.program_value]
 refine ⟨?_,?_⟩
 · change (DFTModelCacheHeight.rowsPrefix x (DFTModelCacheHeight.slotCount x)).length≤_
   exact (DFTModelCacheHeight.rowsPrefix_length _ _).trans (slots.trans (by unfold M rowWordBound;omega))
 · intro i
   have row:=DFTModelCacheHeight.steps_row_words x i.val M (DFTModelCacheHeight.slotCount x)
    (by dsimp [M];omega) input slots
   rw [DFTModelCacheHeight.steps_value] at row
   change Words DFTModelCacheHeight.Row (M^DFTModelCacheHeight.degree DFTModelCacheHeight.row)
    ((DFTModelCacheHeight.rowsPrefix x (DFTModelCacheHeight.slotCount x))[i.val]?.getD
      DFTModelCacheHeight.Row.blank) at row
   exact words_mono _ (by unfold M rowWordBound;omega) _ row

def selectionWordBound (c a e A C P d:ℕ) : ℕ :=
 c+rowWordBound (DFTModelCacheHeightRaw.wordBound a e A C P d)+2*(dag a e).size+16

theorem generated_words (a e A C P d:ℕ) (enabled:Bool) :
 Words (Ty.a DFTModelCacheColor.Row)
  (rowWordBound (DFTModelCacheHeightRaw.wordBound a e A C P d))
  (producedRows a e A C P d enabled) := by
 obtain ⟨u,t,source⟩:=DFTModelCacheTopology.execution_values a e
 have sourceWords:=DFTModelCacheHeightRaw.source_input_words a e A C P d enabled u t source
 have five:5≤DFTModelCacheHeightRaw.wordBound a e A C P d:=by
  unfold DFTModelCacheHeightRaw.wordBound;omega
 have rows:=height_output_words _ _ five sourceWords
 unfold producedRows
 rw [DFTModelCacheHeightRaw.program_run]
 exact rows

theorem selection_words (c a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 Words DFTModelCacheColorSelection.Input (selectionWordBound c a e A C P d)
  (selectionInput c a e A C P d enabled) := by
 let B:=selectionWordBound c a e A C P d
 have bounds:c≤B ∧ rowWordBound (DFTModelCacheHeightRaw.wordBound a e A C P d)≤B ∧
  2*(dag a e).size≤B ∧ 11≤B:=by dsimp [B,selectionWordBound];omega
 have rows:=words_mono _ bounds.2.1 _ (generated_words a e A C P d enabled)
 have proper:=DFTModelCacheColorRebase.degree_six A (localBound a e) 0
  (fun i=>Fin.elim0 i) (producedRows a e A C P d enabled) (edges a e d enabled)
  (physical_rows a e A C P d enabled height) (local_range a e d enabled) (degree_six a e A d enabled)
 have length:(colored a e A C P d enabled).2.2.2.len=(bucket a e d enabled).length:=proper.2.1
 have count:(bucket a e d enabled).length≤2*(dag a e).size:=by
  rw [←(physical_rows a e A C P d enabled height).length]
  exact rows_length a e A C P d enabled
 refine ⟨bounds.1,rows,?_,?_⟩
 · change (colored a e A C P d enabled).2.2.2.len≤B
   exact length.le.trans (count.trans bounds.2.2.1)
 · change ∀i:Fin (colored a e A C P d enabled).2.2.2.len,
    (colored a e A C P d enabled).2.2.2.pos i≤B
   intro i
   let j:Fin (bucket a e d enabled).length:=Fin.cast length i
   have hi:i.val<(colored a e A C P d enabled).2.2.2.len:=i.isLt
   have read:(colored a e A C P d enabled).2.2.2.look j.val 0=
    (colored a e A C P d enabled).2.2.2.pos i:=by
    change (colored a e A C P d enabled).2.2.2.look i.val 0=_
    rw [Tape.look_of_lt _ _ hi]
   have below:=proper.2.2.2.1 j
   change (colored a e A C P d enabled).2.2.2.look j.val 0<11 at below
   rw [read] at below
   exact below.le.trans bounds.2.2.2

def colorPeak (a e:ℕ) : ℕ := 10002*(localBound a e+2*(dag a e).size+1)^2
def peakBudget (c a e A C P d:ℕ) : ℕ :=
 max (DFTModelCacheHeightRaw.peakBudget a e A C P d)
  (max (localBound a e) (max (colorPeak a e)
   ((selectionWordBound c a e A C P d)^DFTModelCacheColorSelection.wordDegree)))

theorem color_peak (a e M:ℕ) (bound:M≤2*(dag a e).size) :
 DFTModelCacheColorRebase.peakBound (localBound a e) M≤colorPeak a e := by
 have h:=DFTModelCacheColor.polynomial_peak (localBound a e) M
 have monotone:=Nat.pow_le_pow_left
  (Nat.add_le_add_right (Nat.add_le_add_left bound (localBound a e)) 1) 2
 have one:1≤localBound a e+2*(dag a e).size+1:=by omega
 have linear:localBound a e+2*(dag a e).size+1≤
  (localBound a e+2*(dag a e).size+1)^2:=by nlinarith
 unfold DFTModelCacheColorRebase.peakBound colorPeak
 apply max_le
 · apply max_le <;> nlinarith
 · exact h.trans ((Nat.mul_le_mul_left 10000 monotone).trans (by omega))


/-- Explicit peak: physical labels/addresses bound integer words, never the
number of color/printer steps. Both real producer calls are included once. -/
theorem program_peak (c a e A C P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 (run program (input c a e A C P d enabled)).peak≤peakBudget c a e A C P d := by
 obtain ⟨_,_,_,raw⟩:=DFTModelCacheHeightRaw.execution_local a e A C P d enabled
 have five:5 ≤ selectionWordBound c a e A C P d:=by unfold selectionWordBound;omega
 have selected:=DFTModelCacheColorRebaseSelected.peak c A (localBound a e) 0
  (selectionWordBound c a e A C P d) (fun i=>Fin.elim0 i)
  (producedRows a e A C P d enabled) (edges a e d enabled)
  (physical_rows a e A C P d enabled height) (local_range a e d enabled) five
  (selection_words c a e A C P d enabled height)
 have localPeak:=color_peak a e (producedRows a e A C P d enabled).len
  (rows_length a e A C P d enabled)
 rw [program_source_run]
 unfold peakBudget
 exact max_le_max raw.2.2 (max_le_max (le_refl _) (selected.trans
  (max_le_max localPeak (le_refl _))))

end
end ExactFourierCircuits.DFTModelCacheHeightColorCaller
