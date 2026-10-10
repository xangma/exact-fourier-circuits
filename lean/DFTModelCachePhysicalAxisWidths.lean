import DFTModelGlobalCompactPoolsProduced

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCachePhysicalAxis
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev WidthInput := p w w
abbrev WidthCell := p WidthInput w
def widthCount : Prog false WidthInput w :=
  .comp (.fork (.atom .fst) (.atom .snd)) (.atom (.int .sub))
def widthCell : Prog false WidthCell w :=
  .ifz (.comp (.fork (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
    (.atom (.int .lt))) (.atom (.lit 1)) (.atom (.lit 2))
def widths : Prog false WidthInput (Ty.a w) := .tab widthCount widthCell

theorem widthCount_run (r M:ℕ) : run widthCount (r,M)=⟨r-M,5,r-M,True⟩ := by
  simp [widthCount,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem widthCell_run (r M j:ℕ) : run widthCell ((r,M),j)=
    ⟨if j<M then 2 else 1,9,if j<M then 2 else 1,True⟩ := by
  by_cases h:j<M <;>
    simp [widthCell,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,h]

attribute [local irreducible] widthCell widthCount

theorem widths_run (r M:ℕ) : run widths (r,M)=
    (Bill.tab (r-M) 0 (fun j=>run widthCell ((r,M),j))).pay 6 (r-M) := by
  unfold widths
  change ((run widthCount (r,M)).pass
    (fun n=>Bill.tab n 0 (fun j=>run widthCell ((r,M),j)))).pay 1 0=_
  rw [widthCount_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem widths_value (r M:ℕ) : (run widths (r,M)).val=
    Tape.tab (r-M) (fun j=>if j<M then 2 else 1) := by
  rw [widths_run]
  change (Bill.tab (r-M) 0 (fun j=>run widthCell ((r,M),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (fun j=>congrArg Bill.val (widthCell_run r M j)))

theorem widths_work (r M:ℕ) : (run widths (r,M)).work=13*(r-M)+8 := by
  rw [widths_run]
  change (Bill.tab (r-M) 0 (fun j=>run widthCell ((r,M),j))).work+6=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw:(fun j=>(run widthCell ((r,M),j)).work)=fun _=>9:=by
    funext j;exact congrArg Bill.work (widthCell_run r M j)
  rw [hw]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem widths_valid (r M:ℕ) : (run widths (r,M)).valid := by
  rw [widths_run]
  change (Bill.tab (r-M) 0 (fun j=>run widthCell ((r,M),j))).valid
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>by rw [widthCell_run];trivial)

theorem widths_peak (r M:ℕ) : (run widths (r,M)).peak ≤ max 2 (r-M) := by
  rw [widths_run]
  change max (Bill.tab (r-M) 0 (fun j=>run widthCell ((r,M),j))).peak (r-M)≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h:(Finset.range (r-M)).sup (fun j=>(run widthCell ((r,M),j)).peak)≤2:=by
    apply Finset.sup_le
    intro j _
    rw [widthCell_run]
    change (if j<M then 2 else 1)≤2
    split <;>omega
  omega

theorem widths_native (r M:ℕ) (capacity:2*M≤r) : (run widths (r,M)).val=
    DFTModelGlobalClockRecords.listTape (UniformMatchingAxisTableMachine.widths r M) := by
  rw [widths_value]
  apply DFTModelGlobalClockRecords.tape_ext 0
  · exact (UniformMatchingAxisTableMachine.widths_length r M capacity).symm
  · intro j hj
    change j<r-M at hj
    have hl:j<(UniformMatchingAxisTableMachine.widths r M).length:=by
      rw [UniformMatchingAxisTableMachine.widths_length r M capacity];exact hj
    simp only [Tape.tab,Tape.look,DFTModelGlobalClockRecords.listTape,hj,hl,↓reduceDIte]
    unfold UniformMatchingAxisTableMachine.widths
    by_cases hm:j<M
    · simp [hm]
    · simp [List.getElem_append,hm]

end
end ExactFourierCircuits.DFTModelCachePhysicalAxis
