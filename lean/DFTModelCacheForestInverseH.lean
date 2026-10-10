import DFTModelCacheForest

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier
noncomputable section

def getInverseH : Prog false Row sc :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def inverseHCell : Prog false (p Output w) sc :=
  .comp (.comp (.fork (.atom .fst) (.atom .snd)) (.atom .look)) getInverseH
/-- Charged extraction, in the actual coefficient order needed by Toeplitz. -/
def inverseHBank : Prog false Output (Ty.a sc) := .tab (.atom .len) inverseHCell
def prepareInverseH : Prog false Input (Ty.a sc) := .comp program inverseHBank

theorem inverseHCell_run (t : Tape Row.T) (j : ℕ) :
    run inverseHCell (t,j)=⟨(t.look j Row.blank).2.2.1,11,0,True⟩ := by
  simp [inverseHCell,getInverseH,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem inverseHBank_run (t : Tape Row.T) :
    run inverseHBank t=
      (Bill.tab t.len sc.blank (fun j => run inverseHCell (t,j))).pay 2 t.len := by
  change ((Bill.word t.len).pass (fun n =>
    Bill.tab n sc.blank (fun j => run inverseHCell (t,j)))).pay 1 0=_
  simp [Bill.word,Bill.pass,Bill.pay]
  omega

theorem inverseHBank_value (t : Tape Row.T) :
    (run inverseHBank t).val=Tape.tab t.len (fun j => (t.look j Row.blank).2.2.1) := by
  rw [inverseHBank_run]
  change (Bill.tab t.len sc.blank (fun j => run inverseHCell (t,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab t.len)
  funext j
  exact congrArg Bill.val (inverseHCell_run t j)

theorem inverseHBank_work (t : Tape Row.T) : (run inverseHBank t).work=15*t.len+4 := by
  rw [inverseHBank_run]
  change (Bill.tab t.len sc.blank (fun j => run inverseHCell (t,j))).work+2=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run inverseHCell (t,j)).work)=(fun _ : ℕ => 11) := by
    funext j
    exact congrArg Bill.work (inverseHCell_run t j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem inverseHBank_peak (t : Tape Row.T) : (run inverseHBank t).peak≤t.len := by
  rw [inverseHBank_run]
  change max (Bill.tab t.len sc.blank (fun j => run inverseHCell (t,j))).peak t.len≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (Finset.range t.len).sup (fun j => (run inverseHCell (t,j)).peak)=0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro j _
    rw [inverseHCell_run]
  rw [h]
  omega

theorem inverseHBank_valid (t : Tape Row.T) : (run inverseHBank t).valid := by
  rw [inverseHBank_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  rw [inverseHCell_run]
  trivial

theorem prepareInverseH_value (r : ℕ) (omega : ℂ) :
    (run prepareInverseH (r,omega)).val=
      Tape.tab r (fun j => (NewtonFourier.H omega j)⁻¹) := by
  change (run inverseHBank (run program (r,omega)).val).val=_
  rw [program_value,inverseHBank_value]
  change (⟨r,fun j : Fin r => ((values r omega).look j.val Row.blank).2.2.1⟩ : Tape ℂ)=
    ⟨r,fun j => (NewtonFourier.H omega j.val)⁻¹⟩
  congr 1
  funext j
  rw [Tape.look_of_lt _ _ (show j.val<(values r omega).len from j.isLt)]
  rfl

theorem prepareInverseH_valid {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) : (run prepareInverseH (r,omega)).valid :=
  ⟨program_valid hr primitive,inverseHBank_valid _⟩

theorem prepareInverseH_work (r : ℕ) (omega : ℂ) :
    (run prepareInverseH (r,omega)).work≤80*(r+1)^2 := by
  change (run program (r,omega)).work+
    (run inverseHBank (run program (r,omega)).val).work+1≤_
  rw [inverseHBank_work,program_length]
  have h := program_work r omega
  nlinarith

theorem prepareInverseH_peak (r : ℕ) (omega : ℂ) :
    (run prepareInverseH (r,omega)).peak≤r := by
  change max (max (run program (r,omega)).peak
    (run inverseHBank (run program (r,omega)).val).peak) 0≤r
  have h := inverseHBank_peak (run program (r,omega)).val
  rw [program_length] at h
  exact max_le (max_le (program_peak r omega) h) (Nat.zero_le _)

end
end ExactFourierCircuits.DFTModelCacheForest
