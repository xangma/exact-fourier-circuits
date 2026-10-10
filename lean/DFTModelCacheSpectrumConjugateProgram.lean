import DFTModelConjugationRun
import DFTModelCacheSpectrumSource
import ModelEquivalenceInterpreter

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheSpectrumConjugate
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelCacheSpectrum.program

abbrev Input := DFTModelCacheSpectrum.Input
abbrev PairBank := Ty.a (Ty.p sc sc)
def inverseArgument : Prog false Input Input :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.comp (.atom .snd) (.atom .snd)) (.atom .inv)))

def banks : Prog false Input (p (Ty.a sc) (Ty.a sc)) :=
  .fork DFTModelCacheSpectrum.program
    (.comp inverseArgument DFTModelCacheSpectrum.program)

def zipCell : Prog false (p (p (Ty.a sc) (Ty.a sc)) w) (p sc sc) :=
  .fork (.comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) (.atom .look))
    (.comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look))

def zip : Prog false (p (Ty.a sc) (Ty.a sc)) PairBank :=
  .tab (.comp (.atom .fst) (.atom .len)) zipCell

def program : Prog false Input PairBank := .comp banks zip

theorem inverseArgument_run (m : DFTModelCacheDisplacement.Metadata.T) (D : ℕ) (z : ℂ) :
    run inverseArgument (m,(D,z))=⟨(m,(D,z⁻¹)),11,0,z≠0⟩ := by
  simp [inverseArgument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem zipCell_run (a b : Tape ℂ) (i : ℕ) :
    run zipCell ((a,b),i)=⟨(a.look i 0,b.look i 0),15,0,True⟩ := by
  simp [zipCell,run,Code.run,Atom.run,Ty.blank,Bill.one,Bill.pass,Bill.pay]

theorem zip_run (a b : Tape ℂ) :
    run zip (a,b)=(Bill.tab a.len (0,0) (fun i=>run zipCell ((a,b),i))).pay 4 a.len := by
  simp [zip,run,Code.run,Atom.run,Ty.blank,Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

theorem zip_value (a b : Tape ℂ) :
    (run zip (a,b)).val=Tape.tab a.len (fun i=>(a.look i 0,b.look i 0)) := by
  rw [zip_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem zip_work (a b : Tape ℂ) : (run zip (a,b)).work=19*a.len+6 := by
  rw [zip_run]
  change (Bill.tab _ _ _).work+4=_
  rw [ModelEquivalenceInterpreter.tab_work]
  change 2+4*a.len+(∑ i ∈ Finset.range a.len,15)+4=_
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem zip_peak (a b : Tape ℂ) : (run zip (a,b)).peak=a.len := by
  rw [zip_run]
  change max (Bill.tab _ _ _).peak a.len=_
  rw [ModelEquivalenceInterpreter.tab_peak]
  change max (max a.len ((Finset.range a.len).sup (fun _=>0))) a.len=_
  simp

theorem zip_valid (a b : Tape ℂ) : (run zip (a,b)).valid := by
  rw [zip_run]
  change (Bill.tab _ _ _).valid
  rw [ModelEquivalenceInterpreter.tab_valid]
  intro i hi
  rw [zipCell_run]
  trivial

def pairedBill (a b : Bill (Tape ℂ)) (nz : Prop) : Bill (Tape (ℂ × ℂ)) :=
  ⟨(run zip (a.val,b.val)).val,a.work+b.work+(run zip (a.val,b.val)).work+14,
    max a.peak (max b.peak (run zip (a.val,b.val)).peak),
    a.valid ∧ nz ∧ b.valid ∧ (run zip (a.val,b.val)).valid⟩

theorem program_run (m : DFTModelCacheDisplacement.Metadata.T) (D : ℕ) (z : ℂ) :
    run program (m,(D,z))=pairedBill
      (run DFTModelCacheSpectrum.program (m,(D,z)))
      (run DFTModelCacheSpectrum.program (m,(D,z⁻¹))) (z≠0) := by
  unfold program banks
  change (((run DFTModelCacheSpectrum.program (m,(D,z))).pass (fun a=>
    (((run inverseArgument (m,(D,z))).pass (run DFTModelCacheSpectrum.program)).pay 1 0).pass
      (fun b=>Bill.one (a,b)))).pass (run zip)).pay 1 0=_
  rw [inverseArgument_run]
  simp only [pairedBill,Bill.pass,Bill.pay,Bill.one,max_zero]
  congr 1 <;> first | omega | simp only [and_assoc,and_comm,and_left_comm,true_and]

end
end ExactFourierCircuits.DFTModelCacheSpectrumConjugate
