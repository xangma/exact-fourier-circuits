import DFTModelMemoryAffinePointwise
import UniformPhysicalCRTConsumerMachine

set_option autoImplicit false

/-! Paper §5.2–5.3: the literal BI gather followed by the literal AP gather.
The two genuine permutation tapes are inputs from preparation. One execution
retains both output banks, including conservative Boolean tags and offsets. -/
namespace ExactFourierCircuits.DFTModelOuterTailCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev GatherInput := p w (p (Ty.a w) (Ty.a Datum))

def gatherTable : Prog false (p GatherInput w) (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def gatherData : Prog false (p GatherInput w) (Ty.a Datum) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def gatherIndex : Prog false (p GatherInput w) w :=
  .comp (.fork gatherTable (.atom .snd)) (.atom .look)
def gatherCell : Prog false (p GatherInput w) Datum :=
  .comp (.fork gatherData gatherIndex) (.atom .look)
def gather : Prog false GatherInput (Ty.a Datum) := .tab (.atom .fst) gatherCell

theorem gatherCell_run (V j : ℕ) (a : Tape ℕ) (z : Tape Datum.T) :
    run gatherCell ((V,(a,z)),j) =
      ⟨z.look (a.look j 0) (0,(0,0)),17,0,True⟩ := by
  simp [gatherCell,gatherData,gatherIndex,gatherTable,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem gather_value (V : ℕ) (a : Tape ℕ) (z : Tape Datum.T) :
    (run gather (V,(a,z))).val =
      Tape.tab V (fun j => z.look (a.look j 0) (0,(0,0))) := by
  change (Bill.tab V Datum.blank (fun j => run gatherCell ((V,(a,z)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab V) (funext (fun j => congrArg Bill.val (gatherCell_run V j a z)))

theorem gather_work (V : ℕ) (a : Tape ℕ) (z : Tape Datum.T) :
    (run gather (V,(a,z))).work = 21*V+4 := by
  change 1+(Bill.tab V Datum.blank (fun j => run gatherCell ((V,(a,z)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run gatherCell ((V,(a,z)),j)).work) = (fun _ => 17) := by
    funext j
    exact congrArg Bill.work (gatherCell_run V j a z)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem gather_peak (V : ℕ) (a : Tape ℕ) (z : Tape Datum.T) :
    (run gather (V,(a,z))).peak = V := by
  change max (max 0 (Bill.tab V Datum.blank
    (fun j => run gatherCell ((V,(a,z)),j))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (fun j => (run gatherCell ((V,(a,z)),j)).peak) = (fun _ => 0) := by
    funext j
    exact congrArg Bill.peak (gatherCell_run V j a z)
  rw [h]
  simp

theorem gather_valid (V : ℕ) (a : Tape ℕ) (z : Tape Datum.T) :
    (run gather (V,(a,z))).valid := by
  change True ∧ (Bill.tab V Datum.blank
    (fun j => run gatherCell ((V,(a,z)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [gatherCell_run]
  trivial

abbrev Input := p w (p (Ty.a w) (p (Ty.a w) (Ty.a Datum)))
abbrev Output := p (Ty.a Datum) (Ty.a Datum)
def volume : Prog false Input w := .atom .fst
def alpha : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def beta : Prog false Input (Ty.a w) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def data : Prog false Input (Ty.a Datum) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def first : Prog false Input (Ty.a Datum) :=
  .comp (.fork volume (.fork beta data)) gather
def second : Prog false (p Input (Ty.a Datum)) (Ty.a Datum) :=
  .comp (.fork (.comp (.atom .fst) volume)
    (.fork (.comp (.atom .fst) alpha) (.atom .snd))) gather
def program : Prog false Input Output :=
  .comp (.fork (.atom .id) first) (.fork second (.atom .snd))

def input (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) : Input.T := (V,(a,(b,z)))
def gatherValue (V : ℕ) (a : Tape ℕ) (z : Tape Datum.T) : Tape Datum.T :=
  Tape.tab V (fun j => z.look (a.look j 0) (0,(0,0)))

attribute [local irreducible] gather
theorem program_run (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    run program (input V a b z) =
      ((run gather (V,(b,z))).pass (fun t =>
        (run gather (V,(a,t))).pass (fun u => Bill.one (u,t)))).pay 30 0 := by
  simp only [program,first,second,volume,alpha,beta,data,input,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  · omega

theorem program_value (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    (run program (input V a b z)).val =
      (gatherValue V a (gatherValue V b z),gatherValue V b z) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [gather_value,gather_value]
  rfl

theorem program_work (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    (run program (input V a b z)).work = 42*V+39 := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [gather_work,gather_work]
  omega

theorem program_peak (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    (run program (input V a b z)).peak = V := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [gather_peak,gather_peak]
  omega

theorem program_valid (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    (run program (input V a b z)).valid := by
  rw [program_run]
  exact ⟨gather_valid _ _ _,gather_valid _ _ _,trivial⟩

def permutation {V : ℕ} (a : Fin V ≃ Fin V) : Tape ℕ :=
  ⟨V,fun j => (a j).val⟩
def taggedTape {V : ℕ} (z : Fin V → Datum.T) : Tape Datum.T := ⟨V,z⟩

theorem gather_permutation {V : ℕ} (a : Fin V ≃ Fin V) (z : Fin V → Datum.T) :
    gatherValue V (permutation a) (taggedTape z) = taggedTape (fun j => z (a j)) := by
  unfold gatherValue taggedTape permutation
  dsimp only [Tape.tab]
  congr 1
  funext j
  simp [Tape.look,j.isLt,(a j).isLt]

theorem permutation_values {V : ℕ} (a b : Fin V ≃ Fin V) (z : Fin V → Datum.T) :
    (run program (input V (permutation a) (permutation b) (taggedTape z))).val =
      (taggedTape (fun j => z (b (a j))),taggedTape (fun j => z (b j))) := by
  rw [program_value,gather_permutation,gather_permutation]

theorem gather_lookup {V : ℕ} (a : Fin V ≃ Fin V) (aT : Tape ℕ) (z : Tape Datum.T)
    (table : ∀j : Fin V, aT.look j.val 0=(a j).val) (j : Fin V) :
    (gatherValue V aT z).look j.val (0,(0,0))=z.look (a j).val (0,(0,0)) := by
  change (Tape.tab V (fun q => z.look (aT.look q 0) (0,(0,0)))).look j.val (0,(0,0)) = _
  rw [Tape.look_of_lt]
  · exact congrArg (fun q => z.look q (0,(0,0))) (table j)
  · exact j.isLt

theorem program_lookups {V : ℕ} (a b : Fin V ≃ Fin V) (aT bT : Tape ℕ)
    (z : Tape Datum.T) (alphaTape : ∀j : Fin V, aT.look j.val 0=(a j).val)
    (betaTape : ∀j : Fin V, bT.look j.val 0=(b j).val) (j : Fin V) :
    (run program (input V aT bT z)).val.1.look j.val (0,(0,0))=
      z.look (b (a j)).val (0,(0,0)) ∧
    (run program (input V aT bT z)).val.2.look j.val (0,(0,0))=
      z.look (b j).val (0,(0,0)) := by
  rw [program_value]
  exact ⟨(gather_lookup a aT _ alphaTape j).trans (gather_lookup b bT z betaTape (a j)),
    gather_lookup b bT z betaTape j⟩

theorem work_preserved (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) :
    (run program (input V a b z)).work ≤ 3*(18*V+18) := by
  rw [program_work]
  omega

end
end ExactFourierCircuits.DFTModelOuterTailCRT
