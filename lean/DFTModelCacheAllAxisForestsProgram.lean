import DFTModelCacheAxisRootsCorrect
import DFTModelCacheSpectrumForestBounds

set_option autoImplicit false

/-! Closed preparation of the spectrum forest of every generated CRT axis.
The second master-order computation is intentional and fully charged.
This produces spectrum banks, not matching factors or a calendar cache. -/
namespace ExactFourierCircuits.DFTModelCacheAllAxisForests
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelCacheAxisRoots.program DFTModelRoot.program
  DFTModelCacheSpectrumForest.program

abbrev Input := p w sc
abbrev RootBank := Ty.a (p w sc)
abbrev Context := p RootBank (p w sc)
abbrev Cell := p Context w
abbrev Output := p RootBank (Ty.a DFTModelCacheSpectrumForest.Output)

def setup : Prog false Input Context :=
  .fork DFTModelCacheAxisRoots.program
    (.fork (.comp (.atom .fst) DFTModelRoot.program) (.atom .snd))
def count : Prog false Context w := .comp (.atom .fst) (.atom .len)
def row : Prog false Cell (p w sc) :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) (.atom .look)
def radix : Prog false Cell w := .comp row (.atom .fst)
def master : Prog false Cell (p w sc) := .comp (.atom .fst) (.atom .snd)
def argument : Prog false Cell DFTModelCacheSpectrumForest.Input :=
  .fork (.fork radix (.atom (.lit 0))) master
def cell : Prog false Cell DFTModelCacheSpectrumForest.Output :=
  .comp argument DFTModelCacheSpectrumForest.program
def forests : Prog false Context (Ty.a DFTModelCacheSpectrumForest.Output) :=
  .tab count cell
def body : Prog false Context Output := .fork (.atom .fst) forests
def program : Prog false Input Output := .comp setup body

theorem setup_run (n : ℕ) (z : ℂ) : run setup (n,z)=
    ⟨((run DFTModelCacheAxisRoots.program (n,z)).val,((run DFTModelRoot.program n).val,z)),
      (run DFTModelCacheAxisRoots.program (n,z)).work+(run DFTModelRoot.program n).work+5,
      max (run DFTModelCacheAxisRoots.program (n,z)).peak (run DFTModelRoot.program n).peak,
      (run DFTModelCacheAxisRoots.program (n,z)).valid ∧ (run DFTModelRoot.program n).valid⟩ := by
  simp [setup,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem cell_run (roots : RootBank.T) (D i : ℕ) (z : ℂ) :
    run cell ((roots,(D,z)),i)=
      (run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).pay 16 0 := by
  simp [cell,argument,radix,row,master,run,Code.run,Atom.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]
  omega

theorem body_run (roots : RootBank.T) (D : ℕ) (z : ℂ) :
    run body (roots,(D,z))=
      ((Bill.tab roots.len DFTModelCacheSpectrumForest.Output.blank
        (fun i=>run cell ((roots,(D,z)),i))).pass
          (fun fs=>Bill.one (roots,fs))).pay 5 roots.len := by
  simp [body,forests,count,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  constructor
  · omega
  · ac_rfl

theorem body_value (roots : RootBank.T) (D : ℕ) (z : ℂ) :
    (run body (roots,(D,z))).val=(roots,Tape.tab roots.len (fun i=>
      (run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).val)) := by
  rw [body_run]
  change (roots,(Bill.tab _ _ _).val)=_
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 1

theorem body_work (roots : RootBank.T) (D : ℕ) (z : ℂ) :
    (run body (roots,(D,z))).work=8+20*roots.len+
      ∑i∈Finset.range roots.len,
        (run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).work := by
  rw [body_run]
  change (Bill.tab _ _ _).work+1+5=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have cells : (∑i∈Finset.range roots.len,(run cell ((roots,(D,z)),i)).work)=
      ∑i∈Finset.range roots.len,
        ((run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).work+16) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [cell_run]
    rfl
  rw [cells,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem body_valid (roots : RootBank.T) (D : ℕ) (z : ℂ)
    (h : ∀i,i<roots.len→
      (run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).valid) :
    (run body (roots,(D,z))).valid := by
  rw [body_run]
  change (Bill.tab _ _ _).valid ∧ True
  refine ⟨(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr ?_,trivial⟩
  intro i hi
  rw [cell_run]
  exact h i hi

theorem body_peak (roots : RootBank.T) (D B : ℕ) (z : ℂ) (hlen : roots.len≤B)
    (h : ∀i,i<roots.len→
      (run DFTModelCacheSpectrumForest.program ((roots.look i (0,0) |>.1,0),(D,z))).peak≤B) :
    (run body (roots,(D,z))).peak≤B := by
  rw [body_run]
  change max (max (Bill.tab _ _ _).peak 0) roots.len≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (max_le hlen ?_) (Nat.zero_le _)) hlen
  apply Finset.sup_le
  intro i hi
  rw [cell_run]
  exact max_le (h i (Finset.mem_range.mp hi)) (Nat.zero_le _)

end
end ExactFourierCircuits.DFTModelCacheAllAxisForests
