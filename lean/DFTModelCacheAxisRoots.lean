import DFTModelWorkingHeadersClosed
import DFTModelRootExtraction
import DFTModelRecursiveScalarCore

set_option autoImplicit false

/-! Charged roots for every actual selected axis, from n and the one master
root. No local-root tape, selected prime list or order is an input.
Paper revision E, §5.3, paragraph after (5.9), p. 23: divisor roots are
obtained by powering the one master root. This does not prepare a cache forest. -/
namespace ExactFourierCircuits.DFTModelCacheAxisRoots
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Input := p w sc
abbrev Context := p DFTModelCRTMetadata.Input (p w sc)
abbrev Cell := p Context w

def setup : Prog false Input Context :=
  .fork (.comp (.atom .fst) DFTModelWorkingHeaders.program)
    (.fork (.comp (.atom .fst) DFTModelRoot.program) (.atom .snd))

def count : Prog false Context w := .comp (.atom .fst) DFTModelCRTMetadata.axisCount
def radix : Prog false Cell w :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd))
    DFTModelCRTMetadata.radix
def rootInput : Prog false Cell DFTModelRootExtraction.Input :=
  .fork radix (.comp (.atom .fst) (.atom .snd))
def scalar : Prog false Cell sc := .comp rootInput DFTModelRootExtraction.program
def cell : Prog false Cell (p w sc) := .fork radix scalar
def bank : Prog false Context (Ty.a (p w sc)) := .tab count cell
def program : Prog false Input (Ty.a (p w sc)) := .comp setup bank

attribute [local irreducible] DFTModelWorkingHeaders.program DFTModelRoot.program
  DFTModelRootExtraction.program

theorem setup_run (n : ℕ) (z : ℂ) : run setup (n,z)=
    ⟨((run DFTModelWorkingHeaders.program n).val,((run DFTModelRoot.program n).val,z)),
      (run DFTModelWorkingHeaders.program n).work+(run DFTModelRoot.program n).work+7,
      max (run DFTModelWorkingHeaders.program n).peak (run DFTModelRoot.program n).peak,
      (run DFTModelWorkingHeaders.program n).valid ∧ (run DFTModelRoot.program n).valid⟩ := by
  simp [setup,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem count_run (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) :
    run count (x,(D,z))=⟨x.1+1,7,x.1+1,True⟩ := by
  rw [count,comp_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [show run DFTModelCRTMetadata.axisCount x=⟨x.1+1,5,x.1+1,True⟩ from
    DFTModelCRTMetadata.axisCount_run x]
  simp

theorem radix_run (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    run radix ((x,(D,z)),i)=⟨DFTModelCRTMetadata.radixValue x i,
      (if i<x.1 then 19 else 15)+6,if i<x.1 then 1 else 0,True⟩ := by
  rw [radix,comp_run,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [show run DFTModelCRTMetadata.radix (x,i)=_ from DFTModelCRTMetadata.radix_run x i]
  simp only [true_and,max_zero,zero_max]
  congr 1
  omega

theorem rootInput_run (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    run rootInput ((x,(D,z)),i)=⟨(DFTModelCRTMetadata.radixValue x i,(D,z)),
      (if i<x.1 then 19 else 15)+10,if i<x.1 then 1 else 0,True⟩ := by
  rw [rootInput,fork_run,radix_run]
  simp [comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem scalar_run (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    run scalar ((x,(D,z)),i)=
      (run DFTModelRootExtraction.program (DFTModelCRTMetadata.radixValue x i,(D,z))).pay
        ((if i<x.1 then 19 else 15)+11) (if i<x.1 then 1 else 0) := by
  rw [scalar,comp_run,rootInput_run]
  simp [Bill.pass,Bill.pay,max_comm]
  omega

theorem cell_value (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    (run cell ((x,(D,z)),i)).val=
      (DFTModelCRTMetadata.radixValue x i,z^(D/DFTModelCRTMetadata.radixValue x i)) := by
  rw [cell,fork_run,radix_run,scalar_run]
  change (DFTModelCRTMetadata.radixValue x i,
    (run DFTModelRootExtraction.program (DFTModelCRTMetadata.radixValue x i,(D,z))).val)=_
  rw [DFTModelRootExtraction.program_value]

theorem cell_valid (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    (run cell ((x,(D,z)),i)).valid := by
  rw [cell,fork_run,radix_run,scalar_run]
  exact ⟨trivial,DFTModelRootExtraction.program_valid _ _ _,trivial⟩

theorem cell_work (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    (run cell ((x,(D,z)),i)).work≤40*(Nat.log2 (D+1)+1)+78 := by
  have h:=DFTModelRootExtraction.program_work (DFTModelCRTMetadata.radixValue x i) D z
  have le : Nat.log2 (D/DFTModelCRTMetadata.radixValue x i+1)≤Nat.log2 (D+1) :=
    (Nat.le_log2 (n:=D+1) (k:=Nat.log2 (D/DFTModelCRTMetadata.radixValue x i+1)) (Nat.succ_ne_zero _)).2
      ((Nat.log2_self_le (n:=D/DFTModelCRTMetadata.radixValue x i+1) (Nat.succ_ne_zero _)).trans
        (Nat.add_le_add_right (Nat.div_le_self D _) 1))
  rw [cell,fork_run,radix_run,scalar_run]
  change (if i<x.1 then 19 else 15)+6+
    ((run DFTModelRootExtraction.program _).work+(if i<x.1 then 19 else 15)+11+1)≤_
  split_ifs <;> omega

theorem cell_peak (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) (i : ℕ) :
    (run cell ((x,(D,z)),i)).peak≤D+2 := by
  have h:=DFTModelRootExtraction.program_peak (DFTModelCRTMetadata.radixValue x i) D z
  rw [cell,fork_run,radix_run,scalar_run]
  change max (if i<x.1 then 1 else 0)
    (max (max (run DFTModelRootExtraction.program _).peak (if i<x.1 then 1 else 0)) 0)≤_
  split_ifs <;> omega

theorem bank_value (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) :
    (run bank (x,(D,z))).val=Tape.tab (x.1+1)
      (fun i=>(DFTModelCRTMetadata.radixValue x i,z^(D/DFTModelCRTMetadata.radixValue x i))) := by
  change (Bill.tab (run count (x,(D,z))).val (p w sc).blank
    (fun i=>run cell ((x,(D,z)),i))).val=_
  rw [count_run,ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (cell_value x D z))

theorem bank_valid (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) :
    (run bank (x,(D,z))).valid := by
  change (run count (x,(D,z))).valid ∧
    (Bill.tab (run count (x,(D,z))).val (p w sc).blank
      (fun i=>run cell ((x,(D,z)),i))).valid
  rw [count_run]
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun i _=>cell_valid x D z i)⟩

theorem bank_work (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) :
    (run bank (x,(D,z))).work≤10+(x.1+1)*(40*(Nat.log2 (D+1)+1)+82) := by
  change (run count (x,(D,z))).work+
    (Bill.tab (run count (x,(D,z))).val (p w sc).blank
      (fun i=>run cell ((x,(D,z)),i))).work+1≤_
  rw [count_run,ModelEquivalenceInterpreter.tab_work]
  have hs : (∑i∈Finset.range (x.1+1),(run cell ((x,(D,z)),i)).work)≤
      (x.1+1)*(40*(Nat.log2 (D+1)+1)+78) := by
    calc
      _≤∑_i∈Finset.range (x.1+1),(40*(Nat.log2 (D+1)+1)+78) :=
        Finset.sum_le_sum (fun i _=>cell_work x D z i)
      _=_ := by simp
  nlinarith

theorem bank_peak (x : DFTModelCRTMetadata.Input.T) (D : ℕ) (z : ℂ) :
    (run bank (x,(D,z))).peak ≤ max (x.1+1) (D+2) := by
  change max (max (run count (x,(D,z))).peak
    (Bill.tab (run count (x,(D,z))).val (p w sc).blank
      (fun i=>run cell ((x,(D,z)),i))).peak) 0≤_
  rw [count_run,ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  exact max_le (le_max_left _ _) (max_le (le_max_left _ _)
    (Finset.sup_le (fun i _=>(cell_peak x D z i).trans (le_max_right _ _))))

end
end ExactFourierCircuits.DFTModelCacheAxisRoots
