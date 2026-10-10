import DFTModelCacheSpectrumSum
import UniformToeplitzCrossDAG

set_option autoImplicit false

/-! A concrete quadratic prepared DFT. Each output row makes one binary
power call and one geometric dot-product loop. No spectrum is supplied. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumDFT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelScalarPower.program DFTModelCacheSpectrumSum.program

abbrev Input := DFTModelCacheSpectrumSum.Input
abbrev RowInput := p Input w

def length : Prog false RowInput w := .comp (.atom .fst) (.atom .fst)
def root : Prog false RowInput sc :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def tape : Prog false RowInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def power : Prog false RowInput sc :=
  .comp (.fork (.atom .snd) root) (.importClosed DFTModelScalarPower.program)
def argument : Prog false RowInput DFTModelCacheSpectrumSum.Input :=
  .fork length (.fork power tape)
def row : Prog false RowInput sc := .comp argument DFTModelCacheSpectrumSum.program
def program : Prog false Input (Ty.a sc) := .tab (.atom .fst) row

theorem argument_run (N j : ℕ) (omega : ℂ) (t : Tape ℂ) :
    run argument ((N,(omega,t)),j)=
      (run DFTModelScalarPower.program (j,omega)).pass
        (fun z=>⟨(N,(z,t)),19,0,True⟩) := by
  simp [argument,length,power,root,tape,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  omega

attribute [local irreducible] argument

theorem row_run (N j : ℕ) (omega : ℂ) (t : Tape ℂ) :
    run row ((N,(omega,t)),j)=
      ⟨DFTModelCacheSpectrumSum.value t (omega^j) N,
        (run DFTModelScalarPower.program (j,omega)).work+42*N+28,
        max (run DFTModelScalarPower.program (j,omega)).peak N,True⟩ := by
  change ((run argument ((N,(omega,t)),j)).pass
    (run DFTModelCacheSpectrumSum.program)).pay 1 0=_
  rw [argument_run]
  dsimp only [Bill.pass]
  rw [DFTModelScalarPower.program_value,DFTModelCacheSpectrumSum.program_run]
  have hv:=DFTModelScalarPower.program_valid j omega
  simp only [Bill.pay]
  congr 1 <;> first | omega | simp [hv]

attribute [local irreducible] row

theorem program_value (N : ℕ) (omega : ℂ) (t : Tape ℂ) :
    (run program (N,(omega,t))).val=
      Tape.tab N (fun j=>DFTModelCacheSpectrumSum.value t (omega^j) N) := by
  change (Bill.tab N (0:ℂ) (fun j=>run row ((N,(omega,t)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 1
  funext j
  rw [row_run]

theorem program_length (N : ℕ) (omega : ℂ) (t : Tape ℂ) :
    (run program (N,(omega,t))).val.len=N := by rw [program_value];rfl

theorem program_valid (N : ℕ) (omega : ℂ) (t : Tape ℂ) :
    (run program (N,(omega,t))).valid := by
  change True ∧ (Bill.tab N (0:ℂ) (fun j=>run row ((N,(omega,t)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [row_run]
  trivial

theorem program_work (N : ℕ) (omega : ℂ) (t : Tape ℂ) :
    (run program (N,(omega,t))).work≤100*(N+1)^2 := by
  change 1+(Bill.tab N (0:ℂ) (fun j=>run row ((N,(omega,t)),j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hsum:(∑j∈Finset.range N,(run row ((N,(omega,t)),j)).work)≤N*(82*N+80) := by
    calc
      _ ≤ ∑j∈Finset.range N,(82*N+80) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [row_run]
        dsimp only [Bill.work]
        have h:=DFTModelScalarPower.program_work j omega
        have hl:=Nat.log2_le_self (j+1)
        have hj:=Finset.mem_range.mp hj
        omega
      _ = _ := by simp [Nat.mul_comm]
  nlinarith

theorem program_peak (N : ℕ) (omega : ℂ) (t : Tape ℂ) :
    (run program (N,(omega,t))).peak≤N+2 := by
  change max (max 0 (Bill.tab N (0:ℂ) (fun j=>run row ((N,(omega,t)),j))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs:(Finset.range N).sup (fun j=>(run row ((N,(omega,t)),j)).peak)≤N+2 := by
    apply Finset.sup_le
    intro j hj
    rw [row_run]
    dsimp only [Bill.peak]
    have h:=DFTModelScalarPower.program_peak j omega
    have hj:=Finset.mem_range.mp hj
    omega
  omega

theorem source_value (N : ℕ) (t : Tape ℂ) (f:Fin N→ℂ)
    (ht:∀j:Fin N,t.look j.val 0=f j) (j:Fin N) :
    (run program (N,(OAI.ExactFourier.zeta N,t))).val.look j.val 0=
      (OAI.ExactFourier.fourierMatrix N).mulVec f j := by
  rw [program_value]
  simp only [Tape.look,Tape.tab,j.isLt,↓reduceDIte]
  unfold DFTModelCacheSpectrumSum.value
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i,←pow_mul]
  rfl

end
end ExactFourierCircuits.DFTModelCacheSpectrumDFT
