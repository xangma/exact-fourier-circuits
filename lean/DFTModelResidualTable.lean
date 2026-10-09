import DFTModelResidualXor
import UniformXorCallerInterface

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualTable
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Sized := p w w
abbrev CellInput := p Sized w

def size : Prog false w Sized := .fork (.atom .id) power
def count : Prog false Sized w := binary .mul (.atom .snd) (.atom .snd)
def exponent : Prog false CellInput w := .comp (.atom .fst) (.atom .fst)
def radix : Prog false CellInput w := .comp (.atom .fst) (.atom .snd)
def argument : Prog false CellInput DFTModelResidualXor.Input :=
  .fork exponent (.fork (binary .div (.atom .snd) radix) (binary .mod (.atom .snd) radix))
def cell : Prog false CellInput w := .comp argument DFTModelResidualXor.program
def build : Prog false Sized (Ty.a w) := .tab count cell
/-- The radix and every table entry are computed, not supplied. -/
def program : Prog false w (Ty.a w) := .comp size build

theorem cell_value (q N j : ℕ) (hN : N=2^q) (hj : j<N*N) :
    (run cell ((q,N),j)).val = j/N^^^j%N := by
  change (run DFTModelResidualXor.program (q,(j/N,j%N))).val = _
  have pos : 0<N := by rw [hN];exact Nat.two_pow_pos q
  apply DFTModelResidualXor.program_value
  · rw [←hN]
    exact (Nat.div_lt_iff_lt_mul pos).2 hj
  · rw [←hN]
    exact Nat.mod_lt j pos

theorem cell_work (q N j : ℕ) : (run cell ((q,N),j)).work = 86*q+32 := by
  have arg : (run argument ((q,N),j)).val=(q,(j/N,j%N)) ∧
      (run argument ((q,N),j)).work=19 := by
    simp [argument,exponent,radix,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word]
  change (run argument ((q,N),j)).work+
    (run DFTModelResidualXor.program (run argument ((q,N),j)).val).work+1 = _
  rw [arg.1,arg.2,DFTModelResidualXor.program_work]
  omega

theorem cell_valid (q N j : ℕ) : (run cell ((q,N),j)).valid := by
  have arg : (run argument ((q,N),j)).val=(q,(j/N,j%N)) ∧
      (run argument ((q,N),j)).valid := by
    simp [argument,exponent,radix,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word]
  change (run argument ((q,N),j)).valid ∧
    (run DFTModelResidualXor.program (run argument ((q,N),j)).val).valid
  exact ⟨arg.2,by rw [arg.1];exact DFTModelResidualXor.program_valid _ _ _⟩

theorem build_value (q N : ℕ) (hN : N=2^q) :
    (run build (q,N)).val = Tape.tab (N*N) (fun j => j/N^^^j%N) := by
  change (Bill.tab (N*N) w.blank (fun j => run cell ((q,N),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (fun f : Fin (N*N)→ℕ => (⟨N*N,f⟩:Tape ℕ))
  funext j
  exact cell_value q N j.val hN j.isLt

theorem build_work (q N : ℕ) : (run build (q,N)).work = (86*q+36)*(N*N)+8 := by
  change 5+(Bill.tab (N*N) w.blank (fun j => run cell ((q,N),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((q,N),j)).work)=(fun _ => 86*q+32) := by
    funext j;exact cell_work _ _ _
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

theorem build_valid (q N : ℕ) : (run build (q,N)).valid := by
  have h : (Bill.tab (N*N) w.blank (fun j => run cell ((q,N),j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _ => cell_valid _ _ _)
  simpa only [build,count,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,and_true,true_and] using h

theorem program_value (q : ℕ) :
    (run program q).val = Tape.tab (2^q*2^q) (fun j => j/2^q^^^j%2^q) := by
  change (run build (q,(run power q).val)).val = _
  rw [power_value]
  exact build_value _ _ rfl

theorem program_work (q : ℕ) :
    (run program q).work = (86*q+36)*(2^q*2^q)+8*q+15 := by
  change (1+(run power q).work+1)+(run build (q,(run power q).val)).work+1 = _
  rw [power_value,power_work,build_work]
  omega

theorem program_valid (q : ℕ) : (run program q).valid := by
  change (True ∧ (run power q).valid ∧ True) ∧ (run build (q,(run power q).val)).valid
  exact ⟨⟨trivial,power_valid q,trivial⟩,build_valid _ _⟩

theorem cell_peak (q N j : ℕ) (hN : N=2^q) (hj : j<N*N) :
    (run cell ((q,N),j)).peak≤N+2 := by
  have pos : 0<N := by rw [hN];exact Nat.two_pow_pos q
  have div : j/N<N := (Nat.div_lt_iff_lt_mul pos).2 hj
  have mod : j%N<N := Nat.mod_lt j pos
  have arg : (run argument ((q,N),j)).val=(q,(j/N,j%N)) ∧
      (run argument ((q,N),j)).peak≤N+2 := by
    constructor
    · rfl
    simp only [argument,exponent,radix,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,max_le_iff]
    repeat' apply And.intro
    all_goals omega
  have xor:=DFTModelResidualXor.program_peak q (j/N) (j%N) (by simpa [←hN] using div)
    (by simpa [←hN] using mod)
  change max (max (run argument ((q,N),j)).peak
    (run DFTModelResidualXor.program (run argument ((q,N),j)).val).peak) 0≤_
  rw [arg.1]
  rw [←hN] at xor
  omega

theorem build_peak (q N : ℕ) (hN : N=2^q) :
    (run build (q,N)).peak≤N*N+N+2 := by
  have cells : ((Finset.range (N*N)).sup (fun j=>(run cell ((q,N),j)).peak))≤N+2 := by
    apply Finset.sup_le
    intro j hj
    exact cell_peak q N j hN (Finset.mem_range.mp hj)
  change max (max (max (max (max 0 0) (N*N)) 0)
    (Bill.tab (N*N) w.blank (fun j=>run cell ((q,N),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  omega

theorem program_peak (q : ℕ) : (run program q).peak≤2^q*2^q+2^q+2 := by
  have pp:=power_peak q
  have bp:=build_peak q (2^q) rfl
  change max (max (max 0 (max (run power q).peak 0))
    (run build (q,(run power q).val)).peak) 0≤_
  rw [power_value]
  omega

theorem table_look (q a b : ℕ) (ha : a<2^q) (hb : b<2^q) :
    (run program q).val.look (a*2^q+b) 0 = a^^^b := by
  rw [program_value]
  have pos:=Nat.two_pow_pos q
  have hlt : a*2^q+b<2^q*2^q := by nlinarith
  simp [Tape.look,Tape.tab,hlt,Nat.add_div,Nat.div_eq_of_lt hb,
    Nat.add_mod,Nat.mod_eq_of_lt hb, Nat.mul_div_cancel _ pos,hb]

theorem work_preserved (q : ℕ) : (run program q).work ≤
    8*(4*q+10+(12*q+15)*(2^q*2^q)) := by
  rw [program_work]
  nlinarith

/-- The typed materialization agrees with every entry actually produced by
source fixed38; there is no supplied XOR table or new bitwise operation. -/
theorem actual_execution (n q base B : ℕ) (x : Fin n→ℂ) (s : UniformMachine.State)
    (pc : s.pc=0) (hq : s.natReg 3420=q) (hb : s.natReg 3421=base)
    (bound : UniformMachine.WordBound B s) (extent : 38≤B)
    (capacity : base+2^q*2^q≤B) :
    ∃u, UniformMachine.BoundedExecution UniformXorTableMachine.tableProgram n x B s
      (4*q+10+(12*q+15)*(2^q*2^q)) u ∧ u.pc=37 ∧
      (∀j,j<2^q*2^q→u.natHeap (base+j)=some ((run program q).val.look j 0)) ∧
      UniformXorTableMachine.Outside q base s.natHeap u ∧
      UniformXorTableMachine.TableFrame s u := by
  obtain ⟨u,hu,upc,_,entries,outside,frame⟩ :=
    UniformXorCallerInterface.table_execution_bounded_size n q base B x s pc hq hb bound extent capacity
  refine ⟨u,hu,upc,?_,outside,frame⟩
  intro j hj
  rw [program_value]
  simpa [Tape.look,Tape.tab,hj] using entries j hj

end
end ExactFourierCircuits.DFTModelResidualTable
