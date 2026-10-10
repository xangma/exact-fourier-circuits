import DFTModelSectorMapCarrySearch

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapCarry
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] closedSearch searchAux

def chunkWidth : Prog false CarryInput w := .atom .fst
def volume : Prog false CarryInput w := .comp (.atom .snd) (.atom .fst)
def directory : Prog false CarryInput Directory := .comp (.atom .snd) (.atom .snd)
def count : Prog false CarryInput w :=
  num .add (num .div volume chunkWidth) (.atom (.lit 1))
def cell : Prog false (p CarryInput w) w :=
  .comp (.fork (.comp (.atom .fst) directory)
    (num .mul (.atom .snd) (.comp (.atom .fst) chunkWidth))) closedSearch
def program : Prog false CarryInput (Ty.a w) := .tab count cell

theorem count_run (b V : ℕ) (d : Tape (ℕ×ℕ)) :
    run count (b,(V,d))=⟨V/b+1,11,V/b+1,True⟩ := by
  simp only [count,num,volume,chunkWidth,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
  have hp : (0:ℕ) ≤ V/b := Nat.zero_le _
  congr 1; omega

attribute [local irreducible] count

theorem cell_run (b V c : ℕ) (d : Tape (ℕ×ℕ)) :
    run cell ((b,(V,d)),c)=(run closedSearch (d,c*b)).pay 14 (c*b) := by
  simp only [run,cell,num,directory,chunkWidth,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
  congr 1 <;> omega

theorem program_run (b V : ℕ) (d : Tape (ℕ×ℕ)) :
    run program (b,(V,d))=
      (Bill.tab (V/b+1) 0 (fun c=>run cell ((b,(V,d)),c))).pay 12 (V/b+1) := by
  change ((run count (b,(V,d))).pass (fun n=>
    Bill.tab n 0 (fun c=>run cell ((b,(V,d)),c)))).pay 1 0=_
  rw [count_run]
  simp only [Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;> omega

attribute [local irreducible] program cell

theorem program_value (b V : ℕ) (d : Tape (ℕ×ℕ)) :
    (run program (b,(V,d))).val=
      Tape.tab (V/b+1) (fun c=>(run closedSearch (d,c*b)).val) := by
  rw [program_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab (V/b+1))
  funext c
  rw [cell_run]
  rfl

theorem program_length (b V : ℕ) (d : Tape (ℕ×ℕ)) :
    (run program (b,(V,d))).val.len=V/b+1 := by
  rw [program_value]
  rfl

theorem program_cut (b V : ℕ) (d : Tape (ℕ×ℕ)) (ho : Ordered d)
    (c : ℕ) (hc : c < V/b+1) :
    Cut d (c*b) ((run program (b,(V,d))).val.look c 0) := by
  rw [program_value]
  simpa [Tape.look,Tape.tab,hc] using (closedSearch_spec d (c*b) ho).1

theorem program_valid (b V : ℕ) (d : Tape (ℕ×ℕ)) (ho : Ordered d) :
    (run program (b,(V,d))).valid := by
  rw [program_run]
  change (Bill.tab _ _ _).valid
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro c _
  rw [cell_run]
  exact (closedSearch_spec d (c*b) ho).2.1

theorem program_work (b V : ℕ) (d : Tape (ℕ×ℕ)) (ho : Ordered d) :
    (run program (b,(V,d))).work ≤
      14+(V/b+1)*(70*Nat.clog 2 (d.len+1)+49) := by
  rw [program_run]
  change (Bill.tab _ _ _).work+12 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑c∈Finset.range (V/b+1),(run cell ((b,(V,d)),c)).work) ≤
      (V/b+1)*(70*Nat.clog 2 (d.len+1)+45) := by
    calc
      _  ≤  ∑_c∈Finset.range (V/b+1),(70*Nat.clog 2 (d.len+1)+45) := by
        apply Finset.sum_le_sum
        intro c _
        rw [cell_run]
        have h:=(closedSearch_spec d (c*b) ho).2.2.1
        change (run closedSearch (d,c*b)).work+14 ≤ _
        omega
      _ = _ := by simp
  nlinarith

theorem program_peak (b V : ℕ) (d : Tape (ℕ×ℕ)) (_hb : 0 < b) (ho : Ordered d) :
    (run program (b,(V,d))).peak ≤ max (V+1) (d.len+2) := by
  rw [program_run]
  change max (Bill.tab _ _ _).peak (V/b+1) ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hc : V/b+1 ≤ V+1 := by have h:=Nat.div_le_self V b;omega
  refine max_le (max_le (hc.trans (le_max_left _ _)) ?_) (hc.trans (le_max_left _ _))
  apply Finset.sup_le
  intro c hc'
  rw [cell_run]
  change max (run closedSearch (d,c*b)).peak (c*b) ≤ _
  refine max_le ((closedSearch_spec d (c*b) ho).2.2.2.trans (le_max_right _ _)) ?_
  have hi:=Finset.mem_range.mp hc'
  have hm : c*b ≤ V := by
    have h : c ≤ V/b := by omega
    exact (Nat.mul_le_mul_right b h).trans (Nat.div_mul_le_self V b)
  exact hm.trans (by omega)

end
end ExactFourierCircuits.DFTModelSectorMapCarry
