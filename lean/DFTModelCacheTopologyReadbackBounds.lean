import DFTModelCacheTopologyReadback
import DFTModelCacheTopologyBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheMatchingNat DFTModelCacheNatControl
noncomputable section

attribute [local irreducible] Code.run Bill.tab

theorem comp_budget {s t u : Ty} (f : Prog false s t) (g : Prog false t u)
    (x : s.T) (F G B : ℕ) (first : Budget (run f x) F B)
    (second : Budget (run g (run f x).val) G B) :
    Budget (run (.comp f g) x) (F+G+1) B := by
  rcases first with ⟨fv,fw,fp⟩
  rcases second with ⟨sv,sw,sp⟩
  rw [comp_run]
  exact ⟨⟨fv,sv⟩,by dsimp only [Bill.pass,Bill.pay];omega,
    by dsimp only [Bill.pass,Bill.pay];omega⟩

theorem rowLength_run (K a e : ℕ) (v : LocalValue) :
    run rowLength (config K a e,v)=
      ⟨5*C K a,(run crossCount (config K a e)).work+6,
        max 5 (max (run crossCount (config K a e)).peak (5*C K a)),
        (run crossCount (config K a e)).valid⟩ := by
  simp only [rowLength,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,
    Bill.pass,Bill.pay,crossCount_value,true_and,and_true,zero_max,max_zero]
  congr 1 <;> omega

theorem readback_bounds (K a e : ℕ) (v : LocalValue) :
    Budget (run readback (config K a e,v)) (4000+5120*C K a) (B K a e) := by
  have dest:=destination_bounds K a e
  have count:=crossCount_bounds K a e
  have dw:=dest.2.1
  have cw:=count.2.1
  have room:=UniformToeplitzCrossTopologyMachine.budget_tape K a e 0 (D K)
  have tail:=UniformToeplitzCrossTopologyMachine.budget_tail K a e 0 (D K)
  have room' : D K+5*C K a+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1)+1000≤B K a e := by
    simpa only [B,C,G,Nat.zero_add] using room
  have tail' : D K+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1)+1000≤B K a e := by
    simpa only [B,G,Nat.zero_add] using tail
  have cells:∀j,j<(run rowLength (config K a e,v)).val→
      Budget (run readCell ((config K a e,v),j)) 1020 (B K a e) := by
    intro j hj
    rw [rowLength_run] at hj
    change j<5*C K a at hj
    have tapeRoom:D K+5*C K a≤B K a e := calc
      _≤D K+5*C K a+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1) := Nat.le_add_right _ _
      _≤D K+5*C K a+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1)+1000 := Nat.le_add_right _ _
      _≤B K a e :=room'
    have address:D K+j≤B K a e := (Nat.add_le_add_left (Nat.le_of_lt hj) (D K)).trans tapeRoom
    rw [readCell_run]
    exact ⟨⟨dest.1,trivial⟩,by dsimp only [Bill.work];omega,
      max_le dest.2.2 address⟩
  have extracted:=tab_program_budget rowLength readCell (config K a e,v) 1020 (B K a e)
    (by rw [rowLength_run];exact count.1) cells
  change Budget (run extract (config K a e,v)) _ _ at extracted
  rw [rowLength_run] at extracted
  have extBudget:Budget (run extract (config K a e,v)) (2000+5120*C K a) (B K a e) := by
    refine ⟨extracted.1,?_,?_⟩
    · have w:=extracted.2.1;dsimp only [Bill.work] at w;omega
    · have pk:=extracted.2.2
      dsimp only [Bill.peak] at pk
      exact pk.trans (max_le (max_le (by omega) (max_le count.2.2 (by omega)))
        (max_le (by omega) le_rfl))
  have kb:Budget (run (.comp (.atom .fst) k : Prog false Computed w) (config K a e,v)) 5 (B K a e) := by
    rw [comp_run,atom_run]
    change Budget ((Bill.one (config K a e)).pass (run k) |>.pay 1 0) 5 (B K a e)
    dsimp only [Budget,Bill.one,Bill.pass,Bill.pay]
    rw [(projections (config K a e)).2.2.1]
    exact ⟨⟨trivial,trivial⟩,by norm_num only [Bill.work],Nat.zero_le _⟩
  have cb:Budget (run (.comp (.atom .fst) crossCount : Prog false Computed w) (config K a e,v)) 1002 (B K a e) := by
    rw [comp_run,atom_run]
    exact ⟨⟨trivial,count.1⟩,by dsimp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay];omega,
      by simpa only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero] using count.2.2⟩
  have inner:=fork_budget (.comp (.atom .fst) crossCount) extract (config K a e,v)
    1002 (2000+5120*C K a) (B K a e) cb extBudget
  have outer:=fork_budget (.comp (.atom .fst) k) (.fork (.comp (.atom .fst) crossCount) extract)
    (config K a e,v) 5 (1002+(2000+5120*C K a)+1) (B K a e) kb inner
  exact budget_mono outer (by omega)

end
end ExactFourierCircuits.DFTModelCacheTopology
