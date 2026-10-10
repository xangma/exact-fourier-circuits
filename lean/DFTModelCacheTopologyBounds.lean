import DFTModelCacheTopologyArithmetic

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheMatchingNat
noncomputable section

attribute [local irreducible] Code.run Bill.tab

private theorem natural_square (s : ℕ) : s ≤ s*s+1 := by nlinarith

private theorem gates_peak (K a e : ℕ) :
    (run gates (config K a e)).peak≤G K+5 := by
  have hn:=UniformRadixTwoDAG.width_pos K
  have hg:=G_formula K
  have product : 3*K≤3*K*UniformRadixTwoDAG.width K := by nlinarith
  simp only [gates,nat_peak,nat_value,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,NOp.run,Bill.word,max_le_iff]
  simp only [config] at *
  repeat' apply And.intro
  all_goals omega

private theorem fftCount_peak (K a e : ℕ) :
    (run fftCount (config K a e)).peak≤G K+5 := by
  have hn:=UniformRadixTwoDAG.width_pos K
  have hg:=G_formula K
  have product : 3*K≤3*K*UniformRadixTwoDAG.width K := by nlinarith
  have div:=Nat.div_le_self (3*K*UniformRadixTwoDAG.width K) 2
  simp only [fftCount,nat_peak,nat_value,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,NOp.run,Bill.word,max_le_iff]
  simp only [config] at *
  repeat' apply And.intro
  all_goals omega

private theorem sum_peak (K a e : ℕ) :
    (run sum (config K a e)).peak≤UniformRadixTwoDAG.width K+G K+a+e+K+6 := by
  have hg:=gates_peak K a e
  simp only [sum,nat_peak,nat_value,gates_run,(projections _).1,(projections _).2.1,
    (projections _).2.2.1,(projections _).2.2.2,atom_run,Atom.run,NOp.run,Bill.word,max_le_iff]
  simp only [config] at *
  repeat' apply And.intro
  all_goals omega

private theorem cap_peak (K a e : ℕ) :
    (run cap (config K a e)).peak≤
      UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K) (UniformRadixTwoDAG.count K) K+G K+10000 := by
  have hf:=fftCount_peak K a e
  have sq:=natural_square (UniformRadixTwoDAG.width K+UniformRadixTwoDAG.count K+K+1)
  simp only [cap,square,nat_peak,nat_value,fftCount_value,(projections _).2.2.1,
    (projections _).2.2.2,atom_run,Atom.run,NOp.run,Bill.word,max_le_iff,
    UniformRadixInstructionMachine.cap,pow_two]
  simp only [config] at *
  repeat' apply And.intro
  all_goals omega

private theorem destination_peak (K a e : ℕ) :
    (run destination (config K a e)).peak≤D K+10 := by
  have hg:=gates_peak K a e
  simp only [destination,nat_peak,nat_value,gates_run,atom_run,Atom.run,NOp.run,Bill.word,max_le_iff]
  simp only [config] at *
  repeat' apply And.intro
  all_goals unfold D;omega

private def peak2 (p q v : ℕ) := max (max p q) v

private theorem allocation_model (w g a e K d c pg pd pc ps b : ℕ)
    (hg : pg≤g+5) (hd : pd≤d+10) (hc : pc≤c+g+10000)
    (hs : ps≤w+g+a+e+K+6)
    (sq : 1≤(w+g+a+e+K+1)*(w+g+a+e+K+1))
    (tail : d+20*(w+g+a+e+K+1)+1000≤b)
    (alloc : b=d+5*(7*g+2*a)+c+10000*((w+g+a+e+K+1)*(w+g+a+e+K+1))) :
    peak2
      (peak2 (peak2 pd
        (peak2 5 (peak2 (peak2 7 pg (7*g)) (peak2 2 0 (2*a)) (7*g+2*a))
          (5*(7*g+2*a))) (d+5*(7*g+2*a))) pc (d+5*(7*g+2*a)+c))
      (peak2 10000 (peak2 ps ps ((w+g+a+e+K+1)*(w+g+a+e+K+1)))
        (10000*((w+g+a+e+K+1)*(w+g+a+e+K+1))))
      (d+5*(7*g+2*a)+c+10000*((w+g+a+e+K+1)*(w+g+a+e+K+1)))≤b := by
  generalize hq : (w+g+a+e+K+1)*(w+g+a+e+K+1)=q at *
  clear hq
  have hpc : pc≤b := by omega
  simp only [peak2,max_le_iff]
  repeat' apply And.intro
  all_goals omega

/-- Every intermediate Nat word fits the actual native allocation budget. -/
theorem allocation_peak (K a e : ℕ) :
    (run allocation (config K a e)).peak≤B K a e := by
  have hn:=UniformRadixTwoDAG.width_pos K
  have tail:=UniformToeplitzCrossTopologyMachine.budget_tail K a e 0 (D K)
  simp only [Nat.zero_add] at tail
  change D K+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1)+1000≤B K a e at tail
  have sq : 1≤(UniformRadixTwoDAG.width K+G K+a+e+K+1)^2 :=
    Nat.succ_le_iff.mpr (pow_pos (by omega) 2)
  have alloc : B K a e =D K+5*(7*G K+2*a)+
      UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K) (UniformRadixTwoDAG.count K) K+
      10000*(UniformRadixTwoDAG.width K+G K+a+e+K+1)^2 := by
    simp only [B,UniformToeplitzCrossTopologyMachine.budget,Nat.zero_add,G]
  rw [pow_two] at sq alloc
  have model:=allocation_model (UniformRadixTwoDAG.width K) (G K) a e K (D K)
    (UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K) (UniformRadixTwoDAG.count K) K)
    _ _ _ _ (B K a e) (gates_peak K a e) (destination_peak K a e) (cap_peak K a e)
    (sum_peak K a e) sq tail alloc
  simpa only [allocation,square,nat_peak,nat_value,destination_value,gates_run,cap_value,sum_value,
    (projections _).1,atom_run,Atom.run,NOp.run,Bill.word,peak2,show (config K a e).1.1=a from rfl] using model

 theorem fuel_bounds (K a e : ℕ) :
    (run fuel (config K a e)).valid ∧
    (run fuel (config K a e)).work≤1000 ∧
    (run fuel (config K a e)).peak≤T K a+1000 := by
  have hn:=UniformRadixTwoDAG.width_pos K
  have hG:=G_formula K
  have product : 3*K≤3*K*UniformRadixTwoDAG.width K := by nlinarith
  have hp:=gates_peak K a e
  constructor
  · simp only [fuel,gates,nat_valid,(projections _).1,(projections _).2.2.1,
      (projections _).2.2.2,atom_run,Atom.run,Bill.word,true_and]
  constructor
  · simp only [fuel,gates,nat_work,(projections _).1,(projections _).2.2.1,
      (projections _).2.2.2,atom_run,Atom.run,Bill.word]
    decide
  · simp only [fuel,nat_peak,nat_value,gates_run,(projections _).1,(projections _).2.2.1,
      atom_run,Atom.run,NOp.run,Bill.word,
      max_le_iff,T]
    simp only [config] at *
    repeat' apply And.intro
    all_goals first | omega | nlinarith


private theorem budget_tail (K a e : ℕ) :
    D K+20*(UniformRadixTwoDAG.width K+G K+a+e+K+1)+1000≤B K a e := by
  simpa only [B,G,Nat.zero_add] using
    UniformToeplitzCrossTopologyMachine.budget_tail K a e 0 (D K)

theorem destination_bounds (K a e : ℕ) :
    Budget (run destination (config K a e)) 1000 (B K a e) := by
  refine ⟨?_,?_,?_⟩
  · simp only [destination,gates,nat_valid,(projections _).2.2.1,(projections _).2.2.2,
      atom_run,Atom.run,Bill.word,true_and]
  · simp only [destination,gates,nat_work,(projections _).2.2.1,(projections _).2.2.2,
      atom_run,Atom.run,Bill.word]
    decide
  · exact (destination_peak K a e).trans (by have h:=budget_tail K a e;omega)

theorem crossCount_bounds (K a e : ℕ) :
    Budget (run crossCount (config K a e)) 1000 (B K a e) := by
  refine ⟨?_,?_,?_⟩
  · simp only [crossCount,gates,nat_valid,(projections _).1,(projections _).2.2.1,
      (projections _).2.2.2,atom_run,Atom.run,Bill.word,true_and]
  · simp only [crossCount,gates,nat_work,(projections _).1,(projections _).2.2.1,
      (projections _).2.2.2,atom_run,Atom.run,Bill.word]
    decide
  · have hg:=gates_peak K a e
    have h:=budget_tail K a e
    simp only [crossCount,nat_peak,nat_value,gates_run,(projections _).1,
      atom_run,Atom.run,NOp.run,Bill.word,max_le_iff]
    simp only [config] at *
    repeat' apply And.intro
    all_goals omega

theorem heapLength_bounds (K a e : ℕ) :
    Budget (run heapLength (config K a e)) 1004 (H K a e) := by
  have h:=allocation_work (config K a e)
  have hp:=allocation_peak K a e
  refine ⟨?_,?_,?_⟩
  · simp only [heapLength,nat_valid,allocation_valid,atom_run,Atom.run,Bill.word,true_and]
  · simp only [heapLength,nat_work,atom_run,Atom.run,Bill.word]
    omega
  · simp only [heapLength,nat_peak,nat_value,allocation_value,atom_run,Atom.run,NOp.run,Bill.word,
      max_le_iff,H]
    exact ⟨⟨by omega,by omega⟩,le_rfl⟩

private theorem indexed_projection (K a e j : ℕ) :
    Budget (run (.comp (.atom .fst : Prog false Indexed Config) k) (config K a e,j)) 30 (2*H K a e+20000) ∧
    Budget (run (.comp (.atom .fst : Prog false Indexed Config) DFTModelCacheTopology.a) (config K a e,j)) 30 (2*H K a e+20000) ∧
    Budget (run (.comp (.atom .fst : Prog false Indexed Config) DFTModelCacheTopology.e) (config K a e,j)) 30 (2*H K a e+20000) ∧
    Budget (run (.comp (.atom .fst : Prog false Indexed Config) destination) (config K a e,j)) 30 (2*H K a e+20000) := by
  have hd:=destination_bounds K a e
  have hp:=hd.2.2
  have room : (run destination (config K a e)).peak≤2*H K a e+20000 :=
    hp.trans (by unfold H;omega)
  simp only [H] at room
  have destwork : (run destination (config K a e)).work=27 := by
    simp only [destination,gates,nat_work,(projections _).2.2.1,(projections _).2.2.2,
      atom_run,Atom.run,Bill.word]
  simp only [Budget,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
    (projections _).1,(projections _).2.1,(projections _).2.2.1,destwork,max_le_iff,H]
  repeat' apply And.intro
  all_goals first | trivial | exact hd.1 | exact room | decide | exact Nat.zero_le _

private theorem registerCell_bounds (K a e j : ℕ) (hj : j<600) :
    Budget (run registerCell (config K a e,j)) 200 (2*H K a e+20000) := by
  let Q:=2*H K a e+20000
  have index : Budget (run (.atom .snd : Prog false Indexed w) (config K a e,j)) 1 Q := by
    rw [atom_run]
    exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  have value : (run (.atom .snd : Prog false Indexed w) (config K a e,j)).val≤Q := by
    rw [atom_run]
    change j≤Q;dsimp [Q];omega
  have bits : ∀n,n≤564→n≤Q := by intro n hn;dsimp [Q];omega
  have branches:=indexed_projection K a e j
  have zero : Budget (run (.atom (.lit 0) : Prog false Indexed w) (config K a e,j)) 30 Q := by
    rw [atom_run]
    change True ∧ 1≤30 ∧ 0≤Q
    exact ⟨trivial,by decide,Nat.zero_le _⟩
  have b4:=select_budget (.atom .snd : Prog false Indexed w) 564 _ _ (config K a e,j) 1 30 Q index value
    (bits 564 le_rfl) branches.2.2.2 zero
  have b3:=select_budget (.atom .snd : Prog false Indexed w) 562 _ _ (config K a e,j) 1 44 Q index value
    (bits 562 (by decide)) (budget_mono branches.2.2.1 (by decide)) b4
  have b2:=select_budget (.atom .snd : Prog false Indexed w) 561 _ _ (config K a e,j) 1 58 Q index value
    (bits 561 (by decide)) (budget_mono branches.2.1 (by decide)) b3
  have b1:=select_budget (.atom .snd : Prog false Indexed w) 560 _ _ (config K a e,j) 1 72 Q index value
    (bits 560 (by decide)) (budget_mono branches.1 (by decide)) b2
  exact budget_mono b1 (by decide)

/-- The 600 registers and every empty heap cell are created by charged tabs. -/
theorem initialize_bounds (K a e : ℕ) :
    (run initializeProgram (config K a e)).valid ∧
    (run initializeProgram (config K a e)).work≤200000+204*H K a e ∧
    (run initializeProgram (config K a e)).peak≤2*H K a e+20000 := by
  let Q:=2*H K a e+20000
  have regs:=tab_program_budget (.atom (.lit 600)) registerCell (config K a e) 200 Q
    (by rw [atom_run];trivial) (by
      intro j hj
      rw [atom_run] at hj
      exact registerCell_bounds K a e j hj)
  have regBudget : Budget (run (.tab (.atom (.lit 600)) registerCell) (config K a e)) 122404 Q := by
    rw [atom_run] at regs
    simpa only [Atom.run,Bill.word,Bill.work,Bill.val,Bill.peak,
      show max 600 (max 600 Q)=Q from by dsimp [Q];omega] using regs
  have emptyBudget : ∀j,j<H K a e→Budget (run emptyCell (config K a e,j)) 200 Q := by
    intro j _
    simp only [emptyCell,Budget,fork_run,atom_run,Atom.run,Bill.word,Bill.one,Bill.pass]
    change (True ∧ True ∧ True) ∧ 3≤200 ∧ 0≤Q
    exact ⟨⟨trivial,trivial,trivial⟩,by decide,Nat.zero_le _⟩
  have heap:=tab_program_budget heapLength emptyCell (config K a e) 200 Q
    (heapLength_bounds K a e).1 (by
      intro j hj
      rw [heapLength_value] at hj
      exact emptyBudget j hj)
  have heapBudget : Budget (run (.tab heapLength emptyCell) (config K a e))
      (1007+204*H K a e) Q := by
    rcases heap with ⟨valid,work,peak⟩
    have hw:=(heapLength_bounds K a e).2.1
    have hp:=(heapLength_bounds K a e).2.2
    rw [heapLength_value] at work peak
    refine ⟨valid,by omega,?_⟩
    have room : H K a e≤Q := by dsimp [Q];omega
    exact peak.trans (max_le (hp.trans room) (max_le room le_rfl))
  have zero : Budget (run (.atom (.lit 0) : Prog false Config w) (config K a e)) 1 Q := by
    rw [atom_run]
    exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  have assembled:=fork_budget (.atom (.lit 0))
    (.fork (.tab (.atom (.lit 600)) registerCell) (.tab heapLength emptyCell)) (config K a e)
    1 (122404+(1007+204*H K a e)+1) Q zero
    (fork_budget (.tab (.atom (.lit 600)) registerCell) (.tab heapLength emptyCell)
      (config K a e) 122404 (1007+204*H K a e) Q regBudget heapBudget)
  exact budget_mono assembled (by omega)

end
end ExactFourierCircuits.DFTModelCacheTopology
