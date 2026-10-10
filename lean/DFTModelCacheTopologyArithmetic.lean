import DFTModelCacheTopologyProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

theorem G_formula (K : ℕ) : G K=3*K*UniformRadixTwoDAG.width K+2*UniformRadixTwoDAG.width K := by
  have h:=UniformRadixTwoDAG.count_exact K
  unfold G UniformToeplitzCrossTopologyMachine.G UniformConvolutionDAG.total
  omega

theorem count_formula (K : ℕ) : 3*K*UniformRadixTwoDAG.width K/2=UniformRadixTwoDAG.count K :=
  UniformRadixInstructionMachine.count_div K

theorem nat_value {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (nat op f g) x).val=(op.run ((run f x).val,(run g x).val)).val := rfl

theorem nat_work {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (nat op f g) x).work=(run f x).work+(run g x).work+3 := by
  cases op <;> simp only [nat,comp_run,fork_run,atom_run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay] <;> omega

theorem nat_valid {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (nat op f g) x).valid ↔ (run f x).valid ∧ (run g x).valid := by
  cases op <;> simp only [nat,comp_run,fork_run,atom_run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay] <;> tauto

theorem nat_peak {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (nat op f g) x).peak=max (max (run f x).peak (run g x).peak)
      (run (nat op f g) x).val := by
  cases op <;> simp only [nat,comp_run,fork_run,atom_run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay] <;> omega

theorem projections (x : Config.T) :
    run DFTModelCacheTopology.a x=⟨x.1.1,3,0,True⟩ ∧
    run DFTModelCacheTopology.e x=⟨x.1.2,3,0,True⟩ ∧
    run k x=⟨x.2.1,3,0,True⟩ ∧ run n x=⟨x.2.2,3,0,True⟩ := by
  simp [DFTModelCacheTopology.a,DFTModelCacheTopology.e,k,n,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] Code.run

theorem gates_run (K a e : ℕ) :
    (run gates (config K a e)).val=G K := by
  simp only [gates,nat_value,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  exact (G_formula K).symm

theorem fftCount_value (K a e : ℕ) :
    (run fftCount (config K a e)).val=UniformRadixTwoDAG.count K := by
  simp only [fftCount,nat_value,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  exact count_formula K

theorem destination_value (K a e : ℕ) : (run destination (config K a e)).val=D K := by
  simp only [destination,nat_value,gates_run,atom_run,Atom.run,NOp.run,Bill.word]
  rfl

theorem sum_value (K a e : ℕ) : (run sum (config K a e)).val=
    UniformRadixTwoDAG.width K+G K+a+e+K+1 := by
  simp only [sum,nat_value,gates_run,(projections _).1,(projections _).2.1,
    (projections _).2.2.1,(projections _).2.2.2,atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]

theorem cap_value (K a e : ℕ) : (run cap (config K a e)).val=
    UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K) (UniformRadixTwoDAG.count K) K := by
  simp only [cap,square,nat_value,fftCount_value,(projections _).2.2.1,
    (projections _).2.2.2,atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  simp only [UniformRadixInstructionMachine.cap,pow_two]

theorem allocation_value (K a e : ℕ) : (run allocation (config K a e)).val=B K a e := by
  simp only [allocation,square,nat_value,destination_value,gates_run,cap_value,sum_value,
    (projections _).1,atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  simp only [B,UniformToeplitzCrossTopologyMachine.budget,G,Nat.zero_add,pow_two]

theorem heapLength_value (K a e : ℕ) : (run heapLength (config K a e)).val=H K a e := by
  simp only [heapLength,nat_value,allocation_value,atom_run,Atom.run,NOp.run,Bill.word]
  rfl

theorem fuel_value (K a e : ℕ) : (run fuel (config K a e)).val=T K a := by
  simp only [fuel,nat_value,gates_run,(projections _).1,(projections _).2.2.1,
    atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  rfl

theorem crossCount_value (K a e : ℕ) : (run crossCount (config K a e)).val=C K a := by
  simp only [crossCount,nat_value,gates_run,(projections _).1,
    atom_run,Atom.run,NOp.run,Bill.word]
  simp only [config]
  rfl

theorem allocation_work (x : Config.T) : (run allocation x).work≤1000 := by
  simp only [allocation,destination,gates,cap,square,sum,fftCount,nat_work,
    (projections _).1,(projections _).2.1,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,Bill.word]
  decide

theorem allocation_valid (x : Config.T) : (run allocation x).valid := by
  simp only [allocation,destination,gates,cap,square,sum,fftCount,nat_valid,
    (projections _).1,(projections _).2.1,(projections _).2.2.1,(projections _).2.2.2,
    atom_run,Atom.run,Bill.word,true_and]

end
end ExactFourierCircuits.DFTModelCacheTopology
