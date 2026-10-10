import DFTModelCacheColorProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open DFTModelCacheMatchingNat (select_value tab_value_code fork_value tab_run)
noncomputable section

theorem registerCell_value (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run registerCell ((r,z),j)).val=registerValue z.len j := by
  simp only [registerCell,select,select_value,count,colorBase,paletteBase,nat,
    DFTModelCacheMatchingNat.count,DFTModelCacheMatchingNat.nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,registerValue,C,U]
  rfl

theorem heapLength_run (r : ℕ) (z : Tape Row.T) :
    run heapLength (r,z)=⟨H r z.len,15,H r z.len,True⟩ := by
  simp [heapLength,paletteBase,radix,count,nat,DFTModelCacheMatchingNat.radix,
    DFTModelCacheMatchingNat.count,DFTModelCacheMatchingNat.nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,H,B,U]
  constructor
  · ring
  · rw [max_eq_right (by omega : z.len≤913+(r+4*z.len)),
      max_eq_right (by omega : 4≤913+(r+4*z.len))]
    ring

theorem runtimeProgram_run (r : ℕ) (z : Tape Row.T) :
    run runtimeProgram (r,z)=⟨UniformGreedyColorMachine.runtimeBudget z.len,21,
      UniformGreedyColorMachine.runtimeBudget z.len,True⟩ := by
  simp [runtimeProgram,count,nat,DFTModelCacheMatchingNat.count,DFTModelCacheMatchingNat.nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    UniformGreedyColorMachine.runtimeBudget,pow_two]


attribute [local irreducible] Code.run

theorem initialize_value (r : ℕ) (z : Tape Row.T) :
    (run initializeProgram (r,z)).val=initialValue r z := by
  unfold initializeProgram
  rw [fork_value,fork_value,tab_value_code,tab_value_code,heapLength_run]
  simp only [atom_run,Atom.run,Bill.word]
  exact congrArg (fun ts=>(0,ts)) (Prod.ext
    (congrArg (Tape.tab 824) (funext (registerCell_value r z)))
    (congrArg (Tape.tab (H r z.len)) (funext (DFTModelCacheMatchingNat.heapCell_value r z))))

theorem compiled_run (r : ℕ) (z : Tape Row.T) :
    run compiled (r,z)=((run initializeProgram (r,z)).pass
      (fun v=>run (DFTModelCacheNatDispatch.fuelProgram instructions)
        (UniformGreedyColorMachine.runtimeBudget z.len,v))).pay
        23 (UniformGreedyColorMachine.runtimeBudget z.len) := by
  rw [compiled,comp_run,fork_run,runtimeProgram_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,true_and,and_true]
  congr 1 <;> omega

end
end ExactFourierCircuits.DFTModelCacheColor
