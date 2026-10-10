import DFTModelCacheTopologyArithmetic

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
noncomputable section

theorem registerCell_value (K a e j : ℕ) :
    (run registerCell (config K a e,j)).val=regValue K a e j := by
  simp only [registerCell,DFTModelCacheMatchingNat.select_value,
    k,DFTModelCacheTopology.a,DFTModelCacheTopology.e,config,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    regValue,←destination_value K a e]
  rfl

theorem initialize_value (K a e : ℕ) :
    (run initializeProgram (config K a e)).val=initialValue K a e := by
  unfold initializeProgram
  rw [DFTModelCacheMatchingNat.fork_value,DFTModelCacheMatchingNat.fork_value,
    DFTModelCacheMatchingNat.tab_value_code,DFTModelCacheMatchingNat.tab_value_code,
    heapLength_value]
  simp only [atom_run,Atom.run,Bill.word]
  apply congrArg (fun z=>(0,z))
  apply Prod.ext
  · exact congrArg (Tape.tab 600) (funext (registerCell_value K a e))
  · rfl

theorem initial_represents (K a e : ℕ) : Represents (initialValue K a e) (sourceState K a e) := by
  refine ⟨rfl,?_,?_⟩
  · intro j hj
    change (Tape.tab 600 (regValue K a e)).look j 0=regValue K a e j
    change j<600 at hj
    rw [Tape.look_of_lt _ _ hj];rfl
  · intro j hj
    change ModelEquivalenceInterpreter.decodeNatCell
      ((Tape.tab (H K a e) (fun _=>(0,0))).look j (0,0))=none
    change j<H K a e at hj
    rw [Tape.look_of_lt _ _ hj];rfl

theorem source_params (K a e : ℕ) :
    UniformToeplitzCrossTopologyMachine.Params K a e 0 (D K) (sourceState K a e) := by
  simp [UniformToeplitzCrossTopologyMachine.Params,sourceState,regValue]

theorem source_wordBound (K a e : ℕ) : UniformMachine.WordBound (B K a e) (sourceState K a e) := by
  have h:=UniformToeplitzCrossTopologyMachine.budget_tail K a e 0 (D K)
  refine ⟨Nat.zero_le _,?_,?_,?_,?_,?_⟩
  · intro j
    change regValue K a e j≤B K a e
    unfold regValue B
    split_ifs <;> omega
  · intro _ _ impossible;cases impossible
  · intro _ _ impossible;cases impossible
  · intro _ _ impossible;cases impossible
  · intro _ impossible;cases impossible

/-- The native witness starts from exactly the state encoded by charged setup;
there is no source-tape entry assumption. -/
theorem native_execution (inputLength K a e : ℕ) (x : Fin inputLength→ℂ) : ∃u t,
    UniformMachine.BoundedExecution UniformToeplitzCrossTopologyMachine.program inputLength x
      (B K a e) (sourceState K a e) t u ∧ t≤T K a ∧ u.pc=270 ∧
    UniformToeplitzCrossTopologyMachine.RowTable
      (UniformToeplitzCrossTopologyMachine.crossRows K a e) (D K) u := by
  obtain ⟨u,t,actual,time,pc,rows,_⟩:=UniformToeplitzCrossTopologyMachine.execution
    inputLength K a e 0 (D K) (B K a e) x (sourceState K a e)
    (source_params K a e) rfl (by unfold D G;omega) (source_wordBound K a e) le_rfl
  exact ⟨u,t,actual,time,pc,rows⟩

end
end ExactFourierCircuits.DFTModelCacheTopology
