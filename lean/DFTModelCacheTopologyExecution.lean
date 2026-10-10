import DFTModelCacheTopologyInitialization

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
noncomputable section

private theorem padded_trace (code : List Instruction) (inputLength nativeB wordB R heapN count total : ℕ)
    (x : Fin inputLength→ℂ) (s u : UniformMachine.State) (v : LocalValue)
    (actual : UniformMachine.BoundedExecution (DFTModelCacheNatDispatch.native code)
      inputLength x nativeB s count u)
    (rep : Represents v s) (regs : v.2.1.len=R) (heap : v.2.2.len=heapN)
    (words : nativeB≤wordB) (enough : count≤total)
    (runningSafe : DFTModelCacheNatDispatch.RunningSafety code inputLength x nativeB wordB R heapN)
    (haltSafe : DFTModelCacheNatDispatch.HaltSafety nativeB wordB R heapN) :
    (run (DFTModelCacheNatDispatch.fuelProgram code) (total,v)).valid ∧
    Represents (run (DFTModelCacheNatDispatch.fuelProgram code) (total,v)).val u ∧
    (run (DFTModelCacheNatDispatch.fuelProgram code) (total,v)).peak≤ max total wordB := by
  let trace:=DFTModelCacheNatDispatch.bounded_trajectory code inputLength x nativeB wordB R heapN
    s u count actual v rep regs heap words runningSafe haltSafe
  have stable : ∀j,count≤j→DFTModelCacheNatDispatch.trajectory code v j=
      DFTModelCacheNatDispatch.trajectory code v count := by
    intro j hj
    rw [show j=count+(j-count) by omega,DFTModelCacheNatDispatch.trajectory_add]
    exact DFTModelCacheNatDispatch.trajectory_halt code _ trace.halted _
  have lengths:=DFTModelCacheNatDispatch.trajectory_lengths code v count
  have last:=haltSafe _ u trace.represents (lengths.1.trans regs) (lengths.2.trans heap)
    actual.final_bound
  refine ⟨(DFTModelCacheNatDispatch.fuel_valid code total v).mpr ?_,?_,?_⟩
  · intro j hj
    by_cases h:j<count
    · exact trace.accepted j h
    · rw [stable j (by omega)];exact ⟨.halt,trace.halted,trivial⟩
  · rw [DFTModelCacheNatDispatch.fuel_value,stable total enough]
    exact trace.represents
  · apply DFTModelCacheNatDispatch.fuel_peak code total v (max total wordB) (le_max_left _ _)
    · intro j hj
      by_cases h:j<count
      · exact (trace.pc j h).trans (le_max_right _ _)
      · rw [stable j (by omega),trace.represents.pc]
        exact actual.final_bound.1.trans (words.trans (le_max_right _ _))
    · intro j hj i chosen
      apply DFTModelCacheNatDispatch.peakBound_mono i _ _ (le_max_right _ _)
      by_cases h:j<count
      · exact trace.peak j h i chosen
      · rw [stable j (by omega)] at chosen ⊢
        rw [trace.halted] at chosen
        have hi:i=.halt := (Option.some.inj chosen).symm
        subst i;exact last

/-- Fixed charged fuel includes every native step and any remaining halt stutters. -/
theorem interpreted_source (K a e : ℕ) : ∃u t,
    UniformMachine.BoundedExecution UniformToeplitzCrossTopologyMachine.program 0
      (fun j=>Fin.elim0 j) (B K a e) (sourceState K a e) t u ∧
    t≤T K a ∧ u.pc=270 ∧
    UniformToeplitzCrossTopologyMachine.RowTable
      (UniformToeplitzCrossTopologyMachine.crossRows K a e) (D K) u ∧
    (run (DFTModelCacheNatDispatch.fuelProgram instructions) (T K a,initialValue K a e)).valid ∧
    Represents (run (DFTModelCacheNatDispatch.fuelProgram instructions) (T K a,initialValue K a e)).val u ∧
    (run (DFTModelCacheNatDispatch.fuelProgram instructions) (T K a,initialValue K a e)).work≤
      4+T K a*(35*(600+H K a e)+105+6*271) ∧
    (run (DFTModelCacheNatDispatch.fuelProgram instructions) (T K a,initialValue K a e)).peak≤
      max (T K a) (DFTModelCacheNatDispatchFinite.wordBound 600 600 (B K a e)) := by
  obtain ⟨u,t,actual,time,pc,rows⟩:=native_execution 0 K a e (fun j=>Fin.elim0 j)
  have converted : UniformMachine.BoundedExecution (DFTModelCacheNatDispatch.native instructions)
      0 (fun j=>Fin.elim0 j) (B K a e) (sourceState K a e) t u :=
    instructions_native.symm ▸ actual
  have typed:=padded_trace instructions 0 (B K a e)
    (DFTModelCacheNatDispatchFinite.wordBound 600 600 (B K a e)) 600 (H K a e) t (T K a)
    (fun j=>Fin.elim0 j) (sourceState K a e) u (initialValue K a e) converted
    (initial_represents K a e) rfl rfl
    (by have:=DFTModelCacheNatDispatchFinite.source_le 600 600 (B K a e);omega)
    time (DFTModelCacheNatDispatchFinite.running_safety instructions 0 (fun j=>Fin.elim0 j)
      (B K a e) 600 600 instructions_footprint)
    (DFTModelCacheNatDispatchFinite.halt_safety (B K a e) 600 600)
  refine ⟨u,t,actual,time,pc,rows,typed.1,typed.2.1,?_,typed.2.2⟩
  simpa only [initialValue,Tape.tab,instructions_length] using
    DFTModelCacheNatDispatch.fuel_work instructions (T K a) (initialValue K a e)

end
end ExactFourierCircuits.DFTModelCacheTopology
