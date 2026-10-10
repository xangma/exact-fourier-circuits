import DFTModelCacheColorSource
import DFTModelCacheColorBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open UniformMatchingAxisTableMachine (InRange)
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

def compiledWork (r M : ℕ) := 200027+204*H r M+
  UniformGreedyColorMachine.runtimeBudget M*(35*(824+H r M)+411)
def compiledPeak (r M : ℕ) := max (4*H r M+3000)
  (UniformGreedyColorMachine.runtimeBudget M)

attribute [local irreducible] Code.run

/-- The fixed typed loop includes all actual native steps and halt stutters.
All native inputs arise from raw Row3 projection and fresh typed allocations. -/
theorem compiled_execution {M : ℕ} (r n : ℕ) (x : Fin n→ℂ)
    (z : Tape Row.T) (E : Fin M→UniformColoring.Edge)
    (rows : Rows E z) (hr : InRange r E) : ∃t u,
    t≤UniformGreedyColorMachine.runtimeBudget z.len ∧
    UniformMachine.BoundedExecution UniformGreedyColorMachine.program n x
      (B r z.len) (sourceState r z) t u ∧ u.pc=50 ∧
    UniformGreedyColorMachine.Colors E (C z.len) M u ∧
    (run compiled (r,z)).valid ∧ Represents (run compiled (r,z)).val u ∧
    (run compiled (r,z)).work≤compiledWork r z.len ∧
    (run compiled (r,z)).peak≤compiledPeak r z.len := by
  obtain ⟨t,u,time,actual,pc,colors⟩:=native_execution r n x z E rows hr
  have nativeRun:UniformMachine.BoundedExecution (DFTModelCacheNatDispatch.native instructions)
      n x (B r z.len) (sourceState r z) t u := by
    simpa only [DFTModelCacheNatDispatch.native,instructions_native] using actual
  have typed:=padded_trace instructions n (B r z.len)
    (DFTModelCacheNatDispatchFinite.wordBound 824 824 (B r z.len)) 824 (H r z.len)
    t (UniformGreedyColorMachine.runtimeBudget z.len) x (sourceState r z) u
    (run initializeProgram (r,z)).val nativeRun (initialized_represents r z)
    (by rw [initialize_value];rfl) (by rw [initialize_value];rfl)
    (by have:=DFTModelCacheNatDispatchFinite.source_le 824 824 (B r z.len);omega)
    time (DFTModelCacheNatDispatchFinite.running_safety instructions n x (B r z.len)
      824 824 instructions_footprint)
    (DFTModelCacheNatDispatchFinite.halt_safety (B r z.len) 824 824)
  have init:=initialize_bounds r z
  have work:=DFTModelCacheNatDispatch.fuel_work instructions
    (UniformGreedyColorMachine.runtimeBudget z.len) (run initializeProgram (r,z)).val
  have regs:(run initializeProgram (r,z)).val.2.1.len=824 := by rw [initialize_value];rfl
  have heap:(run initializeProgram (r,z)).val.2.2.len=H r z.len := by rw [initialize_value];rfl
  rw [regs,heap,instructions_length] at work
  have coeff:35*(824+H r z.len)+105+6*51=35*(824+H r z.len)+411 := by omega
  rw [coeff] at work
  rw [compiled_run]
  refine ⟨t,u,time,actual,pc,colors,⟨init.1,typed.1⟩,typed.2.1,?_,?_⟩
  · change (run initializeProgram (r,z)).work+_+23≤_
    unfold compiledWork
    have initialWork:=init.2.1
    dsimp only at work ⊢
    omega
  · change max (max (run initializeProgram (r,z)).peak _) _≤_
    have bound:DFTModelCacheNatDispatchFinite.wordBound 824 824 (B r z.len)≤4*H r z.len+3000 := by
      unfold DFTModelCacheNatDispatchFinite.wordBound H B U
      omega
    unfold compiledPeak
    have pk:=typed.2.2.trans (max_le_max_left _ bound)
    rw [max_comm] at pk
    dsimp only at pk ⊢
    exact max_le (max_le (init.2.2.trans (le_max_left _ _)) pk) (le_max_right _ _)

end
end ExactFourierCircuits.DFTModelCacheColor
