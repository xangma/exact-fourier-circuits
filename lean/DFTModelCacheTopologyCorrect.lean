import DFTModelCacheTopologyReadback
import DFTModelCacheTopologyPrepare

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
noncomputable section

attribute [local irreducible] Code.run

theorem compiled_value (K a e : ℕ) :
    (run compiled (config K a e)).val=
      (run (DFTModelCacheNatDispatch.fuelProgram instructions) (T K a,initialValue K a e)).val := by
  rw [compiled,comp_run,fork_run]
  change (run (DFTModelCacheNatDispatch.fuelProgram instructions)
    ((run fuel (config K a e)).val,(run initializeProgram (config K a e)).val)).val=_
  rw [fuel_value,initialize_value]

theorem computed_value (K a e : ℕ) :
    (run computed (config K a e)).val=(config K a e,(run compiled (config K a e)).val) := by
  rw [computed,DFTModelCacheMatchingNat.fork_value,atom_run];rfl

theorem body_value (K a e : ℕ) :
    (run body (config K a e)).val=outputValue K a e (run compiled (config K a e)).val := by
  rw [body,comp_run]
  change (run readback (run computed (config K a e)).val).val=_
  rw [computed_value,readback_value]

theorem program_value (a e : ℕ) :
    (run program (a,e)).val=(run body (config (exponent a e) a e)).val := by
  rw [program,comp_run]
  change (run body (run prepare (a,e)).val).val=_
  rw [(prepare_spec a e).1]

/-- Concrete produced output, with the same actual native execution retained. -/
structure Result (a e : ℕ) (u : UniformMachine.State) (ticks : ℕ) : Prop where
  actual : UniformMachine.BoundedExecution UniformToeplitzCrossTopologyMachine.program 0
    (fun j=>Fin.elim0 j) (B (exponent a e) a e) (sourceState (exponent a e) a e) ticks u
  time : ticks≤T (exponent a e) a
  terminal : u.pc=270
  rows : UniformToeplitzCrossTopologyMachine.RowTable
    (UniformToeplitzCrossTopologyMachine.crossRows (exponent a e) a e) (D (exponent a e)) u
  exponent : (run program (a,e)).val.1=DFTModelCacheTopology.exponent a e
  count : (run program (a,e)).val.2.1=C (DFTModelCacheTopology.exponent a e) a
  length : (run program (a,e)).val.2.2.len=5*C (DFTModelCacheTopology.exponent a e) a
  copied : DFTModelCacheDAGDepth.CopiedTopology (C (DFTModelCacheTopology.exponent a e) a)
    (D (DFTModelCacheTopology.exponent a e)) (run program (a,e)).val.2.2 u
  encoded : UniformDAGDepthMachine.EncodedTape
    (UniformToeplitzCrossDAG.crossDAG (DFTModelCacheTopology.exponent a e) a e
      (dimensions_fit a e).1 (dimensions_fit a e).2).program (D (DFTModelCacheTopology.exponent a e)) u

theorem execution_values (a e : ℕ) : ∃u ticks,Result a e u ticks := by
  let K:=exponent a e
  obtain ⟨u,t,actual,time,pc,rows,_valid,rep,_work,_peak⟩:=interpreted_source K a e
  have heapLen : (run compiled (config K a e)).val.2.2.len=H K a e := by
    rw [compiled_value,DFTModelCacheNatDispatch.fuel_value]
    exact (DFTModelCacheNatDispatch.trajectory_lengths instructions (initialValue K a e) (T K a)).2
  have represented : Represents (run compiled (config K a e)).val u := by
    rw [compiled_value];exact rep
  have copy:=copied_topology K a e (run compiled (config K a e)).val u heapLen represented rows
  refine ⟨u,t,actual,time,pc,rows,?_,?_,?_,?_,?_⟩
  · rw [program_value,body_value];rfl
  · rw [program_value,body_value];rfl
  · rw [program_value,body_value];rfl
  · rw [program_value,body_value]
    rw [readback_value] at copy
    exact copy
  · exact encoded_tape K a e (dimensions_fit a e).1 (dimensions_fit a e).2 u rows

end
end ExactFourierCircuits.DFTModelCacheTopology
