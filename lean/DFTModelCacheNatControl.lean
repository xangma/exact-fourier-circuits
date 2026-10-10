import DFTModelCacheNatControlBounds
import DFTModelCacheNatControlSource
import DFTModelCacheNatControlLayout

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatControl
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section

theorem instruction_lengths (i : Instruction) (v : LocalValue) :
    (run (instruction i) v).val.2.1.len=v.2.1.len ∧
      (run (instruction i) v).val.2.2.len=v.2.2.len := by
  rw [instruction_value]
  cases i <;> simp [result,put,putHeap,setPC,Tape.set]
  split_ifs <;> exact ⟨rfl,rfl⟩

/-- An accepted local natural instruction has genuine upstream syntax, exact
native-step correspondence, linear dense-update work and a checked word peak.
`Fits` is the local addressing boundary, not a precomputed output bank. -/
theorem step_specification {i : Instruction} {v : LocalValue}
    {s u : UniformMachine.State} (p : UniformMachine.Program) (n B : ℕ) (x : Fin n→ℂ)
    (h : Represents v s) (fit : Fits i v) (peak : PeakBound i v B)
    (code : p[s.pc]?=some i.native) (step : UniformMachine.step p n x s=.running u) :
    (run (instruction i) v).valid ∧ Represents (run (instruction i) v).val u ∧
      (run (instruction i) v).work≤35*(v.2.1.len+v.2.2.len)+100 ∧
      (run (instruction i) v).peak≤B := by
  have hs:=running_source p n x h fit code step
  exact ⟨hs.1,hs.2,instruction_work i v,instruction_peak i v B peak⟩

end
end ExactFourierCircuits.DFTModelCacheNatControl
