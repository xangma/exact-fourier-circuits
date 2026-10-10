import DFTModelCacheNatProjectionSource
import DFTModelCacheNatDispatchBounded

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatProjection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

/-- The returned tape is only integer metadata. No scalar source state is
translated by this program. Runtime fuel remains an explicitly charged input. -/
def program (p : Program) : Prog false DFTModelCacheNatDispatch.FuelInput
    DFTModelCacheNatControl.Local := DFTModelCacheNatDispatch.fuelProgram (code p)

theorem represents_state_iff (v : DFTModelCacheNatControl.LocalValue) (base current : State) :
    DFTModelCacheNatControl.Represents v (state base current)↔
      DFTModelCacheNatControl.Represents v current :=
  ⟨fun h=>⟨h.pc,h.registers,h.heap⟩,fun h=>⟨h.pc,h.registers,h.heap⟩⟩

/-- A genuine successful mixed source execution feeds the fixed typed Nat
compiler. Finite addressing/peak safety and ordinary initialization are caller
obligations; neither a produced metadata table nor a scalar result is assumed. -/
theorem typed_source {p : Program} {n nativeB count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (actual : BoundedExecution p n x nativeB s count u)
    (wordB R H : ℕ) (v : DFTModelCacheNatControl.LocalValue)
    (rep : DFTModelCacheNatControl.Represents v s)
    (regs : v.2.1.len=R) (heap : v.2.2.len=H) (words : nativeB≤wordB)
    (runningSafe : DFTModelCacheNatDispatch.RunningSafety (code p) n x nativeB wordB R H)
    (haltSafe : DFTModelCacheNatDispatch.HaltSafety nativeB wordB R H) :
    (run (program p) (count,v)).valid ∧
      DFTModelCacheNatControl.Represents (run (program p) (count,v)).val u ∧
      (run (program p) (count,v)).work≤4+count*(35*(R+H)+105+6*p.length) ∧
      (run (program p) (count,v)).peak ≤ max count wordB := by
  have projected:=bounded_source noLength actual
  have compiled:=DFTModelCacheNatDispatch.bounded_source (code p) n x nativeB wordB R H
    s (state s u) count projected v rep regs heap words runningSafe haltSafe
  refine ⟨compiled.1,?_,?_,compiled.2.2.2⟩
  · exact (represents_state_iff _ s u).mp compiled.2.1
  · simpa only [program,code_length] using compiled.2.2.1

end
end ExactFourierCircuits.DFTModelCacheNatProjection
