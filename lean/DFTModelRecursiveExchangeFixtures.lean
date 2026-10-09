import DFTModelRecursiveExchangeSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelRecursiveExchangeFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveExchange
open DFTModelRecursiveScalarSource (paired)
noncomputable section

def overlap : List (UniformNativeExchangeRecordMachine.Pair 3) :=
  [⟨0,1,by decide⟩,⟨1,2,by decide⟩]

theorem overlap_last (q w k : ℕ) (I : ℂ)
    (f f0 : Fin 3 → Fin 1 → UniformMachine.Scalar) :
    (run (program 3) (recordTape q w overlap,((k,I),paired f f0))).val.2.look 2 Tagged.blank=
      encodePaired (f 0 0) (f0 0 0) := by
  have h := program_lookup q w overlap (by omega : 0<1) f f0 k I (2 : Fin 3) (0 : Fin 1)
  simpa [overlap,UniformNativeExchangeRecordMachine.actions,
    UniformFixedNetworkExchangeChildMachine.values,UniformFixedNetworkExchangeChildMachine.negative] using h

theorem overlap_first (q w k : ℕ) (I : ℂ)
    (f f0 : Fin 3 → Fin 1 → UniformMachine.Scalar) :
    (run (program 3) (recordTape q w overlap,((k,I),paired f f0))).val.2.look 0 Tagged.blank=
      encodePaired (f 1 0) (f0 1 0) := by
  have h := program_lookup q w overlap (by omega : 0<1) f f0 k I (0 : Fin 3) (0 : Fin 1)
  simpa [overlap,UniformNativeExchangeRecordMachine.actions,
    UniformFixedNetworkExchangeChildMachine.values] using h

theorem empty_value {R V : ℕ} (q w k : ℕ) (I : ℂ)
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) :
    (run (program R) (recordTape (R:=R) q w [],((k,I),paired f f0))).val=((k,I),paired f f0) := by
  exact program_value q w [] positive f f0 k I

theorem empty_work {R V : ℕ} (q w k : ℕ) (I : ℂ)
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) :
    (run (program R) (recordTape (R:=R) q w [],((k,I),paired f f0))).work≤19 := by
  exact program_work_bound q w [] positive f f0 k I

end
end ExactFourierCircuits.DFTModelRecursiveExchangeFixtures
