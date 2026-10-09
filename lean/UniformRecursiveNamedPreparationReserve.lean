import UniformRecursiveNamedUnitPrinterFacts
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNamedPreparationReserve
open UniformFixedNetworkScheduleMachine
noncomputable section

lemma producer_adapter (seed unit L N m : ℕ)
 (first:seed=3*L+3*N+7) (second:unit=3*(8+m^2)+4) :
 seed+12+unit+15+50 ≤ 3*L+3*N+3*(8+m^2)+1000 := by
 rw [first,second]
 omega

theorem actual_producer_polynomial :
 UniformRecursiveSavingProgram.seedPrinterLength+12+
 UniformRecursiveSavingProgram.unitPrinterLength+15+50 ≤
 3*(serialize baseSchedule).length+3*baseSchedule.length+3*(8+ExplicitSeedBudget.m^2)+1000 :=
 producer_adapter UniformRecursiveSavingProgram.seedPrinterLength
  UniformRecursiveSavingProgram.unitPrinterLength
  (serialize baseSchedule).length baseSchedule.length ExplicitSeedBudget.m
  UniformRecursiveNamedSeedPrinterFacts.seed_printer_eq
  UniformRecursiveNamedUnitPrinterFacts.unit_printer_square

private opaque reserve : {P : ℕ //
 3*(serialize baseSchedule).length+3*baseSchedule.length+3*(8+ExplicitSeedBudget.m^2)+1000 ≤ P} :=
 ⟨3*(serialize baseSchedule).length+3*baseSchedule.length+3*(8+ExplicitSeedBudget.m^2)+1000,le_rfl⟩

def preparationTicks : ℕ := reserve.val
lemma preparationTicks_lower :
 3*(serialize baseSchedule).length+3*baseSchedule.length+3*(8+ExplicitSeedBudget.m^2)+1000 ≤ preparationTicks :=
 reserve.property

theorem actual_producer_bound :
 UniformRecursiveSavingProgram.seedPrinterLength+12+
 UniformRecursiveSavingProgram.unitPrinterLength+15+50 ≤ preparationTicks :=
 actual_producer_polynomial.trans preparationTicks_lower

end
end ExactFourierCircuits.UniformRecursiveNamedPreparationReserve
