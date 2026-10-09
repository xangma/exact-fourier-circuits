import UniformRecursiveNamedSeedPrinterFacts
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNamedUnitPrinterFacts
lemma square_eq (m : ℕ) : 3*(8+m*m)+4=3*(8+m^2)+4 := by rw [pow_two]
theorem unit_printer_eq : UniformRecursiveSavingProgram.unitPrinterLength=
 3*(8+ExplicitSeedBudget.m*ExplicitSeedBudget.m)+4 := by
 norm_num [UniformRecursiveSavingProgram.unitPrinterLength,
  UniformRecursiveSavingProgram.unitLength,ExplicitSeedBudget.m]
theorem unit_printer_square : UniformRecursiveSavingProgram.unitPrinterLength=
 3*(8+ExplicitSeedBudget.m^2)+4 :=
 unit_printer_eq.trans (square_eq ExplicitSeedBudget.m)
end ExactFourierCircuits.UniformRecursiveNamedUnitPrinterFacts
