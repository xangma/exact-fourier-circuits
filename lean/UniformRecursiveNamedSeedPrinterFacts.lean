import UniformRecursiveLocalAllowance
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNamedSeedPrinterFacts
open UniformFixedNetworkScheduleMachine
lemma reflexive_apply {α β : Type*} (f : α→β) (a : α) : f a=f a := Eq.refl _
lemma three_equalities (a b c d : ℕ) (ab:a=b) (bc:b=c) (cd:c=d) : a=d :=
 ab.trans (bc.trans cd)
lemma preparation_polynomial (L N m : ℕ) :
 3*L+3*N+3*(8+m^2)+1000=3*L+3*N+3*(8+m^2)+1000 := Eq.refl _

theorem fixed_program_eq : UniformFixedNetworkLiteralDecoderMachine.fixedProgram=
 UniformFixedNetworkLiteralDecoderMachine.program baseSchedule :=
 reflexive_apply UniformFixedNetworkLiteralDecoderMachine.program baseSchedule

theorem seed_printer_eq : UniformRecursiveSavingProgram.seedPrinterLength=
 3*(serialize baseSchedule).length+3*baseSchedule.length+7 :=
 three_equalities UniformRecursiveSavingProgram.seedPrinterLength
  UniformFixedNetworkLiteralDecoderMachine.fixedProgram.length
  (UniformFixedNetworkLiteralDecoderMachine.program baseSchedule).length
  (3*(serialize baseSchedule).length+3*baseSchedule.length+7)
  UniformRecursiveSavingProgram.seedPrinter_length.symm
  (congrArg List.length fixed_program_eq)
  (UniformFixedNetworkLiteralDecoderMachine.program_length baseSchedule)

end ExactFourierCircuits.UniformRecursiveNamedSeedPrinterFacts
