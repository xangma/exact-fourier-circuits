import UniformFinalDFTExecution
set_option autoImplicit false

example : ExactFourierCircuits.UniformMachine.UniformDFTStatement
    ExactFourierCircuits.UniformExponent.theta :=
  ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT

#print axioms ExactFourierCircuits.UniformFinalDFTExecution.execution
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT
#check ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT
