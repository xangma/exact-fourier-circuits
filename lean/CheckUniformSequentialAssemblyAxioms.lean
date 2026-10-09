import UniformSequentialAssembly
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSequentialAssembly.block_pc
#print axioms ExactFourierCircuits.UniformSequentialAssembly.block_pc._proof_1_4
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code._f
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code._sunfold
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code._unsafe_rec
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code.eq_1
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code.eq_2
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code.eq_def
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code.match_1
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code_length
#print axioms ExactFourierCircuits.UniformSequentialAssembly.code_length._proof_1_7
#print axioms ExactFourierCircuits.UniformSequentialAssembly.final_halt
#print axioms ExactFourierCircuits.UniformSequentialAssembly.get_stage
#print axioms ExactFourierCircuits.UniformSequentialAssembly.get_stage._proof_1_7
#print axioms ExactFourierCircuits.UniformSequentialAssembly.halt_at
#print axioms ExactFourierCircuits.UniformSequentialAssembly.natProgram
#print axioms ExactFourierCircuits.UniformSequentialAssembly.natProgram.eq_1
#print axioms ExactFourierCircuits.UniformSequentialAssembly.natProgram_code
#print axioms ExactFourierCircuits.UniformSequentialAssembly.natProgram_halt
#print axioms ExactFourierCircuits.UniformSequentialAssembly.natProgram_length
#print axioms ExactFourierCircuits.UniformSequentialAssembly.nat_execution
#print axioms ExactFourierCircuits.UniformSequentialAssembly.program
#print axioms ExactFourierCircuits.UniformSequentialAssembly.program.eq_1
#print axioms ExactFourierCircuits.UniformSequentialAssembly.program_length
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size._f
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size._sunfold
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size._unsafe_rec
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size.eq_1
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size.eq_2
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size.eq_def
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size_append
#print axioms ExactFourierCircuits.UniformSequentialAssembly.size_append._proof_1_4
#print axioms ExactFourierCircuits.UniformSequentialAssembly.stage_code

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSequentialAssembly.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"
