import UniformFinalMovementGeometry
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.AP
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.B
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.BI
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.adjacent
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.alpha
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.beforeSource
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.beforeTarget
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.casesOn
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.code
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.disjoint
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.inverse
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.mk
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.rec
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.recOn
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.source
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.Fits.target
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.S
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.T
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.V
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.fits._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.roles_before_target
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.roles_before_target._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalMovementGeometry.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"
