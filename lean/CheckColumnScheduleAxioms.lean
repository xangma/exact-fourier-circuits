import ColumnSchedule
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.BinaryResiduals.tensorBasis.congr_simp
#print axioms ExactFourierCircuits.ColumnSchedule.column
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis._proof_1
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis._proof_2
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis._proof_3
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis._proof_4
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis_orthonormal
#print axioms ExactFourierCircuits.ColumnSchedule.columnBasis_vector
#print axioms ExactFourierCircuits.ColumnSchedule.columnResidualBasis
#print axioms ExactFourierCircuits.ColumnSchedule.columnResidualBasis._proof_1
#print axioms ExactFourierCircuits.ColumnSchedule.columnResidualBasis_orthonormal
#print axioms ExactFourierCircuits.ColumnSchedule.columnSpace
#print axioms ExactFourierCircuits.ColumnSchedule.columnSpace_mono
#print axioms ExactFourierCircuits.ColumnSchedule.columns
#print axioms ExactFourierCircuits.ColumnSchedule.columns._proof_1
#print axioms ExactFourierCircuits.ColumnSchedule.columns_decomposes
#print axioms ExactFourierCircuits.ColumnSchedule.columns_dimension
#print axioms ExactFourierCircuits.ColumnSchedule.columns_exponent
#print axioms ExactFourierCircuits.ColumnSchedule.columns_exponent_flat
#print axioms ExactFourierCircuits.ColumnSchedule.columns_projection
#print axioms ExactFourierCircuits.ColumnSchedule.columns_residual
#print axioms ExactFourierCircuits.ColumnSchedule.columns_space
#print axioms ExactFourierCircuits.ColumnSchedule.columns_vectors_eq
#print axioms ExactFourierCircuits.ColumnSchedule.coordinates_weightModFour
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns._proof_1
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns._proof_2
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns.match_1
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns_dimension
#print axioms ExactFourierCircuits.ColumnSchedule.edgesColumns
#print axioms ExactFourierCircuits.ColumnSchedule.edgesColumns_dimension
#print axioms ExactFourierCircuits.ColumnSchedule.eventColumns
#print axioms ExactFourierCircuits.ColumnSchedule.eventColumns._proof_1
#print axioms ExactFourierCircuits.ColumnSchedule.eventColumns_residualDimension
#print axioms ExactFourierCircuits.ColumnSchedule.eventColumns_scalarMatrix
#print axioms ExactFourierCircuits.ColumnSchedule.finishColumns_word_array
#print axioms ExactFourierCircuits.ColumnSchedule.finishColumns_word_calls
#print axioms ExactFourierCircuits.ColumnSchedule.labelsColumns
#print axioms ExactFourierCircuits.ColumnSchedule.projection_coordinates
#print axioms ExactFourierCircuits.ColumnSchedule.projection_index_equiv
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns._f
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns._sunfold
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns._unsafe_rec
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns.eq_1
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns.eq_2
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns.eq_def
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns.match_1
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns_residualDimension
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns_scalarCount
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns_scalarMatrix
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns_word_array
#print axioms ExactFourierCircuits.ColumnSchedule.scheduleColumns_word_calls
#print axioms ExactFourierCircuits.ColumnSchedule.zero_columns_exponent

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.ColumnSchedule.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"
