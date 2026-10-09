import UniformJointAllocation
import UniformRecursiveReserve

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualGlobalConstants
open UniformJointAllocation
noncomputable section
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program

/-- One fixed conservative constant includes the actual proved recursive
reserve. Neither the role bank nor its astronomical printer is materialized. -/
def constants:Constants:=
 ⟨UniformRecursiveSavingProgram.program.length+UniformRecursiveReserve.reserve,
  UniformRecursiveSavingProgram.seedLength,UniformRecursiveSavingProgram.unitLength,
  UniformRecursiveSelfCallMachine.W⟩
lemma code_eq:constants.code=UniformRecursiveSavingProgram.program.length+UniformRecursiveReserve.reserve:=rfl
lemma seed_eq:constants.seedTape=UniformRecursiveSavingProgram.seedLength:=rfl
lemma unit_eq:constants.unitTape=UniformRecursiveSavingProgram.unitLength:=rfl
lemma roles_eq:constants.roles=UniformRecursiveSelfCallMachine.W:=rfl
lemma roles_positive:0 < constants.roles:=UniformRecursiveSelfCallMachine.W_positive
lemma reserve_code:UniformRecursiveReserve.reserve ≤ constants.code:=by
 change UniformRecursiveReserve.reserve ≤ UniformRecursiveSavingProgram.program.length+UniformRecursiveReserve.reserve
 exact Nat.le_add_left _ _
lemma reserve_le:UniformRecursiveReserve.reserve ≤ fixed constants:=
 reserve_code.trans (program_le constants)
lemma code_le:UniformRecursiveSavingProgram.program.length ≤ constants.code:=by
 change UniformRecursiveSavingProgram.program.length ≤ UniformRecursiveSavingProgram.program.length+UniformRecursiveReserve.reserve
 exact Nat.le_add_right _ _
lemma envelope_bound (u f:ℕ):f ≤ 40*u+f:=by omega
lemma reserve_envelope (n:ℕ):UniformRecursiveReserve.reserve ≤ envelope constants n:=
 reserve_le.trans (envelope_bound _ _)
lemma code_envelope (n:ℕ):UniformRecursiveSavingProgram.program.length ≤ envelope constants n:=
 code_le.trans (program_bound constants n)
end
end ExactFourierCircuits.UniformActualGlobalConstants
