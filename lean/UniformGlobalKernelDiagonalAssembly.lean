import UniformInitializedKernelExecution
import UniformDiagonalHeaderInstallation
import UniformDiagonalReturnNumeric

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalKernelDiagonalAssembly
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Every tick runs the common-C kernel before the actual produced diagonal.
All helper halts are charged jumps in this one literal program. -/
def headerProgram (W:ℕ):Program:=(UniformDiagonalHeaderInstallation.block W).map Op.code++[.halt]
def programFor (child:Program) (W:ℕ):Program:=UniformGlobalMovementAssembly.assembly
 (UniformInitializedKernelExecution.programFor child W) (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
lemma header_length (W:ℕ):(headerProgram W).length=18:=by
 simp only[headerProgram,List.length_append,List.length_map,UniformDiagonalHeaderInstallation.block_length,
 List.length_cons,List.length_nil]
lemma program_length (child:Program) (W:ℕ):(programFor child W).length=child.length+813:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly_length,
 UniformInitializedKernelExecution.program_length,header_length,UniformGlobalDiagonalReturn.program_length]
lemma kernel_code (child:Program) (W:ℕ):
 CodeAt (UniformInitializedKernelExecution.programFor child W) (programFor child W) 0 (child.length+647):=by
 simpa only[programFor,UniformInitializedKernelExecution.program_length] using
  UniformGlobalMovementAssembly.first_code (UniformInitializedKernelExecution.programFor child W)
   (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
lemma header_code (child:Program) (W:ℕ):
 BlockAt (UniformDiagonalHeaderInstallation.block W) (programFor child W) (child.length+647):=by
 have code:=UniformGlobalMovementAssembly.second_code (UniformInitializedKernelExecution.programFor child W)
  (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
 have block:BlockAt (UniformDiagonalHeaderInstallation.block W) (headerProgram W) 0:=
  UniformRankCrossPreparationMachine.block_of_segment _ [] [.halt] 0 rfl
 intro i hi
 have c:=code i (by rw[header_length];have len:=UniformDiagonalHeaderInstallation.block_length W;omega)
 have b:=block i hi
 simp only[Nat.zero_add] at b
 rw[b] at c
 have fixed:∀(o:Op)(base ret:ℕ),relocate base ret o.code=o.code:=by
  intro o base ret;cases o <;>rfl
 simpa only[programFor,UniformInitializedKernelExecution.program_length,Option.map_some,fixed] using c
lemma header_jump (child:Program) (W:ℕ):
 (programFor child W)[child.length+664]?=some (.jump (child.length+665)):=by
 have code:=UniformGlobalMovementAssembly.second_code (UniformInitializedKernelExecution.programFor child W)
  (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
 have c:=code 17 (by rw[header_length];omega)
 have h:(headerProgram W)[17]?=some .halt:=by
  unfold headerProgram
  rw[List.getElem?_append_right (by rw[List.length_map,UniformDiagonalHeaderInstallation.block_length])]
  rfl
 rw[h] at c
 simpa only[programFor,UniformInitializedKernelExecution.program_length,header_length,
 show 647+17=664 by rfl,show 647+18=665 by rfl,Nat.add_assoc,Option.map_some,relocate] using c
lemma diagonal_code (child:Program) (W:ℕ):
 CodeAt (UniformGlobalDiagonalReturn.programFor W) (programFor child W) (child.length+665) (child.length+812):=by
 simpa only[programFor,UniformInitializedKernelExecution.program_length,header_length,
 UniformGlobalDiagonalReturn.program_length,Nat.add_assoc,show 647+18=665 by rfl,show 665+147=812 by rfl] using
  UniformGlobalMovementAssembly.third_code (UniformInitializedKernelExecution.programFor child W)
   (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
lemma halt_at (child:Program) (W:ℕ):(programFor child W)[child.length+812]?=some .halt:=by
 simpa only[programFor,UniformInitializedKernelExecution.program_length,header_length,
 UniformGlobalDiagonalReturn.program_length,Nat.add_assoc,show 647+18=665 by rfl,show 665+147=812 by rfl] using
  UniformGlobalMovementAssembly.halt_at (UniformInitializedKernelExecution.programFor child W)
   (headerProgram W) (UniformGlobalDiagonalReturn.programFor W)
end
end ExactFourierCircuits.UniformGlobalKernelDiagonalAssembly
