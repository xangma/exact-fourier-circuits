import UniformFinalClockEntries
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleStorageAlpha
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformAxisCachePreparationRetention UniformFinalRoleExecution UniformFinalRoleAlpha
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
/-- The actual18 AP gather replaces only role0 after the data loader. -/
theorem execution_with_storage {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (s:State)
 (core:Core n x s) (args:H.Args c n W false s)
 (source:s.natReg 6026=2*UniformJointAllocation.slab c n)
 (tableAddress:s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n)
 (table:UniformGlobalNatPreparation.PermutationBank (V n) (UniformKernelSpectrumStorage.alphaBase c n) s.natHeap AP)
 (old:∀i:Fin W,∀j:Fin (V n),s.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (values x false AP i.val j))
 (pc:s.pc=0) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 BoundedExecution C.alphaProgram n x (UniformJointAllocation.envelope c n) s (9*V n+10) u∧u.pc=17∧
 (∀i:Fin W,∀j:Fin (V n),u.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (physical x AP i.val j))∧
 UniformFinalRoleExecution.Frame n s u∧u.natReg 7300=UniformKernelSpectrumStorage.base c n:=by
 obtain ⟨_,code,extent,_,kernelBefore,tableFit,_⟩:=UniformFinalRoleGeometry.geometry hn
 have oneRole:V n≤W*V n:=by
  have h:1≤W:=by have:=UniformFinalRoleGeometry.roles_two;omega
  simpa only[Nat.one_mul] using Nat.mul_le_mul_right (V n) h
 have inputBefore:UniformPaddedInputPreparation.dataBase n+V n≤2*UniformJointAllocation.slab c n:=by
  unfold UniformChirpKernelPreparation.kernelBase at kernelBefore
  omega
 obtain ⟨u,run,up,gathered,_kept,out,h⟩:=UniformPhysicalCRTConsumerMachine.alpha_execution n
  (UniformJointAllocation.envelope c n) (V n) (UniformPaddedInputPreparation.dataBase n)
  (2*UniformJointAllocation.slab c n) (UniformKernelSpectrumStorage.alphaBase c n) x (standard x) AP s pc
  core.metadata.saved.workingLength args.padded source tableAddress
  (fun j=>core.operands.input j.val j.isLt) table (Or.inl inputBefore)
  (by omega) (by omega) tableFit (by omega) wb
 exact ⟨u,run,up,cells x AP s u old gathered out,frame s u out h,(h.natReg 7300 (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans args.storage⟩
end
end ExactFourierCircuits.UniformFinalRoleStorageAlpha
