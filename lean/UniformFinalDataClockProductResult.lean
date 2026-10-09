import UniformActualCompleteClockResult
import UniformFinalClockEntries
import UniformFinalClockOuterRuntime
import UniformFinalPreparedCellValue

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDataClockProduct
open UniformMachine UniformFinalNumericJoin UniformSelectedPhysicalCRT UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
attribute [local irreducible] Nat.add Nat.mul UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program
abbrev volume(n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev budget(n:ℕ):ℕ:=UniformJointAllocation.envelope c n
abbrev sourceBase:=UniformActualClockEntry.sourceBase
abbrev savedBase:=UniformFinalMovementFrame.Q
abbrev targetBase:=UniformFinalMovementGeometry.T

def product {n:ℕ}(s:State)(j:Fin (volume n)):ℂ:=
 (scalars (volume n) (sourceBase n) s j).value*
 (scalars (volume n) (savedBase n) s j).value

def thirdValues {n:ℕ}(s:State)(y:Fin (volume n)→ℂ):ℕ→Fin (volume n)→Scalar:=
 UniformFinalCRTRoleSource.values
  (UniformRolePointwiseMachine.multiplied (UniformFinalClockHeapTransform.actualValues n s) y)
  (physicalAlpha n) (physicalBeta n)

structure Result {n:ℕ}(hn:0<n)(x:Fin n→ℂ)(y:Fin (volume n)→ℂ)
 (s dataOut productOut thirdIn:State):Prop where
 transform:HeapTransform (physicalAlpha n) (physicalBeta n) (sourceBase n) (sourceBase n) s dataOut
 clockSaved:∀j:Fin (volume n),dataOut.scalarHeap (savedBase n+j.val)=s.scalarHeap (savedBase n+j.val)
 numeric:NumericValues (sourceBase n) (product (n:=n) dataOut) productOut
 reindex:∀j:Fin (volume n),thirdIn.scalarHeap (sourceBase n+j.val)=
  productOut.scalarHeap (sourceBase n+((physicalBeta n).symm (physicalAlpha n j)).val)
 standard:∀j:Fin (volume n),thirdIn.scalarHeap (targetBase n+j.val)=
  productOut.scalarHeap (sourceBase n+((physicalBeta n).symm j).val)
 thirdNumeric:NumericValues (sourceBase n)
  (fun j=>product (n:=n) dataOut ((physicalBeta n).symm (physicalAlpha n j))) thirdIn
 source:UniformActualClockEntry.Source n (thirdValues (n:=n) dataOut y) thirdIn
 entry:UniformFinalClockEntries.Entry hn x (thirdValues (n:=n) dataOut y) (UniformTensorMonomialMachine.setPC thirdIn 0)
 table:UniformFinalPhysicalTablePrefix.Result n x (UniformTensorMonomialMachine.setPC thirdIn 0)
 cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) thirdIn
 runtime:UniformFinalClockRuntime.Runtime n thirdIn
 saved:∀j:Fin (volume n),thirdIn.scalarHeap (savedBase n+j.val)=some (UniformPairMachine.prepared (y j))
 thirdSaved:∀j:Fin (volume n),thirdIn.scalarHeap (savedBase n+j.val)=dataOut.scalarHeap (savedBase n+j.val)
 frame:UniformFinalClockOuterRetention.Frame n s thirdIn
 movement:UniformFinalMovementFrame.Frame n dataOut thirdIn
 pc:thirdIn.pc=33

lemma product_eq {n:ℕ}(s:State)(y:Fin (volume n)→ℂ)
 (saved:∀j:Fin (volume n),s.scalarHeap (savedBase n+j.val)=some (UniformPairMachine.prepared (y j))):
 (fun j=>(UniformFinalClockHeapTransform.actualValues n s 0 j).value*y j)=product (n:=n) s:=by
 exact zero_role_product s y saved

end
end ExactFourierCircuits.UniformFinalDataClockProduct
