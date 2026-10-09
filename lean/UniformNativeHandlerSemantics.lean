import UniformNativeDirectionMetadata
import UniformNativeScheduleSemantics
import UniformRecursiveNativeRecords
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeHandlerSemantics
open OAI.ExactFourier UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformNativeRecordRoles UniformNativeScalarAlgebra
open UniformFixedCoefficientCodec
open scoped BigOperators
noncomputable section

abbrev roleMap := paddingRole (TripleSchedule.Global.size ExplicitSeedBudget.h)
 ExplicitSeedBudget.roleBits MasterBudget.seed_actual_padding

def actualPairs : List (UniformNativeExchangeRecordMachine.Pair W) :=
 UniformNativeTerminalExchange.pairs
  ((TripleSchedule.Global.coordinates ExplicitSeedBudget.h).toEmbedding.trans roleMap)
  Finset.univ.toList

def actualDirections : List (UniformNativeYRecordMachine.Direction W m) :=
 UniformNativeTerminalY.directions
  ((TripleSchedule.Global.coordinates ExplicitSeedBudget.h).toEmbedding.trans roleMap)
  TripleInvocationFrames.bankDirection Finset.univ.toList

/-- Exact complex values of every native role array; Scalar tags remain in Present. -/
def arrayValues (q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 Fin (W*2^(q*m+rest))→ℂ :=
 RoleWords.arrayValues (q*m+rest) (fun i z=>(f i z).value)

def SemanticPresent (A q rest : ℕ) (i : UniformNativeScheduleSemantics.Instruction)
 (f : Fin W→Fin (2^(q*m+rest))→Scalar) (u : State) : Prop :=
 ∃g,UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest)) g u ∧
  arrayValues q rest g=(semantic q rest i).mulVec (arrayValues q rest f)

theorem exchange_values (q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 (semantic q rest .exchange).mulVec (arrayValues q rest f)=
 arrayValues q rest (UniformNativeExchangeRecordMachine.actions actualPairs f) := by
 exact UniformNativeTerminalExchange.native_active_exchange_values
  (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
  (q*m) rest MasterBudget.seed_actual_padding f

theorem translation_values (q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 (semantic q rest .translation).mulVec (arrayValues q rest f)=
 arrayValues q rest (UniformNativeYRecordMachine.actions q m (q*m+rest) actualDirections f) := by
 exact UniformNativeTerminalY.native_active_translation_values
  (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
  q m rest MasterBudget.seed_actual_padding TripleInvocationFrames.bankDirection f

theorem scalar_values (q rest : ℕ) (a : Invocation)
 (d s : Fin (fixedBlock a).width) (ne:d≠s) (c : Fin 5) (hc:decode c≠0)
 (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 (semantic q rest (.macro a (.shear d s ne c hc))).mulVec (arrayValues q rest f)=
 arrayValues q rest (UniformFixedNetworkShearChildMachine.shearValues
  (roleMap ((fixedBlock a).embedding d)) (roleMap ((fixedBlock a).embedding s)) (decode c) f) := by
 exact native_active_shear_values ExplicitSeedBudget.roleBits (q*m) rest
  MasterBudget.seed_actual_padding (fixedBlock a).embedding d s ne (decode c) hc f

theorem initial_values (q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 (semantic q rest .initial).mulVec (arrayValues q rest f)=arrayValues q rest f := by
 simp [semantic,Instruction.word,wordMatrix,UniformNativeScheduleMatrix.nativeMatrix_one,
  UniformNativeScheduleMatrix.spectatorLift_one]

theorem boundary_values (q rest : ℕ) (a : Invocation)
 (f : Fin W→Fin (2^(q*m+rest))→Scalar) :
 (semantic q rest (.boundary a)).mulVec (arrayValues q rest f)=arrayValues q rest f := by
 simp [semantic,Instruction.word,wordMatrix,UniformNativeScheduleMatrix.nativeMatrix_one,
  UniformNativeScheduleMatrix.spectatorLift_one]

theorem exchange_present (A q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) (u : State)
 (out:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest))
  (UniformNativeExchangeRecordMachine.actions actualPairs f) u) :
 SemanticPresent A q rest .exchange f u :=
 ⟨_,out,(exchange_values q rest f).symm⟩

theorem translation_present (A q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar) (u : State)
 (out:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest))
  (UniformNativeYRecordMachine.actions q m (q*m+rest) actualDirections f) u) :
 SemanticPresent A q rest .translation f u :=
 ⟨_,out,(translation_values q rest f).symm⟩

theorem scalar_present (A q rest : ℕ) (a : Invocation)
 (d s : Fin (fixedBlock a).width) (ne:d≠s) (c : Fin 5) (hc:decode c≠0)
 (f : Fin W→Fin (2^(q*m+rest))→Scalar) (u : State)
 (out:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest))
  (UniformFixedNetworkShearChildMachine.shearValues (roleMap ((fixedBlock a).embedding d))
   (roleMap ((fixedBlock a).embedding s)) (decode c) f) u) :
 SemanticPresent A q rest (.macro a (.shear d s ne c hc)) f u :=
 ⟨_,out,(scalar_values q rest a d s ne c hc f).symm⟩

/-- Consume the actual marker handler's two frames; no numerical action premise. -/
theorem initial_present (A q rest : ℕ) (f : Fin W→Fin (2^(q*m+rest))→Scalar)
 (s t u : State) (data:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest)) f s)
 (control:UniformRecursiveRecordControl.ControlFrame s t)
 (frame:UniformFixedNetworkOpcodeMachine.Frame t u) : SemanticPresent A q rest .initial f u := by
 refine ⟨f,?_,(initial_values q rest f).symm⟩
 intro i z
 rw [frame.scalarHeap,control.scalarHeap]
 exact data i z

theorem boundary_present (A q rest : ℕ) (a : Invocation)
 (f : Fin W→Fin (2^(q*m+rest))→Scalar) (s t u : State)
 (data:UniformFixedNetworkShearChildMachine.Present A W (2^(q*m+rest)) f s)
 (control:UniformRecursiveRecordControl.ControlFrame s t)
 (frame:UniformFixedNetworkOpcodeMachine.Frame t u) : SemanticPresent A q rest (.boundary a) f u := by
 refine ⟨f,?_,(boundary_values q rest a f).symm⟩
 intro i z
 rw [frame.scalarHeap,control.scalarHeap]
 exact data i z

theorem scalar_record (q : ℕ) (a : Invocation)
 (d s : Fin (fixedBlock a).width) (ne:d≠s) (c : Fin 5) (hc:decode c≠0) :
 UniformNativeScalarRecordMachine.shearRecord q seedWidth
  (roleMap ((fixedBlock a).embedding d)) (roleMap ((fixedBlock a).embedding s)) c=
 UniformNativeScheduleSemantics.Instruction.record q (.macro a (.shear d s ne c hc)) := by
 simp only [UniformNativeScalarRecordMachine.shearRecord,UniformNativeScheduleSemantics.Instruction.record,
  macroRecord,roleMap,paddingRole_value]

theorem exchange_record (q : ℕ) :
 UniformNativeExchangeRecordMachine.record q seedWidth actualPairs=
 UniformNativeScheduleSemantics.Instruction.record q .exchange := by
 exact UniformNativeDirectionMetadata.exchange_record_model
  (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits q seedWidth
  MasterBudget.seed_actual_padding Finset.univ.toList

theorem translation_record (q : ℕ) :
 UniformNativeYRecordMachine.record q seedWidth actualDirections=
 UniformNativeScheduleSemantics.Instruction.record q .translation := by
 exact UniformNativeDirectionMetadata.translation_record_model
  (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits q m
  MasterBudget.seed_actual_padding TripleInvocationFrames.bankDirection Finset.univ.toList

end
end ExactFourierCircuits.UniformNativeHandlerSemantics
