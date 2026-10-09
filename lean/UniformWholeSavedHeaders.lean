import UniformSixCCorrectedReplay
set_option autoImplicit false
namespace ExactFourierCircuits.UniformWholeSavedHeaders
open UniformMachine UniformAssembly
/-- A purely syntactic footprint for the seven saved startup registers. -/
def writesSaved : Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => [100,101,102,103,104,105,106].contains d
 | _ => false
lemma relocate_saved (b r : ℕ) (i : Instruction) : writesSaved (relocate b r i)=writesSaved i := by
 cases i <;> rfl
lemma chunk_saved : UniformChunkMatchingPreparation.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformChunkMatchingPreparation.program,UniformChunkMatchingPreparation.beforeAxis,
  UniformChunkMatchingPreparation.beforeRow,UniformChunkMatchingPreparation.beforeColor,
  List.all_append,List.all_map,Function.comp_def,relocate_saved]
 decide
lemma sector_saved : UniformSectorPackingMachine.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformSectorPackingMachine.program,List.all_flatten,List.all_cons,List.all_nil,Bool.and_true]
 decide
lemma packing_saved : UniformMatchingPackingPreparation.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformMatchingPackingPreparation.program,UniformMatchingPackingPreparation.beforePacking,
  List.all_append,List.all_map,Function.comp_def,relocate_saved,chunk_saved,sector_saved,Bool.true_and,Bool.and_true]
 decide
lemma phase_saved (p : UniformZeroFreePairShearMachine.Phase) : p.code.all (fun i=>!writesSaved i)=true := by
 cases p with
 | hadamard=>decide
 | diagonal c d=>
   cases c <;> cases d <;> simp [UniformZeroFreePairShearMachine.Phase.code,
    UniformZeroFreePairShearMachine.Coefficient.code,UniformPairDiagonalMachine.program,relocate,writesSaved]
lemma emit_saved (ps:List UniformZeroFreePairShearMachine.Phase) (base:ℕ) :
 (UniformZeroFreePairShearMachine.emit base ps).all (fun i=>!writesSaved i)=true := by
 induction ps generalizing base with
 | nil=>rfl
 | cons p ps ih=>
   simp only [UniformZeroFreePairShearMachine.emit,List.all_append,List.all_map,
    Function.comp_def,relocate_saved,phase_saved,ih,Bool.true_and]
lemma pair_saved : UniformZeroFreePairShearMachine.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformZeroFreePairShearMachine.program,List.all_append,emit_saved,Bool.and_true]
 decide
lemma matching_saved : UniformPackedMatchingShearMachine.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformPackedMatchingShearMachine.program,UniformPackedMatchingShearMachine.beforeScatter,
  UniformPackedMatchingShearMachine.beforePair,UniformPackedMatchingShearMachine.beforeRow,
  List.all_append,List.all_map,Function.comp_def,relocate_saved,pair_saved,Bool.and_true]
 decide
lemma inverse_saved : UniformSixCInverseMatchingPreparation.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformSixCInverseMatchingPreparation.program,UniformSixCInverseMatchingPreparation.beforeMatching,
  UniformSixCInverseMatchingPreparation.beforePacking,UniformSixCInverseMatchingPreparation.beforeAxis,
  List.all_append,List.all_map,Function.comp_def,relocate_saved,matching_saved,sector_saved,Bool.and_true]
 decide
lemma body_saved (backwards : Bool) :
 (UniformSixCDepthColorController.traversalBody backwards).all (fun i=>!writesSaved i)=true := by
 cases backwards with
 | false =>
   simp only [UniformSixCDepthColorController.traversalBody,Bool.false_eq_true,ite_false,
    UniformSixCDepthColorController.forwardProgram,List.all_append,List.all_map,
    Function.comp_def,relocate_saved,packing_saved,matching_saved,Bool.true_and,Bool.and_true]
   decide
 | true =>
   simp only [UniformSixCDepthColorController.traversalBody,ite_true,
    UniformSixCDepthColorController.inverseProgram,List.all_append,List.all_map,
    Function.comp_def,relocate_saved,inverse_saved,Bool.and_true]
   decide
lemma traversal_saved (backwards : Bool) :
 (UniformSixCDepthColorController.traversalProgram backwards).all (fun i=>!writesSaved i)=true := by
 simp only [UniformSixCDepthColorController.traversalProgram,List.all_append,List.all_map,
  Function.comp_def,relocate_saved,body_saved,Bool.and_true]
 cases backwards <;> decide
lemma broadcast_saved (positive : Bool) :
 (UniformSixCBroadcast.program positive).all (fun i=>!writesSaved i)=true := by
 simp only [UniformSixCBroadcast.program,UniformSixCBroadcast.beforeInverse,
  UniformSixCBroadcast.beforeBroadcast,List.all_append,List.all_map,Function.comp_def,
  relocate_saved,inverse_saved,Bool.and_true]
 cases positive <;> decide
lemma whole_saved : UniformSixCFullProgram.program.all (fun i=>!writesSaved i)=true := by
 simp only [UniformSixCFullProgram.program,UniformSixCFullProgram.inverseTwo,
  UniformSixCFullProgram.broadcastTwo,UniformSixCFullProgram.forwardTwo,
  UniformSixCFullProgram.preparedFalse,UniformSixCFullProgram.toggleFalse,
  UniformSixCFullProgram.inverseOne,UniformSixCFullProgram.broadcastOne,
  UniformSixCFullProgram.forwardOne,UniformSixCFullProgram.preparedTrue,
  List.all_append,List.all_map,Function.comp_def,relocate_saved,traversal_saved,
  broadcast_saved,Bool.and_true]
 decide
lemma saved_mem (j:ℕ) (lo:100≤j) (hi:j≤106) :
 ([100,101,102,103,104,105,106]:List ℕ).contains j=true := by
 interval_cases j <;> rfl
lemma whole_keeps (j : ℕ) (lo:100≤j) (hi:j≤106) :
 ∀i∈UniformSixCFullProgram.program,UniformNewtonTableMachine.KeepsNat j i := by
 intro i mem
 have h:=List.all_eq_true.mp whole_saved i mem
 cases i <;> simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals intro eq
 all_goals subst_vars
 all_goals simp [writesSaved] at h
 all_goals omega
/-- Applies to every actual execution of the literal5375 program, including
its corrected-cross theorem. No retention certificate is supplied. -/
theorem execution_saved {B n t : ℕ} {x : Fin n → ℂ} {s u : State}
 (run:BoundedExecution UniformSixCFullProgram.program n x B s t u) :
 ∀j,100≤j→j≤106→u.natReg j=s.natReg j := by
 intro j lo hi
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (whole_keeps j lo hi)
end ExactFourierCircuits.UniformWholeSavedHeaders
