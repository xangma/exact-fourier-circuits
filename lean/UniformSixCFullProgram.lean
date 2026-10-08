import UniformSixCTraversal
import UniformSixCBroadcast
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCFullProgram
open UniformMachine UniformAssembly

def initial : Program := [.natLiteral 1061 1]
def preparedTrue : Program := initial ++ UniformCrossHeightPreparationMachine.program.map (relocate 1 187)
def forwardOne : Program := preparedTrue ++ (UniformSixCDepthColorController.traversalProgram false).map (relocate 187 998)
def broadcastOne : Program := forwardOne ++ (UniformSixCBroadcast.program true).map (relocate 998 1752)
def inverseOne : Program := broadcastOne ++ (UniformSixCDepthColorController.traversalProgram true).map (relocate 1752 2687)
def toggleFalse : Program := inverseOne ++ [.natLiteral 1061 0]
def preparedFalse : Program := toggleFalse ++ UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874)
def forwardTwo : Program := preparedFalse ++ (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685)
def broadcastTwo : Program := forwardTwo ++ (UniformSixCBroadcast.program false).map (relocate 3685 4439)
def inverseTwo : Program := broadcastTwo ++ (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374)
/-- A literal full six-phase driver. Every preparation, cursor and return is
an actual instruction. This definition alone is not a full execution theorem. -/
def program : Program := inverseTwo ++ [.halt]
lemma initial_length : initial.length=1:=rfl
lemma preparedTrue_length : preparedTrue.length=187:=by simp [preparedTrue,initial_length,UniformCrossHeightPreparationMachine.program_length]
lemma forwardOne_length : forwardOne.length=998:=by simp [forwardOne,preparedTrue_length,UniformSixCDepthColorController.traversalProgram_length]
lemma broadcastOne_length : broadcastOne.length=1752:=by simp [broadcastOne,forwardOne_length,UniformSixCBroadcast.program_length]
lemma inverseOne_length : inverseOne.length=2687:=by simp [inverseOne,broadcastOne_length,UniformSixCDepthColorController.traversalProgram_length]
lemma toggleFalse_length : toggleFalse.length=2688:=by simp [toggleFalse,inverseOne_length]
lemma preparedFalse_length : preparedFalse.length=2874:=by simp [preparedFalse,toggleFalse_length,UniformCrossHeightPreparationMachine.program_length]
lemma forwardTwo_length : forwardTwo.length=3685:=by simp [forwardTwo,preparedFalse_length,UniformSixCDepthColorController.traversalProgram_length]
lemma broadcastTwo_length : broadcastTwo.length=4439:=by simp [broadcastTwo,forwardTwo_length,UniformSixCBroadcast.program_length]
lemma inverseTwo_length : inverseTwo.length=5374:=by simp [inverseTwo,broadcastTwo_length,UniformSixCDepthColorController.traversalProgram_length]
lemma program_length : program.length=5375:=by simp [program,inverseTwo_length]
lemma true_at : program[0]?=some (.natLiteral 1061 1):=rfl
lemma false_at : program[2687]?=some (.natLiteral 1061 0):=by
 have eqn:program=inverseOne ++ [.natLiteral 1061 0] ++
  (UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++
  (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]):=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,toggleFalse,List.append_assoc]
 rw [eqn,List.append_assoc,List.getElem?_append,ite_eq_right (by rw [inverseOne_length];omega),inverseOne_length]
 simp
lemma halt_at : program[5374]?=some .halt:=by
 unfold program
 rw [List.getElem?_append,ite_eq_right (by rw [inverseTwo_length];omega),inverseTwo_length];rfl
lemma heightTrue_code : CodeAt UniformCrossHeightPreparationMachine.program program 1 187:=by
 let tail:=(UniformSixCDepthColorController.traversalProgram false).map (relocate 187 998) ++
  (UniformSixCBroadcast.program true).map (relocate 998 1752) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 1752 2687) ++ [.natLiteral 1061 0] ++
  UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++
  (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=initial ++ UniformCrossHeightPreparationMachine.program.map (relocate 1 187) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,toggleFalse,inverseOne,broadcastOne,forwardOne,preparedTrue,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code initial tail _ 1 187 initial_length
lemma forwardOne_code : CodeAt (UniformSixCDepthColorController.traversalProgram false) program 187 998:=by
 let tail:=(UniformSixCBroadcast.program true).map (relocate 998 1752) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 1752 2687) ++ [.natLiteral 1061 0] ++
  UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++
  (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=preparedTrue ++ (UniformSixCDepthColorController.traversalProgram false).map (relocate 187 998) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,toggleFalse,inverseOne,broadcastOne,forwardOne,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code preparedTrue tail _ 187 998 preparedTrue_length
lemma broadcastOne_code : CodeAt (UniformSixCBroadcast.program true) program 998 1752:=by
 let tail:=(UniformSixCDepthColorController.traversalProgram true).map (relocate 1752 2687) ++ [.natLiteral 1061 0] ++
  UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++
  (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=forwardOne ++ (UniformSixCBroadcast.program true).map (relocate 998 1752) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,toggleFalse,inverseOne,broadcastOne,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code forwardOne tail _ 998 1752 forwardOne_length
lemma inverseOne_code : CodeAt (UniformSixCDepthColorController.traversalProgram true) program 1752 2687:=by
 let tail:=[.natLiteral 1061 0] ++ UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++
  (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=broadcastOne ++ (UniformSixCDepthColorController.traversalProgram true).map (relocate 1752 2687) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,toggleFalse,inverseOne,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code broadcastOne tail _ 1752 2687 broadcastOne_length
lemma heightFalse_code : CodeAt UniformCrossHeightPreparationMachine.program program 2688 2874:=by
 let tail:=(UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++
  (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=toggleFalse ++ UniformCrossHeightPreparationMachine.program.map (relocate 2688 2874) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,preparedFalse,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code toggleFalse tail _ 2688 2874 toggleFalse_length
lemma forwardTwo_code : CodeAt (UniformSixCDepthColorController.traversalProgram false) program 2874 3685:=by
 let tail:=(UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  (UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]
 have eqn:program=preparedFalse ++ (UniformSixCDepthColorController.traversalProgram false).map (relocate 2874 3685) ++ tail:=by
  simp [program,inverseTwo,broadcastTwo,forwardTwo,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code preparedFalse tail _ 2874 3685 preparedFalse_length
lemma broadcastTwo_code : CodeAt (UniformSixCBroadcast.program false) program 3685 4439:=by
 have eqn:program=forwardTwo ++ (UniformSixCBroadcast.program false).map (relocate 3685 4439) ++
  ((UniformSixCDepthColorController.traversalProgram true).map (relocate 4439 5374) ++ [.halt]):=by
  simp [program,inverseTwo,broadcastTwo,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code forwardTwo _ _ 3685 4439 forwardTwo_length
lemma inverseTwo_code : CodeAt (UniformSixCDepthColorController.traversalProgram true) program 4439 5374:=
 UniformChunkRowTableMachine.segment_code broadcastTwo [.halt] _ 4439 5374 broadcastTwo_length

/-- The depth/color order used by the actual division/remainder cursor. This
is a pure description of emitted ordinals, not an input traversal table. -/
def layerOrdinals (backwards:Bool) (K:ℕ) : List (ℕ×ℕ) :=
 (List.range ((8*K+7)*11)).map (fun i=>
  (UniformSixCTraversal.layerDepth backwards ((8*K+7)*11) i,
   UniformSixCTraversal.layerColor backwards ((8*K+7)*11) i))
lemma layerOrdinals_length (backwards:Bool) (K:ℕ) : (layerOrdinals backwards K).length=(8*K+7)*11:=by simp [layerOrdinals]
lemma layerOrdinals_mem (backwards:Bool) (K:ℕ) (d c:ℕ) :
 (d,c)∈layerOrdinals backwards K → d<8*K+7 ∧ c<11:=by
 intro h
 obtain ⟨i,hi,eq⟩:=List.mem_map.mp h
 have bounds: i<(8*K+7)*11:=List.mem_range.mp hi
 have e1:=congrArg Prod.fst eq
 have e2:=congrArg Prod.snd eq
 dsimp only at e1 e2
 rw [←e1,←e2]
 exact ⟨UniformSixCTraversal.depth_bound backwards _ i bounds,UniformSixCTraversal.color_bound backwards _ i⟩
end ExactFourierCircuits.UniformSixCFullProgram
