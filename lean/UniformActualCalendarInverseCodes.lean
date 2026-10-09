import UniformActualCalendarForwardCodes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarInverseCodes
open UniformReplayPrint
namespace F
abbrev Config := UniformForwardMatchingFactorPreparation.Config
abbrev Layout := UniformForwardMatchingFactorPreparation.Layout
end F
open UniformInverseMatchingFactorPreparation
noncomputable section
variable {B : ℕ} (c : F.Config) (l : F.Layout c B)
 (ha : c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he : c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)→ℂ)

def negateValue (x : Nat × (Nat × Complex)) : Nat × (Nat × Complex) :=
 (x.1,x.2.1,-x.2.2)

def occurrences : List (Nat × (Nat × Complex)) :=
 List.ofFn (fun i:Fin (rows c l ha he).length=>
  (((rows c l ha he).get i).dst,((rows c l ha he).get i).src,selectedValue c l ha he bank i))

/-- The actual inverse printer reverses the same endpoint occurrences and
negates the real selected coefficient at each occurrence. -/
theorem occurrences_reverse :
 occurrences c l ha he bank=
 (UniformActualCalendarForwardCodes.occurrences c l ha he bank).reverse.map negateValue:=by
 apply List.ext_getElem
 · simp only[occurrences,UniformActualCalendarForwardCodes.occurrences,List.length_ofFn,
    List.length_map,List.length_reverse,rows_length]
 · intro i left right
   have hi:i<(rows c l ha he).length:=by simpa only[occurrences,List.length_ofFn] using left
   have ep:=endpoints c l ha he ⟨i,hi⟩
   simp only[occurrences,List.getElem_ofFn,List.getElem_map,
    UniformActualCalendarForwardCodes.occurrences,List.getElem_reverse,List.length_ofFn,
    List.getElem_ofFn,negateValue,List.get_eq_getElem]
   apply Prod.ext
   · simpa only[reverseIndex,Nat.sub_sub,Nat.add_comm] using ep.1
   · apply Prod.ext
     · simpa only[reverseIndex,Nat.sub_sub,Nat.add_comm] using ep.2
     · simp only[selectedValue,UniformInverseMatchingFactorPreparation.reference,reverseIndex,
        UniformForwardMatchingFactorPreparation.selectedValue,Nat.sub_sub,Nat.add_comm]

lemma code_inverse {R : ℕ} (offset : ℕ) (coordinate : ℕ→ℕ)
 (b : Fin R→ℂ) (s : ShearCode ℕ R) :
 (offset+coordinate s.inverse.dst,offset+coordinate s.inverse.src,s.inverse.coefficient.eval b)=
 negateValue (offset+coordinate s.dst,offset+coordinate s.src,s.coefficient.eval b):=by
 simp only[ShearCode.inverse,Coefficient.eval_negate,negateValue]

/-- Exact inverse color word, including repeated or empty occurrences. -/
theorem occurrences_color (bound : c.chunk.color<11) :
 occurrences c l ha he bank=
 (reverseCode (((UniformDAGLayers.colorBlocks
   (UniformChunkMatchingPreparation.crossWord c.chunk ha he) 6)[c.chunk.color]?).getD [])).map
  (fun code=>(c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity code.dst,
   c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity code.src,code.coefficient.eval bank)):=by
 rw[occurrences_reverse,UniformActualCalendarForwardCodes.occurrences_color c l ha he bank bound]
 simp only[reverseCode,List.map_reverse,List.map_map,Function.comp_def]
 apply congrArg List.reverse
 apply List.map_congr_left
 intro s _
 exact (code_inverse c.offset (UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity) bank s).symm

end
end ExactFourierCircuits.UniformActualCalendarInverseCodes
