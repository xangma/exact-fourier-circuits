import UniformDirectLeafCacheLoopComplete
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheProducedSource
open UniformMachine UniformTensorMonomialMachine UniformTransposeDescriptorMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheLoopBoot UniformDirectLeafCacheLoopChoice
noncomputable section

def records (v o K flip:ℕ):List Record:=
 if flip=0 then leafRecords v o K else (leafRecords v o K).reverse.map Record.transpose
lemma records_length (v o K flip:ℕ):(records v o K flip).length=size v:=by
 by_cases f:flip=0 <;>simp[records,f,leafRecords_length,size]
lemma records_valid (v o K flip r:ℕ) (extent:o+v≤r) :
 ∀q∈records v o K flip,UniformDirectLeafCacheSource.InRange r K q ∧UniformDirectLeafCacheSource.Legal q:=by
 intro q member
 by_cases f:flip=0
 · simp only[records,f,ite_true] at member
   exact UniformDirectLeafCacheChronology.leaf_valid v o K r extent q member
 · simp only[records,f,ite_false] at member
   obtain ⟨p,hp,rfl⟩:=List.mem_map.mp member
   have good:=UniformDirectLeafCacheChronology.leaf_valid v o K r extent p (List.mem_reverse.mp hp)
   exact UniformDirectLeafCacheChronology.transpose_valid r K p good.1 good.2

lemma records_at {v o K flip D E:ℕ} {s:State}
 (forward:UniformFixedNetworkScheduleMachine.Printed D (UniformDirectLeafDescriptorMachine.rows o K v) s)
 (transpose:UniformFixedNetworkScheduleMachine.Printed E
  (reverseWords (recordAt (leafRecords v o K)) (leafRecords v o K).length) s):
 ∀(i:ℕ)(hi:i<(records v o K flip).length),UniformDirectLeafCacheSource.At
  (bank flip D E+4*i) (records v o K flip)[i] s:=by
 intro i hi
 by_cases f:flip=0
 · simp only[records,f,ite_true] at hi⊢
   have b:=bank_of_printed D (leafRecords v o K) s (by rw[leafRecords_words];exact forward)
   simp only[UniformDirectLeafCacheSource.At,bank,ite_true]
   intro j
   have row:=b i hi j
   have eq:recordAt (leafRecords v o K) i=(leafRecords v o K)[i]:=by
    simp only [recordAt,List.getElem?_eq_getElem hi,Option.getD_some]
   rw[eq] at row
   exact row
 · simp only[records,f,ite_false] at hi⊢
   have b:=bank_of_printed E ((leafRecords v o K).reverse.map Record.transpose) s
    (by rw[←reverseWords_records];exact transpose)
   simp only[UniformDirectLeafCacheSource.At,bank,f,ite_false]
   intro j
   have row:=b i hi j
   have eq:recordAt ((leafRecords v o K).reverse.map Record.transpose) i=
    ((leafRecords v o K).reverse.map Record.transpose)[i]:=by
    simp only [recordAt,List.getElem?_eq_getElem hi,Option.getD_some]
   rw[eq] at row
   exact row
end
end ExactFourierCircuits.UniformDirectLeafCacheProducedSource
