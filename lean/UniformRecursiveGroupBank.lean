import UniformRecursiveGroupLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveGroupBank
open UniformMachine UniformBinaryTensorCoordinates
namespace L
export UniformRecursiveGroupLoop (Bank)
end L
abbrev W:=UniformRecursiveSelfCallMachine.W
noncomputable section

/-- The exact complete-batch partition, including empty generic dimensions. -/
def flatten (groups b T V:ℕ) (partition:groups*(b*T)=V):
 (Fin groups×(Fin b×Fin T))≃Fin V:=
 ((Equiv.prodCongr (Equiv.refl (Fin groups)) (finProdFinEquiv:Fin b×Fin T≃Fin (b*T))).trans
  (finProdFinEquiv:Fin groups×Fin (b*T)≃Fin (groups*(b*T)))).trans (finCongr partition)
lemma flatten_value(groups b T V:ℕ)(partition:groups*(b*T)=V)
 (g:Fin groups)(j:Fin b)(t:Fin T):
 (flatten groups b T V partition (g,(j,t))).val=g.val*(b*T)+j.val*T+t.val:=by
 simp [flatten,finProdFinEquiv,Nat.mul_comm,Nat.add_assoc,Nat.add_comm]

/-- Read the actual resulting Scalar, retaining its dependency flag. -/
def array (D V:ℕ)(s:State)(j:Fin V):Scalar:=(s.scalarHeap (D+j.val)).getD Scalar.zero
lemma array_present {D V:ℕ}{s:State}(present:∀j:Fin V,(s.scalarHeap (D+j.val)).isSome=true):
 ∀j:Fin V,s.scalarHeap (D+j.val)=some (array D V s j):=by
 intro j
 have h:=present j
 cases e:s.scalarHeap (D+j.val) with
 | none=>simp only [e,Option.isSome_none,Bool.false_eq_true] at h
 | some z=>simp [array,e]

lemma complete_present {q groups D V:ℕ}{input:Fin groups→Fin W→Fin (2^q)→Scalar}{s:State}
 (partition:groups*(W*2^q)=V)(bank:L.Bank q groups D groups input s):
 ∀j:Fin V,(s.scalarHeap (D+j.val)).isSome=true:=by
 intro j
 obtain ⟨⟨g,⟨i,t⟩⟩,eq⟩:=(flatten groups W (2^q) V partition).surjective j
 rw [←eq,flatten_value]
 simpa only [Nat.add_assoc] using bank.present g g.isLt i t

lemma complete_array {q groups D V:ℕ}{input:Fin groups→Fin W→Fin (2^q)→Scalar}{s:State}
 (partition:groups*(W*2^q)=V)(bank:L.Bank q groups D groups input s):
 ∀j:Fin V,s.scalarHeap (D+j.val)=some (array D V s j):=
 array_present (complete_present partition bank)

/-- The physically read complete array equals the recursive tensor action
on each true batch fiber; there is no action premise for a returned bank. -/
lemma complete_values {q groups D V:ℕ}{input:Fin groups→Fin W→Fin (2^q)→Scalar}{s:State}
 (partition:groups*(W*2^q)=V)(bank:L.Bank q groups D groups input s)
 (g:Fin groups)(i:Fin W)(t:Fin (2^q)):
 (array D V s (flatten groups W (2^q) V partition (g,(i,t)))).value=
 (physicalMatrix q).mulVec (fun z=>(input g i z).value) t:=by
 have h:=bank.values g g.isLt i t
 have read:=complete_array partition bank (flatten groups W (2^q) V partition (g,(i,t)))
 rw [flatten_value] at read
 simp only [Nat.add_assoc] at h read
 rw [read,Option.map_some] at h
 exact Option.some.inj h

end
end ExactFourierCircuits.UniformRecursiveGroupBank
