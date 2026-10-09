import UniformFinalNumericJoin

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDataClockProduct
open UniformMachine UniformFinalNumericJoin
noncomputable section

lemma prepared_cell_value {L Q:ℕ}(s:State)(y:Fin L→ℂ)
 (saved:∀j:Fin L,s.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j)))
 (j:Fin L):(scalars L Q s j).value=y j:=by
 unfold scalars
 rw[saved j]
 rfl

lemma zero_role_product {L A Q:ℕ}(s:State)(y:Fin L→ℂ)
 (saved:∀j:Fin L,s.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))):
 (fun j=>(scalars L (A+0*L) s j).value*y j)=
 (fun j=>(scalars L A s j).value*(scalars L Q s j).value):=by
 rw[Nat.zero_mul,Nat.add_zero]
 funext j
 exact congrArg (fun z:ℂ=>(scalars L A s j).value*z) (prepared_cell_value s y saved j).symm

lemma zero_role_transform {L A:ℕ}(AP BP:Fin L≃Fin L)(s u:State)
 (h:HeapTransform AP BP (A+0*L) (A+0*L) s u):HeapTransform AP BP A A s u:=by
 simpa only[Nat.zero_mul,Nat.add_zero] using h

end
end ExactFourierCircuits.UniformFinalDataClockProduct
