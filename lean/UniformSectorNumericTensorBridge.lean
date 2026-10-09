import UniformSectorPayloadValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorNumericTensorBridge
open UniformMachine UniformSectorPacking UniformSectorTensor
open UniformSectorPhysicalBinaryAction
open UniformConditionalSectorLoop (Geometry Completed)
open UniformSectorPayloadBridge
open scoped BigOperators
noncomputable section
instance positionsFintype (axes:List Axis) (c:BlockChoices axes):Fintype (Positions axes c):=
 Fintype.ofEquiv (Fin (2^sectorPairCount axes c)) (physicalSector axes c).symm
instance choicesFintype (axes:List Axis):Fintype (BlockChoices axes):=
 Fintype.ofEquiv (Fin (sectorWidths axes).length) (sectorIndexEquiv axes).symm
lemma packed_mulVec (axes:List Axis) (v:Fin (radices axes).prod → ℂ)
 (c:BlockChoices axes) (x:Positions axes c):
 (packedTensor axes).mulVec v (packedEquiv axes ⟨c,x⟩)=
  (sectorMatrix axes c).mulVec (fun y=>v (packedEquiv axes ⟨c,y⟩)) x:=by
 classical
 unfold Matrix.mulVec dotProduct packedTensor
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
 change (∑j,Matrix.blockDiagonal' (sectorMatrix axes) ⟨c,x⟩ ((packedEquiv axes).symm j)*v j)=_
 rw[Fintype.sum_equiv (packedEquiv axes).symm _
  (fun y=>Matrix.blockDiagonal' (sectorMatrix axes) ⟨c,x⟩ y*v (packedEquiv axes y))
  (by intro j;simp only[Equiv.apply_symm_apply])]
 simp only[Fintype.sum_sigma]
 rw[Fintype.sum_eq_single c]
 · simp only[Matrix.blockDiagonal'_apply_eq]
 · intro d ne
   apply Finset.sum_eq_zero
   intro y _
   rw[Matrix.blockDiagonal'_apply_ne _ _ _ ne.symm,zero_mul]
lemma physical_mulVec (axes:List Axis) (c:BlockChoices axes)
 (v:Fin (2^sectorPairCount axes c) → ℂ) (x:Positions axes c):
 (UniformBinaryTensorCoordinates.physicalMatrix (sectorPairCount axes c)).mulVec v (physicalSector axes c x)=
 (sectorMatrix axes c).mulVec (fun y=>v (physicalSector axes c y)) x:=by
 classical
 symm
 unfold Matrix.mulVec dotProduct
 exact Fintype.sum_equiv (physicalSector axes c) _ _ (fun y=>by
  simpa only[sectorMatrix] using congrArg (fun z:ℂ=>z*v (physicalSector axes c y)) (sectorTensor_physical axes c x y))
def choiceIndex (axes:List Axis) (c:BlockChoices axes):Fin (sectorStates axes).length:=
 ⟨(sectorIndexEquiv axes c).val,by simpa only[sectorStates,List.length_ofFn] using (sectorIndexEquiv axes c).isLt⟩
lemma choice_state (axes:List Axis) (c:BlockChoices axes):
 (sectorStates axes)[(choiceIndex axes c).val]'(choiceIndex axes c).isLt=expectedBlockState axes c:=by
 simp only[sectorStates,List.getElem_ofFn]
 change expectedBlockState axes ((sectorIndexEquiv axes).symm (sectorIndexEquiv axes c))=_
 rw[Equiv.symm_apply_apply]
lemma payload_at_coordinate {W B F reserve A E:ℕ} (axes:List Axis)
 (g:Geometry W B F reserve A E (sectorStates axes)) (cover:Cover (sectorStates axes) g.volume)
 (v:ℕ → ℕ → Scalar) (s:State) (done:Completed W A (sectorStates axes) v (sectorStates axes).length s)
 (r:ℕ) (hr:r < W) (c:BlockChoices axes) (x:Positions axes c):
 (payload cover W A s r (packedEquiv axes ⟨c,x⟩).val).value=
 (packedTensor axes).mulVec (fun j=>(v r j.val).value) (packedEquiv axes ⟨c,x⟩):=by
 let i:=choiceIndex axes c
 have values:∀t:Fin (2^((sectorStates axes)[i.val]'i.isLt).pairs),
  (payload cover W A s r (((sectorStates axes)[i.val]'i.isLt).start+t.val)).value=
   (UniformBinaryTensorCoordinates.physicalMatrix ((sectorStates axes)[i.val]'i.isLt).pairs).mulVec
    (fun z=>(v r (((sectorStates axes)[i.val]'i.isLt).start+z.val)).value) t:=
  fun t=>UniformSectorPayloadValues.payload_value_at g cover v s done i.val i.isLt r hr t
 have state:(sectorStates axes)[i.val]'i.isLt=expectedBlockState axes c:=choice_state axes c
 rw[state] at values
 have value:=values (physicalSector axes c x)
 change (payload cover W A s r (sectorStart axes c+(physicalSector axes c x).val)).value=
  (UniformBinaryTensorCoordinates.physicalMatrix (sectorPairCount axes c)).mulVec
   (fun z=>(v r (sectorStart axes c+z.val)).value) (physicalSector axes c x) at value
 have point:sectorStart axes c+(physicalSector axes c x).val=(packedEquiv axes ⟨c,x⟩).val:=by
  rw[physicalSector_value,packedEquiv_value]
 rw[point,physical_mulVec] at value
 rw[packed_mulVec]
 refine value.trans ?_
 congr 1
 funext y
 rw[physicalSector_value,packedEquiv_value]
lemma payload_packed {W B F reserve A E:ℕ} (axes:List Axis)
 (g:Geometry W B F reserve A E (sectorStates axes)) (cover:Cover (sectorStates axes) g.volume)
 (v:ℕ → ℕ → Scalar) (s:State) (done:Completed W A (sectorStates axes) v (sectorStates axes).length s)
 (r:ℕ) (hr:r < W) (j:Fin (radices axes).prod):
 (payload cover W A s r j.val).value=(packedTensor axes).mulVec (fun k=>(v r k.val).value) j:=by
 obtain ⟨⟨c,x⟩,rfl⟩:=(packedEquiv axes).surjective j
 exact payload_at_coordinate axes g cover v s done r hr c x
lemma unpack_mulVec (axes:List Axis) (v:Fin (radices axes).prod → ℂ) (j:Fin (radices axes).prod):
 (packedTensor axes).mulVec (fun k=>v (unpackingPermutation axes k)) (packingPermutation axes j)=
 (originalTensor axes).mulVec v j:=by
 rw[←packing_tensor axes]
 unfold Matrix.mulVec dotProduct
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
 exact Fintype.sum_equiv (unpackingPermutation axes) _ _ (by intro k;rfl)
/-- Concrete numeric consequence of actual Completed plus actual inverse stores:
the physical native output is the literal original tensor pair-slot operator. -/
theorem native_tensor {W B F reserve A E:ℕ} (axes:List Axis)
 (g:Geometry W B F reserve A E (sectorStates axes)) (cover:Cover (sectorStates axes) g.volume)
 (v:ℕ → ℕ → Scalar) (input:ℕ → Fin (radices axes).prod → ℂ) (mid u:State)
 (done:Completed W A (sectorStates axes) v (sectorStates axes).length mid)
 (packedInput:∀r,r < W → ∀j:Fin (radices axes).prod,(v r j.val).value=input r (unpackingPermutation axes j))
 (destination:ℕ)
 (stored:∀r,r < W → ∀j:Fin (radices axes).prod,
  u.scalarHeap (destination+r*(radices axes).prod+j.val)=
   some (payload cover W A mid r (packingPermutation axes j).val)):
 ∀r,r < W → ∀j:Fin (radices axes).prod,
 (u.scalarHeap (destination+r*(radices axes).prod+j.val)).map Scalar.value=
  some ((originalTensor axes).mulVec (input r) j):=by
 intro r hr j
 rw[stored r hr j,Option.map_some,payload_packed axes g cover v mid done r hr (packingPermutation axes j)]
 have fn:(fun k:Fin (radices axes).prod=>(v r k.val).value)=fun k=>input r (unpackingPermutation axes k):=
  funext (packedInput r hr)
 rw[fn,unpack_mulVec]
end
end ExactFourierCircuits.UniformSectorNumericTensorBridge
