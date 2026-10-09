import UniformMatchingPackingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingKernelGeometry
open UniformSectorPacking UniformSectorTensor UniformMatchingAxisTableMachine
open UniformMatchingPackingPreparation
open UniformColoring (Edge)
open OAI.ExactFourier
noncomputable section

def localCoordinates (a:Axis):BlockPosition a.widths ≃ Fin a.widths.sum:=
 (blockEquiv a.widths).trans a.originalPermutation
def localKernel (a:Axis):Matrix (Fin a.widths.sum) (Fin a.widths.sum) ℂ:=
 Matrix.reindex (localCoordinates a) (localCoordinates a) (fun p q=>localEntry a p q)
lemma local_on (a:Axis) (p q:BlockPosition a.widths):
 localKernel a (localCoordinates a p) (localCoordinates a q)=localEntry a p q:=by
 change localEntry a ((localCoordinates a).symm (localCoordinates a p))
  ((localCoordinates a).symm (localCoordinates a q))=localEntry a p q
 rw[Equiv.symm_apply_apply,Equiv.symm_apply_apply]
def position {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r):
 (Σ _:Fin M,Fin 2) ↪ Fin (geometry r E hm hr hp).widths.sum where
 toFun:=fun x=>localCoordinates _ (matchingPosition r E hm hr hp x.1 x.2)
 inj':=by
  rintro ⟨i,t⟩ ⟨j,u⟩ equal
  have pos:matchingPosition r E hm hr hp i t=matchingPosition r E hm hr hp j u:=
   (localCoordinates _).injective equal
  have values:=congrArg (fun p:BlockPosition (geometry r E hm hr hp).widths=>
   (blockEncode _ p).val) pos
  rw[matching_position_encode,matching_position_encode] at values
  have ti:=t.isLt;have ui:=u.isLt
  have ij:i=j:=Fin.ext (by omega)
  subst j
  have tu:t=u:=Fin.ext (by omega)
  subst u
  rfl
lemma position_value {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (i:Fin M) (t:Fin 2):(position r E hm hr hp ⟨i,t⟩).val=if t.val=0 then (E i).left else (E i).right:=
 matching_position_original r E hm hr hp i t
lemma pair_form {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (p:BlockPosition (geometry r E hm hr hp).widths) (small:p.1.val < M):
 ∃i:Fin M,∃t:Fin 2,p=matchingPosition r E hm hr hp i t:=by
 let i:Fin M:=⟨p.1.val,small⟩
 have block:p.1=pairBlock r (matching_capacity r E hm hr) i:=Fin.ext rfl
 have width:(geometry r E hm hr hp).widths.get p.1=2:=by
  rw[block];exact pair_width r (matching_capacity r E hm hr) i
 let t:Fin 2:=⟨p.2.val,by exact lt_of_lt_of_eq p.2.isLt width⟩
 refine ⟨i,t,?_⟩
 apply Sigma.ext block
 apply (Fin.heq_ext_iff (congrArg (fun b=>(geometry r E hm hr hp).widths.get b) block)).2
 rfl
lemma singleton_width {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (b:Fin (geometry r E hm hr hp).widths.length) (large:M ≤ b.val):
 (geometry r E hm hr hp).widths.get b=1:=by
 change (widths r M).get ⟨b.val,b.isLt⟩=1
 simp only[List.get_eq_getElem,widths]
 rw[List.getElem_append_right (by simp only[List.length_replicate];exact large)]
 simp
lemma singleton_entry {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (p q:BlockPosition (geometry r E hm hr hp).widths) (large:M ≤ p.1.val):
 localEntry (geometry r E hm hr hp) p q=if p=q then 1 else 0:=by
 rcases p with ⟨b,t⟩
 rcases q with ⟨d,u⟩
 by_cases same:b=d
 · subst d
   have width:=singleton_width r E hm hr hp b large
   have ht:t.val < 1:=lt_of_lt_of_eq t.isLt width
   have hu:u.val < 1:=lt_of_lt_of_eq u.isLt width
   have tu:t=u:=Fin.ext (by omega)
   subst u
   rw[localEntry_same]
   simp only[ite_true]
   change blockEntry ((geometry r E hm hr hp).widths.get b) t.val t.val=1
   exact (congrArg (fun n=>blockEntry n t.val t.val) width).trans (by simp[blockEntry])
 · have ne:(⟨b,t⟩:BlockPosition (geometry r E hm hr hp).widths)≠⟨d,u⟩:=
    fun eq=>same (congrArg Sigma.fst eq)
   simp[localEntry,same,ne]
lemma singleton_outside {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (p:BlockPosition (geometry r E hm hr hp).widths) (large:M ≤ p.1.val):
 localCoordinates _ p∉Set.range (position r E hm hr hp):=by
 rintro ⟨⟨i,t⟩,equal⟩
 have pos:matchingPosition r E hm hr hp i t=p:=(localCoordinates _).injective equal
 have blocks:=congrArg (fun q:BlockPosition (geometry r E hm hr hp).widths=>q.1.val) pos
 change i.val=p.1.val at blocks
 have:=i.isLt
 omega
lemma pair_entry {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (i j:Fin M) (t u:Fin 2):
 localEntry (geometry r E hm hr hp) (matchingPosition r E hm hr hp i t) (matchingPosition r E hm hr hp j u)=
 (Matrix.blockDiagonal' (fun _:Fin M=>C)) ⟨i,t⟩ ⟨j,u⟩:=by
 by_cases equal:i=j
 · subst j
   rw[Matrix.blockDiagonal'_apply_eq]
   change (if pairBlock r (matching_capacity r E hm hr) i=pairBlock r (matching_capacity r E hm hr) i then
    blockEntry ((widths r M).get (pairBlock r (matching_capacity r E hm hr) i)) t.val u.val else 0)=C t u
   rw[ite_eq_left rfl,pair_width]
   exact blockEntry_two t u
 · have blocks:pairBlock r (matching_capacity r E hm hr) i≠pairBlock r (matching_capacity r E hm hr) j:=by
    intro eq
    apply equal
    apply Fin.ext
    have h:=congrArg (fun b:Fin (widths r M).length=>b.val) eq
    exact h
   rw[Matrix.blockDiagonal'_apply_ne _ _ _ equal]
   exact localEntry_off _ _ _ _ _ blocks

/-- The exact Axis printed by Matching55 carries C on every ordered pair and
identity on every actually enumerated singleton. -/
theorem kernel_matrix {M:ℕ} (r:ℕ) (E:Fin M → Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r):
 localKernel (geometry r E hm hr hp)=
 Embedded.matrix (position r E hm hr hp) (Matrix.blockDiagonal' (fun _:Fin M=>C)):=by
 classical
 ext x y
 obtain ⟨p,rfl⟩:=(localCoordinates (geometry r E hm hr hp)).surjective x
 obtain ⟨q,rfl⟩:=(localCoordinates (geometry r E hm hr hp)).surjective y
 rw[local_on]
 by_cases small:p.1.val < M
 · obtain ⟨i,t,rfl⟩:=pair_form r E hm hr hp p small
   by_cases next:q.1.val < M
   · obtain ⟨j,u,rfl⟩:=pair_form r E hm hr hp q next
     change _=Embedded.matrix (position r E hm hr hp) _ (position r E hm hr hp ⟨i,t⟩) (position r E hm hr hp ⟨j,u⟩)
     rw[Embedded.matrix_on]
     exact pair_entry r E hm hr hp i j t u
   · rw[Embedded.matrix_off_col _ _ _ _ (singleton_outside r E hm hr hp q (by omega))]
     have blocks:(matchingPosition r E hm hr hp i t).1≠q.1:=by
      intro eq;have:=congrArg Fin.val eq;change i.val=q.1.val at this;have:=i.isLt;omega
     have ne:localCoordinates _ (matchingPosition r E hm hr hp i t)≠localCoordinates _ q:=
      fun eq=>blocks (congrArg Sigma.fst ((localCoordinates _).injective eq))
     simp only[localEntry,blocks,ite_false,ne]
 · rw[Embedded.matrix_off_row _ _ _ _ (singleton_outside r E hm hr hp p (by omega)),
    singleton_entry r E hm hr hp p q (by omega)]
   simp only[(localCoordinates (geometry r E hm hr hp)).injective.eq_iff]

def singleCoordinate (a:Axis):Fin a.widths.sum ≃ Fin (radices [a]).prod:=finCongr (by simp[radices])
theorem single_original (a:Axis):
 Matrix.reindex (singleCoordinate a).symm (singleCoordinate a).symm (originalTensor [a])=localKernel a:=by
 ext x y
 obtain ⟨p,rfl⟩:=(localCoordinates a).surjective x
 obtain ⟨q,rfl⟩:=(localCoordinates a).surjective y
 have coordinate (p:BlockPosition a.widths):singleCoordinate a (localCoordinates a p)=
  originalEquiv [a] ⟨(p.1,()),(p.2,())⟩:=by
  apply Fin.ext
  exact (single_original_value a p.1 p.2).symm
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm]
 rw[coordinate p,coordinate q,originalTensor_coordinates,local_on]
 change localEntry a p q*1=localEntry a p q
 ring
end
end ExactFourierCircuits.UniformMatchingKernelGeometry
