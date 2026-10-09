import UniformFastPhysicalCRTEmission
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTProgress
open UniformMachine UniformFastPhysicalCRTMachine UniformFastPhysicalCRTEmission
noncomputable section

def Outside (a V:ℕ)(L:Addresses)(heap:ℕ→Option ℕ)(s:State):Prop:=
 ∀q,(q<L.physicalAlpha∨L.physicalAlpha+V≤q)→
 (q<L.inverseBeta∨L.inverseBeta+V≤q)→
 (q<L.work∨L.work+2*a≤q)→s.natHeap q=heap q
structure Progress (a V:ℕ) (L:Addresses) (rho alpha beta:Fin V≃Fin V)
 (p:ℕ) (heap:ℕ→Option ℕ) (s:State):Prop where
 copied:∀j:Fin V,j.val<p→s.natHeap (L.physicalAlpha+j.val)=some (alpha (rho j)).val
 inverted:∀j:Fin V,j.val<p→s.natHeap (L.inverseBeta+(beta (rho j)).val)=some j.val
 outside:Outside a V L heap s
lemma Progress.zero (a V:ℕ) (L:Addresses) (rho alpha beta:Fin V≃Fin V)
 (s:State):Progress a V L rho alpha beta 0 s.natHeap s:=by
 refine ⟨?_,?_,?_⟩
 · intro j hj;omega
 · intro j hj;omega
 · intro j _ _ _;rfl
lemma Progress.heap {a V p:ℕ} {L:Addresses} {rho alpha beta:Fin V≃Fin V}
 {heap:ℕ→Option ℕ} {s u:State} (h:Progress a V L rho alpha beta p heap s)
 (e:u.natHeap=s.natHeap):Progress a V L rho alpha beta p heap u:=by
 constructor
 · intro j hj;rw[e];exact h.copied j hj
 · intro j hj;rw[e];exact h.inverted j hj
 · intro j hj hk hw;rw[e];exact h.outside j hj hk hw

lemma Progress.step {a V p:ℕ} {L:Addresses} {rho alpha beta:Fin V≃Fin V}
 {heap:ℕ→Option ℕ} {s u:State} (h:Progress a V L rho alpha beta p heap s)
 (hp:p<V) (separate:L.physicalAlpha+V≤L.inverseBeta)
 (e:u.natHeap=Function.update
 (Function.update s.natHeap (L.physicalAlpha+p) (some (alpha (rho ⟨p,hp⟩)).val))
 (L.inverseBeta+(beta (rho ⟨p,hp⟩)).val) (some p)):
 Progress a V L rho alpha beta (p+1) heap u:=by
 constructor
 · intro j hj
   have neq:L.physicalAlpha+j.val≠L.inverseBeta+(beta (rho ⟨p,hp⟩)).val:=by omega
   by_cases eq:j.val=p
   · have je:j=⟨p,hp⟩:=Fin.ext eq
     rw[e,Function.update_of_ne neq];simp only[je,Function.update_self]
   · have ne:L.physicalAlpha+j.val≠L.physicalAlpha+p:=by omega
     rw[e];simp only[Function.update_of_ne neq,Function.update_of_ne ne]
     exact h.copied j (by omega)
 · intro j hj
   have ne:L.inverseBeta+(beta (rho j)).val≠L.physicalAlpha+p:=by omega
   by_cases eq:j.val=p
   · have je:j=⟨p,hp⟩:=Fin.ext eq
     rw[e];simp[je]
   · have neq:L.inverseBeta+(beta (rho j)).val≠L.inverseBeta+(beta (rho ⟨p,hp⟩)).val:=by
      intro bad
      have efin:beta (rho j)=beta (rho ⟨p,hp⟩):=Fin.ext (by omega)
      have je:=rho.injective (beta.injective efin)
      exact eq (congrArg Fin.val je)
     rw[e];simp only[Function.update_of_ne neq,Function.update_of_ne ne]
     exact h.inverted j (by omega)
 · intro j hj hk hw
   have ne1:j≠L.physicalAlpha+p:=by omega
   have ne2:j≠L.inverseBeta+(beta (rho ⟨p,hp⟩)).val:=by
    have hval: (beta (rho ⟨p,hp⟩)).val<V:=(beta (rho ⟨p,hp⟩)).isLt
    omega
   rw[e];simp only[Function.update_of_ne ne2,Function.update_of_ne ne1]
   exact h.outside j hj hk hw

lemma Progress.source {a V p d:ℕ} {L:Addresses} {rho alpha beta phi:Fin V≃Fin V}
 {heap:ℕ→Option ℕ} {s:State} (h:Progress a V L rho alpha beta p heap s)
 (fresh:d+V≤L.physicalAlpha) (separate:L.physicalAlpha+V≤L.inverseBeta)
 (workBefore:L.inverseBeta+V≤L.work)
 (table:UniformGlobalNatPreparation.PermutationBank V d heap phi):
 UniformGlobalNatPreparation.PermutationBank V d s.natHeap phi:=by
 intro j
 rw[h.outside (d+j.val) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
 exact table j

lemma Progress.work {a V p:ℕ}{L:Addresses}{rho alpha beta:Fin V≃Fin V}
 {heap:ℕ→Option ℕ}{s u:State}(h:Progress a V L rho alpha beta p heap s)
 (separate:L.physicalAlpha+V≤L.inverseBeta)(before:L.inverseBeta+V≤L.work)
 (outside:UniformFastPhysicalCRTInitialization.Outside a L s.natHeap u):
 Progress a V L rho alpha beta p heap u:=by
 constructor
 · intro j hj;rw[outside _ (Or.inl (by omega))];exact h.copied j hj
 · intro j hj;rw[outside _ (Or.inl (by have lt: (beta (rho j)).val<V:=(beta (rho j)).isLt;omega))]
   exact h.inverted j hj
 · intro q hp hb hw;rw[outside q hw];exact h.outside q hp hb hw
lemma Progress.initialized {a V:ℕ}(L:Addresses)(rho alpha beta:Fin V≃Fin V)(s u:State)
 (outside:UniformFastPhysicalCRTInitialization.Outside a L s.natHeap u):
 Progress a V L rho alpha beta 0 s.natHeap u:=by
 constructor
 · intro j h;omega
 · intro j h;omega
 · intro q _ _ hw;exact outside q hw

lemma Progress.banks {a V:ℕ} {L:Addresses} {rho alpha beta:Fin V≃Fin V}
 {heap:ℕ→Option ℕ} {s:State} (h:Progress a V L rho alpha beta V heap s):
 UniformGlobalNatPreparation.PermutationBank V L.physicalAlpha s.natHeap (rho.trans alpha)∧
 UniformGlobalNatPreparation.PermutationBank V L.inverseBeta s.natHeap (rho.trans beta).symm:=by
 constructor
 · intro j;exact h.copied j j.isLt
 · intro j
   have z:=h.inverted ((rho.trans beta).symm j) ((rho.trans beta).symm j).isLt
   have hz:beta (rho ((rho.trans beta).symm j))=j:=(rho.trans beta).apply_symm_apply j
   rw[hz] at z;exact z
end
end ExactFourierCircuits.UniformFastPhysicalCRTProgress
