import UniformPhysicalCoordinateValue
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGenericPhysicalCoordinate
open UniformSectorPacking UniformSectorTensor UniformTraversal
open scoped BigOperators
noncomputable section

/-- Generic list digits, requiring no minimum radix. -/
def digits:(rs:List ℕ)→Choices (addressLayers rs)→(i:Fin rs.length)→Fin (rs.get i)
 | [],_=>fun i=>Fin.elim0 i
 | _r::rs,(x,xs)=>Fin.cases x (digits rs xs)
def undigits:(rs:List ℕ)→((i:Fin rs.length)→Fin (rs.get i))→Choices (addressLayers rs)
 | [],_=>()
 | _r::rs,f=>(f 0,undigits rs (fun i=>f i.succ))
lemma digits_undigits (rs:List ℕ) (f:∀i:Fin rs.length,Fin (rs.get i)):
 digits rs (undigits rs f)=f:=by
 induction rs with
 | nil=>funext i;exact Fin.elim0 i
 | cons r rs ih=>
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · exact congrFun (ih (fun j=>f j.succ)) j
lemma undigits_digits (rs:List ℕ) (x:Choices (addressLayers rs)):undigits rs (digits rs x)=x:=by
 induction rs with
 | nil=>cases x;rfl
 | cons r rs ih=>
  rcases x with ⟨x,xs⟩
  exact congrArg (fun tail=>(x,tail)) (ih xs)
def digitsEquiv (rs:List ℕ):Choices (addressLayers rs)≃((i:Fin rs.length)→Fin (rs.get i)):=
 ⟨digits rs,undigits rs,undigits_digits rs,digits_undigits rs⟩
def listCoordinate (rs:List ℕ):((i:Fin rs.length)→Fin (rs.get i))≃Fin rs.prod:=
 (digitsEquiv rs).symm.trans (mixedEquiv rs)

theorem list_value (rs:List ℕ) (ds:∀i:Fin rs.length,Fin (rs.get i)):
 (listCoordinate rs ds).val=∑i:Fin rs.length,(rs.drop (i.val+1)).prod*(ds i).val:=by
 induction rs with
 | nil=>change (0:ℕ)=∑i:Fin 0,([].drop (i.val+1)).prod*(ds i).val
        simp only[Finset.univ_eq_empty,Finset.sum_empty]
 | cons r rs ih=>
  change _=∑i:Fin (rs.length+1),((r::rs).drop (i.val+1)).prod*(ds i).val
  rw[Fin.sum_univ_succ]
  simp only[Fin.val_zero,Nat.zero_add,List.drop_succ_cons,Fin.val_succ]
  change (listCoordinate rs (fun i=>ds i.succ)).val+rs.prod*(ds 0).val=
   rs.prod*(ds 0).val+∑i:Fin rs.length,(rs.drop (i.val+1)).prod*(ds i.succ).val
  rw[ih]
  exact Nat.add_comm _ _

def index {a:ℕ} (r:Fin a→ℕ):Fin (List.ofFn r).length≃Fin a:=finCongr (by simp only[List.length_ofFn])
lemma shape {a:ℕ} (r:Fin a→ℕ) (i:Fin (List.ofFn r).length):
 (List.ofFn r).get i=r (index r i):=by
 simp only[List.get_eq_getElem,List.getElem_ofFn]
 rfl

/-- Generic physical MSB ordinal for a finite family of radices. -/
def physical {a:ℕ} (r:Fin a→ℕ):((i:Fin a)→Fin (r i))≃Fin (∏i,r i):=
 ((Equiv.piCongr (index r) (fun i=>finCongr (shape r i))).symm.trans
  (listCoordinate (List.ofFn r))).trans (finCongr (by simp only[List.prod_ofFn]))

lemma castval {a b:ℕ} (h:a=b) (x:Fin b):((finCongr h).symm x).val=x.val:=by subst b;rfl

theorem physical_value {a:ℕ} (r:Fin a→ℕ) (ds:∀i,Fin (r i)):
 (physical r ds).val=∑i:Fin a,((List.ofFn r).drop (i.val+1)).prod*(ds i).val:=by
 change (listCoordinate (List.ofFn r)
  ((Equiv.piCongr (index r) (fun i=>finCongr (shape r i))).symm ds)).val=_
 rw[list_value]
 simp only[Equiv.piCongr_symm_apply,castval]
 exact Fintype.sum_equiv (index r) _ _ (fun i=>rfl)
end
end ExactFourierCircuits.UniformGenericPhysicalCoordinate
