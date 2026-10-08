import UniformSectorTensor
import UniformFixedNetwork

set_option autoImplicit false

/-! The explicit sector codec supplies the binary coordinates required by the
fixed saving network. These are algebraic identities; charging the codec and
the network's RAM traversal remains a separate operational obligation. -/
namespace ExactFourierCircuits.UniformSectorNetworkAction
open UniformSectorPacking UniformSectorTensor UniformTraversal OAI.ExactFourier
open scoped BigOperators
noncomputable section

def emptyCoordinates : Unit ≃ (Fin 0 → Fin 2) where
  toFun := fun _ i => Fin.elim0 i
  invFun := fun _ => ()
  left_inv := fun x => by cases x; rfl
  right_inv := fun x => by funext i; exact Fin.elim0 i

def prependCoordinates (k : ℕ) : (Fin 2 × (Fin k → Fin 2)) ≃ (Fin (k+1) → Fin 2) where
  toFun := fun x => Fin.cons x.1 x.2
  invFun := fun x => (x 0,fun i => x i.succ)
  left_inv := fun x => by rcases x with ⟨x,xs⟩; simp
  right_inv := fun x => by funext i; exact Fin.cases (by simp) (fun j => by simp) i

def dropSingleton (α : Type*) : (Fin 1 × α) ≃ α where
  toFun := Prod.snd
  invFun := fun x => (0,x)
  left_inv := fun x => by rcases x with ⟨i,x⟩; fin_cases i; rfl
  right_inv := fun _ => rfl

theorem count_cons_two (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes) (h : axis.widths.get c=2) :
    sectorPairCount (axis::axes) (c,cs)=sectorPairCount axes cs+1 := by
  change List.countP (fun q => q == 2) (axis.widths.get c::sectorRadices axes cs)=_
  rw [h]; simp [sectorPairCount]

theorem count_cons_one (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes) (h : axis.widths.get c=1) :
    sectorPairCount (axis::axes) (c,cs)=sectorPairCount axes cs := by
  change List.countP (fun q => q == 2) (axis.widths.get c::sectorRadices axes cs)=_
  rw [h]; simp [sectorPairCount]

def positionsCons (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes) :
    Positions (axis::axes) (c,cs) ≃ (Fin (axis.widths.get c) × Positions axes cs) := Equiv.refl _

def consCoordinates (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes)
    (tail : Positions axes cs ≃ (Fin (sectorPairCount axes cs) → Fin 2)) :
    (Fin (axis.widths.get c) × Positions axes cs) ≃
      (Fin (sectorPairCount (axis::axes) (c,cs)) → Fin 2) :=
    if h : axis.widths.get c=2 then
        ((finCongr h).prodCongr tail).trans
          ((prependCoordinates (sectorPairCount axes cs)).trans
            (Equiv.arrowCongr (finCongr (count_cons_two axis axes c cs h)).symm (Equiv.refl _)))
    else
      let h1 : axis.widths.get c=1 :=
        (axis.widths_one_two _ (List.get_mem _ _)).resolve_right h
      ((finCongr h1).prodCongr tail).trans
        ((dropSingleton _).trans
          (Equiv.arrowCongr (finCongr (count_cons_one axis axes c cs h1)).symm (Equiv.refl _)))

/-- Keep the selected width-two axes in their original order; remove singleton
axes. No finite enumeration is used to define this coordinate equivalence. -/
def binaryCoordinates : (axes : List Axis) → (c : BlockChoices axes) →
    Positions axes c ≃ (Fin (sectorPairCount axes c) → Fin 2)
  | [],_ => emptyCoordinates
  | axis::axes,(c,cs) =>
    (positionsCons axis axes c cs).trans (consCoordinates axis axes c cs (binaryCoordinates axes cs))

theorem binaryCoordinates_two (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes) (h : axis.widths.get c=2) (x : Fin (axis.widths.get c))
    (xs : Positions axes cs) (i : Fin (sectorPairCount axes cs+1)) :
    binaryCoordinates (axis::axes) (c,cs) (x,xs)
      ((finCongr (count_cons_two axis axes c cs h)).symm i)=
      Fin.cons (α:=fun _ => Fin 2) (finCongr h x) (binaryCoordinates axes cs xs) i := by
  change consCoordinates axis axes c cs (binaryCoordinates axes cs) (x,xs) _=_
  rw [consCoordinates,dite_eq_left h]
  rfl

theorem binaryCoordinates_one (axis : Axis) (axes : List Axis) (c : Fin axis.widths.length)
    (cs : BlockChoices axes) (h : axis.widths.get c=1) (x : Fin (axis.widths.get c))
    (xs : Positions axes cs) (i : Fin (sectorPairCount axes cs)) :
    binaryCoordinates (axis::axes) (c,cs) (x,xs)
      ((finCongr (count_cons_one axis axes c cs h)).symm i)=binaryCoordinates axes cs xs i := by
  change consCoordinates axis axes c cs (binaryCoordinates axes cs) (x,xs) _=_
  rw [consCoordinates,dite_eq_right (by omega : axis.widths.get c≠2)]
  rfl

theorem blockEntry_cast_two {q : ℕ} (h : q=2) (x y : Fin q) :
    blockEntry q x.val y.val=C (finCongr h x) (finCongr h y) := by
  have hc:=blockEntry_two (finCongr h x) (finCongr h y)
  exact (congrArg (fun q => blockEntry q x.val y.val) h).trans
    (by simpa only [finCongr_apply_coe] using hc)

/-- In these explicit binary coordinates each sector is exactly C tensor k. -/
theorem sectorTensor_product (axes : List Axis) (c : BlockChoices axes)
    (x y : Positions axes c) :
    sectorTensor axes c x y=
      ∏ i : Fin (sectorPairCount axes c),
        C (binaryCoordinates axes c x i) (binaryCoordinates axes c y i) := by
  induction axes with
  | nil =>
    change 1=∏ i : Fin 0, C (binaryCoordinates [] c x i) (binaryCoordinates [] c y i)
    simp
  | cons axis axes ih =>
    rcases c with ⟨c,cs⟩; rcases x with ⟨x,xs⟩; rcases y with ⟨y,ys⟩
    by_cases h : axis.widths.get c=2
    · have hc:=count_cons_two axis axes c cs h
      rw [← (finCongr hc).symm.prod_comp
        (fun i => C (binaryCoordinates (axis::axes) (c,cs) (x,xs) i)
          (binaryCoordinates (axis::axes) (c,cs) (y,ys) i))]
      have heq :
          (∏ i : Fin (sectorPairCount axes cs+1),
            C (binaryCoordinates (axis::axes) (c,cs) (x,xs) ((finCongr hc).symm i))
              (binaryCoordinates (axis::axes) (c,cs) (y,ys) ((finCongr hc).symm i)))=
          (∏ i : Fin (sectorPairCount axes cs+1),
            C (Fin.cons (α:=fun _ => Fin 2) (finCongr h x) (binaryCoordinates axes cs xs) i)
              (Fin.cons (α:=fun _ => Fin 2) (finCongr h y) (binaryCoordinates axes cs ys) i)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg₂ C (binaryCoordinates_two axis axes c cs h x xs i)
          (binaryCoordinates_two axis axes c cs h y ys i)
      rw [heq]
      change blockEntry (axis.widths.get c) x.val y.val*sectorTensor axes cs xs ys=
        ∏ i : Fin (sectorPairCount axes cs+1),
          C (Fin.cons (α:=fun _ => Fin 2) (finCongr h x) (binaryCoordinates axes cs xs) i)
            (Fin.cons (α:=fun _ => Fin 2) (finCongr h y) (binaryCoordinates axes cs ys) i)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,← ih cs xs ys]
      apply congrArg (fun v => v*sectorTensor axes cs xs ys)
      exact blockEntry_cast_two h x y
    · have h1 : axis.widths.get c=1 :=
        (axis.widths_one_two _ (List.get_mem _ _)).resolve_right h
      have hc:=count_cons_one axis axes c cs h1
      rw [← (finCongr hc).symm.prod_comp
        (fun i => C (binaryCoordinates (axis::axes) (c,cs) (x,xs) i)
          (binaryCoordinates (axis::axes) (c,cs) (y,ys) i))]
      have heq :
          (∏ i : Fin (sectorPairCount axes cs),
            C (binaryCoordinates (axis::axes) (c,cs) (x,xs) ((finCongr hc).symm i))
              (binaryCoordinates (axis::axes) (c,cs) (y,ys) ((finCongr hc).symm i)))=
          (∏ i : Fin (sectorPairCount axes cs),
            C (binaryCoordinates axes cs xs i) (binaryCoordinates axes cs ys i)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact congrArg₂ C (binaryCoordinates_one axis axes c cs h1 x xs i)
          (binaryCoordinates_one axis axes c cs h1 y ys i)
      rw [heq]
      change blockEntry (axis.widths.get c) x.val y.val*sectorTensor axes cs xs ys=
        ∏ i : Fin (sectorPairCount axes cs), C (binaryCoordinates axes cs xs i) (binaryCoordinates axes cs ys i)
      simp [blockEntry,h1,ih cs xs ys]

/-- The final adapter records the upstream network's fixed coordinate labeling.
Its use here asserts no runtime bound for that labeling. -/
def networkCoordinates (axes : List Axis) (c : BlockChoices axes) :
    Positions axes c ≃ Fin (2^(sectorPairCount axes c)) :=
  (binaryCoordinates axes c).trans (tensorCoordinates 2 (sectorPairCount axes c)).symm

theorem sectorMatrix_network (axes : List Axis) (c : BlockChoices axes) :
    Matrix.reindex (networkCoordinates axes c) (networkCoordinates axes c)
      (sectorMatrix axes c)=tensorPower C (sectorPairCount axes c) := by
  ext i j
  change sectorTensor axes c ((networkCoordinates axes c).symm i)
    ((networkCoordinates axes c).symm j)=_
  rw [sectorTensor_product]
  apply Finset.prod_congr rfl
  intro k _
  have hi : binaryCoordinates axes c ((networkCoordinates axes c).symm i)=
      tensorCoordinates 2 (sectorPairCount axes c) i :=
    (binaryCoordinates axes c).apply_symm_apply _
  have hj : binaryCoordinates axes c ((networkCoordinates axes c).symm j)=
      tensorCoordinates 2 (sectorPairCount axes c) j :=
    (binaryCoordinates axes c).apply_symm_apply _
  rw [hi,hj]

theorem sectorTensor_network (axes : List Axis) (c : BlockChoices axes)
    (x y : Positions axes c) :
    sectorTensor axes c x y=tensorPower C (sectorPairCount axes c)
      (networkCoordinates axes c x) (networkCoordinates axes c y) := by
  rw [sectorTensor_product]
  unfold tensorPower
  apply Finset.prod_congr rfl
  intro k _
  have hx : tensorCoordinates 2 (sectorPairCount axes c) (networkCoordinates axes c x)=
      binaryCoordinates axes c x := (tensorCoordinates 2 _).apply_symm_apply _
  have hy : tensorCoordinates 2 (sectorPairCount axes c) (networkCoordinates axes c y)=
      binaryCoordinates axes c y := (tensorCoordinates 2 _).apply_symm_apply _
  rw [hx,hy]

theorem tensorPower_cast (k l : ℕ) (h : k=l) (x y : Fin (2^k)) :
    tensorPower C l (finCongr (congrArg (fun k => 2^k) h) x)
      (finCongr (congrArg (fun k => 2^k) h) y)=tensorPower C k x y := by
  subst l; rfl

def batchCoordinates (axes : List Axis) (c : BlockChoices axes) (q : ℕ)
    (h : sectorPairCount axes c=q*UniformFixedNetwork.m) :
    (Fin UniformFixedNetwork.W × Positions axes c) ≃
      Fin (UniformFixedNetwork.W*2^(q*UniformFixedNetwork.m)) :=
  ((Equiv.refl _).prodCongr ((networkCoordinates axes c).trans
    (finCongr (congrArg (fun k => 2^k) h)))).trans
      (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m))

theorem simultaneousWord_entry (q : ℕ) (i j : Fin UniformFixedNetwork.W)
    (x y : Fin (2^(q*UniformFixedNetwork.m))) :
    wordMatrix (UniformFixedNetwork.simultaneousWord q)
      (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m) (i,x))
      (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m) (j,y))=
      if i=j then tensorPower C (q*UniformFixedNetwork.m) x y else 0 := by
  rw [UniformFixedNetwork.simultaneousWord_matrix]
  simp [PaddingWords.copiesMatrix,Matrix.reindex_apply,Matrix.one_apply]

def batchMatrix (axes : List Axis) (c : BlockChoices axes) :
    Matrix (Fin UniformFixedNetwork.W × Positions axes c)
      (Fin UniformFixedNetwork.W × Positions axes c) ℂ :=
  fun x y => if x.1=y.1 then sectorTensor axes c x.2 y.2 else 0

/-- The literal fixed saving word simultaneously transforms W arbitrary sectors
of the required binary width. Every role, including auxiliary roles, is allowed
arbitrary data. This theorem does not execute coordinate movement on RAM. -/
theorem simultaneousWord_sectors (axes : List Axis) (c : BlockChoices axes) (q : ℕ)
    (h : sectorPairCount axes c=q*UniformFixedNetwork.m) :
    Matrix.reindex (batchCoordinates axes c q h).symm (batchCoordinates axes c q h).symm
      (wordMatrix (UniformFixedNetwork.simultaneousWord q))=batchMatrix axes c := by
  ext x y
  rcases x with ⟨i,x⟩; rcases y with ⟨j,y⟩
  change wordMatrix (UniformFixedNetwork.simultaneousWord q)
    (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m)
      (i,finCongr (congrArg (fun k => 2^k) h) (networkCoordinates axes c x)))
    (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m)
      (j,finCongr (congrArg (fun k => 2^k) h) (networkCoordinates axes c y)))=_
  rw [simultaneousWord_entry,tensorPower_cast _ _ h]
  change (if i=j then tensorPower C (sectorPairCount axes c)
    (networkCoordinates axes c x) (networkCoordinates axes c y) else 0)=
      if i=j then sectorTensor axes c x y else 0
  rw [sectorTensor_network]

/-- This is the actual word's count, without crediting movement or printing as
free. Their costs must be added by an operational realization. -/
theorem simultaneousWord_calls (q : ℕ) (hq : 1≤q) :
    wordCalls (UniformFixedNetwork.simultaneousWord q)=
      (q*UniformFixedNetwork.S+2*UniformFixedNetwork.pointwiseCalls)*
        2^(q*UniformFixedNetwork.m-1) := UniformFixedNetwork.simultaneousWord_calls q hq

end
end ExactFourierCircuits.UniformSectorNetworkAction
