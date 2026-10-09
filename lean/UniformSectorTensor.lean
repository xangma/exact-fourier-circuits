import UniformSectorPacking
import KernelIdentities

/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, proof of Proposition 4.2, PDF p. 20 (`prop:tensor-fourier`), following Lemma 4.1, p. 19.

The tensor pair layer is conjugated by the explicit packing permutation into independent sectors. Singleton blocks contribute identity; the remaining factors are precisely copies of C. This is matrix semantics, not an assumed recursive execution.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorTensor
open UniformSectorPacking OAI.ExactFourier UniformTraversal
noncomputable section

/-- Width-two blocks contain the specified C, and width-one blocks identity. -/
def blockEntry (q i j : ℕ) : ℂ :=
  if q=2 then if i=j then a else b else 1

theorem blockEntry_two (i j : Fin 2) : blockEntry 2 i.val j.val=C i j := by
  fin_cases i <;> fin_cases j <;> simp [blockEntry,C]

theorem blockEntry_one (i j : Fin 1) : blockEntry 1 i.val j.val=(1 : Matrix (Fin 1) (Fin 1) ℂ) i j := by
  fin_cases i;fin_cases j;simp [blockEntry]

def localEntry (axis : Axis) (x y : BlockPosition axis.widths) : ℂ :=
  if x.1=y.1 then blockEntry (axis.widths.get x.1) x.2.val y.2.val else 0

theorem localEntry_same (axis : Axis) (c : Fin axis.widths.length)
    (x y : Fin (axis.widths.get c)) :
    localEntry axis ⟨c,x⟩ ⟨c,y⟩=blockEntry (axis.widths.get c) x.val y.val := by
  exact ite_eq_left rfl

theorem localEntry_off (axis : Axis) (c d : Fin axis.widths.length)
    (x : Fin (axis.widths.get c)) (y : Fin (axis.widths.get d)) (h : c≠d) :
    localEntry axis ⟨c,x⟩ ⟨d,y⟩=0 := by
  exact ite_eq_right h

def localTensor : (axes : List Axis) → LocalDigits axes → LocalDigits axes → ℂ
  | [],_,_=>1
  | axis::axes,(x,xs),(y,ys)=>localEntry axis x y*localTensor axes xs ys

def sectorTensor : (axes : List Axis) → (c : BlockChoices axes) → Positions axes c → Positions axes c → ℂ
  | [],_,_,_=>1
  | axis::axes,(c,cs),(x,xs),(y,ys)=>
      blockEntry (axis.widths.get c) x.val y.val*sectorTensor axes cs xs ys

theorem localTensor_same (axes : List Axis) (c : BlockChoices axes) (x y : Positions axes c) :
    localTensor axes (combine axes ⟨c,x⟩) (combine axes ⟨c,y⟩)=sectorTensor axes c x y := by
  induction axes with
  | nil=>rfl
  | cons axis axes ih=>
    rcases c with ⟨c,cs⟩;rcases x with ⟨x,xs⟩;rcases y with ⟨y,ys⟩
    change localEntry axis ⟨c,x⟩ ⟨c,y⟩*localTensor axes (combine axes ⟨cs,xs⟩)
      (combine axes ⟨cs,ys⟩)=blockEntry (axis.widths.get c) x.val y.val*sectorTensor axes cs xs ys
    exact congrArg₂ (fun u v=>u*v) (localEntry_same axis c x y) (ih cs xs ys)

theorem localTensor_off (axes : List Axis) (c d : BlockChoices axes) (x : Positions axes c)
    (y : Positions axes d) (h : c≠d) :
    localTensor axes (combine axes ⟨c,x⟩) (combine axes ⟨d,y⟩)=0 := by
  induction axes with
  | nil=>cases c;cases d;exact (h rfl).elim
  | cons axis axes ih=>
    rcases c with ⟨c,cs⟩;rcases d with ⟨d,ds⟩;rcases x with ⟨x,xs⟩;rcases y with ⟨y,ys⟩
    by_cases hc:c=d
    · subst d
      have ht:cs≠ds:=by intro he;subst ds;exact h rfl
      simp only [combine,localTensor,ih cs ds xs ys ht,mul_zero]
    · change localEntry axis ⟨c,x⟩ ⟨d,y⟩*localTensor axes (combine axes ⟨cs,xs⟩)
        (combine axes ⟨ds,ys⟩)=0
      rw [localEntry_off axis c d x y hc,zero_mul]

instance blockChoiceDecEq (axes : List Axis) : DecidableEq (BlockChoices axes) := by
  induction axes with
  | nil=>exact inferInstanceAs (DecidableEq Unit)
  | cons axis axes ih=>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin axis.widths.length×BlockChoices axes))

/-- The tensor pair slot in the original coordinate order, derived from the
actual local permutation/block codecs. This is a matrix identity, not RAM work. -/
/- Proposition 4.2 proof, p. 20: tensoring ordered local pair/singleton blocks is block diagonal on sectors before applying the explicit packed-coordinate conjugation. -/
def originalTensor (axes : List Axis) : Matrix (Fin (radices axes).prod) (Fin (radices axes).prod) ℂ :=
  fun i j=>localTensor axes
    ((localDigitsEquiv axes).symm ((mixedEquiv (radices axes)).symm i))
    ((localDigitsEquiv axes).symm ((mixedEquiv (radices axes)).symm j))

theorem originalTensor_coordinates (axes : List Axis) (x y : SectorPosition axes) :
    originalTensor axes (originalEquiv axes x) (originalEquiv axes y)=
      localTensor axes (combine axes x) (combine axes y) := by
  simp only [originalTensor,originalEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

def sectorMatrix (axes : List Axis) (c : BlockChoices axes) :
    Matrix (Positions axes c) (Positions axes c) ℂ := sectorTensor axes c

theorem originalTensor_sectors (axes : List Axis) :
    originalTensor axes=Matrix.reindex (originalEquiv axes) (originalEquiv axes)
      (Matrix.blockDiagonal' (sectorMatrix axes)) := by
  ext i j
  obtain ⟨⟨c,x⟩,rfl⟩:=(originalEquiv axes).surjective i
  obtain ⟨⟨d,y⟩,rfl⟩:=(originalEquiv axes).surjective j
  rw [originalTensor_coordinates]
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  by_cases h:c=d
  · subst d
    rw [Matrix.blockDiagonal'_apply_eq]
    exact localTensor_same axes c x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact localTensor_off axes c d x y h

def packedTensor (axes : List Axis) : Matrix (Fin (radices axes).prod) (Fin (radices axes).prod) ℂ :=
  Matrix.reindex (packedEquiv axes) (packedEquiv axes) (Matrix.blockDiagonal' (sectorMatrix axes))

/-- The already proved packing permutation is exactly the conjugation needed
to separate independent sectors; it is not a fresh existential permutation. -/
theorem packing_tensor (axes : List Axis) :
    Matrix.reindex (packingPermutation axes) (packingPermutation axes) (originalTensor axes)=packedTensor axes := by
  rw [originalTensor_sectors]
  ext i j
  simp [packedTensor,Matrix.reindex_apply,Matrix.submatrix_apply,packingPermutation]

/- Proposition 4.2 proof, p. 20: every width-one factor is identity and can be removed; the remaining ordered factors are C^{⊗k}. -/
/-- Remove singleton positions and keep the ordered binary coordinates. -/
def binaryDigits : (axes : List Axis) → (c : BlockChoices axes) → Positions axes c → List ℕ
  | [],_,_=>[]
  | axis::axes,(c,cs),(x,xs)=>
    if axis.widths.get c=2 then x.val::binaryDigits axes cs xs else binaryDigits axes cs xs

theorem binaryDigits_length (axes : List Axis) (c : BlockChoices axes) (x : Positions axes c) :
    (binaryDigits axes c x).length=sectorPairCount axes c := by
  induction axes with
  | nil=>rfl
  | cons axis axes ih=>
    rcases c with ⟨c,cs⟩;rcases x with ⟨x,xs⟩
    by_cases h:axis.widths.get c=2 <;>
      simp [binaryDigits,sectorPairCount,sectorRadices,h,ih cs xs]

theorem binaryDigits_lt_two (axes : List Axis) (c : BlockChoices axes) (x : Positions axes c) :
    ∀i∈binaryDigits axes c x,i<2 := by
  induction axes with
  | nil=>simp [binaryDigits]
  | cons axis axes ih=>
    rcases c with ⟨c,cs⟩;rcases x with ⟨x,xs⟩
    by_cases h:axis.widths.get c=2
    · simp only [binaryDigits,h,ite_true,List.mem_cons]
      intro i hi
      rcases hi with rfl|hi
      · simpa only [h,addressLayer] using x.isLt
      · exact ih cs xs i hi
    · simpa only [binaryDigits,h,ite_false] using ih cs xs

def binaryEntry (is js : List ℕ) : ℂ :=
  (List.zipWith (fun i j=>if i=j then a else b) is js).prod

/-- Every sector carries the literal product of C entries on its selected
binary axes. Singleton identities contribute no coordinate or scalar factor. -/
theorem sectorTensor_binary (axes : List Axis) (c : BlockChoices axes) (x y : Positions axes c) :
    sectorTensor axes c x y=binaryEntry (binaryDigits axes c x) (binaryDigits axes c y) := by
  induction axes with
  | nil=>rfl
  | cons axis axes ih=>
    rcases c with ⟨c,cs⟩;rcases x with ⟨x,xs⟩;rcases y with ⟨y,ys⟩
    have h:=axis.widths_one_two (axis.widths.get c) (List.get_mem _ _)
    rcases h with h|h <;> simp [sectorTensor,blockEntry,binaryDigits,h,binaryEntry] at *
    · exact ih cs xs ys
    · rw [ih cs xs ys]

end
end ExactFourierCircuits.UniformSectorTensor
