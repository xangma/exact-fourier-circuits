import DFTModelNativeSectorRecurrence

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelNativeSectorRecurrence

open UniformTraversal UniformSectorPacking

/-- Local packed digits, before applying any axis's original permutation. -/
def localPackedEquiv : (axes : List Axis) → LocalDigits axes ≃ OriginalDigits axes
  | [] => Equiv.refl _
  | a :: axes => Equiv.prodCongr (blockEquiv a.widths) (localPackedEquiv axes)

/-- Enumerate local packed digits in mixed-radix order and decode their blocks. -/
def addressPositionEquiv (axes : List Axis) :
    Fin (UniformSectorPacking.radices axes).prod ≃ SectorPosition axes :=
  ((localPackedEquiv axes).trans (mixedEquiv (UniformSectorPacking.radices axes))).symm.trans
    (separateEquiv axes)

theorem addressPosition_cons (a : Axis) (axes : List Axis)
    (j : Fin a.widths.sum) (i : Fin (UniformSectorPacking.radices axes).prod) :
    addressPositionEquiv (a :: axes) (finProdFinEquiv (j, i)) =
      prepend a axes (blockDecode a.widths j) (addressPositionEquiv axes i) := by
  change separate (a :: axes)
    ((Equiv.prodCongr (blockEquiv a.widths) (localPackedEquiv axes)).symm
      ((Equiv.prodCongr (Equiv.refl (Fin a.widths.sum))
        (mixedEquiv (UniformSectorPacking.radices axes))).symm
          (finProdFinEquiv.symm (finProdFinEquiv (j, i))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

def extendAddress (a : Axis) (axes : List Axis) (j : Fin a.widths.sum)
    (x : AddressValue) : AddressValue :=
  let u := blockDecode a.widths j
  (a.widths.get u.1 * x.1,
    (blockBefore a.widths u.1 * (UniformSectorPacking.radices axes).prod +
        a.widths.get u.1 * x.2.1,
      (u.2.val * x.1 + x.2.2.1,
        (a.originalPermutation j).val * (UniformSectorPacking.radices axes).prod + x.2.2.2)))

theorem addressValue_enumerated_cons (a : Axis) (axes : List Axis)
    (j : Fin a.widths.sum) (i : Fin (UniformSectorPacking.radices axes).prod) :
    addressValue (a :: axes) (addressPositionEquiv (a :: axes) (finProdFinEquiv (j, i))) =
      extendAddress a axes j (addressValue axes (addressPositionEquiv axes i)) := by
  rw [addressPosition_cons, addressValue_decode_cons]
  rfl

/-- Exact row order used by the suffix producer: local packed digit, then suffix row. -/
def addressRows (axes : List Axis) : List AddressValue :=
  List.ofFn (fun i : Fin (UniformSectorPacking.radices axes).prod =>
    addressValue axes (addressPositionEquiv axes i))

theorem addressRows_length (axes : List Axis) :
    (addressRows axes).length = (UniformSectorPacking.radices axes).prod := by
  simp only [addressRows, List.length_ofFn]

theorem addressRows_get (axes : List Axis)
    (i : Fin (UniformSectorPacking.radices axes).prod) :
    (addressRows axes).get (Fin.cast (addressRows_length axes).symm i) =
      addressValue axes (addressPositionEquiv axes i) := by
  simp [addressRows]
  rfl

theorem addressRows_nil : addressRows [] = [(1, (0, (0, 0)))] := rfl

theorem addressRows_cons (a : Axis) (axes : List Axis) :
    addressRows (a :: axes) = (List.finRange a.widths.sum).flatMap
      (fun j => (addressRows axes).map (extendAddress a axes j)) := by
  unfold addressRows
  change List.ofFn (fun i : Fin (a.widths.sum * (UniformSectorPacking.radices axes).prod) =>
    addressValue (a :: axes) (addressPositionEquiv (a :: axes) i)) = _
  rw [List.ofFn_mul]
  simp only [List.map_ofFn]
  change _ = ((List.finRange a.widths.sum).map (fun j =>
    List.ofFn (fun i : Fin (UniformSectorPacking.radices axes).prod =>
      extendAddress a axes j (addressValue axes (addressPositionEquiv axes i))))).flatten
  rw [← List.ofFn_eq_map]
  congr 1
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  have hi : (⟨j.val * (UniformSectorPacking.radices axes).prod + i.val,
      by nlinarith [j.isLt, i.isLt]⟩ :
        Fin (a.widths.sum * (UniformSectorPacking.radices axes).prod)) =
      finProdFinEquiv (j, i) := by
    apply Fin.ext
    change j.val * (UniformSectorPacking.radices axes).prod + i.val =
      i.val + (UniformSectorPacking.radices axes).prod * j.val
    ring
  rw [hi]
  exact addressValue_enumerated_cons a axes j i

/-- Both maps written by the final scatter are genuine native equivalences. -/
def packedAddressEquiv (axes : List Axis) :
    Equiv.Perm (Fin (UniformSectorPacking.radices axes).prod) :=
  (addressPositionEquiv axes).trans (packedEquiv axes)

def originalAddressEquiv (axes : List Axis) :
    Equiv.Perm (Fin (UniformSectorPacking.radices axes).prod) :=
  (addressPositionEquiv axes).trans (originalEquiv axes)

theorem packedAddress_value (axes : List Axis)
    (i : Fin (UniformSectorPacking.radices axes).prod) :
    (packedAddressEquiv axes i).val =
      (addressValue axes (addressPositionEquiv axes i)).2.1 +
        (addressValue axes (addressPositionEquiv axes i)).2.2.1 :=
  packedEquiv_value axes _

theorem originalAddress_value (axes : List Axis)
    (i : Fin (UniformSectorPacking.radices axes).prod) :
    (originalAddressEquiv axes i).val =
      (addressValue axes (addressPositionEquiv axes i)).2.2.2 := rfl

theorem packingAddress (axes : List Axis)
    (i : Fin (UniformSectorPacking.radices axes).prod) :
    packingPermutation axes (originalAddressEquiv axes i) = packedAddressEquiv axes i :=
  packingPermutation_original axes _

theorem unpackingAddress (axes : List Axis)
    (i : Fin (UniformSectorPacking.radices axes).prod) :
    unpackingPermutation axes (packedAddressEquiv axes i) = originalAddressEquiv axes i := by
  rw [← packingAddress]
  exact unpacking_packing axes _

end ExactFourierCircuits.DFTModelNativeSectorRecurrence
