import UniformTraversal
import UniformNetworkCost

/- Canonical sector packing from ordered width-one/two local block tables.
   Reference decoding is explicit; charged array traversal is a separate implementation. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPacking
open UniformTraversal
open scoped BigOperators

abbrev BlockPosition (ws : List ℕ) := (b : Fin ws.length) × Fin (ws.get b)

def blockEncode (ws : List ℕ) (x : BlockPosition ws) : Fin ws.sum :=
  ⟨blockBefore ws x.1 + x.2.val,
    lt_of_lt_of_le (Nat.add_lt_add_left x.2.isLt _) (block_end_le_sum ws x.1)⟩

def blockSucc (q : ℕ) {ws : List ℕ} (x : BlockPosition ws) : BlockPosition (q :: ws) :=
  ⟨x.1.succ, x.2⟩

theorem blockEncode_zero_value (q : ℕ) (ws : List ℕ) (t : Fin q) :
    (blockEncode (q :: ws) ⟨0, t⟩).val = t.val := by simp [blockEncode, blockBefore]

theorem blockEncode_succ_value (q : ℕ) {ws : List ℕ} (x : BlockPosition ws) :
    (blockEncode (q :: ws) (blockSucc q x)).val = q + (blockEncode ws x).val := by
  simp [blockEncode, blockSucc, blockBefore, Nat.add_assoc]

/-- Explicit inverse: test the next ordered block and subtract its width. -/
def blockDecode : (ws : List ℕ) → Fin ws.sum → BlockPosition ws
  | [], i => Fin.elim0 i
  | q :: ws, i =>
    if h : i.val < q then ⟨0, ⟨i.val, h⟩⟩ else
      blockSucc q (blockDecode ws ⟨i.val - q, by have hi := i.isLt; change i.val < q + ws.sum at hi; omega⟩)

theorem blockEncode_decode (ws : List ℕ) (i : Fin ws.sum) : blockEncode ws (blockDecode ws i) = i := by
  induction ws with
  | nil => exact Fin.elim0 i
  | cons q ws ih =>
    rw [blockDecode]
    split_ifs with h
    · apply Fin.ext
      exact blockEncode_zero_value q ws _
    · apply Fin.ext
      rw [blockEncode_succ_value, ih]
      change q + (i.val - q) = i.val
      omega

theorem blockDecode_encode (ws : List ℕ) (x : BlockPosition ws) : blockDecode ws (blockEncode ws x) = x := by
  induction ws with
  | nil => exact Fin.elim0 x.1
  | cons q ws ih =>
    rcases x with ⟨b, t⟩
    revert t
    refine Fin.cases ?_ (fun b => ?_) b
    · intro t
      have h : (blockEncode (q :: ws) ⟨0, t⟩).val < q := by
        simpa [blockEncode, blockBefore] using t.isLt
      rw [blockDecode, dite_eq_left h]
      exact congrArg (fun v : Fin ((q :: ws).get 0) =>
        (⟨0, v⟩ : BlockPosition (q :: ws))) (Fin.ext (blockEncode_zero_value q ws t))
    · intro t
      have h : ¬(blockEncode (q :: ws) ⟨b.succ, t⟩).val < q := by
        change ¬(q + blockBefore ws b + t.val) < q
        omega
      rw [blockDecode, dite_eq_right h]
      change blockSucc q (blockDecode ws _) = blockSucc q ⟨b, t⟩
      congr 1
      convert ih ⟨b, t⟩ using 1
      congr 1
      apply Fin.ext
      change q + blockBefore ws b + t.val - q = blockBefore ws b + t.val
      omega

def blockEquiv (ws : List ℕ) : BlockPosition ws ≃ Fin ws.sum :=
  ⟨blockEncode ws, blockDecode ws, blockDecode_encode ws, blockEncode_decode ws⟩

/-- The usual mixed-radix order, first digit most significant, with explicit div/mod inverse. -/
def mixedEquiv : (rs : List ℕ) → Choices (addressLayers rs) ≃ Fin rs.prod
  | [] =>
    { toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun i => by apply Fin.ext; have hi := i.isLt; simp only [List.prod_nil] at hi; change 0 = i.val; omega }
  | r :: rs => (Equiv.prodCongr (Equiv.refl (Fin r)) (mixedEquiv rs)).trans finProdFinEquiv

theorem mixedEquiv_value (rs : List ℕ) (x : Choices (addressLayers rs)) :
    (mixedEquiv rs x).val = encode rs x := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases x with ⟨a, ds⟩
    change (mixedEquiv rs ds).val + rs.prod * a.val = a.val * rs.prod + encode rs ds
    have ht := ih ds
    nlinarith

structure Axis where
  widths : List ℕ
  widths_one_two : ∀ q ∈ widths, q = 1 ∨ q = 2
  radix_two : 2 ≤ widths.sum
  originalPermutation : Equiv.Perm (Fin widths.sum)

abbrev radices (axes : List Axis) := axes.map (fun a => a.widths.sum)
abbrev blockCounts (axes : List Axis) := axes.map (fun a => a.widths.length)
abbrev BlockChoices (axes : List Axis) := Choices (addressLayers (blockCounts axes))
abbrev OriginalDigits (axes : List Axis) := Choices (addressLayers (radices axes))

def sectorRadices : (axes : List Axis) → BlockChoices axes → List ℕ
  | [], _ => []
  | a :: axes, (b, bs) => a.widths.get b :: sectorRadices axes bs

abbrev Positions (axes : List Axis) (b : BlockChoices axes) := Choices (addressLayers (sectorRadices axes b))
abbrev SectorPosition (axes : List Axis) := (b : BlockChoices axes) × Positions axes b

def LocalDigits : List Axis → Type
  | [] => Unit
  | a :: axes => BlockPosition a.widths × LocalDigits axes

def localDigitsEquiv : (axes : List Axis) → LocalDigits axes ≃ OriginalDigits axes
  | [] => Equiv.refl _
  | a :: axes => Equiv.prodCongr ((blockEquiv a.widths).trans a.originalPermutation) (localDigitsEquiv axes)

def separate : (axes : List Axis) → LocalDigits axes → SectorPosition axes
  | [], _ => ⟨(), ()⟩
  | _ :: axes, (⟨b, t⟩, ds) =>
    let tail := separate axes ds
    ⟨(b, tail.1), (t, tail.2)⟩

def combine : (axes : List Axis) → SectorPosition axes → LocalDigits axes
  | [], _ => ()
  | _ :: axes, ⟨(b, bs), (t, ts)⟩ => (⟨b, t⟩, combine axes ⟨bs, ts⟩)

theorem combine_separate (axes : List Axis) (x : LocalDigits axes) : combine axes (separate axes x) = x := by
  induction axes with
  | nil => cases x; rfl
  | cons a axes ih =>
    rcases x with ⟨⟨b, t⟩, ds⟩
    apply Prod.ext
    · rfl
    · exact ih ds

theorem separate_combine (axes : List Axis) (x : SectorPosition axes) : separate axes (combine axes x) = x := by
  induction axes with
  | nil => rcases x with ⟨b, t⟩; cases b; cases t; rfl
  | cons a axes ih =>
    rcases x with ⟨⟨b, bs⟩, ⟨t, ts⟩⟩
    exact congrArg (fun tail : SectorPosition axes =>
      (⟨(b, tail.1), (t, tail.2)⟩ : SectorPosition (a :: axes))) (ih ⟨bs, ts⟩)

def separateEquiv (axes : List Axis) : LocalDigits axes ≃ SectorPosition axes :=
  ⟨separate axes, combine axes, combine_separate axes, separate_combine axes⟩

def originalEquiv (axes : List Axis) : SectorPosition axes ≃ Fin (radices axes).prod :=
  (separateEquiv axes).symm.trans ((localDigitsEquiv axes).trans (mixedEquiv (radices axes)))

def rectangleWidths (ws qs : List ℕ) : List ℕ :=
  ws.flatMap (fun q => qs.map (fun x => q * x))

theorem scaled_sum (q : ℕ) (xs : List ℕ) : (xs.map (fun x => q * x)).sum = q * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem rectangle_length (ws qs : List ℕ) : (rectangleWidths ws qs).length = ws.length * qs.length := by
  induction ws with
  | nil => simp [rectangleWidths]
  | cons q ws ih => simp only [rectangleWidths, List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at *; nlinarith

theorem rectangle_sum (ws qs : List ℕ) : (rectangleWidths ws qs).sum = ws.sum * qs.sum := by
  induction ws with
  | nil => simp [rectangleWidths]
  | cons q ws ih =>
    simp only [rectangleWidths, List.flatMap_cons, List.sum_append, scaled_sum, List.sum_cons] at *
    rw [ih]; ring

def rectangleIndex (ws qs : List ℕ) (b : Fin ws.length) (c : Fin qs.length) : Fin (rectangleWidths ws qs).length :=
  ⟨b.val * qs.length + c.val, by
    rw [rectangle_length]
    have h := (finProdFinEquiv (b, c)).isLt
    change c.val + qs.length * b.val < ws.length * qs.length at h
    nlinarith⟩

theorem rectangle_get (ws qs : List ℕ) (b : Fin ws.length) (c : Fin qs.length) :
    (rectangleWidths ws qs).get (rectangleIndex ws qs b c) = ws.get b * qs.get c := by
  induction ws with
  | nil => exact Fin.elim0 b
  | cons q ws ih =>
    refine Fin.cases ?_ (fun b => ?_) b
    · simp only [rectangleWidths, List.flatMap_cons, rectangleIndex, Fin.val_zero, Nat.zero_mul,
        Nat.zero_add, List.get_eq_getElem]
      rw [List.getElem_append_left (by simpa only [List.length_map] using c.isLt)]
      simp
    · simp only [rectangleWidths, List.flatMap_cons, rectangleIndex, Fin.val_succ, List.get_eq_getElem]
      rw [List.getElem_append_right (by simp only [List.length_map]; nlinarith)]
      have he : (b.val + 1) * qs.length + c.val - (qs.map (fun x => q * x)).length = b.val * qs.length + c.val := by
        simp only [List.length_map, Nat.add_mul, Nat.one_mul]; omega
      simp only [he]
      exact ih b

theorem rectangle_before (ws qs : List ℕ) (b : Fin ws.length) (c : Fin qs.length) :
    blockBefore (rectangleWidths ws qs) (rectangleIndex ws qs b c) =
      blockBefore ws b * qs.sum + ws.get b * blockBefore qs c := by
  induction ws with
  | nil => exact Fin.elim0 b
  | cons q ws ih =>
    refine Fin.cases ?_ (fun b => ?_) b
    · simp only [blockBefore, rectangleWidths, List.flatMap_cons, rectangleIndex, Fin.val_zero,
        Nat.zero_mul, Nat.zero_add, List.take_zero, List.sum_nil, List.get_cons_zero]
      rw [List.take_append_of_le_length (by simpa only [List.length_map] using c.isLt.le), ← List.map_take, scaled_sum]
    · have he : (b.val + 1) * qs.length + c.val = (qs.map (fun x => q * x)).length + (b.val * qs.length + c.val) := by
        simp only [List.length_map]; ring
      simp only [blockBefore, rectangleWidths, List.flatMap_cons, rectangleIndex, Fin.val_succ,
        List.take_succ_cons, List.sum_cons]
      rw [he, List.take_length_add_append, List.sum_append, scaled_sum]
      have ht := ih b
      unfold blockBefore rectangleIndex at ht
      change (List.take (b.val * qs.length + c.val) (rectangleWidths ws qs)).sum = _ at ht
      change q * qs.sum + (List.take (b.val * qs.length + c.val) (rectangleWidths ws qs)).sum = _
      rw [ht]
      change q * qs.sum + (blockBefore ws b * qs.sum + ws.get b * blockBefore qs c) =
        (q + blockBefore ws b) * qs.sum + ws.get b * blockBefore qs c
      ring

def sectorWidths : List Axis → List ℕ
  | [] => [1]
  | a :: axes => rectangleWidths a.widths (sectorWidths axes)

theorem sectorWidths_length (axes : List Axis) : (sectorWidths axes).length = (blockCounts axes).prod := by
  induction axes with
  | nil => rfl
  | cons a axes ih => rw [sectorWidths, rectangle_length, ih]; rfl

theorem sectorWidths_sum (axes : List Axis) : (sectorWidths axes).sum = (radices axes).prod := by
  induction axes with
  | nil => rfl
  | cons a axes ih => rw [sectorWidths, rectangle_sum, ih]; rfl

def sectorIndex (axes : List Axis) (b : BlockChoices axes) : Fin (sectorWidths axes).length :=
  Fin.cast (sectorWidths_length axes).symm (mixedEquiv (blockCounts axes) b)

theorem sectorIndex_cons (a : Axis) (axes : List Axis) (b : Fin a.widths.length) (bs : BlockChoices axes) :
    sectorIndex (a :: axes) (b, bs) = rectangleIndex a.widths (sectorWidths axes) b (sectorIndex axes bs) := by
  apply Fin.ext
  change (mixedEquiv (blockCounts axes) bs).val + (blockCounts axes).prod * b.val =
    b.val * (sectorWidths axes).length + (mixedEquiv (blockCounts axes) bs).val
  rw [sectorWidths_length]
  ring

def sectorStart : (axes : List Axis) → BlockChoices axes → ℕ
  | [], _ => 0
  | a :: axes, (b, bs) => blockBefore a.widths b * (radices axes).prod + a.widths.get b * sectorStart axes bs

theorem sectorWidths_get (axes : List Axis) (b : BlockChoices axes) :
    (sectorWidths axes).get (sectorIndex axes b) = (sectorRadices axes b).prod := by
  induction axes with
  | nil => rfl
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    have hidx := sectorIndex_cons a axes b bs
    have hget := congrArg (fun i : Fin (sectorWidths (a :: axes)).length => (sectorWidths (a :: axes)).get i) hidx
    have hrect := rectangle_get a.widths (sectorWidths axes) b (sectorIndex axes bs)
    exact hget.trans (hrect.trans (congrArg (fun x => a.widths.get b * x) (ih bs)))

theorem sectorStart_before (axes : List Axis) (b : BlockChoices axes) :
    blockBefore (sectorWidths axes) (sectorIndex axes b) = sectorStart axes b := by
  induction axes with
  | nil => rfl
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    have hidx := sectorIndex_cons a axes b bs
    have hget := congrArg (fun i : Fin (sectorWidths (a :: axes)).length => blockBefore (sectorWidths (a :: axes)) i) hidx
    have hrect := rectangle_before a.widths (sectorWidths axes) b (sectorIndex axes bs)
    exact hget.trans (hrect.trans (congrArg₂ (fun x y => x + y)
      (congrArg (fun x => blockBefore a.widths b * x) (sectorWidths_sum axes))
      (congrArg (fun x => a.widths.get b * x) (ih bs))))

def sectorIndexEquiv (axes : List Axis) : BlockChoices axes ≃ Fin (sectorWidths axes).length :=
  (mixedEquiv (blockCounts axes)).trans (finCongr (sectorWidths_length axes).symm)

def sectorFiberEquiv (axes : List Axis) (b : BlockChoices axes) :
    Positions axes b ≃ Fin ((sectorWidths axes).get (sectorIndex axes b)) :=
  (mixedEquiv (sectorRadices axes b)).trans (finCongr (sectorWidths_get axes b).symm)

def indexedSectorEquiv (axes : List Axis) : SectorPosition axes ≃ BlockPosition (sectorWidths axes) :=
  Equiv.sigmaCongr (sectorIndexEquiv axes) (sectorFiberEquiv axes)

/-- Canonical order: lexicographic block choices, then lexicographic internal positions. -/
def packedEquiv (axes : List Axis) : SectorPosition axes ≃ Fin (radices axes).prod :=
  (indexedSectorEquiv axes).trans ((blockEquiv (sectorWidths axes)).trans (finCongr (sectorWidths_sum axes)))

theorem packedEquiv_value (axes : List Axis) (x : SectorPosition axes) :
    (packedEquiv axes x).val = sectorStart axes x.1 + encode (sectorRadices axes x.1) x.2 := by
  change blockBefore (sectorWidths axes) (sectorIndex axes x.1) +
    (mixedEquiv (sectorRadices axes x.1) x.2).val = _
  exact congrArg₂ (fun a b => a + b) (sectorStart_before axes x.1) (mixedEquiv_value _ x.2)

/-- The actual permutation and its inverse, derived from local tables and explicit codecs. -/
def packingPermutation (axes : List Axis) : Equiv.Perm (Fin (radices axes).prod) :=
  (originalEquiv axes).symm.trans (packedEquiv axes)
def unpackingPermutation (axes : List Axis) := (packingPermutation axes).symm

theorem packingPermutation_original (axes : List Axis) (x : SectorPosition axes) :
    packingPermutation axes (originalEquiv axes x) = packedEquiv axes x := by
  exact congrArg (packedEquiv axes) ((originalEquiv axes).symm_apply_apply x)

theorem packingPermutation_bijective (axes : List Axis) : Function.Bijective (packingPermutation axes) :=
  (packingPermutation axes).bijective

theorem unpacking_packing (axes : List Axis) (i : Fin (radices axes).prod) :
    unpackingPermutation axes (packingPermutation axes i) = i := (packingPermutation axes).symm_apply_apply i

theorem packing_unpacking (axes : List Axis) (i : Fin (radices axes).prod) :
    packingPermutation axes (unpackingPermutation axes i) = i := (packingPermutation axes).apply_symm_apply i

def sectorCoordinate (axes : List Axis) (b : BlockChoices axes) (i : Fin (sectorRadices axes b).prod) :
    Fin (radices axes).prod := packedEquiv axes ⟨b, (mixedEquiv (sectorRadices axes b)).symm i⟩

theorem sectorCoordinate_value (axes : List Axis) (b : BlockChoices axes) (i : Fin (sectorRadices axes b).prod) :
    (sectorCoordinate axes b i).val = sectorStart axes b + i.val := by
  have h := mixedEquiv_value (sectorRadices axes b) ((mixedEquiv (sectorRadices axes b)).symm i)
  have he : encode (sectorRadices axes b) ((mixedEquiv (sectorRadices axes b)).symm i) = i.val :=
    h.symm.trans (congrArg Fin.val ((mixedEquiv (sectorRadices axes b)).apply_symm_apply i))
  exact (packedEquiv_value axes ⟨b, _⟩).trans (congrArg (fun a => sectorStart axes b + a) he)

theorem sectorCoordinate_injective (axes : List Axis) (b : BlockChoices axes) :
    Function.Injective (sectorCoordinate axes b) := by
  intro i j hij
  have h := congrArg Fin.val hij
  rw [sectorCoordinate_value, sectorCoordinate_value] at h
  exact Fin.ext (Nat.add_left_cancel h)

theorem sectors_disjoint (axes : List Axis) (b c : BlockChoices axes)
    (i : Fin (sectorRadices axes b).prod) (j : Fin (sectorRadices axes c).prod)
    (h : sectorCoordinate axes b i = sectorCoordinate axes c j) : b = c :=
  congrArg Sigma.fst ((packedEquiv axes).injective h)

theorem sectors_cover (axes : List Axis) (j : Fin (radices axes).prod) :
    ∃ b : BlockChoices axes, ∃ i : Fin (sectorRadices axes b).prod, sectorCoordinate axes b i = j := by
  let x := (packedEquiv axes).symm j
  refine ⟨x.1, mixedEquiv (sectorRadices axes x.1) x.2, ?_⟩
  simp only [sectorCoordinate, Equiv.symm_apply_apply]
  exact (packedEquiv axes).apply_symm_apply j

/-- Each sector is exactly its contiguous half-open interval. -/
theorem sector_interval (axes : List Axis) (b : BlockChoices axes) (j : Fin (radices axes).prod) :
    (∃ i : Fin (sectorRadices axes b).prod, sectorCoordinate axes b i = j) ↔
      sectorStart axes b ≤ j.val ∧ j.val < sectorStart axes b + (sectorRadices axes b).prod := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [sectorCoordinate_value]
    have hi := i.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨j.val - sectorStart axes b, by omega⟩, ?_⟩
    apply Fin.ext
    rw [sectorCoordinate_value]
    change sectorStart axes b + (j.val - sectorStart axes b) = j.val
    omega

def packingDigits : (axes : List Axis) → SectorPosition axes → List PackingDigit
  | [], _ => []
  | a :: axes, ⟨(b, bs), (t, ts)⟩ =>
    blockDigit a.widths b t (radices axes).prod a.originalPermutation :: packingDigits axes ⟨bs, ts⟩

theorem packingDigits_products (axes : List Axis) (x : SectorPosition axes) :
    digitProduct (packingDigits axes x) = (radices axes).prod ∧
      blockProduct (packingDigits axes x) = (sectorRadices axes x.1).prod := by
  induction axes with
  | nil => exact ⟨rfl, rfl⟩
  | cons a axes ih =>
    rcases x with ⟨⟨b, bs⟩, ⟨t, ts⟩⟩
    have ht := ih ⟨bs, ts⟩
    simp only [packingDigits, digitProduct, blockProduct, List.map_cons, List.prod_cons, blockDigit]
    exact ⟨congrArg (fun x => a.widths.sum * x) ht.1, congrArg (fun x => a.widths.get b * x) ht.2⟩

theorem packingDigits_addresses (axes : List Axis) (x : SectorPosition axes) :
    startContribution (packingDigits axes x) = sectorStart axes x.1 ∧
      withinAddress (packingDigits axes x) = encode (sectorRadices axes x.1) x.2 ∧
        originalAddress (packingDigits axes x) = (originalEquiv axes x).val := by
  induction axes with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a axes ih =>
    rcases x with ⟨⟨b, bs⟩, ⟨t, ts⟩⟩
    obtain ⟨hS, ho, hI⟩ := ih ⟨bs, ts⟩
    obtain ⟨hR, hQ⟩ := packingDigits_products axes ⟨bs, ts⟩
    constructor
    · exact congrArg (fun z => blockBefore a.widths b * (radices axes).prod + a.widths.get b * z) hS
    constructor
    · exact congrArg₂ (fun z y => t.val * z + y) hQ ho
    · change (a.originalPermutation (blockEncode a.widths ⟨b, t⟩)).val *
        digitProduct (packingDigits axes ⟨bs, ts⟩) + originalAddress (packingDigits axes ⟨bs, ts⟩) =
        (originalEquiv (a :: axes) ⟨(b, bs), (t, ts)⟩).val
      have htail := congrArg₂ (fun z y => (a.originalPermutation (blockEncode a.widths ⟨b, t⟩)).val * z + y) hR hI
      exact htail.trans (by change _ = (originalEquiv axes ⟨bs, ts⟩).val +
        (radices axes).prod * (a.originalPermutation (blockEncode a.widths ⟨b, t⟩)).val; ring)

theorem packingDigits_valid (axes : List Axis) (x : SectorPosition axes) : ValidPacking (packingDigits axes x) := by
  induction axes with
  | nil => trivial
  | cons a axes ih =>
    rcases x with ⟨⟨b, bs⟩, ⟨t, ts⟩⟩
    obtain ⟨hpq, ht, ha⟩ := blockDigit_valid a.widths b t (radices axes).prod a.originalPermutation
    exact ⟨(packingDigits_products axes ⟨bs, ts⟩).1.symm, hpq, ht, ha, ih ⟨bs, ts⟩⟩

/-- The permutation's image is exactly the actual traversal's computed `S+o`. -/
theorem packingFollow_permutation (axes : List Axis) (x : SectorPosition axes) :
    let s := packingFollow (packingDigits axes x) initialPacking
    s.original = (originalEquiv axes x).val ∧
      s.start + s.offset = (packingPermutation axes (originalEquiv axes x)).val ∧
        s.width = (sectorRadices axes x.1).prod := by
  obtain ⟨hS, ho, hI⟩ := packingDigits_addresses axes x
  obtain ⟨hR, hQ⟩ := packingDigits_products axes x
  obtain ⟨fS, fQ, fo, fI⟩ := initialPacking_formulas (packingDigits axes x)
  constructor
  · exact fI.trans hI
  constructor
  · rw [fS, fo, hS, ho, packingPermutation_original]
    exact (packedEquiv_value axes x).symm
  · exact fQ.trans hQ

theorem sectorRadices_one_two (axes : List Axis) (b : BlockChoices axes) :
    ∀ q ∈ sectorRadices axes b, q = 1 ∨ q = 2 := by
  induction axes with
  | nil => simp [sectorRadices]
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · exact hq ▸ a.widths_one_two (a.widths.get b) (List.get_mem _ _)
    · exact ih bs q hq

theorem sectorRadices_length (axes : List Axis) (b : BlockChoices axes) :
    (sectorRadices axes b).length = axes.length := by
  induction axes with
  | nil => rfl
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    exact congrArg Nat.succ (ih bs)

def sectorPairCount (axes : List Axis) (b : BlockChoices axes) : ℕ :=
  (sectorRadices axes b).countP (fun q => q == 2)

theorem widths_product_pow (ws : List ℕ) (hw : ∀ q ∈ ws, q = 1 ∨ q = 2) :
    ws.prod = 2 ^ (ws.countP (fun q => q == 2)) := by
  induction ws with
  | nil => simp
  | cons q ws ih =>
    have ht := ih (fun a ha => hw a (by simp [ha]))
    rcases hw q (by simp) with h | h <;> simp [h, ← ht, pow_succ, Nat.mul_comm]

theorem sectorWidth_pow_two (axes : List Axis) (b : BlockChoices axes) :
    (sectorRadices axes b).prod = 2 ^ sectorPairCount axes b :=
  widths_product_pow _ (sectorRadices_one_two axes b)

theorem sectorPairCount_le (axes : List Axis) (b : BlockChoices axes) : sectorPairCount axes b ≤ axes.length := by
  exact (List.countP_le_length).trans (sectorRadices_length axes b).le

def pairCounts (axes : List Axis) : List ℕ :=
  List.ofFn (fun i : Fin (sectorWidths axes).length => sectorPairCount axes ((sectorIndexEquiv axes).symm i))

theorem pairCounts_widths (axes : List Axis) : (pairCounts axes).map (fun k => 2 ^ k) = sectorWidths axes := by
  unfold pairCounts
  rw [← List.ofFn_comp']
  calc
    _ = List.ofFn (sectorWidths axes).get := by
      apply congrArg List.ofFn
      funext i
      let b := (sectorIndexEquiv axes).symm i
      have hi : sectorIndex axes b = i := (sectorIndexEquiv axes).apply_symm_apply i
      have he := congrArg (fun j => (sectorWidths axes).get j) hi
      exact ((he.symm.trans (sectorWidths_get axes b)).trans (sectorWidth_pow_two axes b)).symm
    _ = _ := List.ofFn_get _

theorem pairCounts_sum_widths (axes : List Axis) : (pairCounts axes |>.map (fun k => 2 ^ k)).sum = (radices axes).prod :=
  congrArg List.sum (pairCounts_widths axes) |>.trans (sectorWidths_sum axes)

theorem pairCounts_axes_bound (axes : List Axis) : ∀ k ∈ pairCounts axes, k ≤ axes.length := by
  intro k hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
  exact sectorPairCount_le axes _

/-- The actual canonical sector list discharges the geometry premises of the cost bound. -/
theorem actual_sector_cost_bound (axes : List Axis) :
    ((pairCounts axes).map UniformNetworkCost.singleCount).sum + 32 * (radices axes).prod ≤
      UniformNetworkCost.layerCount (radices axes).prod axes.length :=
  UniformNetworkCost.sector_partition_bound _ _ _ (pairCounts_axes_bound axes) (pairCounts_sum_widths axes)

structure BlockState where
  start : ℕ
  width : ℕ
  pairs : ℕ
  deriving Repr, DecidableEq

def initialBlockState : BlockState := ⟨0, 1, 0⟩

/-- Fixed-size prefix state, using the prepared suffix, preceding width and pair flag. -/
def blockAdvance (a : Axis) (suffix : ℕ) (b : Fin a.widths.length) (s : BlockState) : BlockState :=
  ⟨s.start + s.width * blockBefore a.widths b * suffix,
    s.width * a.widths.get b, s.pairs + if a.widths.get b = 2 then 1 else 0⟩

def blockLayers : List Axis → List (Layer BlockState)
  | [] => []
  | a :: axes => ⟨a.widths.length, blockAdvance a (radices axes).prod⟩ :: blockLayers axes

def blockTraversalEquiv : (axes : List Axis) → BlockChoices axes ≃ Choices (blockLayers axes)
  | [] => Equiv.refl _
  | a :: axes => Equiv.prodCongr (Equiv.refl (Fin a.widths.length)) (blockTraversalEquiv axes)

theorem blockLayers_radices (axes : List Axis) : UniformTraversal.radices (blockLayers axes) = blockCounts axes := by
  induction axes with
  | nil => rfl
  | cons a axes ih => exact congrArg (List.cons a.widths.length) ih

theorem follow_block_formulas (axes : List Axis) (b : BlockChoices axes) (s : BlockState) :
    let u := follow (blockLayers axes) (blockTraversalEquiv axes b) s
    u.start = s.start + s.width * sectorStart axes b ∧
      u.width = s.width * (sectorRadices axes b).prod ∧
        u.pairs = s.pairs + sectorPairCount axes b := by
  induction axes generalizing s with
  | nil => simp [blockLayers, blockTraversalEquiv, follow, sectorStart, sectorRadices, sectorPairCount]
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    obtain ⟨hS, hQ, hP⟩ := ih bs (blockAdvance a (radices axes).prod b s)
    change _ ∧ _ ∧ _
    constructor
    · exact hS.trans (by simp only [blockAdvance, sectorStart]; ring)
    constructor
    · exact hQ.trans (by simp only [blockAdvance, sectorRadices, List.prod_cons]; ring)
    · exact hP.trans (by simp [blockAdvance, sectorPairCount, sectorRadices, List.countP_cons]; omega)

/-- Preparation enumerates sectors by prefix extensions, maintaining the pair count.
    This counts visited nodes; a RAM realization of the whole traversal remains separate. -/
theorem block_traversal_prefix_bound (axes : List Axis) :
    (run (blockLayers axes) initialBlockState).visits < 2 * (radices axes).prod := by
  rw [run_visits, blockLayers_radices]
  have h := block_partition_prefix_bound (axes.map Axis.widths)
    (by
      intro ws hws q hq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hws
      rcases a.widths_one_two q hq with h | h <;> omega)
    (by
      intro r hr
      obtain ⟨ws, hws, rfl⟩ := List.mem_map.mp hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hws
      exact a.radix_two)
  simpa only [List.map_map, Function.comp_def, blockCounts, radices] using h

def expectedBlockState (axes : List Axis) (b : BlockChoices axes) : BlockState :=
  ⟨sectorStart axes b, (sectorRadices axes b).prod, sectorPairCount axes b⟩

theorem blockState_eq (s t : BlockState) (hS : s.start = t.start)
    (hQ : s.width = t.width) (hP : s.pairs = t.pairs) : s = t := by
  cases s; cases t; simp_all

theorem follow_block_initial (axes : List Axis) (b : BlockChoices axes) :
    follow (blockLayers axes) (blockTraversalEquiv axes b) initialBlockState = expectedBlockState axes b := by
  obtain ⟨hS, hQ, hP⟩ := follow_block_formulas axes b initialBlockState
  apply blockState_eq
  · simpa only [initialBlockState, expectedBlockState, Nat.one_mul, Nat.zero_add] using hS
  · simpa only [initialBlockState, expectedBlockState, Nat.one_mul] using hQ
  · simpa only [initialBlockState, expectedBlockState, Nat.zero_add] using hP

theorem generated_sector_states (axes : List Axis) (y : BlockState) :
    y ∈ (run (blockLayers axes) initialBlockState).output ↔ ∃ b : BlockChoices axes, expectedBlockState axes b = y := by
  rw [run_output_mem]
  constructor
  · rintro ⟨ds, hds⟩
    let b := (blockTraversalEquiv axes).symm ds
    have hfollow := congrArg (fun d => follow (blockLayers axes) d initialBlockState)
      ((blockTraversalEquiv axes).apply_symm_apply ds)
    exact ⟨b, (follow_block_initial axes b).symm.trans (hfollow.trans hds)⟩
  · rintro ⟨b, hb⟩
    exact ⟨blockTraversalEquiv axes b, (follow_block_initial axes b).trans hb⟩

theorem generated_sector_count (axes : List Axis) :
    (run (blockLayers axes) initialBlockState).output.length = (sectorWidths axes).length := by
  rw [run_length, blockLayers_radices, sectorWidths_length]

theorem sectorProduct_pos (axes : List Axis) (b : BlockChoices axes) : 0 < (sectorRadices axes b).prod := by
  induction axes with
  | nil => norm_num [sectorRadices]
  | cons a axes ih =>
    rcases b with ⟨b, bs⟩
    have hq : 0 < a.widths.get b := by
      rcases a.widths_one_two (a.widths.get b) (List.get_mem _ _) with h | h <;> omega
    exact Nat.mul_pos hq (ih bs)

theorem expectedBlockState_injective (axes : List Axis) : Function.Injective (expectedBlockState axes) := by
  intro b c h
  have hS := congrArg BlockState.start h
  have hi : (sectorCoordinate axes b ⟨0, sectorProduct_pos axes b⟩).val =
      (sectorCoordinate axes c ⟨0, sectorProduct_pos axes c⟩).val := by
    rw [sectorCoordinate_value, sectorCoordinate_value]
    simpa only [expectedBlockState, Nat.add_zero] using hS
  exact sectors_disjoint axes b c _ _ (Fin.ext hi)

def sectorStates (axes : List Axis) : List BlockState :=
  List.ofFn (fun i : Fin (sectorWidths axes).length => expectedBlockState axes ((sectorIndexEquiv axes).symm i))

theorem sectorStates_nodup (axes : List Axis) : (sectorStates axes).Nodup :=
  List.nodup_ofFn_ofInjective ((expectedBlockState_injective axes).comp (sectorIndexEquiv axes).symm.injective)

theorem generated_states_finset (axes : List Axis) :
    (run (blockLayers axes) initialBlockState).output.toFinset = (sectorStates axes).toFinset := by
  ext y
  simp only [List.mem_toFinset, generated_sector_states, sectorStates, List.mem_ofFn]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨sectorIndexEquiv axes b, ?_⟩
    exact (congrArg (expectedBlockState axes) ((sectorIndexEquiv axes).symm_apply_apply b)).trans hb
  · rintro ⟨i, hi⟩
    exact ⟨(sectorIndexEquiv axes).symm i, hi⟩

/-- Every sector is enumerated once, with its start, width and pair count in running state. -/
theorem generated_sector_states_nodup (axes : List Axis) :
    (run (blockLayers axes) initialBlockState).output.Nodup := by
  have hc : (run (blockLayers axes) initialBlockState).output.toFinset.card =
      (run (blockLayers axes) initialBlockState).output.length := by
    rw [generated_states_finset, List.toFinset_card_of_nodup (sectorStates_nodup axes), generated_sector_count]
    exact List.length_ofFn
  exact (Multiset.toFinset_card_eq_card_iff_nodup
    (m := ((run (blockLayers axes) initialBlockState).output : Multiset BlockState))).mp hc

def packArray {α : Type*} (axes : List Axis) (x : Fin (radices axes).prod → α) :=
  fun i => x (unpackingPermutation axes i)
def unpackArray {α : Type*} (axes : List Axis) (x : Fin (radices axes).prod → α) :=
  fun i => x (packingPermutation axes i)

theorem unpack_pack_array {α : Type*} (axes : List Axis) (x : Fin (radices axes).prod → α) :
    unpackArray axes (packArray axes x) = x := by
  funext i
  exact congrArg x (unpacking_packing axes i)

theorem pack_unpack_array {α : Type*} (axes : List Axis) (x : Fin (radices axes).prod → α) :
    packArray axes (unpackArray axes x) = x := by
  funext i
  exact congrArg x (packing_unpacking axes i)

theorem sectorStart_paper_sum (axes : List Axis) (x : SectorPosition axes) :
    sectorStart axes x.1 = (startSummands (packingDigits axes x)).sum :=
  (packingDigits_addresses axes x).1.symm.trans (startContribution_eq_sum _)

end ExactFourierCircuits.UniformSectorPacking
