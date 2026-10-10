import UniformSectorTraversalOrder

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelNativeSectorRecurrence

open UniformTraversal UniformSectorPacking UniformSectorTraversalOrder

/-- Transport a suffix sector through an already accumulated prefix. -/
def affineState (s t : BlockState) : BlockState :=
  ⟨s.start + s.width * t.start, s.width * t.width, s.pairs + t.pairs⟩

theorem follow_affine (axes : List Axis) (b : BlockChoices axes) (s : BlockState) :
    follow (blockLayers axes) (blockTraversalEquiv axes b) s =
      affineState s (expectedBlockState axes b) := by
  obtain ⟨hs, hw, hp⟩ := follow_block_formulas axes b s
  exact blockState_eq _ _ hs hw hp

theorem lexOutcomes_affine (axes : List Axis) (s : BlockState) :
    lexOutcomes (blockLayers axes) s = (sectorStates axes).map (affineState s) := by
  rw [← block_lex_sectorStates, block_lex_ofFn, block_lex_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change follow (blockLayers axes)
    (blockTraversalEquiv axes ((mixedEquiv (blockCounts axes)).symm i)) s =
      affineState s (follow (blockLayers axes)
        (blockTraversalEquiv axes ((mixedEquiv (blockCounts axes)).symm i)) initialBlockState)
  rw [follow_block_initial, follow_affine]

/-- One local block followed by a suffix sector, in the native first-axis order. -/
def extendSector (a : Axis) (axes : List Axis) (b : Fin a.widths.length)
    (t : BlockState) : BlockState :=
  ⟨blockBefore a.widths b * (UniformSectorPacking.radices axes).prod +
      a.widths.get b * t.start,
    a.widths.get b * t.width,
    (if a.widths.get b = 2 then 1 else 0) + t.pairs⟩

theorem sectorStates_cons (a : Axis) (axes : List Axis) :
    sectorStates (a :: axes) =
      (List.finRange a.widths.length).flatMap
        (fun b => (sectorStates axes).map (extendSector a axes b)) := by
  rw [← block_lex_sectorStates]
  change (List.finRange a.widths.length).flatMap (fun b =>
    lexOutcomes (blockLayers axes)
      (blockAdvance a (UniformSectorPacking.radices axes).prod b initialBlockState)) = _
  simp_rw [lexOutcomes_affine]
  congr 1
  funext b
  apply congrArg (fun f => (sectorStates axes).map f)
  funext t
  apply blockState_eq <;>
    simp only [affineState, blockAdvance, initialBlockState, extendSector,
      Nat.one_mul, Nat.zero_add]

/-- Prepend one decoded local block position to a suffix position. -/
def prepend (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) : SectorPosition (a :: axes) :=
  ⟨(u.1, x.1), (u.2, x.2)⟩

theorem width_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    (sectorRadices (a :: axes) (prepend a axes u x).1).prod =
      a.widths.get u.1 * (sectorRadices axes x.1).prod := rfl

theorem start_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    sectorStart (a :: axes) (prepend a axes u x).1 =
      blockBefore a.widths u.1 * (UniformSectorPacking.radices axes).prod +
        a.widths.get u.1 * sectorStart axes x.1 := rfl

theorem offset_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    encode (sectorRadices (a :: axes) (prepend a axes u x).1)
        (prepend a axes u x).2 =
      u.2.val * (sectorRadices axes x.1).prod +
        encode (sectorRadices axes x.1) x.2 := rfl

theorem pairs_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    sectorPairCount (a :: axes) (prepend a axes u x).1 =
      (if a.widths.get u.1 = 2 then 1 else 0) + sectorPairCount axes x.1 := by
  simp [sectorPairCount, sectorRadices, prepend, List.countP_cons, Nat.add_comm]

theorem original_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    (originalEquiv (a :: axes) (prepend a axes u x)).val =
      (a.originalPermutation (blockEncode a.widths u)).val *
          (UniformSectorPacking.radices axes).prod +
        (originalEquiv axes x).val := by
  change (originalEquiv axes x).val + (UniformSectorPacking.radices axes).prod *
      (a.originalPermutation (blockEncode a.widths u)).val = _
  ring

theorem packed_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    (packedEquiv (a :: axes) (prepend a axes u x)).val =
      (blockBefore a.widths u.1 * (UniformSectorPacking.radices axes).prod +
        a.widths.get u.1 * sectorStart axes x.1) +
      (u.2.val * (sectorRadices axes x.1).prod +
        encode (sectorRadices axes x.1) x.2) := by
  rw [packedEquiv_value, start_cons, offset_cons]

abbrev AddressValue := Nat × (Nat × (Nat × Nat))

/-- The native width/start/offset/original tuple; no runtime computation is assumed. -/
def addressValue (axes : List Axis) (x : SectorPosition axes) : AddressValue :=
  ((sectorRadices axes x.1).prod,
    (sectorStart axes x.1,
      (encode (sectorRadices axes x.1) x.2, (originalEquiv axes x).val)))

theorem addressValue_cons (a : Axis) (axes : List Axis) (u : BlockPosition a.widths)
    (x : SectorPosition axes) :
    addressValue (a :: axes) (prepend a axes u x) =
      (a.widths.get u.1 * (addressValue axes x).1,
        (blockBefore a.widths u.1 * (UniformSectorPacking.radices axes).prod +
            a.widths.get u.1 * (addressValue axes x).2.1,
          (u.2.val * (addressValue axes x).1 + (addressValue axes x).2.2.1,
            (a.originalPermutation (blockEncode a.widths u)).val *
                (UniformSectorPacking.radices axes).prod +
              (addressValue axes x).2.2.2))) := by
  unfold addressValue
  rw [width_cons, start_cons, offset_cons, original_cons]

theorem addressValue_decode_cons (a : Axis) (axes : List Axis)
    (j : Fin a.widths.sum) (x : SectorPosition axes) :
    addressValue (a :: axes) (prepend a axes (blockDecode a.widths j) x) =
      (a.widths.get (blockDecode a.widths j).1 * (addressValue axes x).1,
        (blockBefore a.widths (blockDecode a.widths j).1 *
              (UniformSectorPacking.radices axes).prod +
            a.widths.get (blockDecode a.widths j).1 * (addressValue axes x).2.1,
          ((blockDecode a.widths j).2.val * (addressValue axes x).1 +
              (addressValue axes x).2.2.1,
            (a.originalPermutation j).val * (UniformSectorPacking.radices axes).prod +
              (addressValue axes x).2.2.2))) := by
  rw [addressValue_cons, blockEncode_decode]

end ExactFourierCircuits.DFTModelNativeSectorRecurrence
