import DFTModelCacheRectanglePreparationSource
import DFTModelCacheSelectedPhysicalRowsNative
import UniformLocalCacheSlotHeaderMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectangleMetadata
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section

/-- The actual native producer replaces the five descriptor fields only. -/
def actual (q : Row) (original : UniformSeedHeightPreparation.Config) :=
  UniformLocalRectangleBankMachine.geometry q original

def kernel (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :=
  (UniformSeedHeightPreparation.parameters n j (actual q original)).base.rank

/-- Reuse ordinary workspace addresses, deriving height and gate geometry
from the same descriptor as the rank kernel. -/
def header (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) :=
  {c with height := (actual q original).height, gates := (actual q original).gates}

def forward (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :=
  UniformLocalCacheSlotHeaderMachine.forward (header q original c) q slot

def chunk (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :=
  (forward q original c slot).chunk

theorem kernel_fields (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :
    (kernel n j q original).H = UniformSeedRankCrossPreparation.hBase n j ∧
    (kernel n j q original).G = UniformSeedRankCrossPreparation.gBase n j ∧
    (kernel n j q original).hSize = radix n j ∧
    (kernel n j q original).gSize = radix n j ∧
    (kernel n j q original).a = q.a ∧ (kernel n j q original).e = q.e ∧
    (kernel n j q original).i0 = q.i0 ∧ (kernel n j q original).j0 = q.j0 ∧
    (kernel n j q original).split = q.split ∧
    (kernel n j q original).N = DFTModelCacheRectanglePreparation.width q ∧
    (kernel n j q original).S = original.S := by
  repeat' apply And.intro
  all_goals rfl

theorem metadata_eq (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :
    DFTModelCacheDisplacement.metadata (radix n j) (kernel n j q original) =
      DFTModelCacheDisplacement.metadata (radix n j)
        (DFTModelCacheRectanglePreparation.parameters (radix n j) q) := rfl

theorem producer_fields (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.K =
      DFTModelCacheRectanglePreparation.height q ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.D =
      UniformMasterRootMachine.order n ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.A = original.A ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.d = original.d ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.C = original.C ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.conv = original.conv ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.tape = original.tape ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).base.depth = original.depth ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).order = original.order ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).directory = original.directory ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).negative = original.negative ∧
    (UniformSeedHeightPreparation.parameters n j (actual q original)).constants = original.constants := by
  repeat' apply And.intro
  all_goals rfl

theorem chunk_fields (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (chunk q original c slot).radix = q.width ∧
    (chunk q original c slot).source = q.j0 ∧
    (chunk q original c slot).target = q.i0 ∧
    (chunk q original c slot).height.K = DFTModelCacheRectanglePreparation.height q ∧
    (chunk q original c slot).height.a = q.a ∧
    (chunk q original c slot).height.e = q.e ∧
    (chunk q original c slot).height.enabled = slot.enabled ∧
    (chunk q original c slot).height.C = original.C ∧
    (chunk q original c slot).height.P = original.constants ∧
    (chunk q original c slot).depth = slot.depth ∧
    (chunk q original c slot).color = slot.color := by
  repeat' apply And.intro
  all_goals rfl

theorem chunk_gates (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    UniformCrossHeightPreparationMachine.gates (chunk q original c slot).height =
      UniformWorkspacePlanner.gateCount q.a q.e := by
  rw [UniformWorkspacePlanner.gateCount_eq]
  change 6 * (3 * UniformWorkspacePlanner.exponent q.a q.e *
    UniformRadixTwoDAG.width (UniformWorkspacePlanner.exponent q.a q.e) +
    2 * UniformRadixTwoDAG.width (UniformWorkspacePlanner.exponent q.a q.e)) + 2*q.a = _
  rw [UniformRadixTwoDAG.width_eq]

theorem chunk_height (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (chunk q original c slot).height =
      {(actual q original).height with
        D := if slot.enabled then original.rows else c.falseRows
        F := if slot.enabled then original.colors else c.falseColors
        U := if slot.enabled then original.palette else c.falsePalette
        J := if slot.enabled then original.heightDirectory else c.falseDirectory
        enabled := slot.enabled} := rfl

theorem chunk_addresses (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (chunk q original c slot).borrowed = c.borrowed ∧
    (chunk q original c slot).selected = c.selected ∧
    (chunk q original c slot).ordinals = c.ordinals ∧
    (chunk q original c slot).mapped = c.mapped ∧
    (chunk q original c slot).permutation = c.permutation ∧
    (chunk q original c slot).widths = c.widths ∧
    (chunk q original c slot).markers = c.markers ∧
    (chunk q original c slot).axis = c.axis := by
  repeat' apply And.intro
  all_goals rfl

theorem chunk_geometry (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    DFTModelCacheSelectedPhysicalRows.chunkGeometry (chunk q original c slot) =
      DFTModelCacheSelectedPhysicalRows.geom q.width q.j0 q.e q.i0 q.a
        (UniformWorkspacePlanner.gateCount q.a q.e) := by
  unfold DFTModelCacheSelectedPhysicalRows.chunkGeometry
    DFTModelCacheSelectedPhysicalRows.rowGeometry
    UniformChunkMatchingPreparation.rowParameters
  rw [chunk_gates]
  rfl

/-- Offset is applied by the later native translated-row stage. The local
matching radix and the final ambient factor-pool radix remain distinct. -/
theorem placement_fields (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (forward q original c slot).offset = q.offset ∧
    (forward q original c slot).ambient = c.ambient ∧
    (forward q original c slot).pool = c.pool ∧
    (forward q original c slot).translated = c.translated ∧
    (forward q original c slot).negative = c.negative ∧
    (forward q original c slot).conjugates = c.conjugates := by
  repeat' apply And.intro
  all_goals rfl

end
end ExactFourierCircuits.DFTModelCacheRectangleMetadata
