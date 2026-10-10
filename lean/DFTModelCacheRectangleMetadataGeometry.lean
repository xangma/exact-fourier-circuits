import DFTModelCacheRectangleMetadataCore
import DFTModelCacheTopologyPrepare

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleMetadata
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section

/-- The true nonempty descriptor supplies bounds in its physical subtree,
including the gate/port fit required by the borrowed-coordinate mapper. -/
theorem produced_local {r : ℕ} {q : Row}
    (source : DFTModelCacheRectanglePreparation.ProducedRow r q) :
    2 ≤ q.width ∧ 0 < q.a ∧ 0 < q.e ∧
    q.i0 + q.a ≤ q.width ∧ q.split < q.width ∧ q.split ≤ q.i0 ∧
    q.j0 + q.e ≤ q.split ∧
    UniformWorkspacePlanner.gateCount q.a q.e + q.a + q.e ≤ q.width ∧
    q.width ≤ r := by
  obtain ⟨v,o,vr,hq⟩ := source
  unfold UniformLocalCacheTreeCoverage.currentRows at hq
  dsimp only [UniformLocalCacheTreeMachine.Task.width] at hq
  split_ifs at hq with empty
  · simp only [List.not_mem_nil] at hq
  · have hv : 0 < UniformWorkspacePlanner.selected v := by omega
    have vn : 2 ≤ v := by omega
    obtain ⟨ha,he,hi,hs,hsi,hj,hfit,hw,_⟩ :=
      UniformLocalRectangleBankMachine.rows_geometry v o q vn hv hq
    exact ⟨hw ▸ vn,ha,he,hw ▸ hi,hw ▸ hs,hsi,hj,hw ▸ hfit,hw.le.trans vr⟩

theorem chunk_computed (q : Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (chunk q original c slot).height.K = DFTModelCacheTopology.exponent q.a q.e := rfl

theorem chunk_widths {r : ℕ} {q : Row}
    (source : DFTModelCacheRectanglePreparation.ProducedRow r q)
    (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    (chunk q original c slot).height.a ≤
      UniformCrossHeightPreparationMachine.widthOf (chunk q original c slot).height ∧
    (chunk q original c slot).height.e ≤
      UniformCrossHeightPreparationMachine.widthOf (chunk q original c slot).height := by
  exact ⟨(DFTModelCacheRectanglePreparation.produced_width source).1,
    (DFTModelCacheRectanglePreparation.produced_width source).2.1⟩

theorem chunk_fit {r : ℕ} {q : Row}
    (source : DFTModelCacheRectanglePreparation.ProducedRow r q)
    (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    UniformCrossHeightPreparationMachine.gates (chunk q original c slot).height +
      (chunk q original c slot).height.e + (chunk q original c slot).height.a ≤
        (chunk q original c slot).radix := by
  rw [chunk_gates]
  have fit := (produced_local source).2.2.2.2.2.2.2.1
  change UniformWorkspacePlanner.gateCount q.a q.e + q.e + q.a ≤ q.width
  omega

theorem chunk_ranges {r : ℕ} {q : Row}
    (source : DFTModelCacheRectanglePreparation.ProducedRow r q)
    (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot) :
    2 ≤ (chunk q original c slot).radix ∧
    (chunk q original c slot).source + (chunk q original c slot).height.e ≤
      (chunk q original c slot).radix ∧
    (chunk q original c slot).target + (chunk q original c slot).height.a ≤
      (chunk q original c slot).radix ∧
    (chunk q original c slot).source + (chunk q original c slot).height.e ≤
      (chunk q original c slot).target := by
  obtain ⟨hw,_,_,hi,hs,hsi,hj,_,_⟩ := produced_local source
  exact ⟨hw,hj.trans hs.le,hi,hj.trans hsi⟩

theorem kernel_shape (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config)
    (source : DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q) :
    DFTModelCacheDisplacement.Shape (kernel n j q original) (radix n j) := by
  obtain ⟨ha,he,hi,hs,hsi,hj,wa,we⟩ :=
    DFTModelCacheRectanglePreparation.produced_shape source
  exact ⟨ha,he,hi,hs,hsi,hj,wa,we⟩

theorem kernel_width (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :
    (kernel n j q original).N = UniformRadixTwoDAG.width
      ((actual q original).exponent) := rfl

end
end ExactFourierCircuits.DFTModelCacheRectangleMetadata
