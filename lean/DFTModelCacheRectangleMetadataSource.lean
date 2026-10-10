import DFTModelCacheRectangleMetadataGeometry
import DFTModelCacheSpectrumConjugateSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleMetadata
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem selected_divisors (n : ℕ) (hn : 0<n) (j : Fin (axisCount n)) (q : Row)
    (source : DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q) :
    0 < UniformMasterRootMachine.order n ∧
    radix n j ∣ UniformMasterRootMachine.order n ∧
    DFTModelCacheRectanglePreparation.width q ∣ UniformMasterRootMachine.order n ∧
    4 ∣ UniformMasterRootMachine.order n := by
  have master := DFTModelCacheRectanglePreparation.selected_master n hn j
  refine ⟨master.positive,master.radixDiv,
    DFTModelCacheRectanglePreparation.produced_divisor source master,?_⟩
  have small : 2^2 ∣ 2^(Nat.clog 2 (radix n j)+2) := pow_dvd_pow 2 (by omega)
  exact (show 4 ∣ 2^(Nat.clog 2 (radix n j)+2) from small).trans master.binaryDiv

/-- The source root and H/G functions belong to the selected axis, regardless
of the smaller physical subtree width in the same row. -/
theorem root_fields (n : ℕ) (j : Fin (axisCount n)) :
    UniformSeedRankCrossPreparation.omega n j = OAI.ExactFourier.zeta (radix n j) ∧
    UniformSeedRankCrossPreparation.hValue n j =
      (fun i => PowerSeries.coeff i
        (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n j)))) ∧
    UniformSeedRankCrossPreparation.gValue n j =
      DFTModelCacheKernelNewton.gValue (OAI.ExactFourier.zeta (radix n j)) := by
  exact ⟨rfl,rfl,rfl⟩

theorem rankKernels_eq (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) :
    DFTModelCacheSpectrum.rankKernels (radix n j) (kernel n j q original)
      (DFTModelCacheRectanglePreparation.height q) (OAI.ExactFourier.zeta (radix n j)) =
    UniformRankCrossPreparationMachine.kernelValues
      (UniformSeedHeightPreparation.parameters n j (actual q original)).base
      (UniformSeedRankCrossPreparation.hValue n j)
      (UniformSeedRankCrossPreparation.gValue n j) := rfl

theorem compact_rankKernels_eq (n : ℕ) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config) (K : ℕ) (z : ℂ) :
    DFTModelCacheSpectrum.rankKernels (radix n j) (kernel n j q original) K z =
    DFTModelCacheSpectrum.rankKernels (radix n j)
      (DFTModelCacheRectanglePreparation.parameters (radix n j) q) K z := rfl

/-- Apply the existing charged paired-spectrum program to these actual native
parameters. This theorem supplies no bank, spectrum or output callback. -/
theorem paired_sharedBank (n : ℕ) (hn : 0<n) (j : Fin (axisCount n)) (q : Row)
    (original : UniformSeedHeightPreparation.Config)
    (source : DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
    (i : Fin (UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q))) :
    (run DFTModelCacheSpectrumConjugate.program
      (DFTModelCacheDisplacement.metadata (radix n j) (kernel n j q original),
        (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val.look
        i.val (0,0) =
    (UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
      (UniformRankCrossPreparationMachine.kernelValues
        (UniformSeedHeightPreparation.parameters n j (actual q original)).base
        (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) i,
     star (UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
      (UniformRankCrossPreparationMachine.kernelValues
        (UniformSeedHeightPreparation.parameters n j (actual q original)).base
        (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) i)) := by
  obtain ⟨hD,hr,hN,_⟩ := selected_divisors n hn j q source
  rw [←rankKernels_eq]
  exact DFTModelCacheSpectrumConjugate.program_sharedBank (radix n j)
    (UniformMasterRootMachine.order n) (kernel n j q original)
    (kernel_shape n j q original source) (DFTModelCacheRectanglePreparation.height q)
    rfl hD hr hN i

end
end ExactFourierCircuits.DFTModelCacheRectangleMetadata
