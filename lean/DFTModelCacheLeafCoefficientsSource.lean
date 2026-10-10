import DFTModelCacheLeafCoefficientsBounds
import DFTModelCacheAxisRootsCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier UniformTransposeDescriptorMachine
noncomputable section
attribute [local irreducible] program

def nativePairs (r K : ℕ) (qs : List Record) : Pairs.T :=
  DFTModelCacheTraversal.ofList (qs.map (fun q=>
    (UniformDirectLeafCacheSource.mu r K q,starRingEnd ℂ (UniformDirectLeafCacheSource.mu r K q))))

theorem canonical_pairs (r K : ℕ) (hr : 0<r) (qs : List Record)
    (range : ∀q∈qs,UniformDirectLeafCacheSource.InRange r K q) :
    coefficientPairs (zeta r) K qs=nativePairs r K qs := by
  apply congrArg DFTModelCacheTraversal.ofList
  apply List.map_congr_left
  intro q hq
  exact canonical_pair r K hr q (range q hq)

theorem program_native_value (r v o K : ℕ) (hr : 0<r) (extent : o+v≤r) :
    (run program ((r,zeta r),(v,(o,K)))).val=
      ((inverseH r (zeta r),inverseH r (zeta r)⁻¹),
        ((encoded (leafRecords v o K),encoded ((leafRecords v o K).reverse.map Record.transpose)),
          (nativePairs r K (leafRecords v o K),
            nativePairs r K ((leafRecords v o K).reverse.map Record.transpose)))) := by
  rw [program_value _ _ _ _ _ extent]
  dsimp only [values]
  rw [canonical_pairs r K hr _ (fun q h=>
    (UniformDirectLeafCacheChronology.leaf_valid v o K r extent q h).1)]
  rw [canonical_pairs r K hr _ (fun q h=>by
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
    have good:=UniformDirectLeafCacheChronology.leaf_valid v o K r extent p (List.mem_reverse.mp hp)
    exact (UniformDirectLeafCacheChronology.transpose_valid r K p good.1 good.2).1)]

theorem nativePairs_lookup (r K : ℕ) (qs : List Record) (i : ℕ) (hi : i<qs.length) :
    (nativePairs r K qs).look i (0,0)=
      (UniformDirectLeafCacheSource.mu r K qs[i],
        starRingEnd ℂ (UniformDirectLeafCacheSource.mu r K qs[i])) := by
  rw [Tape.look_of_lt _ _ (by simpa [nativePairs,DFTModelCacheTraversal.ofList] using hi)]
  simp only [nativePairs,DFTModelCacheTraversal.ofList,List.getElem_map]

/-- Actual selected-axis root provenance, obtained from the charged root-bank producer.
This is a provenance theorem; selection of the axis is not an uncharged new constructor. -/
theorem selected_root (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    (run DFTModelCacheAxisRoots.program (n,zeta (UniformMasterRootMachine.order n))).val.look
      j.val (0,0)=(UniformAllAxisSeedPreparation.radix n j,zeta (UniformAllAxisSeedPreparation.radix n j)) := by
  rw [DFTModelCacheAxisRoots.selected_value n hn,Tape.look_of_lt _ _ j.isLt]
  rfl

/-- The produced scalar pair equals the two physical retained lane3 cells.
Neither a scalar value nor its conjugate is an input oracle. -/
theorem retained_pair {n : ℕ} (axis : Fin (UniformAllAxisSeedPreparation.axisCount n))
    (s : UniformMachine.State)
    (original : UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (conjugate : UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (qs : List Record) (i : ℕ) (hi : i<qs.length)
    (range : UniformDirectLeafCacheSource.InRange (UniformAllAxisSeedPreparation.radix n axis)
      (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) qs[i]) :
    s.scalarHeap qs[i].coefficient=some (UniformPairMachine.prepared
      ((nativePairs (UniformAllAxisSeedPreparation.radix n axis)
        (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) qs).look i (0,0)).1) ∧
    s.scalarHeap (UniformAllAxisConjugatePreparation.axisBase n axis.val+
      3*UniformAllAxisSeedPreparation.radix n axis+
      (qs[i].coefficient-(UniformAllAxisSeedPreparation.axisBase n axis.val+
        3*UniformAllAxisSeedPreparation.radix n axis)))=some (UniformPairMachine.prepared
      ((nativePairs (UniformAllAxisSeedPreparation.radix n axis)
        (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) qs).look i (0,0)).2) := by
  rw [nativePairs_lookup _ _ _ _ hi]
  exact UniformDirectLeafCacheSource.retained_sources axis s original conjugate qs[i] range

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients
