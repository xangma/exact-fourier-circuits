import DFTModelGlobalSectorBillingSelected
import DFTModelGlobalSectorBillingNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorBilling
open UniformMachine UniformSectorPackingMachine
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelCacheTraversal DFTModelGlobalSectorPreparation
noncomputable section

/-- The typed preparation is billed against this same complete native packing
execution. The selected shape is genuine caller geometry; no budget is supplied. -/
theorem selected_source_work {N : ℕ} (hN : 0<N)
 (as:List PhysicalAxis) (L:Layout) (n:ℕ) (x:Fin n → ℂ)
 (v:Fin L.total → Scalar) (s:State) (hlen:as.length=L.ell) (hvolume:physicalVolume as=L.total)
 (shape:UniformSectorPacking.radices (physicalAxes as)=List.ofFn (UniformSelectedCRT.radices N))
 (hh:Header L s) (rows:Rows as 0 L.rows s) (widths:Widths as s) (perms:Permutations as s)
 (widthBelow:∀a∈as,a.widthsBase+a.geometry.widths.length≤L.suffix)
 (permBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum≤L.suffix)
 (source:SourceReady L v s) (hpc:s.pc=0) (hs:WordBound L.B s)
 {ticks:ℕ} {t:State}
 (actual:BoundedExecution UniformSectorPackingMachine.program n x L.B s ticks t) :
 (run withDirectory (ofList ((physicalAxes as).map encodeAxis))).work≤
 preparationFactor*ticks := by
 have lower:=packing_ticks_lower as L n x v s hlen hvolume hh rows widths perms
   widthBelow permBelow source hpc hs actual
 have work:=selected_work hN (physicalAxes as) shape
 have volume:(UniformSectorPacking.radices (physicalAxes as)).prod=L.total:=hvolume
 rw [volume] at work
 exact work.trans (Nat.mul_le_mul_left _ (by omega))

/-- Direct specialization to the family retained by the actual all-axis producer. -/
theorem family_source_work {N : ℕ} (hN : 0<N)
 (f:UniformProducedAllAxisGeometry.Family N) (L:Layout) (n:ℕ) (x:Fin n → ℂ)
 (v:Fin L.total → Scalar) (s:State)
 (hlen:(UniformProducedAllAxisGeometry.geometry f).physical.length=L.ell)
 (hvolume:physicalVolume (UniformProducedAllAxisGeometry.geometry f).physical=L.total)
 (hh:Header L s) (rows:Rows (UniformProducedAllAxisGeometry.geometry f).physical 0 L.rows s)
 (widths:Widths (UniformProducedAllAxisGeometry.geometry f).physical s)
 (perms:Permutations (UniformProducedAllAxisGeometry.geometry f).physical s)
 (widthBelow:∀a∈(UniformProducedAllAxisGeometry.geometry f).physical,
   a.widthsBase+a.geometry.widths.length≤L.suffix)
 (permBelow:∀a∈(UniformProducedAllAxisGeometry.geometry f).physical,
   a.permutationBase+a.geometry.widths.sum≤L.suffix)
 (source:SourceReady L v s) (hpc:s.pc=0) (hs:WordBound L.B s)
 {ticks:ℕ} {t:State}
 (actual:BoundedExecution UniformSectorPackingMachine.program n x L.B s ticks t) :
 (run withDirectory (ofList ((physicalAxes
   (UniformProducedAllAxisGeometry.geometry f).physical).map encodeAxis))).work≤
 preparationFactor*ticks :=
 selected_source_work hN _ L n x v s hlen hvolume (UniformProducedPhysicalCoordinate.radices f)
   hh rows widths perms widthBelow permBelow source hpc hs actual

end
end ExactFourierCircuits.DFTModelGlobalSectorBilling
