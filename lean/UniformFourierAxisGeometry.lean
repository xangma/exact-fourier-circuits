import UniformFourierAxisWorkspaceBindings
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisGeometry
open UniformJointAllocation UniformJointCacheAllocation UniformJointCacheExtent
namespace WS
export UniformFourierAxisWorkspace (axis axisBank natAmount natPrefix)
end WS
noncomputable section

lemma axis_directory_before (c:Constants)(n:ℕ)(j:Fin (ell n)):
 slab c n+2*j.val+2 ≤ (WS.axis c n j).selected:=by
 have hi:=j.isLt
 change slab c n+2*j.val+2 ≤ UniformJointCacheAllocation.natEnd c n+WS.natPrefix n j.val
 unfold UniformJointCacheAllocation.natEnd UniformJointCacheAllocation.natStart
 omega

lemma axis_row_fit (c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 5*slab c n+4*j.val+4 ≤ envelope c n:=by
 have fit:=(UniformJointCacheAllocation.ends_bound c n hn).1
 unfold UniformJointCacheAllocation.natEnd UniformJointCacheAllocation.natStart at fit
 have hi:=j.isLt
 unfold envelope
 omega

lemma seed_source_fit (c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 UniformAllAxisSeedPreparation.axisBase n j.val+5*UniformAllAxisSeedPreparation.radix n j ≤ slab c n ∧
 UniformAllAxisSeedPreparation.directoryBase n+2*j.val+2 ≤ envelope c n:=by
 have previous:=UniformAllAxisSeedPreparation.axisBase_mono n (Nat.succ_le_of_lt j.isLt)
 rw[UniformAllAxisSeedPreparation.axisBase_next n j] at previous
 obtain ⟨last,_conjugate,directory,_conjugateDirectory⟩:=retained_below c n hn
 change UniformAllAxisSeedPreparation.axisBase n (ell n) ≤ slab c n at last
 change UniformAllAxisSeedPreparation.directoryBase n+2*ell n ≤ slab c n at directory
 refine ⟨previous.trans last,?_⟩
 have hi:=j.isLt
 unfold envelope
 omega

structure Geometry (c:Constants)(n:ℕ)(j:Fin (ell n)):Prop where
 radix:2 ≤ UniformAllAxisSeedPreparation.radix n j
 selectedPhase:(WS.axis c n j).selected+2*capacity (UniformAllAxisSeedPreparation.radix n j) ≤ (WS.axis c n j).phase
 selectedBoundary:(WS.axis c n j).selected+2 ≤ (WS.axis c n j).boundary
 boundaryFit:(WS.axis c n j).boundary+3*UniformAllAxisSeedPreparation.radix n j+11 ≤ envelope c n
 phaseRows:(WS.axis c n j).phase+56 ≤ (WS.axis c n j).rawRows
 rowsPermutation:(WS.axis c n j).rawRows+3*UniformAllAxisSeedPreparation.radix n j ≤ (WS.axis c n j).permutation
 permutationWidths:(WS.axis c n j).permutation+UniformAllAxisSeedPreparation.radix n j ≤ (WS.axis c n j).widths
 widthsMarkers:(WS.axis c n j).widths+UniformAllAxisSeedPreparation.radix n j ≤ (WS.axis c n j).markers
 markersRow:(WS.axis c n j).markers+UniformAllAxisSeedPreparation.radix n j ≤ 5*slab c n+4*j.val
 axisRowFit:5*slab c n+4*j.val+4 ≤ envelope c n
 directoryPermutation:slab c n+2*j.val+2 ≤ (WS.axis c n j).permutation
 boundaryMerged:slab c n+9*UniformAllAxisSeedPreparation.radix n j ≤ (WS.axis c n j).pool
 sourceBelow:UniformAllAxisSeedPreparation.axisBase n j.val+5*UniformAllAxisSeedPreparation.radix n j ≤ slab c n
 sourceFit:UniformAllAxisSeedPreparation.directoryBase n+2*j.val+2 ≤ envelope c n
 boundaryPoolFit:slab c n+9*UniformAllAxisSeedPreparation.radix n j ≤ envelope c n
 mergedPoolFit:(WS.axis c n j).pool+9*UniformAllAxisSeedPreparation.radix n j ≤ envelope c n
 natEndFit:(WS.axis c n j).endNat ≤ envelope c n
 code:389 ≤ envelope c n

/-- Every ordinary bound comes from the real selected radix, measured fresh
axis allocation and original seed extent. No desired-produced-data premise. -/
theorem geometry (c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):Geometry c n j:=by
 have positive:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 change 2 ≤ UniformAllAxisSeedPreparation.radix n j at positive
 have ends:=UniformFourierAxisWorkspace.axis_fit c hn j
 have shapes:=UniformFourierAxisWorkspace.axis_geometry c n j
 have directory:=axis_directory_before c n j
 have source:=seed_source_fit c hn j
 have merged:=UniformFourierAxisWorkspace.boundary_before_merged c n j
 have large:=fixed_large c
 have cap:1 ≤ capacity (UniformAllAxisSeedPreparation.radix n j):=
  Nat.mul_le_mul (Nat.one_le_pow 2 (UniformAllAxisSeedPreparation.radix n j) (by omega))
   (show 1 ≤ slotCount (Nat.clog 2 (4*UniformAllAxisSeedPreparation.radix n j))+4 by omega)
 have scalarEnd:(WS.axis c n j).endScalar=(WS.axis c n j).pool+9*UniformAllAxisSeedPreparation.radix n j:=rfl
 have nfit:(WS.axis c n j).endNat ≤ envelope c n:=by unfold envelope;omega
 have sfit:(WS.axis c n j).pool+9*UniformAllAxisSeedPreparation.radix n j ≤ envelope c n:=by
  rw[←scalarEnd]
  unfold envelope
  omega
 constructor
 · exact positive
 · omega
 · omega
 · omega
 · omega
 · exact shapes.2.2.2.1.le
 · exact shapes.2.2.2.2.1.le
 · exact shapes.2.2.2.2.2.1.le
 · omega
 · exact axis_row_fit c hn j
 · omega
 · exact merged
 · exact source.1
 · exact source.2
 · exact merged.trans (Nat.le_add_right _ _ |>.trans sfit)
 · exact sfit
 · exact nfit
 · unfold envelope;omega
end
end ExactFourierCircuits.UniformFourierAxisGeometry
