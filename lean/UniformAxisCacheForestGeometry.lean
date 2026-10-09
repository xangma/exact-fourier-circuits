import UniformAxisCacheForestEntry
import UniformAxisCacheHorizonBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestGeometry
open UniformAxisCacheForestEntry UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformDirectLeafForestGeometry
open UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation
open UniformJointCacheAllocation UniformJointAllocation UniformLocalCacheTimingMetadata
noncomputable section

lemma demand_bound (c:Constants) (n:ℕ) (j:Fin (ell n)):
 demand (visits c n j)≤ (Seed.radix n j)^2:=by
 change demand (UniformLocalCacheTreeMachine.walk (2*Seed.radix n j+1) 0
  (axis c n j).requests [⟨Seed.radix n j,0,0,0⟩]).1≤ (Seed.radix n j)^2
 rw [root_demand]
 exact UniformJointCacheTime.leaf_operations_bound _

lemma capacity (c:Constants) (n:ℕ) (j:Fin (ell n)):
 rectangleCount c n j+2*demand (visits c n j)≤ UniformJointCacheExtent.capacity (Seed.radix n j):=by
 have leaves:=demand_bound c n j
 have rect:=UniformAxisCacheCanonicalRequests.capacity c n j
 change rectangleCount c n j+2*(Seed.radix n j)^2≤ _ at rect
 omega

lemma low_rows (c:Constants) (n:ℕ):
 UniformLocalRectangleWorkspaceHeaders.z n+3≤ slab c n:=by
 have large:=fixed_large c
 have coefficient:4≤ 100000*(fixed c+1):=by omega
 have power:1≤ (n+2)^19:=by have h:0<(n+2)^19:=pow_pos (by omega) 19;omega
 have bound:=Nat.mul_le_mul_right ((n+2)^19) coefficient
 change 4*(n+2)^19≤ slab c n at bound
 change (n+2)^19+3≤ slab c n
 omega

/-- All seed addresses are below the genuine low workspace, which is below
the allocator's persistent regions and measured scalar cache frontier. -/
theorem seed_bounds (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n)):
 SeedBounds (parameters c n j) n:=by
 have original:=(UniformAllAxisSeedPreparation.word_setup hn).2
 have conjugate:=(UniformAllAxisConjugatePreparation.word_setup hn).2
 change _≤ UniformLocalRectangleWorkspaceHeaders.z n ∧_≤ UniformLocalRectangleWorkspaceHeaders.z n at original conjugate
 have lower:=UniformAxisCachePhysical.axis_lower c n j
 have low:=low_rows c n
 constructor <;> try dsimp only[parameters]
 · intro i q t
   have bound:=UniformAllAxisSeedPreparation.compact_address_before i i.isLt q t
   omega
 · intro i q t
   have bound:=UniformAllAxisConjugatePreparation.compact_address_before i i.isLt q t
   omega
 · omega
 · omega
 · exact original.2
 · exact conjugate.2

structure Bounds (c:Constants) (n:ℕ) (j:Fin (ell n)):Prop where
 rows:UniformLocalRectangleWorkspaceHeaders.z n+3≤ (axis c n j).tasks
 constants:6≤ (axis c n j).pool
 original:UniformAllAxisSeedPreparation.axisBase n j.val+4*Seed.radix n j≤ (axis c n j).pool
 conjugate:UniformAllAxisConjugatePreparation.axisBase n j.val+4*Seed.radix n j≤ (axis c n j).pool
 originalDir:Seed.directoryBase n+2*j.val+2≤ UniformLocalRectangleWorkspaceHeaders.z n
 conjugateDir:UniformAllAxisConjugatePreparation.directoryBase n+2*j.val+1≤ UniformLocalRectangleWorkspaceHeaders.z n
 natFit:(axis c n j).endNat≤ envelope c n
 scalarFit:(axis c n j).endScalar≤ envelope c n
 leafFit:(axis c n j).leafForward+3*Seed.radix n j+4≤ (axis c n j).endNat
 descFit:(axis c n j).leafTranspose+4*(Seed.radix n j)^2≤ (axis c n j).endNat
 cacheEnd:(axis c n j).control+(3*Seed.radix n j+11)*
  (rectangleCount c n j+demand (visits c n j))≤ (axis c n j).leafForward
 scalarEnd:(axis c n j).pool+9*Seed.radix n j*
  (rectangleCount c n j+demand (visits c n j))≤ (axis c n j).endScalar
 row:20000*(2*Seed.radix n j+1)≤ envelope c n
 capWord:UniformJointCacheExtent.capacity (Seed.radix n j)≤ envelope c n

theorem bounds (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n)):Bounds c n j:=by
 have positive:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 change 2≤ Seed.radix n j at positive
 have cap:=capacity c n j
 have total:rectangleCount c n j+demand (visits c n j)≤ 
   UniformJointCacheExtent.capacity (Seed.radix n j):=by omega
 have cacheBound:=Nat.mul_le_mul_left (3*Seed.radix n j+11) total
 have scalarBound:=Nat.mul_le_mul_left (9*Seed.radix n j) total
 have fits:=axis_fit c n j
 have ends:=ends_bound c n hn
 have natFit:(axis c n j).endNat≤ envelope c n:=by unfold envelope;omega
 have scalarFit:(axis c n j).endScalar≤ envelope c n:=by unfold envelope;omega
 have lower:=UniformAxisCachePhysical.axis_lower c n j
 have low:=low_rows c n
 have small:6≤ UniformLocalRectangleWorkspaceHeaders.z n:=
  (show 6≤ 469 by decide).trans (UniformAllAxisSeedPreparation.word_setup hn).1
 have original:=(UniformAllAxisSeedPreparation.word_setup hn).2
 have conjugate:=(UniformAllAxisConjugatePreparation.word_setup hn).2
 change _≤ UniformLocalRectangleWorkspaceHeaders.z n ∧_≤ UniformLocalRectangleWorkspaceHeaders.z n at original conjugate
 have nextO:=UniformAllAxisSeedPreparation.axisBase_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformAllAxisSeedPreparation.axisBase_next] at nextO
 change UniformAllAxisSeedPreparation.axisBase n j.val+5*Seed.radix n j≤
  UniformAllAxisSeedPreparation.axisBase n (Seed.axisCount n) at nextO
 have nextC:=UniformAllAxisConjugatePreparation.axisBase_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformAllAxisConjugatePreparation.axisBase_next] at nextC
 change UniformAllAxisConjugatePreparation.axisBase n j.val+5*Seed.radix n j≤
  UniformAllAxisConjugatePreparation.axisBase n (Seed.axisCount n) at nextC
 have nodes:=UniformAxisCacheTimingGeometry.nodes_bound (Seed.radix n j) (axis c n j).requests
 change (visits c n j).length≤ 2*Seed.radix n j+1 at nodes
 have budget:=UniformAxisCacheAllocationMachine.selected_wordBudget c n hn j
 have row:=((UniformAxisCacheAllocationMachine.numeric_bounds (Seed.radix n j)
   (natAt c n j.val) (scalarAt c n j.val)).mono budget).rowBudget
 change 20000*(2*Seed.radix n j+1)≤ envelope c n at row
 have leafFit:(axis c n j).leafForward+3*Seed.radix n j+4≤ (axis c n j).endNat:=by
  dsimp only[axis,axisBank]
  omega
 have leafEnd:(axis c n j).leafForward≤ (axis c n j).endNat:=by omega
 have descFit:(axis c n j).leafTranspose+4*(Seed.radix n j)^2≤ (axis c n j).endNat:=by
  dsimp only[axis,axisBank]
  omega
 have cacheEnd:(axis c n j).control+(3*Seed.radix n j+11)*
   (rectangleCount c n j+demand (visits c n j))≤ (axis c n j).leafForward:=by
  change (axis c n j).control+_≤ (axis c n j).control+_
  exact Nat.add_le_add_left cacheBound _
 have scalarEnd:(axis c n j).pool+9*Seed.radix n j*
   (rectangleCount c n j+demand (visits c n j))≤ (axis c n j).endScalar:=by
  change (axis c n j).pool+_≤ (axis c n j).pool+_
  exact Nat.add_le_add_left scalarBound _
 have capWord:UniformJointCacheExtent.capacity (Seed.radix n j)≤ envelope c n:=by
  have mul:UniformJointCacheExtent.capacity (Seed.radix n j)≤ 
    9*Seed.radix n j*UniformJointCacheExtent.capacity (Seed.radix n j):=by
   simpa only[Nat.one_mul] using Nat.mul_le_mul_right (UniformJointCacheExtent.capacity (Seed.radix n j))
    (show 1≤ 9*Seed.radix n j by omega)
  change (axis c n j).pool+9*Seed.radix n j*UniformJointCacheExtent.capacity (Seed.radix n j)≤ 
   envelope c n at scalarFit
  omega
 refine ⟨low.trans lower.1,?_,?_,?_,?_,?_,natFit,scalarFit,leafFit,descFit,cacheEnd,scalarEnd,row,capWord⟩
 · omega
 · omega
 · omega
 · have index: j.val<Seed.axisCount n:=j.isLt
   omega
 · have index: j.val<Seed.axisCount n:=j.isLt
   omega

theorem layout (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n)):
 UniformDirectLeafForestGeometry.Layout (parameters c n j)
  (UniformAllAxisSeedPreparation.axisBase n j.val)
  (UniformAllAxisConjugatePreparation.axisBase n j.val) (envelope c n) (visits c n j):=by
 have b:=bounds c n hn j
 constructor
 · change UniformLocalRectangleWorkspaceHeaders.z n+3≤
    (axis c n j).control+(3*Seed.radix n j+11)*rectangleCount c n j
   have order:=UniformAxisCachePhysical.control_after_tasks c n j
   have rows:=b.rows
   omega
 · rfl
 · rfl
 · rfl
 · rfl
 · simpa only[parameters,Nat.mul_add,Nat.add_assoc] using b.cacheEnd
 · have margin:(axis c n j).leafForward+(3*Seed.radix n j+4)≤ envelope c n:=by
    simpa only[Nat.add_assoc] using b.leafFit.trans b.natFit
   have bound:=(Nat.add_le_add_right b.cacheEnd (3*Seed.radix n j+4)).trans margin
   simpa only[parameters,Nat.mul_add,Nat.add_assoc] using bound
 · simpa only[parameters,Nat.mul_add,Nat.add_assoc] using b.scalarEnd.trans b.scalarFit
 · rfl
 · exact b.descFit.trans b.natFit
 · change 6≤ (axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
   have h:=b.constants;omega
 · exact b.originalDir
 · exact b.conjugateDir
 · change UniformAllAxisSeedPreparation.axisBase n j.val+4*Seed.radix n j≤
    (axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
   have h:=b.original;omega
 · change UniformAllAxisConjugatePreparation.axisBase n j.val+4*Seed.radix n j≤
    (axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
   have h:=b.conjugate;omega
 · exact UniformAxisCacheHorizonBounds.selected_horizon_fits c n hn j
 · change 9*Seed.radix n j≤ envelope c n
   have h:=b.row;omega
 · change 3*Seed.radix n j+11≤ envelope c n
   have h:=b.row;omega
 · have h:=b.row;omega

/-- The real allocator supplies every leaf/range/timestamp layout bound. -/
theorem placement (c:Constants) (n:ℕ) (hn:0<n) (j:Fin (ell n)):
 Placement (parameters c n j)
  (UniformAllAxisSeedPreparation.axisBase n j.val)
  (UniformAllAxisConjugatePreparation.axisBase n j.val) (envelope c n) (visits c n j):=by
 have geometry:=layout c n hn j
 have b:=bounds c n hn j
 have nodes:=UniformAxisCacheTimingGeometry.nodes_bound (Seed.radix n j) (axis c n j).requests
 change (visits c n j).length≤ 2*Seed.radix n j+1 at nodes
 have total:rectangleCount c n j+demand (visits c n j)≤ UniformJointCacheExtent.capacity (Seed.radix n j):=by
  have h:=capacity c n j;omega
 refine ⟨geometry,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals dsimp only[parameters]
 · dsimp only[axis,axisBank]
   omega
 · dsimp only[axis,axisBank]
   omega
 · omega
 · exact b.rows
 · dsimp only[axis,axisBank]
   omega
 · dsimp only[axis,axisBank]
   omega
 · dsimp only[axis,axisBank]
   omega
 · have bound:(axis c n j).nodeStarts+(visits c n j).length≤ (axis c n j).endNat:=by
    dsimp only[axis,axisBank]
    omega
   exact bound.trans b.natFit
 · exact total.trans b.capWord

end
end ExactFourierCircuits.UniformAxisCacheForestGeometry
