import UniformSeedChunkAllocation

set_option autoImplicit false
namespace ExactFourierCircuits.SeedChunkAllocationFixtures
open UniformAllAxisSeedPreparation (axisCount radix)
open UniformSeedChunkAllocation

/-- The global envelope holds even at the smallest original input length. -/
example : 200*slot 1 ≤ (1+2)^19 := slot_canonical (by decide)

example : slot 1=900000 := by decide

/-- Actual selected-axis nonvacuity, with a=e=1 and canonical budget. -/
example : ∃n,0<n ∧ ∃j:Fin (axisCount n),
    UniformSeedChunkPreparation.Layout n j (chunk n j 1 1 1 0 1 false) ((n+2)^19) :=
  exists_selected_unit_layout

/-- Enabled/disabled bucket selection does not alter the physical allocation. -/
example {n : ℕ} (hn : 0<n) (j : Fin (axisCount n)) (hr : 196 ≤ radix n j) :
    UniformSeedChunkPreparation.Layout n j (chunk n j 1 1 1 0 1 true) ((n+2)^19) := by
  have capacity : UniformWorkspacePlanner.gateCount 1 1+1+1 ≤ radix n j := by
    have count : UniformWorkspacePlanner.gateCount 1 1+1+1=196 := by decide
    simpa only [count] using hr
  exact chunk_layout hn j 1 1 1 0 1 true (by decide) (by decide)
    (by omega) (by omega) (by omega) (by omega) capacity

/-- A positive local child width may be smaller than the actual selected axis;
    measured fit still supplies the exact-width allocation capacity. -/
example {n v a e i0 j0 s : ℕ} (hn : 0<n) (j : Fin (axisCount n))
    (hv : 0<UniformWorkspacePlanner.selected v)
    (hvaxis : v ≤ radix n j)
    (hat : a ∈ UniformWorkspacePlanner.chunkSizes (v-v/2) (UniformWorkspacePlanner.selected v))
    (hes : e ∈ UniformWorkspacePlanner.chunkSizes (v/2) (UniformWorkspacePlanner.selected v))
    (ha : 0<a) (he : 0<e) (hrow : i0+a ≤ radix n j)
    (hs : s < radix n j) (hi : s ≤ i0) (hc : j0+e ≤ s) :
    UniformSeedChunkPreparation.Layout n j (chunk n j a e i0 j0 s false) ((n+2)^19) :=
  chunk_layout hn j a e i0 j0 s false ha he hrow hs hi hc
    ((UniformWorkspacePlanner.selected_fit hv hat hes).trans hvaxis)

/-- The old allocator's precise fresh pool coordinates are retained. -/
example (n : ℕ) (j : Fin (axisCount n)) (c : UniformSeedHeightPreparation.Config) :
    (extend n j c).borrowed=heightEnd c ∧
    (extend n j c).axis=heightEnd c+15*c.gates+3*radix n j := ⟨rfl,rfl⟩

/-- Small axes cannot be forced through the nonempty unit cross. -/
example {r : ℕ} (hr : r<196) :
    ¬(UniformWorkspacePlanner.gateCount 1 1+1+1 ≤ r) := by
  have count : UniformWorkspacePlanner.gateCount 1 1+1+1=196 := by decide
  rw [count]
  omega

end ExactFourierCircuits.SeedChunkAllocationFixtures
