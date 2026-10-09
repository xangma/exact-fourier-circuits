import UniformProducedAllAxisAlignment
import UniformMatchingKernelAmbient
import UniformFourierAxisWorkspace
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedCalendarFamily
open UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformMatchingAxisTableMachine UniformMatchingKernelAmbient
open UniformActualGlobalConstants (constants)
noncomputable section

lemma workspace_regions (r N S:ℕ):
 (UniformFourierAxisWorkspace.axisBank r N S).permutation+r≤(UniformFourierAxisWorkspace.axisBank r N S).endNat ∧
 (UniformFourierAxisWorkspace.axisBank r N S).widths+r≤(UniformFourierAxisWorkspace.axisBank r N S).endNat:=by
 dsimp only[UniformFourierAxisWorkspace.axisBank]
 omega

def physical {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (i:Fin (axisCount n)):UniformSectorPackingMachine.PhysicalAxis:=
 let a:=UniformFourierAxisWorkspace.axis constants n i
 physicalAxis (radix n i) a.widths a.permutation (edges (position i))
  (matching (position i)) (UniformMatchingKernelAmbient.range (position i))
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i)

lemma physical_radix {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (i:Fin (axisCount n)):(physical hn es position i).geometry.widths.sum=radix n i:=
 widths_sum _ _ (matching_capacity _ _ (matching (position i)) (UniformMatchingKernelAmbient.range (position i)))

/-- The actual281 and55 output addresses produce an ordinary all-axis family.
Only the geometry of the genuine ordered call unions is required here; bank
contents are supplied by the executed per-axis loop. -/
def family {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)):
 UniformProducedAllAxisGeometry.Family n where
 physical:=physical hn es position
 pool:=fun i=>(UniformFourierAxisWorkspace.axis constants n i).pool
 value:=fun i lane j=>if lane.val=0 then foldValues (es i) (fun _=>1) j.val else 1
 radix_eq:=physical_radix hn es position
 widths:=by
  intro i
  have fits:=(UniformFourierAxisWorkspace.axis_fit constants hn i).1
  have regions:=(workspace_regions (radix n i)
   (UniformFourierAxisWorkspace.Arena.natBase constants n+UniformFourierAxisWorkspace.natPrefix n i.val)
   (UniformFourierAxisWorkspace.Arena.scalarBase constants n+9*prefixSum n i.val)).2
  have cap:=matching_capacity _ _ (matching (position i)) (UniformMatchingKernelAmbient.range (position i))
  change (UniformFourierAxisWorkspace.axis constants n i).widths+
   (widths (radix n i) (callTotal (radix n i) (es i))).length≤_
  rw[widths_length _ _ cap]
  exact (Nat.add_le_add_left (Nat.sub_le _ _) _).trans (regions.trans fits)
 permutations:=by
  intro i
  have fits:=(UniformFourierAxisWorkspace.axis_fit constants hn i).1
  have regions:=(workspace_regions (radix n i)
   (UniformFourierAxisWorkspace.Arena.natBase constants n+UniformFourierAxisWorkspace.natPrefix n i.val)
   (UniformFourierAxisWorkspace.Arena.scalarBase constants n+9*prefixSum n i.val)).1
  change (UniformFourierAxisWorkspace.axis constants n i).permutation+
   (physical hn es position i).geometry.widths.sum≤_
  rw[physical_radix]
  exact regions.trans fits
 pools:=by
  intro i
  exact (UniformFourierAxisWorkspace.axis_fit constants hn i).2

lemma family_physical {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)):
 (family hn es position).physical=physical hn es position:=rfl
lemma family_values {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (i:Fin (axisCount n)) (j:Fin (radix n i)):
 (family hn es position).value i 0 j=foldValues (es i) (fun _=>1) j.val:=rfl
end
end ExactFourierCircuits.UniformProducedCalendarFamily
