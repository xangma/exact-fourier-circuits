import UniformJointInverseBanks
import UniformProducedInversePacking
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointInversePackingPreparation
open UniformJointAllocation
noncomputable section
/-- Genuine137 producer uses scalar7U→8U and the retained physical metadata. -/
def layout (c : Constants) (n : ℕ) (hn : 0 < n) (roles : 0 < c.roles) :
 UniformSectorPackingMachine.Layout :=
 let L:=packingLayout c n hn 0 roles
 {L with
  source:=7*slab c n
  destination:=8*slab c n
  sourceBelow:=by
   have h:=actual_arithmetic c n hn
   dsimp only at h
   rw [Nat.mul_assoc 2 c.roles] at h
   change 7*slab c n+UniformInitialPreparation.len n ≤ 8*slab c n
   omega
  destinationBound:=by
   have h:=actual_arithmetic c n hn
   dsimp only at h
   rw [Nat.mul_assoc 2 c.roles] at h
   change 8*slab c n+UniformInitialPreparation.len n ≤ envelope c n
   unfold envelope
   omega}
/-- Actual163 inverse packing into2U; it produces its own inverse table. -/
def preparation (c : Constants) (n : ℕ) (hn : 0 < n) (roles : 0 < c.roles) :
 UniformProducedInversePacking.Preparation c.roles where
 layout:=layout c n hn roles
 destination:=2*slab c n
 code:=by
  have h:=fixed_large c
  change 163 ≤ envelope c n
  unfold envelope
  omega
 roles:=roles_bound c n
 tempAfterAll:=by
  have h:=UniformJointInverseBanks.roles_volume c n hn
  change 7*slab c n+c.roles*UniformInitialPreparation.len n ≤ 8*slab c n
  omega
 destinationFit:=by
  have h:=(UniformJointInverseBanks.separation c n hn).2.2.2.2.2
  exact h
 disjoint:=by
  apply Or.inr
  exact (UniformJointInverseBanks.separation c n hn).2.2.2.1
lemma addresses (c : Constants) (n : ℕ) (hn : 0 < n) (roles : 0 < c.roles) :
 let p:=preparation c n hn roles
 p.layout.source=7*slab c n ∧ p.layout.destination=8*slab c n ∧
 p.destination=2*slab c n ∧ p.layout.inverse=11*slab c n ∧
 p.layout.rows=5*slab c n ∧ p.layout.suffix=7*slab c n ∧ p.layout.stack=8*slab c n ∧
 p.layout.total=UniformInitialPreparation.len n ∧ p.layout.B=envelope c n := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end
end ExactFourierCircuits.UniformJointInversePackingPreparation
