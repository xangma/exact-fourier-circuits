import UniformDirectLeafForestFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestLoop
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformDirectLeafForestIteration UniformDirectLeafForestFrame
open UniformLocalCacheTreeMachine
noncomputable section

/-- Finite execution over every actual directory node, with all earlier
cache/range outputs retained. No callback supplies any producer execution. -/
theorem remaining {p:Parameters}{visits:List Visit}{n B:ℕ}
 (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))(x:Fin n→ℂ)
 (positive:2≤p.radix)(facts:Facts p visits)(bounds:SeedBounds p n)
 (radix:p.radix=UniformAllAxisSeedPreparation.radix n axis)
 (od:p.start.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:p.start.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (l:Placement p (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B visits):
 ∀k i (s:State),i+k=visits.length→
 Invariant p visits n (UniformAllAxisSeedPreparation.axisBase n axis.val) i positive s→
 WordBound B s→∃u ticks,
 BoundedRuns UniformDirectLeafForestProgram.program n x B s ticks u ∧
 ticks+(62*p.radix+246)*before visits i+93*i≤(62*p.radix+246)*demand visits+93*visits.length ∧
 Invariant p visits n (UniformAllAxisSeedPreparation.axisBase n axis.val) visits.length positive u ∧
 Frame p visits s u:=by
 intro k
 induction k with
 | zero=>
  intro i s eq inv wb
  have ie:i=visits.length:=by omega
  subst i
  refine ⟨s,0,.refl wb,?_,inv,Frame.refl p visits s⟩
  simp only[before_length,Nat.zero_add]
  exact le_rfl
 | succ k ih=>
  intro i s eq inv wb
  have hi:i<visits.length:=by omega
  obtain ⟨u,ticks,run,cost,next,frame⟩:=UniformDirectLeafForestIteration.execution axis x s hi positive
   inv facts bounds radix od cd l wb
  obtain ⟨v,rest,tail,budget,last,kept⟩:=ih (i+1) u (by omega) next run.final_bound
  refine ⟨v,ticks+rest,run.trans tail,?_,last,(of_step hi frame).trans kept⟩
  have following:=before_next visits i hi
  rw[following,Nat.mul_add,Nat.mul_add] at budget
  omega
end
end ExactFourierCircuits.UniformDirectLeafForestLoop
