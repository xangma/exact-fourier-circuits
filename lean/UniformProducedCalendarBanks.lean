import UniformProducedCalendarFamily
import UniformGlobalProducedAxisBanks
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedCalendarBanks
open UniformMachine UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformActualGlobalConstants (constants)
open UniformActualGlobalTickContext
noncomputable section

lemma banks {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)) (s:State)
 (rows:∀i,UniformSectorPackingMachine.Rows [UniformProducedCalendarFamily.physical hn es position i] 0
  (5*UniformJointAllocation.slab constants n+4*i.val) s)
 (widths:∀i,UniformSectorPackingMachine.Widths [UniformProducedCalendarFamily.physical hn es position i] s)
 (permutations:∀i,UniformSectorPackingMachine.Permutations [UniformProducedCalendarFamily.physical hn es position i] s):
 let f:=UniformProducedCalendarFamily.family hn es position
 UniformGlobalRolePackingMachine.Banks (kernel hn (UniformProducedAllAxisGeometry.geometry f)).packing
  (UniformProducedAllAxisGeometry.geometry f).physical s:=
 UniformGlobalProducedAxisBanks.banks_ofFn _ _ s rows widths permutations

lemma directory {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)) (s:State)
 (produced:∀i,s.natHeap (UniformJointAllocation.slab constants n+2*i.val)=some (radix n i) ∧
  s.natHeap (UniformJointAllocation.slab constants n+2*i.val+1)=
   some (UniformFourierAxisWorkspace.axis constants n i).pool):
 let f:=UniformProducedCalendarFamily.family hn es position
 UniformGlobalDiagonalRowsMachine.Directory
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).rows.directory
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).entries 0 s:=by
 intro f
 apply UniformGlobalProducedAxisBanks.directory_ofFn
 intro i
 change s.natHeap (UniformJointAllocation.slab constants n+2*(0+i.val))=some (radix n i)∧
  s.natHeap (UniformJointAllocation.slab constants n+2*(0+i.val)+1)=
   some (UniformFourierAxisWorkspace.axis constants n i).pool
 simpa only[Nat.zero_add] using produced i

lemma pools {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)) (s:State)
 (produced:∀i,∀lane:Fin 9,∀j:Fin (radix n i),
  s.scalarHeap ((UniformFourierAxisWorkspace.axis constants n i).pool+lane.val*radix n i+j.val)=
   some (UniformPairMachine.prepared (if lane.val=0 then foldValues (es i) (fun _=>1) j.val else 1))):
 let f:=UniformProducedCalendarFamily.family hn es position
 UniformGlobalDiagonalRowsMachine.Pools
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).entries s:=by
 intro f
 apply UniformGlobalProducedAxisBanks.pools_ofFn
 exact produced
end
end ExactFourierCircuits.UniformProducedCalendarBanks
