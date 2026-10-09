import UniformActualCalendarFactoryEvents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleRegistry
open UniformMachine UniformActualCalendarRegistry UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry UniformLocalCacheSlotConductorMachine
noncomputable section

lemma family_make {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R T:ℕ}
 (g:Geometry constants n axisIndex qs R T){s:State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R T g i hi s)
 (hn:0<n){O N:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤N)
 (radixRoom:radix n axisIndex≤envelope constants n)(i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)
 (ht:t<slotCount n qs[i].row):
 (family g all hn scalarRoom natRoom radixRoom i hi).make t elapsed=
 (data g all i hi t ht).event _ _ _ _ _ _ _ _ elapsed:=by
 have length:t<(block n qs[i]).length:=by rw[block,List.length_ofFn];exact ht
 rw[Family.make,dite_eq_left length]
 rfl

end
end ExactFourierCircuits.UniformActualCalendarRectangleRegistry
namespace ExactFourierCircuits.UniformActualCalendarForestRegistry
open UniformMachine UniformActualCalendarRegistry UniformDirectLeafForestContents
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestModel UniformLocalCacheTreeMachine
noncomputable section

lemma family_make {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:State}
 (h:Contents p visits A positive s){O T B:ℕ}(facts:Facts p visits)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*demand visits≤O)(nat:p.start.permutation+(3*p.radix+11)*demand visits≤T)
 (radix:p.radix≤B)(i:Fin visits.length)(j:Fin (operations visits[i]))(elapsed:ℕ):
 (family h facts entry pool nat radix i).make j.val elapsed=
 UniformActualCalendarDirectProduced.event (data h i j) elapsed:=by
 have length:j.val<(block p visits A i).length:=by rw[block,List.length_ofFn];exact j.isLt
 rw[Family.make,dite_eq_left length]
 rfl

end
end ExactFourierCircuits.UniformActualCalendarForestRegistry
