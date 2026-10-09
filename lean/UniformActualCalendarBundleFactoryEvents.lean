import UniformCalendarScanFactoryIndices
import UniformActualCalendarGlobalEvents
import UniformActualCalendarRegistryActual

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
noncomputable section

attribute [local irreducible] Nat.add Nat.mul of_actual

def nodeIndex (p:UniformDirectLeafForestData.Parameters)(visits:List UniformLocalCacheTreeMachine.Visit)
 (A:ℕ)(i:Fin visits.length):
 Fin (UniformDirectLeafForestRangeSource.nodeRanges p visits A).length:=
 ⟨i.val,by simpa only[UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt⟩

lemma Family.range_make_mpr {r O T B stride:ℕ}{s:UniformMachine.State}
 (q q':UniformCacheRangeSelector.Range)(e:q=q')
 (f:Family r O T B q'.base stride (List.ofFn (fun j:Fin q'.count=>q'.records j.val)) s):
 (Eq.mpr (congrArg (fun q:UniformCacheRangeSelector.Range=>
  Family r O T B q.base stride (List.ofFn (fun j:Fin q.count=>q.records j.val)) s) e) f).make=f.make:=by
 subst q';rfl

open UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents
open UniformLocalCacheTreeMachine

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R N:ℕ}
 (g:Geometry constants n axisIndex qs R N){s:State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R N g i hi s)
 {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}
 (forest:Contents p visits A positive s)(facts:Facts p visits)(hn:0<n)
 {O T:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤T)
 (radixRoom:radix n axisIndex≤envelope constants n)(sameRadix:p.radix=radix n axisIndex)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*UniformDirectLeafForestModel.demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*UniformDirectLeafForestModel.demand visits≤T)

lemma actual_rectangle_make (i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)(ht:t<slotCount n qs[i].row):
 (of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
  (slotPrefix n qs i+t) elapsed=
 (UniformActualCalendarRectangleRegistry.data g all i hi t ht).event _ _ _ _ _ _ _ _ elapsed:=by
 have bound:=UniformActualCalendarRectangleRegistry.global_bound n qs i hi t ht
 have main:=Scan.append_make_left
  (of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).rectangle.scan
  (Scan.flatten (List.ofFn (fun j=>
   ((of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).node j).scan)))
  (slotPrefix n qs i+t) elapsed bound
 refine main.trans ?_
 unfold of_actual
 dsimp only[Family.scan]
 change ((UniformActualCalendarRectangleRegistry.wholeFamily g all hn scalarRoom natRoom radixRoom).cast
  sameRadix.symm rfl (congrArg (fun r=>3*r+11) sameRadix.symm) rfl).make _ _=_
 rw[Family.cast_make]
 exact UniformActualCalendarRectangleRegistry.wholeFamily_make g all hn scalarRoom natRoom radixRoom i hi t elapsed ht

lemma actual_node_make (i:Fin visits.length)(j:Fin (UniformDirectLeafForestModel.operations visits[i]))(elapsed:ℕ):
 ((of_actual (p:=p) (visits:=visits) (A:=A) g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).node
  (nodeIndex p visits A i)).make j.val elapsed=
 UniformActualCalendarDirectProduced.event (UniformActualCalendarForestRegistry.data (p:=p) (A:=A) forest i j) elapsed:=by
 let f:=UniformActualCalendarForestRegistry.family forest facts entry pool nat (sameRadix.trans_le radixRoom) i
 have get:(UniformDirectLeafForestRangeSource.nodeRanges p visits A).get (nodeIndex p visits A i)=
  (⟨(position p visits i.val).entry,UniformDirectLeafForestModel.operations visits[i],
   UniformDirectLeafForestRangeSource.nodeRecords p visits A i.val i.isLt⟩:UniformCacheRangeSelector.Range):=
  List.getElem_ofFn (nodeIndex p visits A i).isLt
 have projection:
  ((of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).node
   (nodeIndex p visits A i)).make=f.make:=by
  unfold of_actual
  exact Family.range_make_mpr _ _ get f
 exact (congrFun (congrFun projection j.val) elapsed).trans
  (UniformActualCalendarForestRegistry.family_make forest facts entry pool nat
   (sameRadix.trans_le radixRoom) i j elapsed)

end
end ExactFourierCircuits.UniformActualCalendarRegistry
