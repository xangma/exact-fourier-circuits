import UniformCalendarActualAtoms
import UniformActualCacheRectangleSource
import UniformActualCalendarForestRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarAtomRecords
noncomputable section
open UniformLocalCacheTiming UniformLocalRequestPlan UniformCalendarActualAtoms UniformActualCalendarMacroOrder
open UniformCalendarIntervalPartition UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformLocalCacheTreeMachine

lemma rectangle_records (n:ℕ)(q:Request):
 records n ⟨q.time,.rectangle q.row⟩=UniformActualCacheRectangleSource.block n q:=by
 apply List.ext_getElem
 · simp only[records_length,durations,List.length_replicate,
    UniformActualCacheRectangleSource.block_length]
 · intro i hi hj
   have bound:i<slotCount n q.row:=by
    simpa only[UniformActualCacheRectangleSource.block_length] using hj
   have get:=records_get n ⟨q.time,.rectangle q.row⟩ ⟨i,hi⟩
   have clock:=rectangle_prefix n q.row i bound.le
   have value:(durations n (.rectangle q.row)).get ⟨i,by simpa only[records_length] using hi⟩=28:=
    List.getElem_replicate (by simpa only[records_length,durations] using hi)
   have right:(UniformActualCacheRectangleSource.block n q)[i]'hj=(q.time+28*i,0):=List.getElem_ofFn hj
   apply get.trans
   apply Eq.trans ?_ right.symm
   change (q.time+prefixDuration (durations n (.rectangle q.row)) i,kind ((durations n (.rectangle q.row)).get _))=_
   rw[clock,value]
   rfl

lemma leaf_durations (v o K:ℕ):
 (leafRecords v o K).map duration=(leafRecords v o 0).map duration:=by
 simp only[leafRecords,List.map_map]
 congr 1
 funext op
 cases op <;>rfl

lemma leaf_prefix (v o K j:ℕ):
 elapsed ((leafRecords v o K).take j)=prefixDuration (durations 0 (.direct v o)) j:=by
 rw[elapsed,List.map_take,leaf_durations]
 rfl

lemma record_kind (q:Record):kind (duration q)=cacheKind q:=by
 by_cases scale:q.kind=0
 · simp only[duration,cacheKind,scale,ite_true,kind,ite_true]
 · simp only[duration,cacheKind,scale,ite_false,kind,show ¬(28:ℕ)=1 by decide,ite_false]

lemma node_record (p:Parameters)(visits:List Visit)(A:ℕ)(i:Fin visits.length)(j:ℕ)
 (bound:j<(UniformDirectLeafForestLeafEnd.qs p A (visits.get i)).length):
 UniformDirectLeafForestRangeSource.nodeRecords p visits A i.val i.isLt j=
 (elapsed ((UniformDirectLeafForestLeafEnd.qs p A (visits.get i)).take j),
  cacheKind ((UniformDirectLeafForestLeafEnd.qs p A (visits.get i))[j]'bound)):=by
 have exactBound:j<(UniformDirectLeafForestLeafEnd.qs p A visits[i.val]).length:=bound
 rw[UniformDirectLeafForestRangeSource.nodeRecords,dite_eq_left exactBound]
 change (0+elapsed ((UniformDirectLeafForestLeafEnd.qs p A (visits.get i)).take j),_)=_
 rw[Nat.zero_add]
 rfl

lemma forest_block (n:ℕ)(p:Parameters)(visits:List Visit)(A:ℕ)(i:Fin visits.length):
 UniformActualCalendarForestRegistry.block p visits A i=
 (directEvents (visits.get i)).flatMap (records n):=by
 by_cases stop:leaf (visits.get i)
 · have bad:(visits.get i).task.width<2 ∨UniformWorkspacePlanner.selected (visits.get i).task.width=0:=stop
   have count:operations visits[i]=UniformDirectLeafCacheLoopBoot.size (visits.get i).task.width:=ite_eq_left stop
   simp only[UniformActualCalendarMacroOrder.directEvents,bad,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   apply List.ext_getElem
   · rw[UniformActualCalendarForestRegistry.block,List.length_ofFn,count,records_length]
     simp only[durations,List.length_map,leafRecords_length]
     rfl
   · intro j hj hk
     have bound:j<(UniformDirectLeafForestLeafEnd.qs p A (visits.get i)).length:=by
      rw[UniformDirectLeafForestLeafEnd.count]
      rw[UniformActualCalendarForestRegistry.block,List.length_ofFn,count] at hj
      exact hj
     have physical:=UniformActualCalendarForestRegistry.block_get (p:=p) (A:=A) i ⟨j,hj⟩
     have canonical:=records_get n ⟨0,.direct (visits.get i).task.width (visits.get i).task.offset⟩ ⟨j,hk⟩
     apply physical.trans
     apply Eq.trans ?_ canonical.symm
     rw[node_record p visits A i j bound]
     change (elapsed ((leafRecords (visits.get i).task.width (visits.get i).task.offset (A+3*p.radix)).take j),_)=
      (0+prefixDuration (durations n (.direct (visits.get i).task.width (visits.get i).task.offset)) j,_)
     rw[Nat.zero_add]
     apply Prod.ext
     · exact leaf_prefix _ _ _ _
     · have left:j<(leafRecords (visits.get i).task.width (visits.get i).task.offset (A+3*p.radix)).length:=bound
       have right:j<(leafRecords (visits.get i).task.width (visits.get i).task.offset 0).length:=by
        simpa only[leafRecords_length] using left
       have value:=congrArg (fun L:List ℕ=>L[j]?)
        (leaf_durations (visits.get i).task.width (visits.get i).task.offset (A+3*p.radix))
       have eq:duration ((leafRecords (visits.get i).task.width (visits.get i).task.offset (A+3*p.radix))[j]'left)=
        duration ((leafRecords (visits.get i).task.width (visits.get i).task.offset 0)[j]'right):=by
         simpa only[List.getElem?_map,List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,
          Option.map_some,Option.some.injEq] using value
       have mapped:(durations n (.direct (visits.get i).task.width (visits.get i).task.offset)).get
        ⟨j,by simpa only[records_length] using hk⟩=
        duration ((leafRecords (visits.get i).task.width (visits.get i).task.offset 0)[j]'right):=List.getElem_map duration
       exact (record_kind _).symm.trans ((congrArg kind eq).trans (congrArg kind mapped).symm)
 · have bad:¬((visits.get i).task.width<2 ∨UniformWorkspacePlanner.selected (visits.get i).task.width=0):=stop
   have count:operations visits[i]=0:=ite_eq_right stop
   have empty:UniformActualCalendarForestRegistry.block p visits A i=[]:=by
    apply List.eq_nil_of_length_eq_zero
    rw[UniformActualCalendarForestRegistry.block,List.length_ofFn,count]
   rw[empty,UniformActualCalendarMacroOrder.directEvents,ite_eq_right bad]
   rfl

end
end ExactFourierCircuits.UniformActualCalendarAtomRecords
