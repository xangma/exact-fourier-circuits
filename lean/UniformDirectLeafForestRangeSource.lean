import UniformDirectLeafForestContents
import UniformCacheRangeSelectorData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestRangeSource
open UniformMachine UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestModel
open UniformDirectLeafForestContents UniformLocalCacheTreeMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
noncomputable section

def nodeRecords(p:Parameters)(visits:List Visit)(A i:ℕ)(hi:i<visits.length)(j:ℕ):ℕ×ℕ:=
 let qs:=UniformDirectLeafForestLeafEnd.qs p A visits[i]
 if hj:j<qs.length then
  ((slot (UniformDirectLeafForestForward.config p visits i) p.radix qs j).time,
   UniformDirectLeafCacheChronology.cacheKind qs[j]) else (0,0)
def nodeRanges(p:Parameters)(visits:List Visit)(A:ℕ):List UniformCacheRangeSelector.Range:=
 List.ofFn (fun i:Fin visits.length=>⟨(position p visits i.val).entry,operations visits[i],
  nodeRecords p visits A i.val i.isLt⟩)

lemma node_source {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:State}
 (h:Contents p visits A positive s):UniformCacheRangeSelector.NodeSource p.radix p.ranges 0
  (nodeRanges p visits A) s.natHeap:=by
 intro i hi
 have il:i<visits.length:=by simpa only[nodeRanges,List.length_ofFn] using hi
 have get:(nodeRanges p visits A)[i]=
  (⟨(position p visits i).entry,operations visits[i],nodeRecords p visits A i il⟩:UniformCacheRangeSelector.Range):=by
  simp only[nodeRanges,List.getElem_ofFn]
  rfl
 obtain ⟨first,count⟩:=h.ranges i il il
 rw[get]
 refine ⟨by simpa only[Nat.zero_add] using first,by simpa only[Nat.zero_add] using count,?_⟩
 intro j hj
 have stop:leaf visits[i]:=by
  by_contra neg
  simp only[operations,ite_eq_right neg] at hj
  omega
 have jl:j<(UniformDirectLeafForestLeafEnd.qs p A visits[i]).length:=by
  simpa only[operations,ite_eq_left stop,UniformDirectLeafForestLeafEnd.count] using hj
 obtain ⟨event⟩:=h.cached i il il stop j jl
 have time:=event.entry.1
 have kind:=event.entry.2.2.2.2.2.2
 rw[event.kind_eq] at kind
 change s.natHeap ((position p visits i).entry+(3*p.radix+11)*j)=some (nodeRecords p visits A i il j).1 ∧
  s.natHeap ((position p visits i).entry+(3*p.radix+11)*j+6)=some (nodeRecords p visits A i il j).2
 simpa only[nodeRecords,dite_eq_left jl,slot,UniformDirectLeafForestForward.config] using And.intro time kind

/-- The actual durable forest fields and generated leaf entries supply the
whole range selector bank; only the independently generated rectangle bank
is combined here. No leaf count/start/kind table is supplied separately. -/
lemma range_source {p:Parameters}{visits:List Visit}{A control:ℕ}{positive:2≤p.radix}{s:State}
 (h:Contents p visits A positive s)(rectangle:ℕ→ℕ×ℕ)
 (rect:UniformGlobalCalendarSelector.Source (control+3*p.radix+4) (3*p.radix+11) p.rectangles rectangle s.natHeap):
 UniformCacheRangeSelector.RangeSource p.radix p.ranges control p.rectangles rectangle
  (nodeRanges p visits A) s.natHeap:=by
 refine ⟨h.counts.rectangles,?_,rect,node_source h⟩
 simpa only[nodeRanges,List.length_ofFn,Nat.add_assoc,UniformDirectLeafForestBoot.countHeader] using h.counts.nodes
end
end ExactFourierCircuits.UniformDirectLeafForestRangeSource
