import UniformDirectLeafForestState
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestTransport
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformLocalCacheTreeMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
noncomputable section
lemma sources {p:Parameters}{visits:List Visit}{n:ℕ}{s u:State}
 (h:Sources p visits n s)(nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap):Sources p visits n u:=by
 refine ⟨UniformDirectLeafForestLeafCall.original_transport h.original nh sh,
  UniformDirectLeafForestLeafCall.conjugate_transport h.conjugate nh sh,
  UniformDirectLeafForestLeafCall.constants_transport h.constants sh,?_,?_⟩
 · intro i hi z
   change u.natHeap (p.nodes+7*i+z.val)=some (UniformLocalCacheTreeIteration.nodeWords visits[i].task visits[i].rectangleBase)[z]
   rw[nh]
   exact h.nodes i hi z
 · intro i hi
   rw[nh]
   exact h.starts i hi
lemma counts {p:Parameters}{visits:List Visit}{s u:State}
 (h:UniformDirectLeafForestBoot.Counts p visits s)(nh:u.natHeap=s.natHeap):
 UniformDirectLeafForestBoot.Counts p visits u:=by
 constructor
 · rw[nh];exact h.rectangles
 · rw[nh];exact h.nodes
lemma ranges {p:Parameters}{visits:List Visit}{upto:ℕ}{s u:State}
 (h:Ranges p visits upto s)(nh:u.natHeap=s.natHeap):Ranges p visits upto u:=by
 intro i hi low
 constructor
 · rw[nh];exact (h i hi low).first
 · rw[nh];exact (h i hi low).count
lemma cached {p:Parameters}{visits:List Visit}{A C B upto:ℕ}{positive:2≤p.radix}{s u:State}
 (h:Cached p visits A positive upto s)(l:UniformDirectLeafForestGeometry.Layout p A C B visits)
 (facts:Facts p visits)(nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap):
 Cached p visits A positive upto u:=by
 intro i hi low stop j hj
 obtain ⟨event⟩:=h i hi low stop j hj
 have extent:=facts.extent i hi
 have duration:=facts.duration i hi stop
 have layout:=UniformDirectLeafForestGeometry.phase_layout l hi stop (by omega) duration
 have good:=records_valid visits[i].task.width visits[i].task.offset (A+3*p.radix) 0 p.radix extent
  (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j] (List.getElem_mem hj)
 apply Nonempty.intro
 apply UniformDirectLeafCacheSemanticRetention.result event
  (UniformDirectLeafHighGeometry.slot_layout layout j hj) good.1.1 good.1.2.1
 · intro a _ _;exact congrFun sh a
 · intro a _ _;exact congrFun nh a
end
end ExactFourierCircuits.UniformDirectLeafForestTransport
