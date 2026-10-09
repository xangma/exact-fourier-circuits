import UniformDirectLeafForestFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestContents
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformLocalCacheTreeMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
noncomputable section

/-- Durable factual cache/range data. Mutable controller registers and the
separately retained global seed banks are deliberately absent. -/
structure Contents(p:Parameters)(visits:List Visit)(A:ℕ)(positive:2≤p.radix)(s:State):Prop where
 counts:UniformDirectLeafForestBoot.Counts p visits s
 ranges:Ranges p visits visits.length s
 cached:Cached p visits A positive visits.length s
 root:s.natHeap p.durations=some p.rootDuration
lemma ofPost {p:Parameters}{visits:List Visit}{n A:ℕ}{positive:2≤p.radix}{s:State}
 (h:UniformDirectLeafForestExecution.Post p visits n A positive s):Contents p visits A positive s:=
 ⟨h.counts,h.ranges,h.cached,h.root⟩

lemma slot_bounds {p:Parameters}{visits:List Visit}{A i j:ℕ}
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (hi:i<visits.length)(stop:leaf visits[i])
 (hj:j<(UniformDirectLeafForestLeafEnd.qs p A visits[i]).length):
 p.start.pool≤(slot (UniformDirectLeafForestForward.config p visits i) p.radix
  (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j).pool ∧
 (slot (UniformDirectLeafForestForward.config p visits i) p.radix
  (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j).pool+9*p.radix≤
  p.start.pool+9*p.radix*demand visits ∧
 p.start.permutation≤(slot (UniformDirectLeafForestForward.config p visits i) p.radix
  (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j).permutation ∧
 (slot (UniformDirectLeafForestForward.config p visits i) p.radix
  (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j).entry+7≤
  p.start.permutation+(3*p.radix+11)*demand visits:=by
 rw[UniformDirectLeafForestLeafEnd.count] at hj
 have next:=before_next visits i hi
 rw[show operations visits[i]=size visits[i].task.width from ite_eq_left stop] at next
 have total:=before_le visits (i+1)
 have rank:before visits i+j+1≤demand visits:=by omega
 have scalar:=Nat.mul_le_mul_left (9*p.radix) rank
 have nat:=Nat.mul_le_mul_left (3*p.radix+11) rank
 simp only[slot,UniformDirectLeafForestForward.config,position]
 refine ⟨by omega,?_,by omega,?_⟩
 · nlinarith only[scalar]
 · nlinarith only[nat,entry]

/-- Equality of the actual retained axis intervals transports every generated
factor/axis/range cell, after later axis controllers have overwritten registers. -/
lemma transport {p:Parameters}{visits:List Visit}{A C B N H S E:ℕ}{positive:2≤p.radix}{s u:State}
 (old:Contents p visits A positive s)(l:Placement p A C B visits)(facts:Facts p visits)
 (natLow:N≤p.ranges)(natEnd:p.start.permutation+(3*p.radix+11)*demand visits≤H)
 (headerEnd:UniformDirectLeafForestBoot.countHeader p+2≤H)(durationLow:N≤p.durations)(durationEnd:p.durations<H)
 (scalarLow:S≤p.start.pool)(scalarEnd:p.start.pool+9*p.radix*demand visits≤E)
 (nh:∀a,N≤a→a<H→u.natHeap a=s.natHeap a)
 (sh:∀a,S≤a→a<E→u.scalarHeap a=s.scalarHeap a):Contents p visits A positive u:=by
 have pLow:N≤p.start.permutation:=by have:=l.rangeEnd;have:=l.nodeEnd;omega
 have pEnd:p.start.permutation≤H:=by omega
 constructor
 · constructor
   · rw[nh _ (by unfold UniformDirectLeafForestBoot.countHeader;omega) (by omega)]
     exact old.counts.rectangles
   · rw[nh _ (by unfold UniformDirectLeafForestBoot.countHeader;omega) (by omega)]
     exact old.counts.nodes
 · intro i hi _
   constructor
   · rw[nh _ (by omega) (by have:=l.rangeEnd;have:=l.nodeEnd;omega)]
     exact (old.ranges i hi hi).first
   · rw[nh _ (by omega) (by have:=l.rangeEnd;have:=l.nodeEnd;omega)]
     exact (old.ranges i hi hi).count
 · intro i hi low stop j hj
   obtain ⟨event⟩:=old.cached i hi low stop j hj
   have extent:=facts.extent i hi
   have duration:=facts.duration i hi stop
   have layout:=UniformDirectLeafForestGeometry.phase_layout l.toLayout hi stop (by omega) duration
   have good:=records_valid visits[i].task.width visits[i].task.offset (A+3*p.radix) 0 p.radix extent
    (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j] (List.getElem_mem hj)
   have bounds:=slot_bounds l.entry hi stop hj
   apply Nonempty.intro
   apply UniformDirectLeafCacheSemanticRetention.result event
    (UniformDirectLeafHighGeometry.slot_layout layout j hj) good.1.1 good.1.2.1
   · intro a low high
     exact sh a (by omega) (by omega)
   · intro a low high
     exact nh a (by omega) (by omega)
 · rw[nh _ durationLow durationEnd]
   exact old.root
end
end ExactFourierCircuits.UniformDirectLeafForestContents
