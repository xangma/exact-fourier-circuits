import UniformDirectLeafForestState
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestCacheRetention
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestModel
open UniformDirectLeafForestPrefix UniformDirectLeafForestState UniformLocalCacheTreeMachine
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
noncomputable section

lemma earlier_bounds {p:Parameters}{visits:List Visit}{A C B i j k:ℕ}
 (l:Placement p A C B visits)(_facts:Facts p visits)(hi:i<visits.length)(hj : j < i)
 (stop:leaf visits[j])(hk:k<(UniformDirectLeafForestLeafEnd.qs p A visits[j]).length):
 (slot (UniformDirectLeafForestForward.config p visits j) p.radix
   (UniformDirectLeafForestLeafEnd.qs p A visits[j]) k).pool+9*p.radix≤(position p visits i).pool ∧
 (slot (UniformDirectLeafForestForward.config p visits j) p.radix
   (UniformDirectLeafForestLeafEnd.qs p A visits[j]) k).entry+7≤(position p visits i).permutation ∧
 p.start.permutation≤(slot (UniformDirectLeafForestForward.config p visits j) p.radix
   (UniformDirectLeafForestLeafEnd.qs p A visits[j]) k).permutation:=by
 have jl:j<visits.length:=by omega
 have next:=before_next visits j jl
 rw[show operations visits[j]=size visits[j].task.width from ite_eq_left stop] at next
 rw[UniformDirectLeafForestLeafEnd.count] at hk
 have mono:=before_mono visits (show j+1≤ i by omega)
 have rank:before visits j+k+1≤before visits i:=by omega
 have scalar:=Nat.mul_le_mul_left (9*p.radix) rank
 have nat:=Nat.mul_le_mul_left (3*p.radix+11) rank
 have entry:=l.entry
 simp only[slot,UniformDirectLeafForestForward.config,position]
 constructor
 · nlinarith only[scalar]
 constructor
 · nlinarith only[nat,entry]
 · omega

lemma cached_transport {p:Parameters}{visits:List Visit}{i A C B:ℕ}{s u:State}
 (l:Placement p A C B visits)(facts:Facts p visits)(hi:i<visits.length)(positive:2≤p.radix)
 (old:Cached p visits A positive i s)
 (frame:UniformDirectLeafForestLeafStep.StepFrame p visits i s u):Cached p visits A positive i u:=by
 intro j hj lower stop k hk
 obtain ⟨event⟩:=old j hj lower stop k hk
 have bounds:=earlier_bounds l facts hi lower stop hk
 have extent:=facts.extent j hj
 have duration:=facts.duration j hj stop
 have layout:=UniformDirectLeafForestGeometry.phase_layout l.toLayout hj stop (by omega) duration
 have good:=records_valid visits[j].task.width visits[j].task.offset (A+3*p.radix) 0 p.radix extent
  (UniformDirectLeafForestLeafEnd.qs p A visits[j])[k] (List.getElem_mem hk)
 apply Nonempty.intro
 apply UniformDirectLeafCacheSemanticRetention.result event
  (UniformDirectLeafHighGeometry.slot_layout layout k hk) good.1.1 good.1.2.1
 · intro a _ upper
   exact frame.scalarOutside a (Or.inl (upper.trans_le bounds.1))
 · intro a lower upper
   exact frame.natBefore a (upper.trans_le bounds.2.1)
    (Or.inr (by have:=l.rows;omega))
    (Or.inr (by have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;omega))

lemma ranges_transport {p:Parameters}{visits:List Visit}{i A C B:ℕ}{s u:State}
 (l:Placement p A C B visits)(hi:i<visits.length)(old:Ranges p visits i s)
 (frame:UniformDirectLeafForestLeafStep.StepFrame p visits i s u):Ranges p visits i u:=by
 intro j hj lower
 obtain ⟨first,count⟩:=old j hj lower
 have perm:p.start.permutation≤(position p visits i).permutation:=by simp only[position];omega
 constructor
 · rw[frame.natBefore _ (by have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;omega)
     (Or.inr (by have:=l.rangesAbove;omega)) (Or.inl (by omega))]
   exact first
 · rw[frame.natBefore _ (by have:=l.rangeEnd;have:=l.nodeEnd;have:=l.rows;omega)
     (Or.inr (by have:=l.rangesAbove;omega)) (Or.inl (by omega))]
   exact count

lemma counts_transport {p:Parameters}{visits:List Visit}{i A C B:ℕ}{s u:State}
 (l:Placement p A C B visits)(hi:i<visits.length)(old:UniformDirectLeafForestBoot.Counts p visits s)
 (frame:UniformDirectLeafForestLeafStep.StepFrame p visits i s u):UniformDirectLeafForestBoot.Counts p visits u:=by
 have perm:p.start.permutation≤(position p visits i).permutation:=by simp only[position];omega
 constructor
 · rw[frame.natBefore _ (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.headerEnd;have:=l.nodeEnd;have:=l.rows;omega)
    (Or.inr (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.rangesAbove;omega))
    (Or.inr (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.rangeCount;omega))]
   exact old.rectangles
 · rw[frame.natBefore _ (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.headerEnd;have:=l.nodeEnd;have:=l.rows;omega)
    (Or.inr (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.rangesAbove;omega))
    (Or.inr (by unfold UniformDirectLeafForestBoot.countHeader;have:=l.rangeCount;omega))]
   exact old.nodes
end
end ExactFourierCircuits.UniformDirectLeafForestCacheRetention
