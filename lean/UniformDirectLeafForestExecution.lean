import UniformDirectLeafForestInitialization
import UniformDirectLeafForestTransport
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestExecution
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformDirectLeafForestIteration UniformDirectLeafForestBoot
open UniformLocalCacheTreeMachine
noncomputable section

structure Post(p:Parameters)(visits:List Visit)(n A:ℕ)(positive:2≤p.radix)(s:State):Prop where
 pc:s.pc=460
 sources:Sources p visits n s
 counts:Counts p visits s
 ranges:Ranges p visits visits.length s
 cached:Cached p visits A positive visits.length s
 endpoints:UniformDirectLeafForestExit.Endpoints p visits s
 root:s.natHeap p.durations=some p.rootDuration

structure Frame(p:Parameters)(visits:List Visit)(s u:State):Prop where
 scalarOutside:∀a,(a<p.start.pool∨(position p visits visits.length).pool≤a)→u.scalarHeap a=s.scalarHeap a
 natBefore:∀a,a<p.start.permutation→(a<p.start.rows∨p.start.rows+3≤a)→
  (a<p.ranges∨p.ranges+2*visits.length≤a)→
  (a<countHeader p∨countHeader p+2≤a)→u.natHeap a=s.natHeap a
 natHigh:∀a,p.transpose+4*p.radix^2≤a→u.natHeap a=s.natHeap a
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

/-- The fixed461 program derives its rectangle count from measured real
pool endpoints, writes both durable counts, scans the actual directory,
executes388 only on genuine leaves, and returns measured cache ends.
Coefficient banks come solely from the retained original/conjugate seeds. -/
theorem execution {p:Parameters}{visits:List Visit}{n B:ℕ}
 (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))(x:Fin n→ℂ)(s:State)
 (h:Header p visits s)(src:Sources p visits n s)(facts:Facts p visits)(bounds:SeedBounds p n)
 (radix:p.radix=UniformAllAxisSeedPreparation.radix n axis)(positive:2≤p.radix)
 (od:p.start.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:p.start.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (l:Placement p (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B visits)
 (index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)
 (pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution UniformDirectLeafForestProgram.program n x B s ticks u ∧
 ticks≤(62*p.radix+246)*demand visits+93*visits.length+40 ∧
 Post p visits n (UniformAllAxisSeedPreparation.axisBase n axis.val) positive u ∧
 Frame p visits s u:=by
 have headerB:countHeader p+2≤B:=by unfold countHeader;have:=l.headerEnd;have:=l.nodeEnd;have:=l.natEnd;omega
 have boot:=complete_execution x s h index (by omega) l.scalarStride headerB l.code pc wb
 have initial:=UniformDirectLeafForestInitialization.invariant h index positive src l bounds pc
 obtain ⟨u,ticks,body,cost,inv,frame⟩:=UniformDirectLeafForestLoop.remaining axis x positive facts bounds
  radix od cd l visits.length 0 (completed s) (by omega) initial boot.final_bound
 have exit:=UniformDirectLeafForestExit.execution x u inv.cursor l.code inv.pc body.final_bound
 let v:=UniformDirectLeafForestExit.finished u
 have total:BoundedExecution UniformDirectLeafForestProgram.program n x B s (31+ticks+9) v:=
  (boot.trans body).executes exit
 have kept:Frame p visits s v:=by
  constructor
  · intro a outside
    exact frame.scalarOutside a outside
  · intro a lower rows ranges counts
    exact (frame.natBefore a lower rows ranges).trans (UniformDirectLeafForestInitialization.completed_outside h index (by omega) a counts)
  · intro a high
    exact (frame.natHigh a high).trans (UniformDirectLeafForestInitialization.completed_outside h index (by omega) a (Or.inr (by
     unfold countHeader;have:=l.headerEnd;have:=l.nodeEnd;have:=l.cacheEnd;have:=l.descriptors;omega)))
  · exact frame.outputs
  · exact frame.roots
 refine ⟨v,31+ticks+9,total,?_,?_,kept⟩
 · simp only[before_zero,Nat.mul_zero,Nat.add_zero] at cost
   omega
 · refine ⟨rfl,UniformDirectLeafForestTransport.sources inv.sources rfl rfl,
    UniformDirectLeafForestTransport.counts inv.counts rfl,
    UniformDirectLeafForestTransport.ranges inv.ranges rfl,
    UniformDirectLeafForestTransport.cached inv.cached l.toLayout facts rfl rfl,
    UniformDirectLeafForestExit.endpoints inv.cursor,?_⟩
   rw[kept.natHigh p.durations l.durationsHigh]
   exact h.root
end
end ExactFourierCircuits.UniformDirectLeafForestExecution
