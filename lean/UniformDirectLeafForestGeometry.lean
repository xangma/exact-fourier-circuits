import UniformDirectLeafForestData
import UniformCacheTimingBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafCacheLoopGeometry
open UniformDirectLeafCacheProducedSource UniformDirectLeafCacheChronology UniformDirectLeafCacheLoopBoot
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformWorkspacePlanner
open UniformCacheTimingBounds UniformLocalCacheTiming UniformCacheTimingReference
noncomputable section

lemma walk_extent(fuel k c v o:ℕ)(tasks:List Task)(good:Good v o tasks):
 ∀q∈(walk fuel k c tasks).1,q.task.width≤v ∧q.task.offset+q.task.width≤o+v:=by
 induction fuel generalizing k c tasks with
 | zero=>simp [walk]
 | succ fuel ih=>
  cases tasks with
  | nil=>simp [walk]
  | cons t ts=>
   intro q hq
   simp only[walk,List.mem_cons] at hq
   rcases hq with rfl|hq
   · exact good t (by simp)
   · exact ih (k+1) (c+7*UniformLocalRectangleDescriptors.emittedCount t.width) (children t k++ts) (good.children k) q hq
lemma root_extent(r R:ℕ)(q:Visit)(hq:q∈(walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1):
 q.task.width≤r ∧q.task.offset+q.task.width≤r:=by
 simpa only[Nat.zero_add] using walk_extent (2*r+1) 0 R r 0 [⟨r,0,0,0⟩]
  (by intro t ht;simp only[List.mem_singleton] at ht;subst t;simp) q hq
lemma root_leaf_duration(r R i:ℕ)(hi:i<(walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1.length)
 (stop:leaf (walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i]):
 (walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i].task.width+
  14*(walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i].task.width*
  ((walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i].task.width-1)≤
 planDuration (UniformBalancedToeplitz.plan r):=by
 have h:=root_duration_le r 0 R i hi
 unfold taskDuration at h
 change (walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i].task.width<2 ∨
  selected (walk (2*r+1) 0 R [⟨r,0,0,0⟩]).1[i].task.width=0 at stop
 rw[UniformBalancedToeplitz.plan,dite_eq_left stop] at h
 simpa only[ofPlan,treeDuration,directDuration] using h

structure Layout(p:Parameters)(A C B:ℕ)(visits:List Visit):Prop where
 rows:p.start.rows+3≤p.start.permutation
 widths:p.start.widths=p.start.permutation+p.radix
 markers:p.start.markers=p.start.permutation+2*p.radix
 axis:p.start.axis=p.start.permutation+3*p.radix
 entry:p.start.entry=p.start.permutation+3*p.radix+4
 cacheEnd:p.start.permutation+(3*p.radix+11)*demand visits≤p.forward
 natEnd:p.start.permutation+(3*p.radix+11)*demand visits+3*p.radix+4≤B
 scalarEnd:p.start.pool+9*p.radix*demand visits≤B
 descriptors:p.forward+4*p.radix^2≤p.transpose
 descriptorEnd:p.transpose+4*p.radix^2≤B
 constants:6≤p.start.pool
 directory:p.start.originalDirectory+2≤p.start.rows
 conjugateDirectory:p.start.conjugateDirectory+1≤p.start.rows
 original:A+4*p.radix≤p.start.pool
 conjugate:C+4*p.radix≤p.start.pool
 time:2*p.rootDuration+5≤B
 scalarStride:9*p.radix≤B
 natStride:3*p.radix+11≤B
 code:461≤B

def config(p:Parameters)(visits:List Visit)(i:ℕ):UniformDirectLeafCacheReader.Config:=
 {position p visits i with record:=p.forward,time:=0}

/-- Full ordinary layout for the next literal388 follows from the actual
prefix count and the genuine leaf's extent/duration, not a ready pool. -/
lemma phase_layout {p:Parameters}{A C B i:ℕ}{visits:List Visit}
 (l:Layout p A C B visits)(hi:i<visits.length)(stop:leaf visits[i])
 (extent:visits[i].task.width≤p.radix)
 (duration:visits[i].task.width+14*visits[i].task.width*(visits[i].task.width-1)≤p.rootDuration):
 UniformDirectLeafHighGeometry.Layout (config p visits i) p.radix A C B
  (records visits[i].task.width visits[i].task.offset (A+3*p.radix) 0):=by
 have next:=before_next visits i hi
 have oper:operations visits[i]=UniformDirectLeafCacheLoopBoot.size visits[i].task.width:=ite_eq_left stop
 rw[oper] at next
 have endCount:=before_le visits (i+1)
 have current:=before_le visits i
 have scalar:=l.scalarEnd
 have nat:=l.natEnd
 have desc:=l.cacheEnd
 have countBound:UniformDirectLeafCacheLoopBoot.size visits[i].task.width≤p.radix^2:=by
  have h:=UniformJointCacheTime.leaf_records_bound visits[i].task.width 0 0
  rw[UniformTransposeDescriptorMachine.leafRecords_length] at h
  change visits[i].task.width+visits[i].task.width*(visits[i].task.width-1)/2≤visits[i].task.width^2 at h
  exact h.trans (Nat.pow_le_pow_left extent 2)
 constructor
 · simp only[config,position];have:=l.rows;omega
 · simp only[config,position];rw[l.widths];omega
 · simp only[config,position];rw[l.markers];omega
 · simp only[config,position];rw[l.axis];omega
 · simp only[config,position];rw[l.entry];omega
 · simp only[config,position,records_length]
   nlinarith
 · simp only[config,position,records_length]
   nlinarith
 · simp only[config,position];have:=l.constants;omega
 · simp only[config,position,records_length]
   have:=l.descriptors;have:=l.descriptorEnd;nlinarith
 · simp only[config,position,records_length]
   nlinarith
 · simpa only[config,position] using l.directory
 · simpa only[config,position] using l.conjugateDirectory
 · simp only[config,position];have:=l.original;nlinarith
 · simp only[config,position];have:=l.conjugate;nlinarith
 · simp only[config,UniformDirectLeafHighFinal.records_elapsed]
   have:=l.time;omega
 · have:=l.code;omega
end
end ExactFourierCircuits.UniformDirectLeafForestGeometry
