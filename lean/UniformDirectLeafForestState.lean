import UniformDirectLeafForestSplit
import UniformDirectLeafForestPrefix
import UniformDirectLeafForestBoot
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestState
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestModel
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource UniformDirectLeafCacheLoopBoot
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration
noncomputable section

structure Placement(p:Parameters)(A C B:ℕ)(visits:List Visit):Prop extends
 UniformDirectLeafForestGeometry.Layout p A C B visits where
 rangeEnd:p.ranges+2*visits.length≤p.nodes
 headerEnd:p.ranges+4*p.radix+6≤p.nodes
 rangeCount:2*visits.length≤4*p.radix+4
 rangesAbove:p.start.rows+3≤p.ranges
 nodeEnd:p.nodes+7*visits.length≤p.start.permutation
 startsHigh:p.transpose+4*p.radix^2≤p.starts
 durationsHigh:p.transpose+4*p.radix^2≤p.durations
 startsEnd:p.starts+visits.length≤B
 ordinal:p.rectangles+demand visits≤B

structure SeedBounds(p:Parameters)(n:ℕ):Prop where
 original:∀(j:Fin (UniformAllAxisSeedPreparation.axisCount n))(q:Fin 5)
  (t:Fin (UniformAllAxisSeedPreparation.radix n j)),
  UniformAllAxisSeedPreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+t.val<p.start.pool
 conjugate:∀(j:Fin (UniformAllAxisSeedPreparation.axisCount n))(q:Fin 5)
  (t:Fin (UniformAllAxisSeedPreparation.radix n j)),
  UniformAllAxisConjugatePreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+t.val<p.start.pool
 originalDir:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤p.ranges
 conjugateDir:UniformAllAxisConjugatePreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤p.ranges
 originalDirLow:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤p.start.rows
 conjugateDirLow:UniformAllAxisConjugatePreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤p.start.rows

structure Sources(p:Parameters)(visits:List Visit)(n:ℕ)(s:State):Prop where
 original:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s
 conjugate:UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s
 constants:UniformHadamardPairMachine.Constants s
 nodes:∀i (hi:i<visits.length),AtNode p.nodes i visits[i].task visits[i].rectangleBase s
 starts:∀i,i<visits.length→s.natHeap (p.starts+i)=some 0

structure RangeAt(p:Parameters)(visits:List Visit)(i:ℕ)(hi:i<visits.length)(s:State):Prop where
 first:s.natHeap (p.ranges+2*i)=some (position p visits i).entry
 count:s.natHeap (p.ranges+2*i+1)=some (operations visits[i])
def Ranges(p:Parameters)(visits:List Visit)(upto:ℕ)(s:State):Prop:=
 ∀i (hi:i<visits.length),i<upto→RangeAt p visits i hi s

def Cached(p:Parameters)(visits:List Visit)(A:ℕ)(positive:2≤p.radix)(upto:ℕ)(s:State):Prop:=
 ∀i (hi:i<visits.length),i<upto→leaf visits[i]→
 ∀j (hj:j<(UniformDirectLeafForestLeafEnd.qs p A visits[i]).length),Nonempty
  (UniformDirectLeafCacheSemanticExecution.SemanticResult
   (slot (UniformDirectLeafForestForward.config p visits i) p.radix
    (UniformDirectLeafForestLeafEnd.qs p A visits[i]) j) p.radix
   (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j]
   (UniformDirectLeafCacheSource.mu p.radix (A+3*p.radix)
    (UniformDirectLeafForestLeafEnd.qs p A visits[i])[j]) positive s)

structure Facts(p:Parameters)(visits:List Visit):Prop where
 extent:∀i (hi:i<visits.length),visits[i].task.offset+visits[i].task.width≤p.radix
 duration:∀i (hi:i<visits.length),leaf visits[i]→visits[i].task.width+
  14*visits[i].task.width*(visits[i].task.width-1)≤p.rootDuration

lemma Sources.withPC {p:Parameters}{visits:List Visit}{n pc:ℕ}{s:State}(h:Sources p visits n s):
 Sources p visits n (setPC s pc):=by
 refine ⟨UniformDirectLeafForestLeafCall.original_transport h.original rfl rfl,
  UniformDirectLeafForestLeafCall.conjugate_transport h.conjugate rfl rfl,
  UniformDirectLeafForestLeafCall.constants_transport h.constants rfl,?_,?_⟩
 · exact h.nodes
 · exact h.starts

lemma sources_transport {p:Parameters}{visits:List Visit}{i n A C B:ℕ}{s u:State}
 (h:Sources p visits n s)(bounds:SeedBounds p n)(l:Placement p A C B visits)
 (hi:i<visits.length)(frame:UniformDirectLeafForestLeafStep.StepFrame p visits i s u):
 Sources p visits n u:=by
 have current:p.start.pool≤(position p visits i).pool:=by simp only[position];omega
 have perm:p.start.permutation≤(position p visits i).permutation:=by simp only[position];omega
 have rows:=l.rows
 have ranges:=l.rangeEnd
 have nodeEnd:=l.nodeEnd
 constructor
 · constructor
   · intro j hj q t
     exact (frame.scalarOutside _ (Or.inl ((bounds.original j q t).trans_le current))).trans (h.original.coefficients j hj q t)
   · intro j hj
     exact (frame.natBefore _ (by have:=bounds.originalDir;have:=j.isLt;omega)
      (Or.inl (by have:=bounds.originalDirLow;have:=j.isLt;omega))
      (Or.inl (by have:=bounds.originalDir;have:=j.isLt;omega))).trans (h.original.address j hj)
   · intro j hj
     exact (frame.natBefore _ (by have:=bounds.originalDir;have:=j.isLt;omega)
      (Or.inl (by have:=bounds.originalDirLow;have:=j.isLt;omega))
      (Or.inl (by have:=bounds.originalDir;have:=j.isLt;omega))).trans (h.original.width j hj)
 · constructor
   · intro j hj q t
     exact (frame.scalarOutside _ (Or.inl ((bounds.conjugate j q t).trans_le current))).trans (h.conjugate.coefficients j hj q t)
   · intro j hj
     exact (frame.natBefore _ (by have:=bounds.conjugateDir;have:=j.isLt;omega)
      (Or.inl (by have:=bounds.conjugateDirLow;have:=j.isLt;omega))
      (Or.inl (by have:=bounds.conjugateDir;have:=j.isLt;omega))).trans (h.conjugate.address j hj)
   · intro j hj
     exact (frame.natBefore _ (by have:=bounds.conjugateDir;have:=j.isLt;omega)
      (Or.inl (by have:=bounds.conjugateDirLow;have:=j.isLt;omega))
      (Or.inl (by have:=bounds.conjugateDir;have:=j.isLt;omega))).trans (h.conjugate.width j hj)
 · have keep(j:ℕ)(lt:j<6):u.scalarHeap j=s.scalarHeap j:=
    frame.scalarOutside j (Or.inl (by have:=l.constants;omega))
   rcases h.constants with ⟨a,b,c,d,e⟩
   exact ⟨(keep _ (by omega)).trans a,(keep _ (by omega)).trans b,(keep _ (by omega)).trans c,
    (keep _ (by omega)).trans d,(keep _ (by omega)).trans e⟩
 · intro j hj z
   have zl:=z.isLt
   change u.natHeap (p.nodes+7*j+z.val)=some (UniformLocalCacheTreeIteration.nodeWords visits[j].task visits[j].rectangleBase)[z] 
   rw[frame.natBefore _ (by have:=l.nodeEnd;omega) (Or.inr (by have:=l.rangesAbove;omega))
     (Or.inr (by omega))]
   exact h.nodes j hj z
 · intro j hj
   rw[frame.natHigh _ (by have:=l.startsHigh;omega)]
   exact h.starts j hj
end
end ExactFourierCircuits.UniformDirectLeafForestState
