import UniformDirectLeafForestExit
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestInitialization
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformDirectLeafForestIteration UniformDirectLeafForestBoot
open UniformLocalCacheTreeMachine
noncomputable section

lemma completed_outside {p:Parameters}{visits:List Visit}{s:State}
 (h:Header p visits s)(index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)
 (positive:0<p.radix)(a:ℕ)(outside:a<countHeader p∨countHeader p+2≤a):
 (completed s).natHeap a=s.natHeap a:=by
 rw[completed_heap h index positive]
 simp (disch:=omega)

lemma sources {p:Parameters}{visits:List Visit}{n A C B:ℕ}{s:State}
 (h:Header p visits s)(index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)
 (positive:0<p.radix)(src:Sources p visits n s)(l:Placement p A C B visits)
 (bounds:SeedBounds p n):Sources p visits n (completed s):=by
 have range:p.ranges≤countHeader p:=by unfold countHeader;omega
 have headerEnd:countHeader p+2≤p.nodes:=by unfold countHeader;exact l.headerEnd
 constructor
 · constructor
   · exact src.original.coefficients
   · intro j hj
     rw[completed_outside h index positive _ (Or.inl (by have:=bounds.originalDir;have:=j.isLt;omega))]
     exact src.original.address j hj
   · intro j hj
     rw[completed_outside h index positive _ (Or.inl (by have:=bounds.originalDir;have:=j.isLt;omega))]
     exact src.original.width j hj
 · constructor
   · exact src.conjugate.coefficients
   · intro j hj
     rw[completed_outside h index positive _ (Or.inl (by have:=bounds.conjugateDir;have:=j.isLt;omega))]
     exact src.conjugate.address j hj
   · intro j hj
     rw[completed_outside h index positive _ (Or.inl (by have:=bounds.conjugateDir;have:=j.isLt;omega))]
     exact src.conjugate.width j hj
 · exact src.constants
 · intro i hi z
   change (completed s).natHeap (p.nodes+7*i+z.val)=some
    (UniformLocalCacheTreeIteration.nodeWords visits[i].task visits[i].rectangleBase)[z]
   rw[completed_outside h index positive _ (Or.inr (by omega))]
   exact src.nodes i hi z
 · intro i hi
   rw[completed_outside h index positive _ (Or.inr (by
    have:=l.nodeEnd;have:=l.cacheEnd;have:=l.descriptors;have:=l.startsHigh;omega))]
   exact src.starts i hi

lemma invariant {p:Parameters}{visits:List Visit}{n A C B:ℕ}{s:State}
 (h:Header p visits s)(index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)
 (positive:2≤p.radix)(src:Sources p visits n s)(l:Placement p A C B visits)
 (bounds:SeedBounds p n)(hp:s.pc=0):
 Invariant p visits n A 0 positive (completed s):=by
 refine ⟨?_,completed_cursor h index (by omega),sources h index (by omega) src l bounds,
  completed_counts h index (by omega),?_,?_⟩
 · simp only[completed,applyBlock_pc,UniformDirectLeafForestProgram.durable_length,
    UniformDirectLeafForestBoot.initialized,writeNat,next,(left_values h).2.2,hp]
 · intro i hi lower
   omega
 · intro i hi lower
   omega
end
end ExactFourierCircuits.UniformDirectLeafForestInitialization
