import UniformCacheTimingReverseData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingReverseInitialization
open UniformMachine UniformCacheTimingProgram UniformCacheTimingControl
open UniformCacheTimingReverseData UniformCacheTimingReference
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeIteration (AtNode)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformCacheTimingRows (TableAt)

noncomputable section
/-- Physical producer directory/source tables survive the charged zeroing pass;
the suffix invariant starts at the actual all-zero duration bank. -/
theorem execution (n D R U V T K B:ℕ)(visits:List Visit)(x:Fin n→ℂ)(s:State)
 (header:UniformCacheTimingStartup.Input D R U V T visits.length K s)
 (directory:∀j,(hj:j<visits.length)→AtNode D j visits[j].task visits[j].rectangleBase s)
 (rows:∀q∈visits,TableAt q.rectangleBase 0 (currentRows q.task) s)
 (layout:Layout D U V T visits.length K B)(metadata:Metadata R U K B visits)
 (hp:s.pc=0)(hs:WordBound B s):∃u,
 BoundedRuns program n x B s (5*visits.length+15) u∧u.pc=19∧
 Init D R U V T visits.length K visits.length u∧Bank D R U V T visits visits.length u∧
 (∀a,a<U∨U+visits.length≤a→u.natHeap a=s.natHeap a):=by
 obtain ⟨u,run,up,out,zero,frame⟩:=UniformCacheTimingStartup.startup n D R U V T visits.length K B x s header hp hs
  layout.code (by have a:=layout.durations;have b:=layout.starts;have c:=layout.requests;omega)
 refine ⟨u,run,up,out,?_,frame⟩
 constructor
 · intro j hj f
   rw [frame (D+7*j+f.val) (Or.inl (by have a:=layout.directory;have b:=f.isLt;omega))]
   exact directory j hj f
 · intro q hq j hj
   have bounds:=metadata.source q hq
   have len:=UniformLocalCacheTreeCoverage.currentRows_length q.task
   have source:=rows q hq j hj
   constructor
   · rw [frame _ (Or.inl (by simp only [Nat.zero_add];omega))]
     exact source.1
   · rw [frame _ (Or.inl (by simp only [Nat.zero_add];omega))]
     exact source.2
 · intro j hj
   rw [processedSuffix_end]
   exact zero j hj
 · intro j hj lower
   omega
 · intro j hj lower
   omega
end
end ExactFourierCircuits.UniformCacheTimingReverseInitialization
