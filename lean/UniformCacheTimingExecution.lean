import UniformCacheTimingReverse
import UniformCacheTimingForwardCanonical
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingExecution
open UniformMachine UniformCacheTimingProgram UniformCacheTimingControl
open UniformLocalCacheTreeMachine (Visit walk)
open UniformLocalCacheTreeExecution (Directory visitSum)
open UniformLocalCacheTreeIteration (AtNode)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformCacheTimingReference UniformCacheTimingReverseData

abbrev visits (v o R:ℕ):List Visit:=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1

lemma directory_of_at (D start:ℕ)(L:List Visit)(s:State)
 (cells:∀j,(hj:j<L.length)→AtNode D (start+j) L[j].task L[j].rectangleBase s):Directory D start L s:=by
 induction L generalizing start with
 | nil=>trivial
 | cons q qs ih=>
  constructor
  · have head:=cells 0 (by simp)
    change AtNode D (start+0) q.task q.rectangleBase s at head
    simpa only [Nat.add_zero] using head
  · apply ih (start+1)
    intro j hj
    have tail:=cells (j+1) (by simp;omega)
    change AtNode D (start+(j+1)) qs[j].task qs[j].rectangleBase s at tail
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

noncomputable section
/-- The whole literal122 printer starts from actual173 directory/request words.
It initializes duration cells, computes subtree maxima and relative prefixes,
then writes physical node/request starts and genuinely halts. -/
theorem execution (n v o D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (header:UniformCacheTimingStartup.Input D R U V T (visits v o R).length (visitSum (visits v o R)) s)
 (directory:Directory D 0 (visits v o R) s)
 (rows:∀q∈visits v o R,UniformCacheTimingRows.TableAt q.rectangleBase 0 (currentRows q.task) s)
 (layout:Layout D U V T (visits v o R).length (visitSum (visits v o R)) B)
 (metadata:Metadata R U (visitSum (visits v o R)) B (visits v o R))
 (word:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (hp:s.pc=0)(hs:WordBound B s):∃t u,
 BoundedExecution program n x B s t u∧
 t≤5*(visits v o R).length+15+ticks (visits v o R) (visits v o R).length+
  UniformCacheTimingForwardLoop.ticks (UniformCacheTimingForwardCanonical.data (visits v o R)) 0 (visits v o R).length+2∧
 (∀k,k<(visits v o R).length→u.natHeap (U+k)=some (bottomUp (visits v o R) k))∧
 (∀k,k<(visits v o R).length→u.natHeap (V+k)=some 0)∧
 (∀k,(hk:k<(visits v o R).length)→∀j,j<UniformLocalRectangleDescriptors.emittedCount (visits v o R)[k].task.width→
  u.natHeap (T+visitSum ((visits v o R).take k)+j)=some (requestStart (visits v o R)[k] j))∧
 (∀a,(a<U∨U+(visits v o R).length≤a)→(a<V∨V+(visits v o R).length≤a)→
  (a<T∨T+visitSum (visits v o R)≤a)→u.natHeap a=s.natHeap a)∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀r,r<6500∨6600≤r→u.natReg r=s.natReg r):=by
 have cells:∀k,(hk:k<(visits v o R).length)→AtNode D k (visits v o R)[k].task (visits v o R)[k].rectangleBase s:=by
  intro k hk
  simpa only [Nat.zero_add] using UniformCacheTimingForwardCanonical.directory_at directory k hk
 obtain ⟨rt,a,reverse,reverseBound,ap,ah,bank,rf⟩:=UniformCacheTimingReverse.execution n D R U V T _ B (visits v o R) x s
  header cells rows layout metadata hp hs
 have stored:UniformCacheTimingForwardCanonical.Stored U V T (visits v o R) a:=by
  constructor
  · intro k hk
    simpa only [processedSuffix_zero] using bank.durations k hk
  · intro k hk
    exact bank.corrections k hk (by omega)
  · intro k hk j hj
    have out:=bank.prefixes k hk (by omega) j (by simpa only [UniformLocalCacheTreeCoverage.currentRows_length] using hj)
    have ord:=UniformCacheTimingMetadata.root_request_ordinal v o R k hk
    simpa only [ordinal,ord] using out
 have dir:Directory D 0 (visits v o R) a:=directory_of_at D 0 (visits v o R) a
  (fun k hk=>by simpa only [Nat.zero_add] using bank.directory k hk)
 have g:UniformCacheTimingForwardLoop.Layout D U V T (visits v o R).length (visitSum (visits v o R)) B:=
  ⟨layout.directory,layout.durations,layout.starts,layout.requests,layout.code⟩
 obtain ⟨u,forward,starts,requests,ff⟩:=UniformCacheTimingForwardCanonical.execution n v o D R U V T B x a g word ah.toHeader dir stored ap reverse.final_bound
 have whole:=reverse.executes forward
 refine ⟨rt+(UniformCacheTimingForwardLoop.ticks (UniformCacheTimingForwardCanonical.data (visits v o R)) 0 (visits v o R).length+2),
  u,whole,by omega,?_,starts,requests,?_,execution_scalarFrame whole,fun r hr=>execution_natFrame whole r hr⟩
 · intro k hk
   rw [ff _ (Or.inl (by have:=layout.durations;omega)) (Or.inl (by have:=layout.durations;have:=layout.starts;omega))]
   exact stored.durations k hk
 · intro z hzU hzV hzT
   rw [ff z hzV hzT,rf z hzU hzV hzT]
end
end ExactFourierCircuits.UniformCacheTimingExecution
