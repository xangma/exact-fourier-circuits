import UniformCacheTimingReverseData
import UniformCacheTimingHeap
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingBankStep
open UniformMachine UniformCacheTimingRows
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformCacheTimingReverseData UniformCacheTimingReference UniformCacheTimingHeap

noncomputable section
lemma Bank.pc {D R U V T i:ℕ}{visits:List Visit}{s:State}
 (h:Bank D R U V T visits i s)(p:ℕ):Bank D R U V T visits i (UniformTensorMonomialMachine.setPC s p):=
 ⟨h.directory,h.rows,h.durations,h.corrections,h.prefixes⟩

lemma bank_step {D R U V T K B k:ℕ}(visits:List Visit)(s u:State)
 (layout:Layout D U V T visits.length K B)(metadata:Metadata R U K B visits)
 (h:Bank D R U V T visits (k+1) s)(hk:k<visits.length)
 (heap:u.natHeap=UniformCacheTimingNode.outputHeap U V T R k
  (processedSuffix visits (k+1) k) (processedSuffix visits (k+1) visits[k].task.parent) visits[k] s.natHeap):
 Bank D R U V T visits k u:=by
 let q:=visits[k]
 let d:=processedSuffix visits (k+1)
 have pi:q.task.parent≤k:=metadata.parentIndex k hk
 have pb:k=0∨q.task.parent<k:=by by_cases zero:k=0;exact Or.inl zero;exact Or.inr (metadata.parentBefore k hk (by omega))
 have uv:=layout.durations
 have vt:=layout.starts
 have below:∀a,a<U→u.natHeap a=s.natHeap a:=by
  intro a ha
  rw [heap]
  exact output_belowU U V T R k visits.length (d k) (d q.task.parent) q s.natHeap hk pi uv vt a ha
 constructor
 · intro j hj f
   rw [below _ (by have a:=layout.directory;have b:=f.isLt;omega)]
   exact h.directory j hj f
 · intro a ha j hj
   have source:=metadata.source a ha
   have len:=UniformLocalCacheTreeCoverage.currentRows_length a.task
   have old:=h.rows a ha j hj
   constructor
   · rw [below _ (by simp only [Nat.zero_add];omega)]
     exact old.1
   · rw [below _ (by simp only [Nat.zero_add];omega)]
     exact old.2
 · intro j hj
   rw [heap,output_duration U V T R k visits.length q s.natHeap d h.durations hk pb uv vt j hj]
   rw [processedSuffix_step visits k hk]
 · intro j hj lower
   rw [heap]
   by_cases same:j=k
   · subst j
     exact output_correction U V T R k visits.length (d k) (d q.task.parent) q s.natHeap hk pi uv vt
   · rw [output_correction_other U V T R k visits.length (d k) (d q.task.parent) q s.natHeap hk pi uv vt j hj same]
     exact h.corrections j hj (by omega)
 · intro j hj lower z hz
   rw [heap]
   by_cases same:j=k
   · subst j
     exact output_prefix U V T R k visits.length (d k) (d q.task.parent) q s.natHeap hk pi uv vt z hz
   · have after:k<j:=by omega
     have ord:ordinal R q+(currentRows q.task).length≤ordinal R visits[j]:=metadata.ordered k j hk hj after
     have keep:=output_prefix_other U V T R k visits.length (d k) (d q.task.parent) q s.natHeap hk pi uv vt
      (ordinal R visits[j]+z) (Or.inr (by change ordinal R q+(currentRows q.task).length≤_;omega))
     rw [Nat.add_assoc,keep]
     simpa only [Nat.add_assoc] using h.prefixes j hj (by omega) z hz

lemma outside {R U V T K B k:ℕ}(visits:List Visit)(s u:State)
 (metadata:Metadata R U K B visits)(hk:k<visits.length)
 (heap:u.natHeap=UniformCacheTimingNode.outputHeap U V T R k
  (processedSuffix visits (k+1) k) (processedSuffix visits (k+1) visits[k].task.parent) visits[k] s.natHeap)
 (a:ℕ)(hu:a<U∨U+visits.length≤a)(hv:a<V∨V+visits.length≤a)(ht:a<T∨T+K≤a):u.natHeap a=s.natHeap a:=by
 rw [heap]
 apply output_outside U V T R k visits.length _ _ visits[k] s.natHeap hk (metadata.parentIndex k hk) a hu hv
 have req:=metadata.requests visits[k] (List.getElem_mem hk)
 unfold ordinal at req
 rcases ht with low|high
 · left;omega
 · right;omega
end
end ExactFourierCircuits.UniformCacheTimingBankStep
