import UniformChunkPortMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBorrowedCoordinateBridge
namespace B
export UniformBorrowedCoordinateMachine (Eligible available borrowed embedding)
end B
namespace P
export UniformWorkspacePlanner (available availableList borrowed borrowedEmbedding)
end P
open UniformChunkPortMachine UniformToeplitzChunkWord

lemma positions_interval {v start length:ℕ}(bound:start+length ≤ v)(i:Fin v):
 i ∈ positions (intervalEmbedding v start length bound)  ↔  start ≤ i.val  ∧ i.val<start+length:=by
 simp only[positions,Finset.mem_map,Finset.mem_univ,true_and]
 constructor
 · rintro ⟨j,hj⟩
   have eqn:=congrArg Fin.val hj
   change start+j.val=i.val at eqn
   have:=j.isLt
   omega
 · intro h
   refine ⟨⟨i.val-start,by omega⟩,?_⟩
   apply Fin.ext
   change start+(i.val-start)=i.val
   omega

lemma eligible_iff {v s e t a:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)(i:Fin v):
 B.Eligible s e t a i.val  ↔ 
 i ∉ positions (intervalEmbedding v s e he) ∪positions (intervalEmbedding v t a ha):=by
 simp only[Finset.mem_union,positions_interval]
 unfold B.Eligible
 omega

lemma finRange_values (v:ℕ):(List.finRange v).map Fin.val=List.range v:=by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

/-- The machine's Nat scan and the circuit planner's Fin scan enumerate the
same complement in the same increasing order, including overlapping intervals. -/
lemma available_values {v s e t a:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v):
 (P.availableList (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha))).map Fin.val=B.available v s e t a:=by
 have pred:(fun i:Fin v=>decide (i ∉ positions (intervalEmbedding v s e he) ∪
  positions (intervalEmbedding v t a ha)))=(fun i:Fin v=>decide (B.Eligible s e t a i.val)):=by
  funext i
  simp only[eligible_iff he ha i]
 unfold P.availableList B.available
 rw[pred]
 have h:=(List.filter_map (f:=Fin.val) (p:=fun z:ℕ=>decide (B.Eligible s e t a z)) (l:=List.finRange v)).symm
 simpa only[Function.comp_def,finRange_values] using h

lemma borrowed_values {v s e t a g:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v):
 (P.borrowed (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha)) g).map Fin.val=B.borrowed v s e t a g:=by
 unfold P.borrowed B.borrowed
 rw[List.map_take,available_values he ha]

lemma available_capacity {v s e t a g:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)(fit:g+e+a ≤ v):
 g ≤ (P.available (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha))).card:=by
 rw[←UniformWorkspacePlanner.availableList_length]
 have h:=congrArg List.length (available_values he ha)
 simp only[List.length_map] at h
 rw[h]
 exact UniformBorrowedCoordinateMachine.available_capacity v s e t a g fit

/-- Exact coordinate equality, rather than a chosen or merely disjoint labeling. -/
theorem embedding_eq {v s e t a g:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)(fit:g+e+a ≤ v)
 (hg:g ≤ (P.available (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha))).card):
 B.embedding v s e t a g fit=
 P.borrowedEmbedding (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha)) g hg:=by
 apply Function.Embedding.ext
 intro i
 apply Fin.ext
 have hi:i.val<(B.borrowed v s e t a g).length:=by
  rw[UniformBorrowedCoordinateMachine.borrowed_length v s e t a g fit]
  exact i.isLt
 have hp:i.val<(P.borrowed (positions (intervalEmbedding v s e he))
  (positions (intervalEmbedding v t a ha)) g).length:=by
  rw[UniformWorkspacePlanner.borrowed_length _ _ g hg]
  exact i.isLt
 change (B.borrowed v s e t a g)[i.val]'hi=
  ((P.borrowed (positions (intervalEmbedding v s e he))
   (positions (intervalEmbedding v t a ha)) g)[i.val]'hp).val
 have eqn:=borrowed_values (g:=g) he ha
 have h:=congrArg (fun z:List ℕ=>z[i.val]?) eqn
 simpa only[List.getElem?_map,List.getElem?_eq_getElem hp,Option.map_some,
  List.getElem?_eq_getElem hi,Option.some.injEq] using h.symm

lemma interval_separated {v s e t a:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)
 (separated:s+e ≤ t  ∨ t+a ≤ s):∀i j,intervalEmbedding v s e he i ≠ intervalEmbedding v t a ha j:=by
 intro i j eqn
 have h:=congrArg Fin.val eqn
 change s+i.val=t+j.val at h
 have:=i.isLt
 have:=j.isLt
 omega

lemma placement_ext {e g a v:ℕ}(p q:Placement e g a v)
 (source:p.source=q.source)(gates:p.gates=q.gates)(target:p.target=q.target):p=q:=by
 cases p
 cases q
 simp_all

/-- The real Borrowed17/ChunkPort14 labeling is the exact placement used by the
abstract six-C chunk word. There is no arbitrary permutation or action premise. -/
theorem placement_eq {v s e t a g:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)
 (separated:s+e ≤ t  ∨ t+a ≤ s)(fit:g+e+a ≤ v):
 UniformChunkPortMachine.placement v s e t a g he ha separated fit=
 placementOfFit (g:=g) (intervalEmbedding v s e he) (intervalEmbedding v t a ha)
  (interval_separated he ha separated) (by omega):=by
 apply placement_ext
 · rfl
 · exact embedding_eq he ha fit (available_capacity he ha fit)
 · rfl

theorem mapped_natPorts_eq {v s e t a g:ℕ}(he:s+e ≤ v)(ha:t+a ≤ v)
 (separated:s+e ≤ t  ∨ t+a ≤ s)(fit:g+e+a ≤ v)(i:Fin (e+g+a)):
 mapped e g s t (borrowedCoordinate v s e t a g fit) (natPorts e g a i)=
  ((placementOfFit (g:=g) (intervalEmbedding v s e he) (intervalEmbedding v t a ha)
   (interval_separated he ha separated) (by omega)).embedding i).val:=by
 rw[←placement_eq he ha separated fit]
 exact mapped_natPorts v s e t a g he ha separated fit i

end ExactFourierCircuits.UniformBorrowedCoordinateBridge
