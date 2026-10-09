import UniformGlobalDiagonalRowsIteration
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section
lemma amount_cons (a:Entry) (as:List Entry):amount (a::as)=a.radix+amount as:=rfl
lemma Directory.transfer {L:Layout} (as:List Entry) (i:ℕ) {s u:State}
 (length:i+as.length ≤ L.ell) (h:Directory L.directory as i s)
 (nat:∀q,q < L.rows→u.natHeap q=s.natHeap q):Directory L.directory as i u:=by
 induction as generalizing i with
 | nil=>trivial
 | cons a as ih=>
   have hi:i < L.ell:=by simp only[List.length_cons] at length;omega
   have bound:=L.directoryBelow
   refine ⟨⟨?_,?_⟩,ih (i+1) (by simp only[List.length_cons] at length;omega) h.2⟩
   · exact (nat _ (by omega)).trans h.1.1
   · exact (nat _ (by omega)).trans h.1.2
lemma Pools.transfer {L:Layout} (as:List Entry) {s u:State} (h:Pools as s)
 (bound:∀a∈as,a.pool+9*a.radix ≤ L.coefficient)
 (scalar:∀q,q < L.coefficient→u.scalarHeap q=s.scalarHeap q):Pools as u:=by
 intro a ha lane j
 have lv:lane.val+1 ≤ 9:=by have:=lane.isLt;omega
 have mult:=Nat.mul_le_mul_right a.radix lv
 have aa:=bound a ha;have jj:=j.isLt
 exact (scalar _ (by nlinarith)).trans (h a ha lane j)
structure Outside (L:Layout) (as:List Entry) (i o:ℕ) (s u:State):Prop where
 nat:∀q,(q < L.rows+3*i ∨L.rows+3*(i+as.length) ≤ q)→
  (q < L.permutation+o ∨L.permutation+o+amount as ≤ q)→u.natHeap q=s.natHeap q
 scalar:∀q,q < L.coefficient+o ∨L.coefficient+o+amount as ≤ q→u.scalarHeap q=s.scalarHeap q
lemma row_low {L:Layout} {lane:Fin 9} {a:Entry} {i o:ℕ} {s u:State}
 (h:RowData L lane a i o s u):
 (∀q,q < L.rows→u.natHeap q=s.natHeap q) ∧
 (∀q,q < L.coefficient→u.scalarHeap q=s.scalarHeap q):=by
 refine ⟨?_,?_⟩
 · intro q hq
   exact h.2.2.2.2.2.1 q (Or.inl (by omega)) (Or.inl (by have:=L.rowsBelow;omega))
 · intro q hq
   exact h.2.2.2.2.2.2 q (Or.inl (by omega))
lemma Produced.cons {L:Layout} {lane:Fin 9} {a:Entry} {as:List Entry} {i o:ℕ} {s t u:State}
 (len:i+(a::as).length=L.ell) (fresh:RowData L lane a i o s t)
 (rest:Produced L lane as (i+1) (o+a.radix) u)
 (outside:Outside L as (i+1) (o+a.radix) t u):Produced L lane (a::as) i o u:=by
 have rowsBefore:=L.rowsBelow
 have currentRow:∀q,q < L.rows+3*(i+1)→u.natHeap q=t.natHeap q:=by
  intro q hq
  exact outside.nat q (Or.inl hq) (Or.inl (by simp only[List.length_cons] at len;omega))
 have currentPerm:∀j:Fin a.radix,u.natHeap (L.permutation+o+j.val)=t.natHeap (L.permutation+o+j.val):=by
  intro j
  exact outside.nat _ (Or.inr (by simp only[List.length_cons] at len;omega)) (Or.inl (by have:=j.isLt;omega))
 have currentCoef:∀j:Fin a.radix,u.scalarHeap (L.coefficient+o+j.val)=t.scalarHeap (L.coefficient+o+j.val):=by
  intro j
  exact outside.scalar _ (Or.inl (by have:=j.isLt;omega))
 refine ⟨⟨?_,?_,?_,rest.1⟩,?_,?_⟩
 · exact (currentRow _ (by omega)).trans fresh.2.2.1
 · exact (currentRow _ (by omega)).trans fresh.2.2.2.1
 · exact (currentRow _ (by omega)).trans fresh.2.2.2.2.1
 · intro b hb j
   simp only[axes,List.mem_cons] at hb
   rcases hb with equal|hb
   · subst b
     exact (currentPerm j).trans (fresh.1 j)
   · exact rest.2.1 b hb j
 · intro b hb j
   simp only[axes,List.mem_cons] at hb
   rcases hb with equal|hb
   · subst b
     exact (currentCoef j).trans (fresh.2.1 j)
   · exact rest.2.2 b hb j

/-- The same49 bytecode executes all actual axis records. Induction is over
remaining records, not over a host callback or preprinted output bank. -/
lemma loop (as:List Entry) (L:Layout) (lane:Fin 9) {n:ℕ} (x:Fin n→ℂ)
 (poolBound:∀a∈as,a.pool+9*a.radix ≤ L.coefficient):
 ∀(i o:ℕ) (s:State), i+as.length=L.ell → o+amount as=L.total → Cursor L lane i o s →
 Directory L.directory as i s → Pools as s → s.pc=5 → WordBound L.B s →
 ∃u,BoundedExecution program n x L.B s (9*amount as+35*as.length+2) u ∧u.pc=48 ∧
 Produced L lane as i o u ∧Frame s u ∧Outside L as i o s u:=by
 induction as with
 | nil=>
   intro i o s len off cursor dir pools pc wb
   have ii:i=L.ell:=by simpa using len
   let u:=setPC s 48
   have ub:=changePC_bound L.B s 48 wb (by have:=L.code;omega)
   have branch:BoundedRuns program n x L.B s 1 u:=.next wb
    (by simp[step,pc,branch_at,cursor.index,cursor.count,ii,u,setPC]) (.refl ub)
   have stop:BoundedExecution program n x L.B u 1 u:=.halt ub (by simp[step,u,setPC,halt_at])
   refine ⟨u,by simpa[amount] using branch.executes stop,rfl,?_,Frame.refl s,⟨fun _ _ _=>rfl,fun _ _=>rfl⟩⟩
   simp[Produced,axes,Rows]
 | cons a as ih=>
   intro i o s len off cursor dir pools pc wb
   have hi:i < L.ell:=by simp only[List.length_cons] at len;omega
   have bound:a.pool+9*a.radix ≤ L.coefficient:=poolBound a (by simp)
   have offset:o+a.radix ≤ L.total:=by rw[amount_cons] at off;omega
   have source:=pools a (by simp) lane
   obtain ⟨t,first,tp,next,frame,data⟩:=iteration L lane a x s hi offset bound cursor dir.1 source pc wb
   have low:=row_low data
   have tailDir:Directory L.directory as (i+1) t:=Directory.transfer as (i+1)
    (by simp only[List.length_cons] at len;omega) dir.2 low.1
   have tailPools:Pools as t:=Pools.transfer as (by intro b hb;exact pools b (by simp[hb]))
    (by intro b hb;exact poolBound b (by simp[hb])) low.2
   obtain ⟨u,rest,up,done,frame2,out⟩:=ih (by intro b hb;exact poolBound b (by simp[hb]))
    (i+1) (o+a.radix) t (by simp only[List.length_cons] at len;omega)
    (by rw[amount_cons] at off;omega) next tailDir tailPools tp first.final_bound
   refine ⟨u,?_,up,Produced.cons len data done out,frame.trans frame2,⟨?_,?_⟩⟩
   · convert first.executes rest using 1
     simp only[amount,List.map_cons,List.sum_cons,List.length_cons]
     ring
   · intro q hq hp
     have laterRows:q < L.rows+3*(i+1) ∨L.rows+3*(i+1+as.length) ≤ q:=by
      simp only[List.length_cons] at hq;omega
     have laterPerm:q < L.permutation+(o+a.radix) ∨L.permutation+(o+a.radix)+amount as ≤ q:=by
      rw[amount_cons] at hp;omega
     have nowRows:q < L.rows+i*3 ∨L.rows+i*3+3 ≤ q:=by
      simp only[List.length_cons] at hq;omega
     have nowPerm:q < L.permutation+o ∨L.permutation+o+a.radix ≤ q:=by
      rw[amount_cons] at hp;omega
     exact (out.nat q laterRows laterPerm).trans (data.2.2.2.2.2.1 q nowRows nowPerm)
   · intro q hq
     have later:q < L.coefficient+(o+a.radix) ∨L.coefficient+(o+a.radix)+amount as ≤ q:=by
      rw[amount_cons] at hq;omega
     have now:q < L.coefficient+o ∨L.coefficient+o+a.radix ≤ q:=by
      rw[amount_cons] at hq;omega
     exact (out.scalar q later).trans (data.2.2.2.2.2.2 q now)
end
end ExactFourierCircuits.UniformGlobalDiagonalRowsMachine
