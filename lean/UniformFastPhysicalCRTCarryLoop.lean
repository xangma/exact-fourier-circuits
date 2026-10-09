import UniformFastPhysicalCRTInitialization
import UniformFastPhysicalCRTCarry
import UniformFastPhysicalCRTVisits
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTCarryLoop
open UniformMachine UniformFastPhysicalCRTMachine UniformCRTTraversalCycle
open UniformFastPhysicalCRTInitialization UniformFastPhysicalCRTArithmetic
open scoped BigOperators
noncomputable section

lemma work_update{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(ds:Fin a→ℕ)(i:Fin a)(d:ℕ)(s u:State)
 (work:Work r L ds s)(heap:u.natHeap=Function.update s.natHeap (L.work+2*i.val) (some d)):
 Work r L (Function.update ds i d) u:=by
 intro j
 rw[heap]
 constructor
 · by_cases eq:j=i
   · subst j;simp
   · rw[Function.update_of_ne (by have ne:j.val≠i.val:=fun e=>eq (Fin.ext e);omega),Function.update_of_ne eq]
     exact (work j).1
 · rw[Function.update_of_ne (by omega)]
   exact (work j).2
lemma update_outside{a:ℕ}(L:Addresses)(i:Fin a)(d:ℕ)(s u:State)
 (heap:u.natHeap=Function.update s.natHeap (L.work+2*i.val) (some d)):
 Outside a L s.natHeap u:=by
 intro q hq
 rw[heap,Function.update_of_ne (by omega)]

/-- The real carry loop stops at the first non-wrapping digit. Its charged
work is bounded by the actual mixed-radix visit count. -/
theorem execution{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)(x:Fin n→ℂ)
 (t j fuel:ℕ)(ht:0<t)(tv:t<∏i,r i)(length:j+fuel=a)
 (divides:place (reverse r) j∣t)(s:State)(pc:s.pc=31)
 (idx:s.natReg 7804=a-j)(normalized:s.natReg 7806=value r (front r t j))
 (args:Args a (∏i,r i) L s)(c:Constants s)(work:Work r L (front r t j) s)
 (reads:∀i:Fin a,s.natHeap (L.directory+2*i.val+1)=some (r i))
 (before:L.directory+2*a≤L.work)(fit:L.work+2*a≤B)(volume:(∏i,r i)≤B)
 (code:53≤B)(wb:WordBound B s):∃ticks u,
 BoundedRuns program n x B s ticks u∧ticks≤18*visitsFrom (reverse r) t j∧
 u.pc=19∧u.natReg 7806=normal r t∧Args a (∏i,r i) L u∧Constants u∧Frame s u∧
 Work r L (digits r t) u∧Outside a L s.natHeap u∧u.natReg 7803=s.natReg 7803:=by
 induction fuel generalizing j s with
 | zero=>
   have ja:j=a:=by omega
   have vd:(∏i,r i)∣t:=by simpa only[ja,place_all,reverse_product] using divides
   have le:=Nat.le_of_dvd ht vd
   omega
 | succ fuel ih=>
   have ja:j<a:=by omega
   let q:Fin a:=⟨j,ja⟩
   let i:=q.rev
   let d:=digits r (t-1) i
   let N:=value r (front r t j)
   let nextD:=((d+1)%r i)
   have current:front r t j i=d:=front_current r t q
   have dd:s.natHeap (L.work+2*i.val)=some d:=by rw[←current];exact (work i).1
   have wd:= (work i).2
   have digit:d<r i:=digits_bound r hr (t-1) i
   have ix:s.natReg 7804=i.val+1:=by rw[idx];simp only[i,q,Fin.val_rev];omega
   have updated:Function.update (front r t j) i nextD=front r t (j+1):=
    front_update_mod r hr t ht q divides
   have modEq:(if d+1<r i then d+1 else 0)=nextD:=increment_mod d (r i) digit
   have valueEq:value r (front r t (j+1))=N-d*place r i.val+nextD*place r i.val:=
    carry_value r hr t ht q divides
   have newBound:d+1<r i→N-d*place r i.val+(d+1)*place r i.val≤B:=by
    intro hs
    have e:nextD=d+1:=by dsimp[nextD];exact Nat.mod_eq_of_lt hs
    rw[←e,←valueEq]
    exact le_trans (Nat.le_of_lt (front_value_bound r hr t (j+1))) volume
   obtain ⟨u,run,up,ui,un,uh,ua,uc,uf,uph⟩:=UniformFastPhysicalCRTCarry.execution L i x s
    args c pc ix N d (place r i.val) (r i) normalized (reads i) dd wd digit
    (carry_remove_le r t q) newBound (by omega) fit code wb
   have uw:Work r L (front r t (j+1)) u:=by
    rw[←updated,←modEq]
    exact work_update r L _ i _ s u work uh
   have uv:u.natReg 7806=value r (front r t (j+1)):=by
    have e:(if d+1<r i then (d+1)*place r i.val else 0)=nextD*place r i.val:=by
     rw[←modEq];split_ifs <;>simp
    rw[un,e,←valueEq]
   have outside:=update_outside L i _ s u uh
   have visit:=visits_step (reverse r) t q divides
   have iffSuccess:d+1<r i↔¬place (reverse r) (j+1)∣t:=by
    simpa only[d,i,digits,reverse,Fin.rev_rev] using
     success_iff (reverse r) (reverse_positive r hr) t ht q divides
   by_cases hs:d+1<r i
   · have finished:=front_success r hr t ht q (iffSuccess.mp hs)
     change front r t (j+1)=digits r t at finished
     refine ⟨18,u,?_,?_,?_,?_,ua,uc,uf,?_,outside,uph⟩
     · simpa only[hs,ite_true] using run
     · dsimp only[q] at visit;omega
     · simpa only[hs,ite_true] using up
     · rw[finished] at uv;exact uv
     · rw[finished] at uw;exact uw
   · have nextDiv:place (reverse r) (j+1)∣t:=by
      by_contra h;exact hs (iffSuccess.mpr h)
     have readsU:∀k:Fin a,u.natHeap (L.directory+2*k.val+1)=some (r k):=by
      intro k;rw[outside _ (Or.inl (by omega))];exact reads k
     obtain ⟨ticks,v,tail,bound,vp,vn,va,vc,vf,vw,vh,vph⟩:=ih (j+1) (by omega) nextDiv u
      (by simpa only[hs,ite_false] using up) (by rw[ui];simp only[i,q,Fin.val_rev])
      uv ua uc uw readsU run.final_bound
     refine ⟨17+ticks,v,?_,?_,vp,vn,va,vc,uf.trans vf,vw,?_,vph.trans uph⟩
     · have first:BoundedRuns program n x B s 17 u:=by simpa only[hs,ite_false] using run
       exact first.trans tail
     · dsimp only[q] at visit;omega
     · intro k hk;rw[vh k hk];exact outside k hk
end
end ExactFourierCircuits.UniformFastPhysicalCRTCarryLoop
