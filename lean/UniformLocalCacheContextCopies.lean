import UniformLocalCacheSlotHeaderMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextCopies
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine

def Safe (ps:List (ℕ×ℕ)):Prop :=
 ∀p∈ps,p.1≠6190 ∧ ∀q∈ps,p.1≠q.2
def Sources (ps:List (ℕ×ℕ)) (values:ℕ→ℕ) (s:State):Prop :=
 ∀p∈ps,s.natReg p.2=values p.2

lemma copy_sources {ps:List (ℕ×ℕ)} {values:ℕ→ℕ} {s:State}
 (h:Sources ps values s) (d r:ℕ) (keep:∀p∈ps,d≠p.2):
 Sources ps values ((Op.add d r 6190).apply s):=by
 intro p hp
 simpa [Op.apply,writeNat,next,Function.update_apply,Ne.symm (keep p hp)] using h p hp

lemma copy_nat (ps:List (ℕ×ℕ)) (values:ℕ→ℕ) (s:State)
 (h:Sources ps values s) (zero:s.natReg 6190=0) (safe:Safe ps):
 (applyBlock (copyOps ps) s).natReg=copyEnv ps values s.natReg:=by
 induction ps generalizing s with
 | nil=>rfl
 | cons p ps ih=>
  have sp:=safe p (by simp)
  have tail:Safe ps:=by
   intro q hq
   exact ⟨(safe q (by simp[hq])).1,fun r hr=>(safe q (by simp[hq])).2 r (by simp[hr])⟩
  have inputs:Sources ps values s:=fun q hq=>h q (by simp[hq])
  have nextInputs:=copy_sources inputs p.1 p.2 (fun q hq=>sp.2 q (by simp[hq]))
  have nextZero:=copyOp_zero (r:=p.2) zero sp.1
  have eq:((Op.add p.1 p.2 6190).apply s).natReg=
   Function.update s.natReg p.1 (values p.2):=by
   simp only [Op.apply,writeNat,next]
   rw [h p (by simp),zero,Nat.add_zero]
  change (applyBlock (copyOps ps) ((Op.add p.1 p.2 6190).apply s)).natReg=_
  rw [ih _ nextInputs nextZero tail,eq];rfl

lemma copy_safe (ps:List (ℕ×ℕ)) (values:ℕ→ℕ) (s:State) (B:ℕ)
 (h:Sources ps values s) (zero:s.natReg 6190=0) (safe:Safe ps)
 (bound:∀p∈ps,values p.2≤B):readable (copyOps ps) s ∧ peak (copyOps ps) s≤B:=by
 induction ps generalizing s with
 | nil=>exact ⟨trivial,Nat.zero_le _⟩
 | cons p ps ih=>
  have sp:=safe p (by simp)
  have tail:Safe ps:=by
   intro q hq
   exact ⟨(safe q (by simp[hq])).1,fun r hr=>(safe q (by simp[hq])).2 r (by simp[hr])⟩
  have inputs:Sources ps values s:=fun q hq=>h q (by simp[hq])
  have nextInputs:=copy_sources inputs p.1 p.2 (fun q hq=>sp.2 q (by simp[hq]))
  have nextZero:=copyOp_zero (r:=p.2) zero sp.1
  have rest:=ih _ nextInputs nextZero tail (fun q hq=>bound q (by simp[hq]))
  refine ⟨⟨trivial,rest.1⟩,?_⟩
  change max (s.natReg p.2+s.natReg 6190) (peak (copyOps ps) ((Op.add p.1 p.2 6190).apply s))≤B
  rw [h p (by simp),zero,Nat.add_zero]
  exact max_le (bound p (by simp)) rest.2

lemma copy_keeps (ps:List (ℕ×ℕ)) (s:State) (q:ℕ)
 (keep:∀p∈ps,p.1≠q):(applyBlock (copyOps ps) s).natReg q=s.natReg q:=by
 apply block_keeps
 intro o ho
 obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ho
 simp only [Op.code,UniformNewtonTableMachine.KeepsNat]
 exact keep p hp

lemma copy_heaps (ps:List (ℕ×ℕ)) (s:State):
 (applyBlock (copyOps ps) s).natHeap=s.natHeap ∧
 (applyBlock (copyOps ps) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (copyOps ps) s).scalarReg=s.scalarReg ∧
 (applyBlock (copyOps ps) s).outputs=s.outputs ∧
 (applyBlock (copyOps ps) s).rootOrders=s.rootOrders:=by
 induction ps generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons p ps ih=>exact ih ((Op.add p.1 p.2 6190).apply s)

end ExactFourierCircuits.UniformLocalCacheContextCopies
