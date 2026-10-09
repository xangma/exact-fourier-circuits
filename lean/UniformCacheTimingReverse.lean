import UniformCacheTimingBankStep
import UniformCacheTimingReverseInitialization
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingReverse
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeIteration (AtNode)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformCacheTimingReverseData UniformCacheTimingReference UniformCacheTimingBankStep

noncomputable section
/-- All reverse iterations execute, maintaining the mixed accumulator/completed
bank represented by the exact suffix fold. No execution certificate is an input. -/
theorem loop (n D R U V T K B i:ℕ)(visits:List Visit)(x:Fin n→ℂ)(s:State)
 (layout:Layout D U V T visits.length K B)(metadata:Metadata R U K B visits)
 (h:Init D R U V T visits.length K i s)(bank:Bank D R U V T visits i s)
 (bound:i≤visits.length)(hp:s.pc=19)(hs:WordBound B s):∃t u,
 BoundedRuns program n x B s t u∧t≤ticks visits i∧u.pc=86∧
 Init D R U V T visits.length K 0 u∧Bank D R U V T visits 0 u∧
 (∀a,(a<U∨U+visits.length≤a)→(a<V∨V+visits.length≤a)→(a<T∨T+K≤a)→u.natHeap a=s.natHeap a):=by
 induction i generalizing s with
 | zero=>
  have step:UniformMachine.step program n x s=.running (setPC s 86):=by
   simp [UniformMachine.step,hp,code_19,h.zero,h.index,setPC]
  refine ⟨1,setPC s 86,control_run program n B 86 x s hs (by have:=layout.code;omega) step,?_,rfl,h.pc 86,UniformCacheTimingBankStep.Bank.pc bank 86,fun _ _ _ _=>rfl⟩
  simp [ticks]
 | succ k ih=>
  have hk:k<visits.length:=by omega
  let q:=visits[k]
  let d:=processedSuffix visits (k+1)
  have member:q∈visits:=List.getElem_mem hk
  have pi:q.task.parent≤k:=metadata.parentIndex k hk
  have pb:k=0∨q.task.parent<k:=by by_cases zero:k=0;exact Or.inl zero;exact Or.inr (metadata.parentBefore k hk (by omega))
  have uv:=layout.durations
  have vt:=layout.starts
  have tk:=layout.requests
  have du:=layout.directory
  have source:=metadata.source q member
  have destination:=metadata.requests q member
  have valueFit:UniformCacheTimingNodeBody.value q (d k)≤B:=by
   rw [UniformCacheTimingReverseData.value_eq visits k hk pb]
   exact metadata.durations k (by omega) k hk
  have correctionFit:UniformCacheTimingRows.amounts (currentRows q.task)≤B:=by
   rw [UniformCacheTimingPrefix.amounts_eq]
   exact metadata.corrections q member
  obtain ⟨nt,a,node,nodeBound,ap,ah,aheap⟩:=UniformCacheTimingNode.execution n D R U V T visits.length K k
   (d k) (d q.task.parent) B q x s h (bank.directory k hk) (bank.rows q member)
   (bank.durations k hk) (bank.durations q.task.parent (by omega)) hp hs layout.code
   (by omega) (by omega) (by omega) (by omega) (by omega) pb pi (by omega) (by omega)
   (by unfold ordinal at destination;omega) valueFit correctionFit (metadata.rowBudgets q member)
  have abank:=bank_step visits s a layout metadata bank hk aheap
  obtain ⟨tt,u,tail,tailBound,up,uh,ubank,frame⟩:=ih a ah abank (by omega) ap node.final_bound
  refine ⟨nt+tt,u,node.trans tail,?_,up,uh,ubank,?_⟩
  · rw [ticks_succ visits k hk]
    have nb:nt≤UniformCacheTimingNode.budget visits[k]:=nodeBound
    omega
  · intro z hzU hzV hzT
    rw [frame z hzU hzV hzT]
    exact outside visits s a metadata hk aheap z hzU hzV hzT

/-- The actual counters produced by173 feed charged initialization followed by
all reverse iterations. Durations/corrections/prefixes are outputs of this run. -/
theorem execution (n D R U V T K B:ℕ)(visits:List Visit)(x:Fin n→ℂ)(s:State)
 (header:UniformCacheTimingStartup.Input D R U V T visits.length K s)
 (directory:∀j,(hj:j<visits.length)→AtNode D j visits[j].task visits[j].rectangleBase s)
 (rows:∀q∈visits,UniformCacheTimingRows.TableAt q.rectangleBase 0 (currentRows q.task) s)
 (layout:Layout D U V T visits.length K B)(metadata:Metadata R U K B visits)
 (hp:s.pc=0)(hs:WordBound B s):∃t u,
 BoundedRuns program n x B s t u∧t≤5*visits.length+15+ticks visits visits.length∧u.pc=86∧
 Init D R U V T visits.length K 0 u∧Bank D R U V T visits 0 u∧
 (∀a,(a<U∨U+visits.length≤a)→(a<V∨V+visits.length≤a)→(a<T∨T+K≤a)→u.natHeap a=s.natHeap a):=by
 obtain ⟨a,start,ap,ah,abank,aframe⟩:=UniformCacheTimingReverseInitialization.execution n D R U V T K B visits x s
  header directory rows layout metadata hp hs
 obtain ⟨tt,u,tail,tailBound,up,uh,ubank,frame⟩:=loop n D R U V T K B visits.length visits x a
  layout metadata ah abank (by omega) ap start.final_bound
 refine ⟨5*visits.length+15+tt,u,start.trans tail,by omega,up,uh,ubank,?_⟩
 intro z hzU hzV hzT
 rw [frame z hzU hzV hzT,aframe z hzU]
end
end ExactFourierCircuits.UniformCacheTimingReverse
