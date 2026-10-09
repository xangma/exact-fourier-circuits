import UniformLocalCacheContextConductor
import UniformLocalCacheSlotPriorRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextConductor.PriorRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotConductorMachine UniformLocalFactorDispatchMachine
noncomputable section
/-- Header44 and the complete physical rectangle cache loop are continuously
placed in one fixed1381-instruction program. The Banks input is supplied by
the actual2308 producer in the next assembly; no callback is used here. -/
theorem execution {B n:ℕ}(c:Header.Parameters)(q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)(I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I)(H:ℕ)
 (workspaces:∀j (hj:j<352*c.height.K+330) slot (witness:SlotWitness c.height.K j slot),
  natEnd (Cursor.shifted c j) q slot (geometry.layout j hj slot witness) (geometry.broadcast j hj) ha he I ≤ H)
 (x:Fin n → ℂ)(s:State)
 (sources:UniformLocalCacheContextMachine.Sources c I s)(banks:Banks c q ha he bank s)
 (code:1381 ≤ B)(total:352*c.height.K+330 ≤ B)(scalar:9*c.ambient ≤ B)
 (natural:3*c.ambient+11 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u  ∧ 
 ticks ≤ (352*c.height.K+330)*(bodyBudget c q+11)+61  ∧ u.pc=1380  ∧ 
 (∀k,k < 352*c.height.K+330 → Cached (B:=B) c q ha he bank geometry.positive k u)  ∧ 
 u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧ 
 (∀i,i < c.borrowed → u.natHeap i=s.natHeap i)  ∧ 
 (∀i,(i < c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) → i ≠ c.mu → i ≠ c.conjugateMu → u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,H ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 Cursor.Control c (352*c.height.K+330) u ∧
 (∀i,H ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i):=by
 obtain ⟨a,first,ap,args,inverse,nh,sh,sr,out,roots,keep⟩:=
  UniformLocalCacheContextMachine.execution x s sources (by omega) pc wb
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed context_code
  (by rw [UniformLocalCacheContextMachine.program_length];omega) (by omega) first
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedFirst
 let start:=setPC a 0
 have bw:=changePC_bound B a 0 first.final_bound (by omega)
 have ready:Inputs c q ha he I bank start:=banks.inputs geometry.inputs nh sh inverse
 obtain ⟨last,t,second,cost,lp,control,inputs,cached,lout,lroots,low,ss,prior,high⟩:=
  UniformLocalCacheSlotConductorMachine.PriorRetention.execution c q ha he I bank geometry H workspaces x start args ready
   (by omega) total scalar natural rfl bw
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed loop_code
  (by rw [UniformLocalCacheSlotConductorMachine.program_length];omega) (by omega) second
 have eq:placed 44 start=setPC a 44:=by cases a;rfl
 rw [eq] at placedSecond
 let u:=setPC last 1380
 have stop:BoundedExecution program n x B u 1 u:=.halt placedSecond.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,44+t+1,?_,by omega,rfl,?_,lout.trans out,lroots.trans roots,?_,?_,?_,control.withPC 1380,?_⟩
 · simpa only [Nat.add_assoc] using placedFirst.executes (placedSecond.executes stop)
 · intro k hk
   exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 · intro i hi;exact (low i hi).trans (congrFun nh i)
 · intro i outside hm hb;exact (ss i outside hm hb).trans (congrFun sh i)

 · intro i hi before;exact (prior i hi before).trans (congrFun nh i)
 · intro i hi afterCache;exact (high i hi afterCache).trans (congrFun nh i)

end
end ExactFourierCircuits.UniformLocalCacheContextConductor.PriorRetention
