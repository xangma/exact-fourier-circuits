import UniformLocalCacheContextExecution
import UniformLocalCacheSlotFrames

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextConductor
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace C
abbrev program:=UniformLocalCacheContextMachine.program
end C
namespace L
abbrev program:=UniformLocalCacheSlotConductorMachine.program
end L
def program:Program:=C.program.map (relocate 0 44)++L.program.map (relocate 44 1380)++[.halt]
lemma program_length:program.length=1381:=by
 simp only [program,List.length_append,List.length_map,
  UniformLocalCacheContextMachine.program_length,UniformLocalCacheSlotConductorMachine.program_length,
  List.length_singleton]
attribute [local irreducible] UniformLocalCacheContextMachine.program
 UniformLocalCacheSlotConductorMachine.program
lemma context_code:CodeAt C.program program 0 44:=by
 have eq:program=[]++C.program.map (relocate 0 44)++
  (L.program.map (relocate 44 1380)++[.halt]):=by simp only [program,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code [] _ _ 0 44 rfl
lemma loop_code:CodeAt L.program program 44 1380:=
 UniformChunkRowTableMachine.segment_code (C.program.map (relocate 0 44)) [.halt] _ 44 1380
  (by simp only [List.length_map,UniformLocalCacheContextMachine.program_length])
lemma halt_at:program[1380]?=some .halt:=by
 let before:=C.program.map (relocate 0 44)++L.program.map (relocate 44 1380)
 have len:before.length=1380:=by simp only [before,List.length_append,List.length_map,
  UniformLocalCacheContextMachine.program_length,UniformLocalCacheSlotConductorMachine.program_length]
 change (before++[.halt])[1380]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

open UniformLocalCacheSlotConductorMachine
noncomputable section
/-- Physical outputs of2308 before the charged6200 inverse-header write.
There is no ready controller/header/action or per-slot execution field. -/
structure Banks (c:Header.Parameters)(q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)(s:State):Prop where
 rectangle:UniformLocalRectangleBankMachine.RowSource c.rectangle q s
 generated:UniformLocalReplayAssembly.Generated c.height.K c.slot 6 s
 enabled:UniformCrossHeightPreparationMachine.Processed (enabledHeight c q true) c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s
 disabled:UniformCrossHeightPreparationMachine.Processed (enabledHeight c q false) c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) s
 sources:UniformMatchingConjugateLoadMachine.Sources c.height.K c.height.C c.negative c.height.P c.conjugates bank s
 constants:UniformHadamardPairMachine.Constants s

lemma Banks.inputs {c q ha he bank s u I}(h:Banks c q ha he bank s)
 (layout:InputLayout c q)(nat:u.natHeap=s.natHeap)(scalar:u.scalarHeap=s.scalarHeap)
 (inverse:u.natReg 6200=I):Inputs c q ha he I bank u:=by
 have size:(UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q true):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q true) ha he
 have sizeFalse:(UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=
  UniformCrossHeightPreparationMachine.gates (enabledHeight c q false):=
  UniformCrossHeightPreparationMachine.cross_size (enabledHeight c q false) ha he
 refine ⟨?_,h.generated.transport (fun i _=>congrFun nat i),?_,?_,?_,?_,inverse⟩
 · intro f;exact (congrFun nat _).trans (h.rectangle f)
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.enabled size layout.enabled
    (fun i _=>congrFun nat i)
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix _ _ _ h.disabled sizeFalse layout.disabled
    (fun i _=>congrFun nat i)
 · exact UniformConjugatePackedMatchingPreparation.sources_transport h.sources scalar
 · simpa only [UniformHadamardPairMachine.Constants,scalar] using h.constants

/-- Header44 and the complete physical rectangle cache loop are continuously
placed in one fixed1381-instruction program. The Banks input is supplied by
the actual2308 producer in the next assembly; no callback is used here. -/
theorem execution {B n:ℕ}(c:Header.Parameters)(q:UniformLocalRectangleDescriptors.Row)
 (ha:q.a  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)(I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.height.K) → ℂ)
 (geometry:Geometry B c q ha he I)(x:Fin n → ℂ)(s:State)
 (sources:UniformLocalCacheContextMachine.Sources c I s)(banks:Banks c q ha he bank s)
 (code:1381 ≤ B)(total:352*c.height.K+330 ≤ B)(scalar:9*c.ambient ≤ B)
 (natural:3*c.ambient+11 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u  ∧ 
 ticks ≤ (352*c.height.K+330)*(bodyBudget c q+11)+61  ∧ u.pc=1380  ∧ 
 (∀k,k < 352*c.height.K+330 → Cached (B:=B) c q ha he bank geometry.positive k u)  ∧ 
 u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧ 
 (∀i,i < c.borrowed → u.natHeap i=s.natHeap i)  ∧ 
 (∀i,(i < c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) → i ≠ c.mu → i ≠ c.conjugateMu → u.scalarHeap i=s.scalarHeap i):=by
 obtain ⟨a,first,ap,args,inverse,nh,sh,sr,out,roots,keep⟩:=
  UniformLocalCacheContextMachine.execution x s sources (by omega) pc wb
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed context_code
  (by rw [UniformLocalCacheContextMachine.program_length];omega) (by omega) first
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedFirst
 let start:=setPC a 0
 have bw:=changePC_bound B a 0 first.final_bound (by omega)
 have ready:Inputs c q ha he I bank start:=banks.inputs geometry.inputs nh sh inverse
 obtain ⟨last,t,second,cost,lp,control,inputs,cached,lout,lroots,low,ss⟩:=
  UniformLocalCacheSlotConductorMachine.execution c q ha he I bank geometry x start args ready
   (by omega) total scalar natural rfl bw
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed loop_code
  (by rw [UniformLocalCacheSlotConductorMachine.program_length];omega) (by omega) second
 have eq:placed 44 start=setPC a 44:=by cases a;rfl
 rw [eq] at placedSecond
 let u:=setPC last 1380
 have stop:BoundedExecution program n x B u 1 u:=.halt placedSecond.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,44+t+1,?_,by omega,rfl,?_,lout.trans out,lroots.trans roots,?_,?_⟩
 · simpa only [Nat.add_assoc] using placedFirst.executes (placedSecond.executes stop)
 · intro k hk
   exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 · intro i hi;exact (low i hi).trans (congrFun nh i)
 · intro i outside hm hb;exact (ss i outside hm hb).trans (congrFun sh i)

end
end ExactFourierCircuits.UniformLocalCacheContextConductor
