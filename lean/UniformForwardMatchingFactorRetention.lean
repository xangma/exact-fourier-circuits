import UniformForwardMatchingFactorHeaderCount
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
lemma translate_execution_high {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
 (s a:State) (args:Header c s) (ap:a.pc=238) (h:AfterChunk c l ha he s a) (wb:WordBound B a):∃u,
 BoundedRuns program n x B a (19*(rows c l ha he).length+9) u ∧u.pc=265 ∧
 AfterTranslation c l ha he s u ∧
 (∀q,c.translated+3*(rows c l ha he).length≤q→u.natHeap q=s.natHeap q):=by
 have safe:=translationSetup_safe h.zero wb
 have start:=block_runs translationSetup program 238 n B x a translationSetup_code ap wb
  (by rw[translationSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock translationSetup a
 have bp:b.pc=242:=by rw[applyBlock_pc,ap,translationSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have hh:∀q,4410≤q → q≤4429 → ready.natReg q=s.natReg q:=by
  intro q lo hi
  exact (translationSetup_nat a q (Or.inl (by omega))).trans (h.high q lo hi)
 have c0:ready.natReg 4990=(originalRows c l ha he).length:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.count,
   rows,originalRows,List.length_map]
 have ca:ready.natReg 4991=c.chunk.mapped:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.header.mapped]
 have cd:ready.natReg 4992=c.translated:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4422 (by omega) (by omega),args.translated]
 have co:ready.natReg 4993=c.offset:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4423 (by omega) (by omega),args.offset]
 have src:UniformCrossShearTableMachine.Table c.chunk.mapped (originalRows c l ha he) ready:=h.table
 have len:(originalRows c l ha he).length=(rows c l ha he).length:=by
  simp only[rows,originalRows,List.length_map]
 have mBound:=row_count_bound c l ha he
 have mappedBelow:c.chunk.mapped+3*(originalRows c l ha he).length≤c.translated:=by
  have l0:=l.chunk.mappedFresh;have l1:=l.chunk.permutationFresh;have l2:=l.chunk.widthsFresh
  have l3:=l.chunk.markersFresh;have l4:=l.translatedFresh
  rw[len];omega
 have db:c.translated+3*(originalRows c l ha he).length≤B:=by
  rw[len];have:=l.translatedBound;omega
 have extent:c.offset+c.ambient≤B:=by
  have:=l.poolBound;have:=l.extent;omega
 obtain ⟨z,run,table,_,frame,out,zp⟩:=UniformTranslatedMatchingRows.execution n B
  c.chunk.mapped c.translated c.offset c.ambient (originalRows c l ha he) x ready rfl c0 ca cd co
  src (original_range c l ha he) mappedBelow (by have:=l.code;omega)
  (by omega) db extent rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed translation_code
  (by rw[UniformTranslatedMatchingRows.program_length];have:=l.code;omega)
  (by have:=l.code;omega) run
 rw[show placed 242 ready=b by change {b with pc:=242}=b;rw[←bp]] at moved
 let u:=setPC z 265
 have high:∀q,4410≤q → q≤4429 → u.natReg q=s.natReg q:=by
  intro q lo hi;exact (frame.2.2.2.2 q (Or.inl (by omega))).trans (hh q lo hi)
 have zero:u.natReg 4430=0:=by
  exact (frame.2.2.2.2 4430 (Or.inl (by omega))).trans
   ((translationSetup_nat a 4430 (Or.inl (by omega))).trans h.zero)
 have count:u.natReg 894=(rows c l ha he).length:=by
  exact (frame.2.2.2.2 894 (Or.inl (by omega))).trans
   ((translationSetup_nat a 894 (Or.inl (by omega))).trans h.count)
 have pos:u.natReg 1060=c.chunk.height.C:=by
  exact (frame.2.2.2.2 1060 (Or.inl (by omega))).trans
   ((translationSetup_nat a 1060 (Or.inl (by omega))).trans h.header.height.coefficients)
 have constants:u.natReg 1062=c.chunk.height.P:=by
  exact (frame.2.2.2.2 1062 (Or.inl (by omega))).trans
   ((translationSetup_nat a 1062 (Or.inl (by omega))).trans h.header.height.constants)
 refine ⟨u,?_,rfl,⟨table,?_,?_,?_,high,zero,count,pos,constants,?_,?_⟩,?_⟩
 · convert start.trans moved using 1
   · simp only[translationSetup_length,len]
     omega
   · rfl
 · exact frame.1.trans ((translationSetup_heap a).2.1.trans h.scalar)
 · exact frame.2.2.1.trans ((translationSetup_heap a).2.2.1.trans h.outputs)
 · exact frame.2.2.2.1.trans ((translationSetup_heap a).2.2.2.trans h.roots)
 · intro q lo hi
   exact (frame.2.2.2.2 q (Or.inl (by omega))).trans
    ((translationSetup_nat a q (Or.inl (by omega))).trans (h.saved q lo hi))
 · intro q hq
   have below:c.chunk.borrowed≤c.translated:=by
    have l0:=l.chunk.borrowFresh;have l1:=l.chunk.selectedFresh;have l2:=l.chunk.ordinalFresh
    have l3:=l.chunk.mappedFresh;have l4:=l.chunk.permutationFresh;have l5:=l.chunk.widthsFresh
    have l6:=l.chunk.markersFresh;have l7:=l.translatedFresh;omega
   exact (out q (Or.inl (by omega))).trans (h.outside q (Or.inl hq))
 · intro q hq
   exact (out q (Or.inr (by omega))).trans (h.outside q (Or.inr (by have:=l.translatedFresh;omega)))
lemma factors_execution_allheap {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s a:State)
 (args:Header c s) (h:AfterTranslation c l ha he s a)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:a.pc=265) (wb:WordBound B a):∃u t,
 BoundedExecution program n x B a t u ∧t≤45*c.ambient+117*(rows c l ha he).length+24 ∧u.pc=414 ∧
 Result c l ha he bank s u ∧u.natReg 894=(rows c l ha he).length ∧u.natHeap=a.natHeap:=by
 have safe:=factorSetup_safe h.zero wb
 have start:=block_runs factorSetup program 265 n B x a factorSetup_code pc wb
  (by rw[factorSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock factorSetup a
 have bp:b.pc=275:=by rw[applyBlock_pc,pc,factorSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have sc:ready.scalarHeap=s.scalarHeap:=(factorSetup_heap a).2.1.trans h.scalar
 have src:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank ready:=by
  constructor
  · intro i;rw[sc];exact sources.positive i
  · intro i;rw[sc];exact sources.negative i
  · intro i;rw[sc];exact sources.conjugate i
  · intro i hi;rw[sc];exact sources.constants i hi
 have cons:UniformHadamardPairMachine.Constants ready:=by
  simpa only[UniformHadamardPairMachine.Constants,sc] using constants
 have hp:ready.natReg 4424=c.pool:=(factorSetup_nat a 4424 (Or.inr (by omega))
  (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))).trans ((h.high 4424 (by omega) (by omega)).trans args.pool)
 have before:UniformMatchingConjugateLoadMachine.RowArgs c.chunk.height.C c.negative c.chunk.height.P
  c.conjugates c.mu c.conjugate c.translated (b.natReg 2141) b:=
  factorSetup_args h.zero h.positive h.constants
   ((h.high 4429 (by omega) (by omega)).trans args.negative)
   ((h.high 4428 (by omega) (by omega)).trans args.conjugates)
   ((h.high 4426 (by omega) (by omega)).trans args.mu)
   ((h.high 4427 (by omega) (by omega)).trans args.conjugate)
   ((h.high 4422 (by omega) (by omega)).trans args.translated)
 have head:UniformMatchingConjugateLoadMachine.RowArgs c.chunk.height.C c.negative c.chunk.height.P
  c.conjugates c.mu c.conjugate c.translated (ready.natReg 2141) ready:=
  ⟨before.positive,before.negative,before.constants,before.conjugates,before.original,before.conjugate,before.rows,before.index⟩
 have pool:=factorSetup_pool (c:=c) h.zero
  ((h.high 4424 (by omega) (by omega)).trans args.pool)
  ((h.high 4425 (by omega) (by omega)).trans args.ambient)
 have count:ready.natReg 894=(rows c l ha he).length:=
  (factorSetup_nat a 894 (Or.inl (by omega)) (Or.inl (by omega))
   (Or.inl (by omega)) (Or.inl (by omega))).trans h.count
 have table:UniformCrossShearTableMachine.Table c.translated (rows c l ha he) ready:=h.table
 have geometry:=rows_geometry c l ha he
 have rowB:c.translated+3*(rows c l ha he).length≤B:=by
  have:=row_count_bound c l ha he;have:=l.translatedBound;omega
 obtain ⟨z,t,run,cost,zp,done,src',cons',table',nh,outs,roots,outside⟩:=
  UniformGlobalMatchingPoolPreparation.execution (rows c l ha he) (coefficient c l ha he)
   (coefficient_address c l ha he) head src cons table count pool.1 pool.2
   geometry.1 geometry.2.1 geometry.2.2 l.coefficient l.low l.poolFresh rowB l.poolBound
   (by have:=l.code;omega) x rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed factor_code
  (by rw[UniformGlobalMatchingPoolPreparation.program_length];have:=l.code;omega)
  (by have:=l.code;omega) run
 rw[show placed 275 ready=b by change {b with pc:=275}=b;rw[←bp]] at placedRun
 let u:=setPC z 414
 have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
  (by simp[step,u,setPC,halt_at])
 have countFinal:u.natReg 894=(rows c l ha he).length:=
  (UniformGlobalMatchingPoolPreparation.execution_nat run (q:=894) (by decide)).trans count
 refine ⟨u,10+t+1,?_,by omega,rfl,?_,countFinal,?_⟩
 · simpa only[factorSetup_length,u,setPC,Nat.add_assoc] using start.executes (placedRun.executes stop)
 · refine ⟨⟨done.done,done.remaining,done.untouched⟩,
   ⟨src'.positive,src'.negative,src'.conjugate,src'.constants⟩,cons',table',?_,?_,?_,?_,?_⟩
   · exact outs.trans ((factorSetup_heap a).2.2.1.trans h.outputs)
   · exact roots.trans ((factorSetup_heap a).2.2.2.trans h.roots)
   · intro q lo hi
     exact (UniformGlobalMatchingPoolPreparation.execution_saved run q lo hi).trans
      ((factorSetup_nat a q (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))).trans (h.saved q lo hi))
   · intro q hq;exact (congrArg (fun heap=>heap q) nh).trans (h.natPrefix q hq)
   · intro q hq qa qb;exact (outside q hq qa qb).trans (congrArg (fun heap=>heap q) sc)

 · exact nh.trans (factorSetup_heap a).1
theorem execution_high {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s:State)
 (args:Header c s) (slot:Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution program n x B s t u ∧
 t≤4*c.chunk.height.K+180*c.chunk.radix+45*c.ambient+136*(rows c l ha he).length+148 ∧
 u.pc=414 ∧Result c l ha he bank s u ∧u.natReg 894=(rows c l ha he).length ∧
 (∀q,c.translated+3*(rows c l ha he).length≤q→u.natHeap q=s.natHeap q):=by
 obtain ⟨a,t,first,cost,ap,ready⟩:=chunk_execution c l ha he x s args slot processed pc wb
 obtain ⟨b,second,bp,translated,high⟩:=translate_execution_high c l ha he x s a args ap ready first.final_bound
 obtain ⟨u,t',last,cost',up,result,count,heap⟩:=factors_execution_allheap c l ha he x bank s b args translated
  sources constants bp second.final_bound
 exact ⟨u,t+(19*(rows c l ha he).length+9)+t',first.trans second |>.executes last,by omega,up,result,count,fun q hq=>(congrFun heap q).trans (high q hq)⟩
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
