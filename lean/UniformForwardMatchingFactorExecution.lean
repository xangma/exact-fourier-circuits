import UniformForwardMatchingFactorTranslation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
structure Result (c:Config) (l:Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s u:State):Prop where
 factors:UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=c.chunk.height.K)
  c.pool c.ambient (rows c l ha he) bank (coefficient c l ha he) (rows c l ha he).length u
 sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank u
 constants:UniformHadamardPairMachine.Constants u
 table:UniformCrossShearTableMachine.Table c.translated (rows c l ha he) u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 saved:∀q,100≤q → q≤106 → u.natReg q=s.natReg q
 natPrefix:∀q,q<c.chunk.borrowed → u.natHeap q=s.natHeap q
 scalarOutside:∀q,(q<c.pool ∨c.pool+9*c.ambient≤q) → q≠c.mu → q≠c.conjugate → u.scalarHeap q=s.scalarHeap q
lemma factors_execution {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s a:State)
 (args:Header c s) (h:AfterTranslation c l ha he s a)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:a.pc=265) (wb:WordBound B a):∃u t,
 BoundedExecution program n x B a t u ∧t≤45*c.ambient+117*(rows c l ha he).length+24 ∧u.pc=414 ∧
 Result c l ha he bank s u:=by
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
 refine ⟨u,10+t+1,?_,by omega,rfl,⟨⟨done.done,done.remaining,done.untouched⟩,
  ⟨src'.positive,src'.negative,src'.conjugate,src'.constants⟩,cons',table',?_,?_,?_,?_,?_⟩⟩
 · simpa only[factorSetup_length,u,setPC,Nat.add_assoc] using start.executes (placedRun.executes stop)
 · exact outs.trans ((factorSetup_heap a).2.2.1.trans h.outputs)
 · exact roots.trans ((factorSetup_heap a).2.2.2.trans h.roots)
 · intro q lo hi
   exact (UniformGlobalMatchingPoolPreparation.execution_saved run q lo hi).trans
    ((factorSetup_nat a q (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (h.saved q lo hi))
 · intro q hq;exact (congrArg (fun heap=>heap q) nh).trans (h.natPrefix q hq)
 · intro q hq qa qb;exact (outside q hq qa qb).trans (congrArg (fun heap=>heap q) sc)

/-- Actual stored forward slot→local-v matching→translated rows→nine prepared
factor lanes. All setup and helper transitions are executed by the same415. -/
theorem execution {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
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
 u.pc=414 ∧Result c l ha he bank s u:=by
 obtain ⟨a,t,first,cost,ap,ready⟩:=chunk_execution c l ha he x s args slot processed pc wb
 obtain ⟨b,second,bp,translated⟩:=translate_execution c l ha he x s a args ap ready first.final_bound
 obtain ⟨u,t',last,cost',up,result⟩:=factors_execution c l ha he x bank s b args translated
  sources constants bp second.final_bound
 exact ⟨u,t+(19*(rows c l ha he).length+9)+t',first.trans second |>.executes last,by omega,up,result⟩
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
