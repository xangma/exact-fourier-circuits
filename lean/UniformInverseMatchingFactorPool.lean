import UniformInverseMatchingFactorExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
lemma factorSetup_args {c:F.Config} {I:ℕ} {s:State}
 (z:s.natReg 4461=0)
 (hc:s.natReg 1060=c.chunk.height.C) (hp:s.natReg 1062=c.chunk.height.P)
 (hn:s.natReg 4429=c.negative) (hv:s.natReg 4428=c.conjugates)
 (ha:s.natReg 4426=c.mu) (hb:s.natReg 4427=c.conjugate)
 (hd:s.natReg 4460=I):
 UniformMatchingConjugateLoadMachine.RowArgs c.chunk.height.C c.negative c.chunk.height.P
  c.conjugates c.mu c.conjugate I ((applyBlock factorSetup s).natReg 2141)
  (applyBlock factorSetup s):=by
 constructor <;>simp[factorSetup,applyBlock,Op.apply,writeNat,next,z,hc,hp,hn,hv,ha,hb,hd]
lemma factorSetup_pool {c:F.Config} {s:State} (z:s.natReg 4461=0)
 (hp:s.natReg 4424=c.pool) (hr:s.natReg 4425=c.ambient):
 (applyBlock factorSetup s).natReg 4330=c.pool ∧(applyBlock factorSetup s).natReg 4331=c.ambient:=by
 simp[factorSetup,applyBlock,Op.apply,writeNat,next,z,hp,hr]
structure Result (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s u:State):Prop where
 factors:UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=c.chunk.height.K)
  c.pool c.ambient (rows c l ha he) bank (coefficient c l ha he) (rows c l ha he).length u
 sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank u
 constants:UniformHadamardPairMachine.Constants u
 table:UniformCrossShearTableMachine.Table I (rows c l ha he) u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 saved:∀q,100≤q → q≤106 → u.natReg q=s.natReg q
 natPrefix:∀q,q<c.chunk.borrowed → u.natHeap q=s.natHeap q
 scalarOutside:∀q,(q<c.pool ∨c.pool+9*c.ambient≤q) → q≠c.mu → q≠c.conjugate → u.scalarHeap q=s.scalarHeap q

lemma factors_execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ) (il:InverseLayout c l I) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s a:State)
 (args:UniformForwardMatchingFactorPreparation.Header c s) (h:AfterInverse c l ha he I s a)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:a.pc=43) (wb:WordBound B a):∃u t,
 BoundedExecution program n x B a t u ∧t≤45*c.ambient+117*(rows c l ha he).length+24 ∧u.pc=192 ∧
 Result c l ha he I bank s u ∧u.natReg 894=(rows c l ha he).length:=by
 have safe:=factorSetup_safe h.zero wb
 have start:=block_runs factorSetup program 43 n B x a factorSetup_code pc wb
  (by rw[factorSetup_length];have:=il.code;omega) safe.1 safe.2
 let b:=applyBlock factorSetup a
 have bp:b.pc=53:=by rw[applyBlock_pc,pc,factorSetup_length]
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
  c.conjugates c.mu c.conjugate I (b.natReg 2141) b:=
  factorSetup_args h.zero h.positive h.constants
   ((h.high 4429 (by omega) (by omega)).trans args.negative)
   ((h.high 4428 (by omega) (by omega)).trans args.conjugates)
   ((h.high 4426 (by omega) (by omega)).trans args.mu)
   ((h.high 4427 (by omega) (by omega)).trans args.conjugate)
   h.inverse
 have head:UniformMatchingConjugateLoadMachine.RowArgs c.chunk.height.C c.negative c.chunk.height.P
  c.conjugates c.mu c.conjugate I (ready.natReg 2141) ready:=
  ⟨before.positive,before.negative,before.constants,before.conjugates,before.original,before.conjugate,before.rows,before.index⟩
 have pool:=factorSetup_pool (c:=c) h.zero
  ((h.high 4424 (by omega) (by omega)).trans args.pool)
  ((h.high 4425 (by omega) (by omega)).trans args.ambient)
 have count:ready.natReg 894=(rows c l ha he).length:=
  (factorSetup_nat a 894 (Or.inl (by omega)) (Or.inl (by omega))
   (Or.inl (by omega)) (Or.inl (by omega))).trans h.count
 have table:UniformCrossShearTableMachine.Table I (rows c l ha he) ready:=h.table
 have geometry:=rows_geometry c l ha he
 have rowB:I+3*(rows c l ha he).length≤B:=by
  rw[rows_length];have:=UniformForwardMatchingFactorPreparation.row_count_bound c l ha he;have:=il.bound;omega
 obtain ⟨z,t,run,cost,zp,done,src',cons',table',nh,outs,roots,outside⟩:=
  UniformGlobalMatchingPoolPreparation.execution (rows c l ha he) (coefficient c l ha he)
   (coefficient_address c l ha he) head src cons table count pool.1 pool.2
   geometry.1 geometry.2.1 geometry.2.2 l.coefficient l.low l.poolFresh rowB l.poolBound
   (by have:=il.code;omega) x rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed factor_code
  (by rw[UniformGlobalMatchingPoolPreparation.program_length];have:=il.code;omega)
  (by have:=il.code;omega) run
 rw[show placed 53 ready=b by change {b with pc:=53}=b;rw[←bp]] at placedRun
 let u:=setPC z 192
 have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
  (by simp[step,u,setPC,halt_at])
 have countFinal:u.natReg 894=(rows c l ha he).length:=
  (UniformGlobalMatchingPoolPreparation.execution_nat run (q:=894) (by decide)).trans count
 refine ⟨u,10+t+1,?_,by omega,rfl,?_,countFinal⟩
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
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
