import UniformInverseMatchingFactorMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
structure InverseLayout (c:F.Config) (l:F.Layout c B) (I:ℕ):Prop where
 fresh:c.translated+6*UniformCrossHeightPreparationMachine.gates c.chunk.height≤I
 bound:I+6*UniformCrossHeightPreparationMachine.gates c.chunk.height≤B
 code:193≤B
structure AfterInverse (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ) (s u:State):Prop where
 table:UniformCrossShearTableMachine.Table I (rows c l ha he) u
 forwardTable:UniformCrossShearTableMachine.Table c.translated
  (UniformForwardMatchingFactorPreparation.rows c l ha he) u
 scalar:u.scalarHeap=s.scalarHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 high:∀q,4410≤q → q≤4429 → u.natReg q=s.natReg q
 zero:u.natReg 4461=0
 inverse:u.natReg 4460=I
 count:u.natReg 894=(rows c l ha he).length
 positive:u.natReg 1060=c.chunk.height.C
 constants:u.natReg 1062=c.chunk.height.P
 saved:∀q,100≤q → q≤106 → u.natReg q=s.natReg q
 natPrefix:∀q,q<c.chunk.borrowed → u.natHeap q=s.natHeap q
lemma inverseSetup_args (s:State) (M F I C T P:ℕ)
 (hm:s.natReg 894=M) (hf:s.natReg 4422=F) (hi:s.natReg 4460=I)
 (hc:s.natReg 1060=C) (ht:s.natReg 4429=T) (hp:s.natReg 1062=P):
 UniformInverseShearTableMachine.Header M F I C T P (applyBlock inverseSetup s):=by
 constructor <;>simp[inverseSetup,applyBlock,Op.apply,writeNat,next,hm,hf,hi,hc,ht,hp]
lemma inverse_execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ)
 (il:InverseLayout c l I) (x:Fin n → ℂ) (orig s:State)
 (args:UniformForwardMatchingFactorPreparation.Header c orig)
 (h:UniformForwardMatchingFactorPreparation.AfterTranslation c l ha he orig s)
 (ip:s.natReg 4460=I) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤25*(rows c l ha he).length+13 ∧u.pc=43 ∧
 AfterInverse c l ha he I orig u:=by
 have code:=il.code
 have safe:=inverseSetup_safe wb
 have start:=block_runs inverseSetup program 0 n B x s inverseSetup_code pc wb
  (by rw[inverseSetup_length];omega) safe.1 safe.2
 let b:=applyBlock inverseSetup s
 have bp:b.pc=7:=by rw[applyBlock_pc,pc,inverseSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have head:UniformInverseShearTableMachine.Header
  (UniformForwardMatchingFactorPreparation.rows c l ha he).length c.translated I c.chunk.height.C
  c.negative c.chunk.height.P ready:=by
  have a:=inverseSetup_args s _ _ _ _ _ _ h.count
   ((h.high 4422 (by omega) (by omega)).trans args.translated) ip h.positive
   ((h.high 4429 (by omega) (by omega)).trans args.negative) h.constants
  exact ⟨a.count,a.source,a.output,a.positive,a.negative,a.constants⟩
 have src:UniformInverseShearTableMachine.Rows c.translated
  (UniformForwardMatchingFactorPreparation.rows c l ha he) ready:=h.table
 have countBound:=UniformForwardMatchingFactorPreparation.row_count_bound c l ha he
 have fromB:c.translated+3*(UniformForwardMatchingFactorPreparation.rows c l ha he).length≤I:=by
  have:=il.fresh;omega
 have toB:I+3*(UniformForwardMatchingFactorPreparation.rows c l ha he).length≤B:=by
  have:=il.bound;omega
 have pb:c.chunk.height.P+3≤B:=by
  have:=l.coefficient.constantsBelow;have:=l.coefficient.conjugatesBelow;have:=l.coefficient.destinations
  have:=l.poolFresh;have:=l.poolBound;omega
 obtain ⟨t,z,cost,run,zp,_,table,forwardTable,outside,frame⟩:=
  UniformInverseShearTableMachine.execution _ c.translated I c.chunk.height.C c.negative c.chunk.height.P
   (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) B n x
   (UniformForwardMatchingFactorPreparation.rows c l ha he) ready head rfl rfl src
   (forward_domain c l ha he) l.coefficient.positiveBelow l.coefficient.negativeBelow pb
   fromB toB (by omega) rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed inverse_code
  (by rw[UniformInverseShearTableMachine.program_length];omega) (by omega) run
 rw[show placed 7 ready=b by change {b with pc:=7}=b;rw[←bp]] at placedRun
 let u:=setPC z 43
 have scalar:u.scalarHeap=orig.scalarHeap:=frame.1.trans ((inverseSetup_heap s).2.1.trans h.scalar)
 refine ⟨u,7+t,?_,?_,rfl,table,forwardTable,scalar,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only[inverseSetup_length,u,setPC] using start.trans placedRun
 · rw[rows_length];unfold UniformInverseShearTableMachine.runtimeBudget at cost;omega
 · exact frame.2.2.1.trans ((inverseSetup_heap s).2.2.1.trans h.outputs)
 · exact frame.2.2.2.1.trans ((inverseSetup_heap s).2.2.2.trans h.roots)
 · intro q lo hi
   exact (frame.2.2.2.2 q (Or.inr (by omega))).trans
    ((inverseSetup_nat s q (Or.inr (by omega)) (by omega)).trans (h.high q lo hi))
 · exact (frame.2.2.2.2 4461 (Or.inr (by omega))).trans rfl
 · exact (frame.2.2.2.2 4460 (Or.inr (by omega))).trans
    ((inverseSetup_nat s 4460 (Or.inr (by omega)) (by omega)).trans ip)
 · rw[rows_length]
   exact (frame.2.2.2.2 894 (Or.inl (by omega))).trans
    ((inverseSetup_nat s 894 (Or.inl (by omega)) (by omega)).trans h.count)
 · exact (frame.2.2.2.2 1060 (Or.inr (by omega))).trans
    ((inverseSetup_nat s 1060 (Or.inr (by omega)) (by omega)).trans h.positive)
 · exact (frame.2.2.2.2 1062 (Or.inr (by omega))).trans
    ((inverseSetup_nat s 1062 (Or.inr (by omega)) (by omega)).trans h.constants)
 · intro q lo hi
   exact (frame.2.2.2.2 q (Or.inl (by omega))).trans
    ((inverseSetup_nat s q (Or.inl (by omega)) (by omega)).trans (h.saved q lo hi))
 · intro q hq
   have below:c.chunk.borrowed≤c.translated:=by
    have l0:=l.chunk.borrowFresh;have l1:=l.chunk.selectedFresh;have l2:=l.chunk.ordinalFresh
    have l3:=l.chunk.mappedFresh;have l4:=l.chunk.permutationFresh;have l5:=l.chunk.widthsFresh
    have l6:=l.chunk.markersFresh;have l7:=l.translatedFresh;omega
   exact (outside q (Or.inl (by have:=il.fresh;omega))).trans (h.natPrefix q hq)
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
