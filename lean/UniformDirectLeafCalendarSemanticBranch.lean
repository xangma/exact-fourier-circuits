import UniformDirectLeafCacheBranches
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCalendarSemanticBranch
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheSetup UniformDirectLeafCacheProgram
open UniformDirectLeafCacheBranches
open UniformTransposeDescriptorMachine (Record)
noncomputable section
lemma shear_execution {c:Config} {r A C n B:ℕ} {q:Record} (mu:ℂ) (x:Fin n→ℂ) (s:State)
 (h:Installed c r A C q s)
 (src:UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) s)
 (constants:UniformHadamardPairMachine.Constants s)
 (ones:UniformGlobalScalePoolMachine.Prefix c.pool (9*r) s)
 (kind:q.kind=1) (dest:q.dest<r) (source:q.source<r) (distinct:q.dest≠q.source)
 (rows:c.rows+1≤B) (pool:c.pool+9*r≤B) (code:264≤B) (pc:s.pc=53)
 (wb:WordBound B s) : ∃u,
 BoundedRuns UniformDirectLeafCacheProgram.program n x B s 95 u ∧u.pc=183 ∧
 UniformGlobalMatchingScaleMachine.FullFactorTable c.pool r q.dest q.source mu u ∧
 UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry 0 1 u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) ∧
 (∀(lane:Fin 9)(i:Fin r),i.val≠q.dest→i.val≠q.source→
  u.scalarHeap (c.pool+lane.val*r+i.val)=some (UniformPairMachine.prepared 1)) := by
 let a:=setPC s 60
 have ab:=changePC_bound B s 60 wb (by omega)
 have first:step UniformDirectLeafCacheProgram.program n x s=.running a:=by
  simp [step,pc,branch_at,h.read.kind,h.read.one,kind,a,setPC]
 have safe:readable mark a∧peak mark a≤B:=by simp[mark,readable,peak,Op.readable,Op.peak];omega
 have marked:=block_runs mark UniformDirectLeafCacheProgram.program 60 n B x a mark_code rfl ab
  (by change 60+2≤B;omega) safe.1 safe.2
 let b:=applyBlock mark a
 have bp:b.pc=62:=by rw[applyBlock_pc,mark_length];rfl
 let j:=setPC b 92
 have jb:=changePC_bound B b 92 marked.final_bound (by omega)
 have jump:step UniformDirectLeafCacheProgram.program n x b=.running j:=by
  simp only[step,bp,shear_jump];rfl
 let start:=setPC j 29
 have swb:=changePC_bound B j 29 jb (by omega)
 have kept (q:ℕ) (n894:q≠894) (n5849:q≠5849):start.natReg q=s.natReg q:=mark_nat a q n894 n5849
 have head:UniformZeroFreePairShearMachine.Args 0 0 q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) start:=by
  exact ⟨(kept _ (by omega) (by omega)).trans h.scales.leftAddress,
   (kept _ (by omega) (by omega)).trans h.scales.rightAddress,
   (kept _ (by omega) (by omega)).trans h.scales.coefficient,
   (kept _ (by omega) (by omega)).trans h.scales.conjugateCoefficient⟩
 obtain ⟨out,tailRun,outp,factors,nh,outs,roots,outside,pairOutside⟩:=UniformDirectLeafFactorTail.execution mu
  q.coefficient (C+3*r+(q.coefficient-(A+3*r))) c.pool r c.rows q.dest q.source n B x start
  head src constants ((kept _ (by omega) (by omega)).trans h.pool)
  ((kept _ (by omega) (by omega)).trans h.radix)
  ((kept _ (by omega) (by omega)).trans h.rows)
  ((kept _ (by omega) (by omega)).trans h.index) h.dest h.source rows dest source distinct pool
  (by omega) ones rfl swb
 have place:=UniformBoundedAssembly.boundedExecution_placed factor_code
  (by rw[UniformGlobalMatchingScaleMachine.rowProgram_length];omega) (by omega) tailRun
 rw[show placed 63 start=j by change {j with pc:=92}=j;rfl] at place
 let u:=setPC out 183
 have retained (i:ℕ) (hi:i∉UniformGlobalMatchingScaleMachine.natScratch):
  u.natReg i=start.natReg i:=by
  change out.natReg i=start.natReg i
  exact UniformGlobalMatchingScaleMachine.execution_nat tailRun hi
 have core:Core c r u:=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.time)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.radix)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.pool)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.permutation)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.widths)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.markers)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.axis)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.rows)
   |exact (retained _ (by simp[UniformGlobalMatchingScaleMachine.natScratch])).trans ((kept _ (by omega) (by omega)).trans h.core.directory)
 have dir:UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry 0 1 u:=by
  refine ⟨core.time,core.radix,core.pool,core.permutation,core.widths,core.markers,core.axis,
   core.rows,core.directory,?_,?_⟩
  · rw[retained 5849 (by simp[UniformGlobalMatchingScaleMachine.natScratch])]
    simp[start,j,b,a,setPC,mark,applyBlock,Op.apply,writeNat,next]
  · rw[retained 894 (by simp[UniformGlobalMatchingScaleMachine.natScratch])]
    simp[start,j,b,a,setPC,mark,applyBlock,Op.apply,writeNat,next]
 refine ⟨u,?_,rfl,factors,dir,nh,outs,roots,outside,?_⟩
 · convert (BoundedRuns.next wb first marked).trans
    ((BoundedRuns.next marked.final_bound jump (.refl jb)).trans place) using 1 <;>rfl
 · intro lane i neDest neSource
   have outsidePair:UniformGlobalMatchingScaleMachine.PairOutside c.pool r q.dest q.source
     (c.pool+lane.val*r+i.val):=by
    intro chosen
    constructor
    · change c.pool+lane.val*r+i.val≠c.pool+chosen.val*r+q.dest
      intro equal
      have eq:lane.val*r+i.val=chosen.val*r+q.dest:=by omega
      have same:lane.val=chosen.val:=by
       by_contra ne
       rcases lt_or_gt_of_ne ne with lower|upper
       · have mul:=Nat.mul_le_mul_right r (show lane.val+1≤chosen.val by omega)
         have ir:=i.isLt
         have dr:=dest
         nlinarith
       · have mul:=Nat.mul_le_mul_right r (show chosen.val+1≤lane.val by omega)
         have ir:=i.isLt
         have dr:=dest
         nlinarith
      rw[same] at eq
      exact neDest (Nat.add_left_cancel eq)
    · change c.pool+lane.val*r+i.val≠c.pool+chosen.val*r+q.source
      intro equal
      have eq:lane.val*r+i.val=chosen.val*r+q.source:=by omega
      have same:lane.val=chosen.val:=by
       by_contra ne
       rcases lt_or_gt_of_ne ne with lower|upper
       · have mul:=Nat.mul_le_mul_right r (show lane.val+1≤chosen.val by omega)
         have ir:=i.isLt
         have sr:=source
         nlinarith
       · have mul:=Nat.mul_le_mul_right r (show chosen.val+1≤lane.val by omega)
         have ir:=i.isLt
         have sr:=source
         nlinarith
      rw[same] at eq
      exact neSource (Nat.add_left_cancel eq)
   change out.scalarHeap (c.pool+lane.val*r+i.val)=_
   rw[pairOutside _ outsidePair]
   have bound:lane.val*r+i.val<9*r:=by
    have lr:=lane.isLt;have ir:=i.isLt;nlinarith
   simpa only[start,j,b,a,setPC,mark,applyBlock,Op.apply,writeNat,next,Nat.add_assoc] using ones _ bound

end
end ExactFourierCircuits.UniformDirectLeafCalendarSemanticBranch
