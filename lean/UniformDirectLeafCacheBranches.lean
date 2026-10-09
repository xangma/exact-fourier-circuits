import UniformDirectLeafCacheScale
import UniformDirectLeafCacheBootstrap
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheBranches
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheSetup UniformDirectLeafCacheProgram
open UniformTransposeDescriptorMachine (Record)
noncomputable section

lemma scale_execution {c:Config} {r A C n B:ℕ} {q:Record} (mu:ℂ) (x:Fin n→ℂ) (s:State)
 (h:Installed c r A C q s) (src:s.scalarHeap q.coefficient=some (UniformPairMachine.prepared mu))
 (ones:UniformGlobalScalePoolMachine.Prefix c.pool (9*r) s)
 (kind:q.kind=0) (dest:q.dest<r) (pool:c.pool+9*r≤B) (coefficient:q.coefficient≤B)
 (code:264≤B) (pc:s.pc=53) (wb:WordBound B s) : ∃u,
 BoundedRuns UniformDirectLeafCacheProgram.program n x B s 7 u ∧u.pc=183 ∧
 UniformDirectLeafCacheScale.Table c.pool r q.dest mu u ∧
 UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry 1 0 u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) := by
 let a:=setPC s 54
 have ab:=changePC_bound B s 54 wb (by omega)
 have first:step UniformDirectLeafCacheProgram.program n x s=.running a:=by
  simp [step,pc,branch_at,h.read.kind,h.read.one,kind,a,setPC]
 have safe:=UniformDirectLeafCacheScale.scale_safe h.args h.read src dest (by omega) coefficient code
 have body:=block_runs scale UniformDirectLeafCacheProgram.program 54 n B x a scale_code rfl ab
  (by rw[scale_length];omega) safe.1 safe.2
 let b:=applyBlock scale a
 have bp:b.pc=59:=by rw[applyBlock_pc,scale_length];rfl
 let u:=setPC b 183
 have ub:=changePC_bound B b 183 body.final_bound (by omega)
 have jump:step UniformDirectLeafCacheProgram.program n x b=.running u:=by simp only[step,bp,scale_jump];rfl
 have dir:=UniformDirectLeafCacheScale.scale_directory (h.core.setPC 54)
 have finalDir:UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry 1 0 u:=⟨dir.time,dir.radix,dir.pool,dir.permutation,dir.widths,dir.markers,
   dir.axis,dir.rows,dir.directory,dir.kind,dir.count⟩
 refine ⟨u,?_,rfl,UniformDirectLeafCacheScale.scale_values (UniformDirectLeafCacheSetup.Args.setPC h.args 54) (UniformDirectLeafCacheSetup.Read.setPC h.read 54) src ones dest,
  finalDir,rfl,rfl,rfl,?_⟩
 · convert (BoundedRuns.next wb first body).trans (.next body.final_bound jump (.refl ub)) using 1; rfl
 · intro j hj
   exact UniformDirectLeafCacheScale.scale_other (UniformDirectLeafCacheSetup.Args.setPC h.args 54) (UniformDirectLeafCacheSetup.Read.setPC h.read 54) src j hj dest

def mark : List Op := [.literal 894 1,.literal 5849 0]
lemma mark_code : BlockAt mark UniformDirectLeafCacheProgram.program 60 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma mark_length : mark.length=2 := rfl
lemma mark_nat (s:State) (j:ℕ) (a:j≠894) (b:j≠5849) :
 (applyBlock mark s).natReg j=s.natReg j:=by simp[mark,applyBlock,Op.apply,writeNat,next,a,b]
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
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) := by
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
 obtain ⟨out,tailRun,outp,factors,nh,outs,roots,outside,_pair⟩:=UniformDirectLeafFactorTail.execution mu
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
 refine ⟨u,?_,rfl,factors,dir,nh,outs,roots,outside⟩
 · convert (BoundedRuns.next wb first marked).trans
    ((BoundedRuns.next marked.final_bound jump (.refl jb)).trans place) using 1 <;>rfl
end
end ExactFourierCircuits.UniformDirectLeafCacheBranches
