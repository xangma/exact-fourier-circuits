import UniformForwardMatchingFactorHeaderPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorHeaderPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
lemma coreResult {c:F.Config} {l:UniformForwardMatchingFactorPreparation.Layout c B} {ha he}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:UniformForwardMatchingFactorPreparation.Result c l ha he bank (setPC (applyBlock setup s) 0) u)
 (pc:ℕ):UniformForwardMatchingFactorPreparation.Result c l ha he bank s (setPC u pc):=by
 refine ⟨⟨h.factors.done,h.factors.remaining,h.factors.untouched⟩,
  ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩,
  h.constants,h.table,h.outputs,h.roots,?_,h.natPrefix,h.scalarOutside⟩
 intro q lo hi
 exact (h.saved q lo hi).trans (setup_nat s q (Or.inl (by omega)) (by omega))
/-- Charged bank switching removes the current-low-header requirement. The
bank itself must be the genuine enabled-specific Processed output; copying
header fields never manufactures rows or coefficients. -/
theorem execution {n:ℕ} (c:F.Config) (l:UniformForwardMatchingFactorPreparation.Layout c B)
 (code:430≤B) (ha he) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s:State)
 (args:Args c s) (slot:UniformForwardMatchingFactorPreparation.Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution program n x B s t u ∧
 t≤4*c.chunk.height.K+180*c.chunk.radix+45*c.ambient+
  136*(UniformForwardMatchingFactorPreparation.rows c l ha he).length+163 ∧
 u.pc=429 ∧UniformForwardMatchingFactorPreparation.Result c l ha he bank s u:=by
 have safe:=setup_safe wb
 have start:=block_runs setup program 0 n B x s setup_code pc wb
  (by rw[setup_length];omega) safe.1 safe.2
 let b:=applyBlock setup s
 have bp:b.pc=14:=by rw[applyBlock_pc,pc,setup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have head:UniformForwardMatchingFactorPreparation.Header c ready:=setup_header_zero args
 have source:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank ready:=by
  have heap:ready.scalarHeap=s.scalarHeap:=rfl
  constructor
  · intro i;rw[heap];exact sources.positive i
  · intro i;rw[heap];exact sources.negative i
  · intro i;rw[heap];exact sources.conjugate i
  · intro i hi;rw[heap];exact sources.constants i hi
 obtain ⟨z,t,run,cost,zp,result⟩:=UniformForwardMatchingFactorPreparation.execution c l ha he x bank ready
  head slot processed source constants rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed body_code
  (by rw[UniformForwardMatchingFactorPreparation.program_length];omega) (by omega) run
 rw[show placed 14 ready=b by change {b with pc:=14}=b;rw[←bp]] at placedRun
 let u:=setPC z 429
 have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
  (by simp[step,u,setPC,halt_at])
 refine ⟨u,14+t+1,?_,by omega,rfl,coreResult result 429⟩
 simpa only[setup_length,u,setPC,Nat.add_assoc] using start.executes (placedRun.executes stop)
end
end ExactFourierCircuits.UniformForwardMatchingFactorHeaderPreparation
