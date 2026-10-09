import UniformInverseMatchingFactorWholeExecution
import UniformForwardMatchingFactorHeaderPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
def reloadProgram:Program:=UniformForwardMatchingFactorHeaderPreparation.setup.map Op.code++
 wholeProgram.map (relocate 14 473)++[.halt]
lemma reloadProgram_length:reloadProgram.length=474:=by
 simp[reloadProgram,UniformForwardMatchingFactorHeaderPreparation.setup_length,wholeProgram_length]
lemma reload_setup_code:BlockAt UniformForwardMatchingFactorHeaderPreparation.setup reloadProgram 0:=by
 intro i hi;change i<14 at hi;interval_cases i <;>rfl
lemma reload_body_code:CodeAt wholeProgram reloadProgram 14 473:=
 UniformChunkRowTableMachine.segment_code (UniformForwardMatchingFactorHeaderPreparation.setup.map Op.code)
  [.halt] _ 14 473 (by rw[List.length_map,UniformForwardMatchingFactorHeaderPreparation.setup_length])
lemma reload_halt:reloadProgram[473]?=some .halt:=by
 rw[reloadProgram,List.getElem?_append_right (by simp[UniformForwardMatchingFactorHeaderPreparation.setup_length,wholeProgram_length])]
 simp only[List.length_append,List.length_map,UniformForwardMatchingFactorHeaderPreparation.setup_length,wholeProgram_length];rfl
lemma reloadResult {c:F.Config} {l:F.Layout c B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he I bank (setPC (applyBlock UniformForwardMatchingFactorHeaderPreparation.setup s) 0) u)
 (pc:ℕ):Result c l ha he I bank s (setPC u pc):=by
 refine ⟨⟨h.factors.done,h.factors.remaining,h.factors.untouched⟩,
  ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩,
  h.constants,h.table,h.outputs,h.roots,?_,h.natPrefix,h.scalarOutside⟩
 intro q lo hi
 exact (h.saved q lo hi).trans (UniformForwardMatchingFactorHeaderPreparation.setup_nat s q (Or.inl (by omega)) (by omega))
theorem reload_execution {n:ℕ} (c:F.Config) (l:UniformForwardMatchingFactorPreparation.Layout c B)
 (code:474≤B) (ha he) (I:ℕ) (il:InverseLayout c l I) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s:State)
 (args:UniformForwardMatchingFactorHeaderPreparation.Args c s) (slot:Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (ip:s.natReg 4460=I) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution reloadProgram n x B s t u ∧
 t≤4*c.chunk.height.K+180*c.chunk.radix+45*c.ambient+
  161*(rows c l ha he).length+177 ∧
 u.pc=473 ∧Result c l ha he I bank s u ∧
 u.natReg 894=(rows c l ha he).length:=by
 have safe:=UniformForwardMatchingFactorHeaderPreparation.setup_safe wb
 have start:=block_runs UniformForwardMatchingFactorHeaderPreparation.setup reloadProgram 0 n B x s reload_setup_code pc wb
  (by rw[UniformForwardMatchingFactorHeaderPreparation.setup_length];omega) safe.1 safe.2
 let b:=applyBlock UniformForwardMatchingFactorHeaderPreparation.setup s
 have bp:b.pc=14:=by rw[applyBlock_pc,pc,UniformForwardMatchingFactorHeaderPreparation.setup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have head:UniformForwardMatchingFactorPreparation.Header c ready:=UniformForwardMatchingFactorHeaderPreparation.setup_header_zero args
 have source:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank ready:=by
  have heap:ready.scalarHeap=s.scalarHeap:=rfl
  constructor
  · intro i;rw[heap];exact sources.positive i
  · intro i;rw[heap];exact sources.negative i
  · intro i;rw[heap];exact sources.conjugate i
  · intro i hi;rw[heap];exact sources.constants i hi
 obtain ⟨z,t,run,cost,zp,result,count⟩ :=whole_execution c l ha he I il (by omega) x bank ready
  head slot processed source constants
  ((UniformForwardMatchingFactorHeaderPreparation.setup_nat s 4460 (Or.inr (by omega)) (by omega)).trans ip) rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed reload_body_code
  (by rw[wholeProgram_length];omega) (by omega) run
 rw[show placed 14 ready=b by change {b with pc:=14}=b;rw[←bp]] at placedRun
 let u:=setPC z 473
 have stop:BoundedExecution reloadProgram n x B u 1 u:=.halt placedRun.final_bound
  (by simp[step,u,setPC,reload_halt])
 refine ⟨u,14+t+1,?_,by omega,rfl,reloadResult result 473,count⟩
 simpa only[UniformForwardMatchingFactorHeaderPreparation.setup_length,u,setPC,Nat.add_assoc] using start.executes (placedRun.executes stop)
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
