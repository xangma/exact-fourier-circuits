import UniformInverseMatchingFactorWhole
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
lemma Result.withPC {c:F.Config} {l:F.Layout c B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he I bank s u) (pc:ℕ):Result c l ha he I bank s (setPC u pc):=
 ⟨⟨h.factors.done,h.factors.remaining,h.factors.untouched⟩,
  ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩,
  h.constants,h.table,h.outputs,h.roots,h.saved,h.natPrefix,h.scalarOutside⟩
lemma translationWithPC {c:F.Config} {l:F.Layout c B} {ha he} {s u:State}
 (h:UniformForwardMatchingFactorPreparation.AfterTranslation c l ha he s u) (pc:ℕ):
 UniformForwardMatchingFactorPreparation.AfterTranslation c l ha he s (setPC u pc):=
 ⟨h.table,h.scalar,h.outputs,h.roots,h.high,h.zero,h.count,h.positive,h.constants,h.saved,h.natPrefix⟩
/-- Genuine physical inverse slot→actual chunk matching→translation→actual
inverse-pointer printer→nine-lane pool. No inverse table or factor readiness
is an entry premise. The inverse flag is read from its produced descriptor. -/
theorem whole_execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ)
 (il:InverseLayout c l I) (code:459≤B) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (s:State)
 (args:UniformForwardMatchingFactorPreparation.Header c s) (slot:Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (ip:s.natReg 4460=I) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution wholeProgram n x B s t u ∧
 t≤4*c.chunk.height.K+180*c.chunk.radix+45*c.ambient+161*(rows c l ha he).length+162 ∧
 u.pc=458 ∧Result c l ha he I bank s u ∧u.natReg 894=(rows c l ha he).length:=by
 obtain ⟨a,t,first,cost,ap,chunk,ai⟩:=chunk_execution c l ha he x s args slot processed pc wb
 obtain ⟨b,second,bp,translated,bi⟩:=translate_execution c l ha he x s a args ap chunk first.final_bound
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 second.final_bound (by omega)
 obtain ⟨z,t',last,cost',zp,result,count⟩:=execution c l ha he I il x bank s ready args
  (translationWithPC translated 0) sources constants (bi.trans (ai.trans ip)) rfl rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed continuation_code
  (by rw[program_length];omega) (by omega) last
 rw[show placed 265 ready=b by change {b with pc:=265}=b;rw[←bp]] at moved
 let u:=setPC z 458
 have stop:BoundedExecution wholeProgram n x B u 1 u:=.halt moved.final_bound
  (by simp[step,u,setPC,whole_halt])
 refine ⟨u,t+(19*(UniformForwardMatchingFactorPreparation.rows c l ha he).length+9)+t'+1,
  ?_,?_,rfl,result.withPC 458,count⟩
 · simpa only[u,setPC,Nat.add_assoc] using first.trans second |>.executes (moved.executes stop)
 · have lengthEq:=rows_length c l ha he;omega
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
