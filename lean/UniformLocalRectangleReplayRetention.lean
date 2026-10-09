import UniformLocalRectangleCoefficientRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleReplayPreparation.Retention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalRectangleReplayPreparation UniformCacheRetentionRegions
attribute [local irreducible] UniformLocalRectangleCoefficientMachine.program UniformLocalReplayAssembly.program
noncomputable section
theorem execution {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:UniformRankCrossPreparationMachine.Parameters)
 (dest A B:ℕ) (x:Fin n → ℂ) (s:State)
 (args:UniformLocalRectangleBankMachine.Args j D original s)
 (nextArgs:UniformLocalRectangleCoefficientMachine.NextArgs work dest s) (slotAddress:s.natReg 4230=A)
 (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (conj:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (ops:UniformInitialPreparation.Operands n x s)
 (layout:UniformSeedHeightPreparation.Layout n j (UniformLocalRectangleBankMachine.geometry q original) B)
 (fresh:UniformLocalRectangleCoefficientMachine.PrefixFresh n (UniformLocalRectangleBankMachine.geometry q original))
 (rowBefore:∀base∈[(UniformLocalRectangleBankMachine.geometry q original).d,
  (UniformLocalRectangleBankMachine.geometry q original).conv,(UniformLocalRectangleBankMachine.geometry q original).tape,
  (UniformLocalRectangleBankMachine.geometry q original).depth,(UniformLocalRectangleBankMachine.geometry q original).order,
  (UniformLocalRectangleBankMachine.geometry q original).directory,(UniformLocalRectangleBankMachine.geometry q original).rows,
  (UniformLocalRectangleBankMachine.geometry q original).colors,(UniformLocalRectangleBankMachine.geometry q original).palette,
  (UniformLocalRectangleBankMachine.geometry q original).heightDirectory],D+7 ≤ base)
 (allocation:UniformConjugateRankSpectrumPreparation.Allocation n j (C.nextParameters n j q original work) dest B)
 (nativeBefore:∀base∈[work.d,work.conv,work.tape,work.depth],
  UniformCrossHeightPreparationMachine.recordBase (UniformLocalRectangleBankMachine.geometry q original).height
   (8*(UniformLocalRectangleBankMachine.geometry q original).exponent+7) ≤ base)
 (positive:(UniformLocalRectangleBankMachine.geometry q original).C+7*(UniformLocalRectangleBankMachine.geometry q original).width+1 ≤ work.S)
 (negative:(UniformLocalRectangleBankMachine.geometry q original).negative+7*(UniformLocalRectangleBankMachine.geometry q original).width ≤ work.S)
 (constants:(UniformLocalRectangleBankMachine.geometry q original).constants+6 ≤ work.S)
 (slotsFresh:UniformCrossHeightPreparationMachine.recordBase (UniformLocalRectangleBankMachine.geometry q original).height
  (8*(UniformLocalRectangleBankMachine.geometry q original).exponent+7) ≤ A)
 (originalDirectory:directoryBase n+2*axisCount n ≤ A)
 (conjugateDirectory:UniformConjugateRankSpectrumPreparation.dirEnd n ≤ A)
 (slotHeight:8*(UniformLocalRectangleBankMachine.geometry q original).exponent+7 ≤ B)
 (slotEnvelope:A+55*UniformLocalReplayAssembly.phasePrefix
  (8*(UniformLocalRectangleBankMachine.geometry q original).exponent+6) 6 ≤ B)
 (rowBound:D+6 ≤ B) (code:2114 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧
 t ≤ UniformLocalRectangleCoefficientMachine.runtimeBudget n j q original work+
  247*UniformLocalReplayAssembly.phasePrefix (8*(UniformLocalRectangleBankMachine.geometry q original).exponent+6) 6+113 ∧
 u.pc=2113 ∧
 UniformLocalReplayAssembly.Generated (UniformLocalRectangleBankMachine.geometry q original).exponent A 6 u ∧
 UniformSeedHeightPreparation.Result n j (UniformLocalRectangleBankMachine.geometry q original) B
  (layout.replay hn j (UniformLocalRectangleBankMachine.geometry q original) B) u ∧
 UniformMatchingConjugateLoadMachine.Sources (UniformLocalRectangleBankMachine.geometry q original).exponent
  (UniformLocalRectangleBankMachine.geometry q original).C (UniformLocalRectangleBankMachine.geometry q original).negative
  (UniformLocalRectangleBankMachine.geometry q original).constants dest
  (fun i:Fin (7*(UniformLocalRectangleBankMachine.geometry q original).width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j (UniformLocalRectangleBankMachine.geometry q original))
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) u ∧
 Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 ReplayFrame (UniformLocalRectangleBankMachine.geometry q original) (C.nextParameters n j q original work) dest A s u := by
 let c:=UniformLocalRectangleBankMachine.geometry q original
 obtain ⟨v,t,first,bound,vp,new,height,sources,vr,vc,vm,vo,out,roots,kept⟩:=
  UniformLocalRectangleCoefficientMachine.Retention.execution hn j D q original work dest B x s args nextArgs source
   metadata ret conj ops layout fresh rowBefore allocation nativeBefore positive negative constants rowBound
   (by omega) pc hs
 have retainedA:v.natReg 4230=A:=(UniformNewtonTableMachine.Executes.keeps_nat first.executes coefficient_keeps_slot).trans slotAddress
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed coefficient_code
  (by rw [UniformLocalRectangleCoefficientMachine.program_length];omega) (by omega) first
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedFirst
 let w:=setPC v 1851
 have safe:=setup_safe w placedFirst.final_bound
 have headers:=setup_headers w height.cursor.header.exponent retainedA
 have install:=block_runs setup program 1851 n B x w setup_code rfl placedFirst.final_bound
  (by rw [setup_length];omega) safe.1 safe.2
 let z:=applyBlock setup w
 have zp:z.pc=1854:=by rw [applyBlock_pc,setup_length];rfl
 let entry:=setPC z 0
 have eb:=changePC_bound B z 0 install.final_bound (by omega)
 obtain ⟨last,run,lastPC,generated,cursor,outside⟩:=UniformLocalReplayAssembly.execution n c.exponent A B x entry
  headers.1 headers.2 rfl eb (by omega) slotHeight slotEnvelope
 have call:=UniformBoundedAssembly.boundedExecution_placed replay_code
  (by rw [UniformLocalReplayAssembly.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero z 1854 zp] at call
 let u:=setPC last 2113
 have stop:BoundedExecution program n x B u 1 u:=.halt call.final_bound (by simp [step,u,setPC,halt_at])
 have scalar:=UniformLocalReplayAssembly.execution_scalarFrame run
 have entryScalar:entry.scalarHeap=v.scalarHeap:=rfl
 have entryNat:entry.natHeap=v.natHeap:=rfl
 have before:UniformSeedRankCrossPreparation.PreservedFrame n v entry:=
  (UniformLocalRectangleBankMachine.reset_frame v 1851).trans
   ((setup_frame w).trans (UniformLocalRectangleBankMachine.reset_frame z 0))
 have after:UniformSeedRankCrossPreparation.PreservedFrame n entry last:=by
  refine ⟨?_,?_,?_,scalar.outputs,scalar.rootOrders⟩
  · intro i hi;exact outside i (Or.inl (lt_of_lt_of_le hi originalDirectory))
  · intro i _;exact congrFun scalar.1 i
  · intro r lo hi
    exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (replay_keeps r (by omega))
 have oldEntry:UniformSeedHeightPreparation.Result n j c B (layout.replay hn j c B) entry:=
  UniformLocalRectangleCoefficientMachine.result_withPC
   (setup_result (UniformLocalRectangleCoefficientMachine.result_withPC height))
 have lastHeight:=result_replay hn j c B A _ x entry last layout oldEntry run outside slotsFresh
 have finalFrame:=UniformLocalRectangleBankMachine.reset_frame (n:=n) last 2113
 have full:=before.trans (after.trans finalFrame)
 have finalConjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=by
  apply UniformLocalRectangleCoefficientMachine.conjugate_retained vc
  · intro i _;exact (congrFun scalar.1 i).trans (congrFun entryScalar i)
  · intro i hi
    exact (outside i (Or.inl (lt_of_lt_of_le hi conjugateDirectory))).trans (congrFun entryNat i)
 have finalSources:UniformMatchingConjugateLoadMachine.Sources c.exponent c.C c.negative c.constants dest
  (fun i:Fin (7*c.width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j c) (UniformSeedRankCrossPreparation.hValue n j)
   (UniformSeedRankCrossPreparation.gValue n j) i.val) u:=by
  have scalarEq:∀i,u.scalarHeap i=v.scalarHeap i:=fun i=>(congrFun scalar.1 i).trans (congrFun entryScalar i)
  refine ⟨fun i=>(scalarEq _).trans (sources.positive i),fun i=>(scalarEq _).trans (sources.negative i),
   fun i=>(scalarEq _).trans (sources.conjugate i),fun i hi=>(scalarEq _).trans (sources.constants i hi)⟩
 refine ⟨u,t+3+(247*UniformLocalReplayAssembly.phasePrefix (8*c.exponent+6) 6+109)+1,
  ?_,by dsimp only [c];omega,rfl,generated,UniformLocalRectangleCoefficientMachine.result_withPC lastHeight,
  finalSources,full.retained vr,finalConjugate,full.protected.metadata vm,full.protected.operands vo,?_,?_,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using placedFirst.executes (install.executes (call.executes stop))
 · exact full.2.2.2.1.trans out
 · exact full.2.2.2.2.trans roots

 · constructor
   · intro i ho hc hs
     exact (slot_nat outside i hs).trans ((congrFun entryNat i).trans (kept.1 i ho hc))
   · intro i ho hc
     exact (congrFun scalar.1 i).trans ((congrFun entryScalar i).trans (kept.2 i ho hc))

end
end ExactFourierCircuits.UniformLocalRectangleReplayPreparation.Retention
