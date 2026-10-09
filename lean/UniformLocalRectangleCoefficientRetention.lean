import UniformCacheRetentionRegions
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleCoefficientMachine.Retention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
open UniformLocalRectangleCoefficientMachine UniformCacheRetentionRegions
attribute [local irreducible] UniformLocalRectangleBankMachine.program UniformConjugateRankSpectrumPreparation.program
noncomputable section
theorem execution {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:C.Parameters) (dest B:ℕ)
 (x:Fin n → ℂ) (s:State)
 (args:UniformLocalRectangleBankMachine.Args j D original s) (nextArgs:NextArgs work dest s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (conj:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (ops:UniformInitialPreparation.Operands n x s)
 (layout:UniformSeedHeightPreparation.Layout n j (O.c q original) B)
 (fresh:PrefixFresh n (O.c q original))
 (rowBefore:∀base∈[(O.c q original).d,(O.c q original).conv,(O.c q original).tape,
  (O.c q original).depth,(O.c q original).order,(O.c q original).directory,
  (O.c q original).rows,(O.c q original).colors,(O.c q original).palette,(O.c q original).heightDirectory],D+7 ≤ base)
 (allocation:C.Allocation n j (nextParameters n j q original work) dest B)
 (nativeBefore:∀base∈[work.d,work.conv,work.tape,work.depth],
  UniformCrossHeightPreparationMachine.recordBase (O.c q original).height (8*(O.c q original).exponent+7) ≤ base)
 (positive:(O.c q original).C+7*(O.c q original).width+1 ≤ work.S)
 (negative:(O.c q original).negative+7*(O.c q original).width ≤ work.S)
 (constants:(O.c q original).constants+6 ≤ work.S)
 (rowBound:D+6 ≤ B) (code:1851 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget n j q original work ∧ u.pc=1850 ∧
 UniformConjugateRankSpectrumPreparation.Result n j (nextParameters n j q original work) dest u ∧
 UniformSeedHeightPreparation.Result n j (O.c q original) B (layout.replay hn j (O.c q original) B) u ∧
 UniformMatchingConjugateLoadMachine.Sources (O.c q original).exponent (O.c q original).C
  (O.c q original).negative (O.c q original).constants dest
  (fun i:Fin (7*(O.c q original).width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j (O.c q original))
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) u ∧
 Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 CoefficientFrame (O.c q original) (nextParameters n j q original work) dest s u := by
 obtain ⟨v,t,run,time,vp,result,vr,vm,vo,frame,outside⟩:=
  UniformLocalRectangleBankMachine.execution hn j D q original B x s args source metadata ret ops
   layout rowBound (by omega) pc hs
 have pref:=outside_prefix fresh outside
 have vc:=conjugate_retained conj pref.1 pref.2
 have row:=row_source_retained source rowBefore outside
 have reg:∀r,1230 ≤ r → r∉[4202,4203,4204,4205,4206] → v.natReg r=s.natReg r:=by
  intro r lo allowed
  exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (original_keeps r lo allowed)
 have axis:v.natReg 4200=j.val:=(reg _ (by omega) (by simp)).trans args.1
 have address:v.natReg 4201=D:=(reg _ (by omega) (by simp)).trans args.2.1
 have next:NextArgs work dest v:=by
  intro r lo hi
  rw [reg r (by omega) (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)]
  exact nextArgs r lo hi
 let w:=setPC v 1064
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed original_code
  (by rw [UniformLocalRectangleBankMachine.program_length];omega) (by omega) run
 have pe:placed 0 s=s:=by cases s;simp [placed]
 rw [pe] at placedRun
 have wb:=placedRun.final_bound
 have safe:=setup_safe w address row wb rowBound (by omega)
 have install:=block_runs setup program 1064 n B x w setup_code rfl wb
  (by rw [setup_length];omega) safe.1 safe.2
 have installedPC:(installedState w).pc=1087:=by
  rw [installedState_eq,applyBlock_pc,setup_length];rfl
 have installedArgs:UniformConjugateRankSpectrumPreparation.Arguments n j
  (nextParameters n j q original work) dest (installedState w):=by
  rw [installedState_eq]
  exact setup_spec j D q original work dest w axis address row result.cursor.header.exponent vm.saved.masterRoot next
 have startFrame:UniformSeedRankCrossPreparation.PreservedFrame n v (applyBlock setup w):=
  (UniformLocalRectangleBankMachine.reset_frame v 1064).trans (setup_frame w)
 have installedOriginal:Retained n (axisCount n) (installedState w):=by
  rw [installedState_eq];exact startFrame.retained vr
 have installedMetadata:UniformPermutationInversePreparation.Metadata n (installedState w):=by
  rw [installedState_eq];exact startFrame.protected.metadata vm
 have installedOperands:UniformInitialPreparation.Operands n x (installedState w):=by
  rw [installedState_eq];exact startFrame.protected.operands vo
 have installedConjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) (installedState w):=by
  rw [installedState_eq]
  exact conjugate_retained vc (fun _ _=>rfl) (fun _ _=>rfl)
 let entry:=setPC (installedState w) 0
 have eb:=changePC_bound B (installedState w) 0 (by rw [installedState_eq];exact install.final_bound) (by omega)
 obtain ⟨z,time2,second,bound,zp,new,newFrame,originalRet,conjRet,metadataOut,oper,master⟩:=
  UniformConjugateRankSpectrumPreparation.execution_retained j (nextParameters n j q original work)
   dest B x entry
    ((UniformLocalRectangleBankMachine.reset_frame (installedState w) 0).protected.metadata installedMetadata)
    ((UniformLocalRectangleBankMachine.reset_frame (installedState w) 0).protected.operands installedOperands)
    ((UniformLocalRectangleBankMachine.reset_frame (installedState w) 0).retained installedOriginal)
    installedConjugate.withPC installedArgs allocation rfl eb
 have call:=UniformBoundedAssembly.boundedExecution_placed conjugate_code
  (by rw [UniformConjugateRankSpectrumPreparation.program_length];omega) (by omega) second
 rw [UniformSeedRankCrossPreparation.placed_zero (installedState w) 1087 installedPC] at call
 let u:=setPC z 1850
 have stop:BoundedExecution program n x B u 1 u:=.halt call.final_bound (by simp [step,u,setPC,halt_at])
 have origResult:UniformSeedHeightPreparation.Result n j (O.c q original) B (layout.replay hn j (O.c q original) B) entry:=by
  change UniformSeedHeightPreparation.Result n j (O.c q original) B _ (setPC (installedState w) 0)
  rw [installedState_eq]
  exact result_withPC (result_setup (result_withPC result))
 have sources:=UniformConjugateRankSpectrumPreparation.seedHeight_sources_retained j (O.c q original)
  B dest (layout.replay hn j (O.c q original) B) work entry z origResult new allocation newFrame (by omega) negative constants
 have kept:∀r,1050 ≤ r → r ≤ 1079 → z.natReg r=entry.natReg r:=by
  intro r lo hi
  exact UniformNewtonTableMachine.Executes.keeps_nat second.executes
   (UniformConjugatePackedMatchingPreparation.spectrum_keeps r (Or.inl ⟨by omega,by omega⟩))
 have originalFinal:=height_result_retained hn j (O.c q original) B layout work dest entry z
  origResult allocation newFrame nativeBefore positive negative constants kept
 have finalFrame:=UniformLocalRectangleBankMachine.reset_frame (n:=n) z 1850
 have finalSources:UniformMatchingConjugateLoadMachine.Sources (O.c q original).exponent (O.c q original).C
  (O.c q original).negative (O.c q original).constants dest
  (fun i:Fin (7*(O.c q original).width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j (O.c q original))
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) u:=
   ⟨sources.positive,sources.negative,sources.conjugate,sources.constants⟩
 refine ⟨u,t+23+time2+1,?_,?_,rfl,new,result_withPC originalFinal,finalSources,finalFrame.retained originalRet,conjRet.withPC,
  finalFrame.protected.metadata metadataOut,finalFrame.protected.operands oper,?_,?_,?_⟩
 · rw [installedState_eq] at call
   simpa only [setup_length,Nat.add_assoc] using placedRun.executes (install.executes (call.executes stop))
 · unfold runtimeBudget
   change t ≤ UniformSeedHeightPreparation.runtimeBudget n j (O.c q original)+18 at time
   have eq:(nextParameters n j q original work).K=(O.c q original).exponent:=rfl
   rw [eq] at bound
   change _ ≤ UniformSeedHeightPreparation.runtimeBudget n j (O.c q original)+
    UniformRankCrossPreparationMachine.runtimeBudget _+91*(UniformRadixTwoDAG.width (O.c q original).exponent)+71
   omega
 · have eq:entry.outputs=v.outputs:=by dsimp only [entry];rw [installedState_eq];rfl
   exact newFrame.2.2.1.trans (eq.trans frame.2.2.2.1)
 · have eq:entry.rootOrders=v.rootOrders:=by dsimp only [entry];rw [installedState_eq];rfl
   exact newFrame.2.2.2.1.trans (eq.trans frame.2.2.2.2)

 · have en:entry.natHeap=v.natHeap:=by dsimp only [entry];rw [installedState_eq];rfl
   have es:entry.scalarHeap=v.scalarHeap:=by dsimp only [entry];rw [installedState_eq];rfl
   constructor
   · intro i ho hc
     exact (conjugate_nat newFrame i hc).trans ((congrFun en i).trans (original_nat outside i ho))
   · intro i ho hc
     exact (conjugate_scalar newFrame i hc).trans ((congrFun es i).trans (original_scalar outside i ho))

end
end ExactFourierCircuits.UniformLocalRectangleCoefficientMachine.Retention
