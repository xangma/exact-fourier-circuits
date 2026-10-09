import UniformLocalRectangleCachePreparation
import UniformLocalCacheContextPriorRetention
import UniformLocalCacheRetainedPrefixes
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleCachePreparation.PriorRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotConductorMachine UniformLocalRectangleCacheBindings
noncomputable section
/-- One actual fixed program produces the original/conjugate shared spectra,
both enabled depth banks, all six control phases and every cached factor/axis
entry. Its inputs are physical retained seeds, an emitted forest request,
ordinary placement and actual allocator registers; no produced-bank premise. -/
theorem execution {n:ℕ}(hn:0<n)(j:Fin (axisCount n))(D:ℕ)(q:Row)
 (original:UniformSeedHeightPreparation.Config)(work:UniformRankCrossPreparationMachine.Parameters)
 (dest A FD FF FU FJ B H I:ℕ)(c:Header.Parameters)(x:Fin n→ℂ)(s:State)
 (layout:UniformSeedHeightPreparation.Layout n j (P.actual q original) B)
 (entry:UniformLocalRectanglePhaseBanks.Entry hn j D q original work dest A B x s layout)
 (falseArgs:UniformLocalDisabledHeightMachine.Args FD FF FU FJ s)
 (falseLayout:UniformCrossHeightPreparationMachine.Layout
  (UniformLocalDisabledHeightMachine.disabled (P.actual q original).height FD FF FU FJ))
 (falseBudget:UniformCrossHeightPreparationMachine.wordBudget
  (UniformLocalDisabledHeightMachine.disabled (P.actual q original).height FD FF FU FJ) ≤ B)
 (trueBefore:UniformCrossHeightPreparationMachine.recordBase (P.actual q original).height
  (8*(P.actual q original).exponent+7) ≤ FD)
 (slotsBefore:A+55*UniformLocalReplayAssembly.phasePrefix (8*(P.actual q original).exponent+6) 6 ≤ FD)
 (binding:Bindings c q original D A dest FD FF FU FJ)
 (driver:Driver j c I H s)
 (ends:UniformCacheRetentionRegions.PhaseEnds (P.actual q original)
  (UniformLocalRectanglePhaseBanks.nextParameters n j q original work) dest A
  (UniformLocalDisabledHeightMachine.disabled (P.actual q original).height FD FF FU FJ) H)
 (ha:q.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height)
 (geometry:Geometry B c q ha he I)
 (prefixPlacement:UniformLocalCacheContextConductor.Prefixes n c)
 (workspaces:∀j (hj:j<352*c.height.K+330) slot (witness:SlotWitness c.height.K j slot),
  UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c j) q slot
   (geometry.layout j hj slot witness) (geometry.broadcast j hj) ha he I ≤ H)
 (code:3690 ≤ B)(total:352*c.height.K+330 ≤ B)(scalar:9*c.ambient ≤ B)
 (natural:3*c.ambient+11 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ UniformLocalRectanglePhaseBanks.runtimeBudget n j q original work+
  (352*c.height.K+330)*(bodyBudget c q+11)+62 ∧ u.pc=3689 ∧
 (∀k,k<352*c.height.K+330 → Cached (B:=B) c q ha he (coefficientBank j q original c) geometry.positive k u) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀i,H ≤ i → (i<c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) →
  i≠c.mu → i≠c.conjugateMu → u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,H ≤ i → i<c.cachePermutation → u.natHeap i=s.natHeap i) ∧
 Cursor.Control c (352*c.height.K+330) u ∧
 Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 (∀r,6160 ≤ r → r ≤ 6179 → u.natReg r=s.natReg r) ∧
 (∀r,6400 ≤ r → u.natReg r=s.natReg r) ∧
 (∀i,H ≤ i → c.cachePermutation+(3*c.ambient+11)*(352*c.height.K+330) ≤ i → u.natHeap i=s.natHeap i):=by
 obtain ⟨a,t,first,cheap,ap,generated,source,yes,cursor,no,sources,retained,conjugate,metadata,operands,out,roots,frame⟩:=
  UniformLocalRectanglePhaseBanks.Retention.execution hn j D q original work dest A FD FF FU FJ B x s
   layout entry falseArgs falseLayout falseBudget trueBefore slotsBefore (by omega) pc wb
 have high:=frame.high ends
 have row:=frame.row hn j D q original work dest A FD FF FU FJ B x s a layout entry falseLayout trueBefore
 have kept:=UniformLocalRectanglePhaseBanks.execution_keeps_driver first
 have readyDriver:=driver.retained kept high.1
 have readySources:=sources_of_cursor j c q original D A dest FD FF FU FJ I H a binding readyDriver cursor retained
 have banks:=banks_of_outputs hn j c q original D A dest FD FF FU FJ B a binding layout ha he row generated yes no sources
  (constants_of_operands operands)
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed phase_code
  (by rw [UniformLocalRectanglePhaseBanks.program_length];omega) (by omega) first
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedFirst
 let start:=setPC a 0
 have bounds:=changePC_bound B a 0 first.final_bound (by omega)
 have startSources:UniformLocalCacheContextMachine.Sources c I start:=
  ⟨readySources.registers,readySources.radix,readySources.time,readySources.kind⟩
 have startBanks:UniformLocalCacheContextConductor.Banks c q ha he (coefficientBank j q original c) start:=by
  refine ⟨banks.rectangle,banks.generated.transport (fun _ _=>rfl),banks.enabled,banks.disabled,?_,banks.constants⟩
  exact UniformConjugatePackedMatchingPreparation.sources_transport banks.sources rfl
 obtain ⟨last,nt,second,cost,lp,cached,lout,lroots,low,ss,prior,control,suffix⟩:=
  UniformLocalCacheContextConductor.PriorRetention.execution c q ha he I (coefficientBank j q original c) geometry H workspaces x start
   startSources startBanks (by omega) total scalar natural rfl bounds
 obtain ⟨prefixFrame,scalarPrefix,natPrefix⟩:=
  UniformLocalCacheContextConductor.prefix_frame c prefixPlacement second low ss lout lroots
 have startFrame:UniformSeedRankCrossPreparation.PreservedFrame n a start:=
  ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
 have finalConjugate:=UniformLocalRectangleCoefficientMachine.conjugate_retained
  (UniformLocalRectangleCoefficientMachine.conjugate_retained
   (s:=a) (u:=start) conjugate (fun _ _=>rfl) (fun _ _=>rfl))
  scalarPrefix natPrefix
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed cache_code
  (by rw [UniformLocalCacheContextConductor.program_length];omega) (by omega) second
 have eq:placed 2308 start=setPC a 2308:=by cases a;rfl
 rw [eq] at placedSecond
 let u:=setPC last 3689
 have finishFrame:UniformSeedRankCrossPreparation.PreservedFrame n last u:=
  ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
 have finalConjugate:=UniformLocalRectangleCoefficientMachine.conjugate_retained
  (s:=last) (u:=u) finalConjugate (fun _ _=>rfl) (fun _ _=>rfl)
 have stop:BoundedExecution program n x B u 1 u:=.halt placedSecond.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,t+nt+1,?_,by omega,rfl,?_,lout.trans out,lroots.trans roots,?_,?_,control.withPC 3689,
  finishFrame.retained (prefixFrame.retained (startFrame.retained retained)),finalConjugate,
  finishFrame.protected.metadata (prefixFrame.protected.metadata (startFrame.protected.metadata metadata)),
  finishFrame.protected.operands (prefixFrame.protected.operands (startFrame.protected.operands operands)),?_,?_,?_⟩
 · simpa only [Nat.add_assoc] using placedFirst.executes (placedSecond.executes stop)
 · intro k hk;exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 · intro i hi outside hm hb;exact (ss i outside hm hb).trans (high.2 i hi)
 · intro i hi before;exact (prior i hi before).trans (high.1 i hi)
 · intro r lo hi
   exact (UniformLocalCacheContextConductor.execution_nat second r (Or.inr ⟨lo,hi⟩)).trans (kept r (by omega))
 · intro r hr
   exact (UniformLocalCacheContextConductor.execution_nat_high second r hr).trans (kept r (by omega))
 · intro i hi afterCache;exact (suffix i hi afterCache).trans (high.1 i hi)

end
end ExactFourierCircuits.UniformLocalRectangleCachePreparation.PriorRetention
