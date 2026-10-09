import UniformLocalRectangleCacheBindings
import UniformLocalRectanglePhaseRetention
import UniformCacheRetentionBounds

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleCachePreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotConductorMachine UniformLocalRectangleCacheBindings
namespace P
abbrev program:=UniformLocalRectanglePhaseBanks.program
abbrev actual:=UniformLocalRectanglePhaseBanks.actual
end P
namespace C
abbrev program:=UniformLocalCacheContextConductor.program
end C

def program:Program:=P.program.map (relocate 0 2308)++C.program.map (relocate 2308 3689)++[.halt]
lemma program_length:program.length=3690:=by
 simp only [program,List.length_append,List.length_map,
  UniformLocalRectanglePhaseBanks.program_length,UniformLocalCacheContextConductor.program_length,List.length_singleton]
attribute [local irreducible] UniformLocalRectanglePhaseBanks.program UniformLocalCacheContextConductor.program
lemma phase_code:CodeAt P.program program 0 2308:=by
 have eq:program=[]++P.program.map (relocate 0 2308)++(C.program.map (relocate 2308 3689)++[.halt]):=by
  simp only [program,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code [] _ _ 0 2308 rfl
lemma cache_code:CodeAt C.program program 2308 3689:=
 UniformChunkRowTableMachine.segment_code (P.program.map (relocate 0 2308)) [.halt] _ 2308 3689
  (by simp only [List.length_map,UniformLocalRectanglePhaseBanks.program_length])
lemma halt_at:program[3689]?=some .halt:=by
 let before:=P.program.map (relocate 0 2308)++C.program.map (relocate 2308 3689)
 have len:before.length=3689:=by simp only [before,List.length_append,List.length_map,
  UniformLocalRectanglePhaseBanks.program_length,UniformLocalCacheContextConductor.program_length]
 change (before++[.halt])[3689]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

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
 (code:3690 ≤ B)(total:352*c.height.K+330 ≤ B)(scalar:9*c.ambient ≤ B)
 (natural:3*c.ambient+11 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ UniformLocalRectanglePhaseBanks.runtimeBudget n j q original work+
  (352*c.height.K+330)*(bodyBudget c q+11)+62 ∧ u.pc=3689 ∧
 (∀k,k<352*c.height.K+330 → Cached (B:=B) c q ha he (coefficientBank j q original c) geometry.positive k u) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀i,H ≤ i → (i<c.pool ∨ c.pool+9*c.ambient*(352*c.height.K+330) ≤ i) →
  i≠c.mu → i≠c.conjugateMu → u.scalarHeap i=s.scalarHeap i):=by
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
 obtain ⟨last,nt,second,cost,lp,cached,lout,lroots,low,ss⟩:=
  UniformLocalCacheContextConductor.execution c q ha he I (coefficientBank j q original c) geometry x start
   startSources startBanks (by omega) total scalar natural rfl bounds
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed cache_code
  (by rw [UniformLocalCacheContextConductor.program_length];omega) (by omega) second
 have eq:placed 2308 start=setPC a 2308:=by cases a;rfl
 rw [eq] at placedSecond
 let u:=setPC last 3689
 have stop:BoundedExecution program n x B u 1 u:=.halt placedSecond.final_bound
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,t+nt+1,?_,by omega,rfl,?_,lout.trans out,lroots.trans roots,?_⟩
 · simpa only [Nat.add_assoc] using placedFirst.executes (placedSecond.executes stop)
 · intro k hk;exact (cached k hk).heaps (cache_shift geometry.cache k) rfl rfl
 · intro i hi outside hm hb;exact (ss i outside hm hb).trans (high.2 i hi)
end
end ExactFourierCircuits.UniformLocalRectangleCachePreparation
