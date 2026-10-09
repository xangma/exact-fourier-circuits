import UniformLocalDisabledHeightMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectanglePhaseBanks
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
namespace R
abbrev program := UniformLocalRectangleReplayPreparation.program
end R
namespace H
abbrev program := UniformLocalDisabledHeightMachine.program
end H

/-- The real original/conjugate coefficient producer, six-phase control
printer, and second disabled-input height printer form one literal machine. -/
def program : Program := R.program.map (relocate 0 2114)++
 H.program.map (relocate 2114 2307)++[.halt]
lemma program_length : program.length=2308 := by
 simp only [program,List.length_append,List.length_map,
  UniformLocalRectangleReplayPreparation.program_length,
  UniformLocalDisabledHeightMachine.program_length,List.length_singleton]
attribute [local irreducible] UniformLocalRectangleReplayPreparation.program
 UniformLocalDisabledHeightMachine.program
lemma replay_code : CodeAt R.program program 0 2114 := by
 let rest:=H.program.map (relocate 2114 2307)++[.halt]
 have eq:program=[]++R.program.map (relocate 0 2114)++rest:=by
  simp only [program,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] rest _ 0 2114 rfl
lemma disabled_code : CodeAt H.program program 2114 2307 :=
 UniformRankCrossPreparationMachine.segment_code (R.program.map (relocate 0 2114)) [.halt] _ 2114 2307 (by
  simp only [List.length_map,UniformLocalRectangleReplayPreparation.program_length])
lemma halt_at : program[2307]?=some .halt := by
 let before:=R.program.map (relocate 0 2114)++H.program.map (relocate 2114 2307)
 have len:before.length=2307:=by
  simp only [before,List.length_append,List.length_map,
   UniformLocalRectangleReplayPreparation.program_length,UniformLocalDisabledHeightMachine.program_length]
 change (before++[.halt])[2307]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

open UniformNewtonTableMachine (KeepsNat)
lemma coefficient_keeps (q:ℕ) (lo:4232 ≤ q) :
 ∀i∈UniformLocalRectangleCoefficientMachine.program,KeepsNat q i := by
 intro i hi
 simp only [UniformLocalRectangleCoefficientMachine.program,List.mem_append,List.mem_map,List.mem_singleton] at hi
 rcases hi with ((⟨i,hi,rfl⟩|⟨o,ho,rfl⟩)|⟨i,hi,rfl⟩)|rfl
 · exact UniformLocalRectangleReplayPreparation.relocate_keeps _ _
    (UniformLocalRectangleCoefficientMachine.original_keeps q (by omega) (by
     simp only [List.mem_cons,List.not_mem_nil,or_false];omega) i hi)
 · simp only [UniformLocalRectangleCoefficientMachine.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,KeepsNat];omega
 · exact UniformLocalRectangleReplayPreparation.relocate_keeps _ _
    (UniformConjugatePackedMatchingPreparation.spectrum_keeps q (Or.inr (by omega)) i hi)
 · trivial
lemma slot_keeps (q:ℕ) (lo:4232 ≤ q) :
 ∀i∈UniformLocalReplayAssembly.program,KeepsNat q i := by
 intro i hi
 simp only [UniformLocalReplayAssembly.program,List.mem_append,List.mem_map,List.mem_flatMap,List.mem_singleton] at hi
 rcases hi with (⟨o,ho,rfl⟩|⟨j,_,i,hi,rfl⟩)|rfl
 · simp only [UniformLocalReplayAssembly.boot,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,KeepsNat];omega
 · apply UniformLocalRectangleReplayPreparation.relocate_keeps
   simp only [UniformLocalReplayAssembly.piece,List.mem_append,List.mem_map] at hi
   rcases hi with (⟨o,ho,rfl⟩|⟨i,hi,rfl⟩)|⟨o,ho,rfl⟩
   · simp only [UniformLocalReplayAssembly.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
     rcases ho with rfl|rfl|rfl
     all_goals simp only [Op.code,KeepsNat];omega
   · exact UniformLocalRectangleReplayPreparation.relocate_keeps _ _
      (UniformLocalReplaySlotMachine.keeps_nat q (Or.inr (by omega)) i hi)
   · simp only [UniformLocalReplayAssembly.copy,List.mem_singleton] at ho
     subst o;simp only [Op.code,KeepsNat];omega
 · trivial
lemma replay_keeps (q:ℕ) (lo:4232 ≤ q) : ∀i∈R.program,KeepsNat q i := by
 intro i hi
 simp only [R.program,UniformLocalRectangleReplayPreparation.program,List.mem_append,List.mem_map,List.mem_singleton] at hi
 rcases hi with ((⟨i,hi,rfl⟩|⟨o,ho,rfl⟩)|⟨i,hi,rfl⟩)|rfl
 · exact UniformLocalRectangleReplayPreparation.relocate_keeps _ _ (coefficient_keeps q lo i hi)
 · simp only [UniformLocalRectangleReplayPreparation.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl
   all_goals simp only [Op.code,KeepsNat];omega
 · exact UniformLocalRectangleReplayPreparation.relocate_keeps _ _ (slot_keeps q lo i hi)
 · trivial

noncomputable section
abbrev actual (q:Row) (c:UniformSeedHeightPreparation.Config) := UniformLocalRectangleBankMachine.geometry q c
abbrev nextParameters := UniformLocalRectangleCoefficientMachine.nextParameters

/-- Genuine entry to the preceding2114 producer. All stored rows, seed banks,
metadata, and operand values are physical; the other fields are ordinary
address/disjointness/word envelopes. No generated height bank is supplied. -/
structure Entry {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:UniformRankCrossPreparationMachine.Parameters)
 (dest A B:ℕ) (x:Fin n→ℂ) (s:State)
 (layout:UniformSeedHeightPreparation.Layout n j (actual q original) B) : Prop where
 args : UniformLocalRectangleBankMachine.Args j D original s
 nextArgs : UniformLocalRectangleCoefficientMachine.NextArgs work dest s
 slotAddress : s.natReg 4230=A
 source : UniformLocalRectangleBankMachine.RowSource D q s
 metadata : UniformPermutationInversePreparation.Metadata n s
 retained : Retained n (axisCount n) s
 conjugate : UniformAllAxisConjugatePreparation.Retained n (axisCount n) s
 operands : UniformInitialPreparation.Operands n x s
 fresh : UniformLocalRectangleCoefficientMachine.PrefixFresh n (actual q original)
 rowBefore : ∀base∈[(actual q original).d,(actual q original).conv,(actual q original).tape,
  (actual q original).depth,(actual q original).order,(actual q original).directory,(actual q original).rows,
  (actual q original).colors,(actual q original).palette,(actual q original).heightDirectory],D+7 ≤ base
 allocation : UniformConjugateRankSpectrumPreparation.Allocation n j (nextParameters n j q original work) dest B
 nativeBefore : ∀base∈[work.d,work.conv,work.tape,work.depth],
  UniformCrossHeightPreparationMachine.recordBase (actual q original).height (8*(actual q original).exponent+7) ≤ base
 positiveBefore : (actual q original).C+7*(actual q original).width+1 ≤ work.S
 negativeBefore : (actual q original).negative+7*(actual q original).width ≤ work.S
 constantsBefore : (actual q original).constants+6 ≤ work.S
 slotsFresh : UniformCrossHeightPreparationMachine.recordBase (actual q original).height (8*(actual q original).exponent+7) ≤ A
 originalDirectory : directoryBase n+2*axisCount n ≤ A
 conjugateDirectory : UniformConjugateRankSpectrumPreparation.dirEnd n ≤ A
 slotHeight : 8*(actual q original).exponent+7 ≤ B
 slotEnvelope : A+55*UniformLocalReplayAssembly.phasePrefix (8*(actual q original).exponent+6) 6 ≤ B
 rowBound : D+6 ≤ B

def runtimeBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row) (original:UniformSeedHeightPreparation.Config)
 (work:UniformRankCrossPreparationMachine.Parameters) :=
 UniformLocalRectangleCoefficientMachine.runtimeBudget n j q original work+
 247*UniformLocalReplayAssembly.phasePrefix (8*(actual q original).exponent+6) 6+113+
 (4*(actual q original).exponent+34+(8*(actual q original).exponent+7)*
  (64*(actual q original).gates+200*(2*(actual q original).gates+1)^2+56))+1

/-- This continuous2308 program derives both enabled and disabled physical
depth/color banks and all six control phases. It does not execute the shears. -/
theorem execution {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:UniformRankCrossPreparationMachine.Parameters)
 (dest A FD FF FU FJ B:ℕ) (x:Fin n→ℂ) (s:State)
 (layout:UniformSeedHeightPreparation.Layout n j (actual q original) B)
 (entry:Entry hn j D q original work dest A B x s layout)
 (falseArgs:UniformLocalDisabledHeightMachine.Args FD FF FU FJ s)
 (falseLayout:UniformCrossHeightPreparationMachine.Layout
  (UniformLocalDisabledHeightMachine.disabled (actual q original).height FD FF FU FJ))
 (falseBudget:UniformCrossHeightPreparationMachine.wordBudget
  (UniformLocalDisabledHeightMachine.disabled (actual q original).height FD FF FU FJ) ≤ B)
 (trueBefore:UniformCrossHeightPreparationMachine.recordBase (actual q original).height
  (8*(actual q original).exponent+7) ≤ FD)
 (slotsBefore:A+55*UniformLocalReplayAssembly.phasePrefix (8*(actual q original).exponent+6) 6 ≤ FD)
 (code:2308 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ runtimeBudget n j q original work ∧ u.pc=2307 ∧
 UniformLocalReplayAssembly.Generated (actual q original).exponent A 6 u ∧
 UniformCrossHeightPreparationMachine.Source (actual q original).height
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j (actual q original))
   (layout.replay hn j (actual q original) B)).program u ∧
 UniformCrossHeightPreparationMachine.Processed (actual q original).height (actual q original).negative
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j (actual q original))
   (layout.replay hn j (actual q original) B)).program (8*(actual q original).exponent+7) u ∧
 UniformCrossHeightPreparationMachine.Cursor
  (UniformLocalDisabledHeightMachine.disabled (actual q original).height FD FF FU FJ)
  (8*(actual q original).exponent+7) u ∧
 UniformCrossHeightPreparationMachine.Processed
  (UniformLocalDisabledHeightMachine.disabled (actual q original).height FD FF FU FJ) (actual q original).negative
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j (actual q original))
   (layout.replay hn j (actual q original) B)).program (8*(actual q original).exponent+7) u ∧
 UniformMatchingConjugateLoadMachine.Sources (actual q original).exponent (actual q original).C
  (actual q original).negative (actual q original).constants dest
  (fun i:Fin (7*(actual q original).width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j (actual q original))
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) u ∧
 Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let c:=actual q original
 obtain ⟨v,t,first,bound,vp,generated,height,sources,vr,vc,vm,vo,out,roots⟩:=
  UniformLocalRectangleReplayPreparation.execution hn j D q original work dest A B x s
   entry.args entry.nextArgs entry.slotAddress entry.source entry.metadata entry.retained entry.conjugate
   entry.operands layout entry.fresh entry.rowBefore entry.allocation entry.nativeBefore
   entry.positiveBefore entry.negativeBefore entry.constantsBefore entry.slotsFresh
   entry.originalDirectory entry.conjugateDirectory entry.slotHeight entry.slotEnvelope entry.rowBound
   (by omega) pc hs
 have fargs:UniformLocalDisabledHeightMachine.Args FD FF FU FJ v:=by
  constructor
  all_goals first
  | exact (UniformNewtonTableMachine.Executes.keeps_nat first.executes (replay_keeps _ (by omega))).trans falseArgs.rows
  | exact (UniformNewtonTableMachine.Executes.keeps_nat first.executes (replay_keeps _ (by omega))).trans falseArgs.colors
  | exact (UniformNewtonTableMachine.Executes.keeps_nat first.executes (replay_keeps _ (by omega))).trans falseArgs.palette
  | exact (UniformNewtonTableMachine.Executes.keeps_nat first.executes (replay_keeps _ (by omega))).trans falseArgs.directory
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed replay_code
  (by rw [UniformLocalRectangleReplayPreparation.program_length];omega) (by omega) first
 have zero:placed 0 s=s:=by cases s;simp [placed]
 rw [zero] at placedFirst
 let start:=setPC v 0
 have hb:=changePC_bound B v 0 first.final_bound (by omega)
 let pl:=layout.replay hn j c B
 have ha:c.height.a ≤ UniformCrossHeightPreparationMachine.widthOf c.height:=pl.original.1.widthA
 have he:c.height.e ≤ UniformCrossHeightPreparationMachine.widthOf c.height:=pl.original.1.widthE
 have src:UniformCrossHeightPreparationMachine.Source c.height
  (UniformToeplitzCrossDAG.crossDAG c.height.K c.height.a c.height.e ha he).program start:=height.source.withPC
 have done:UniformCrossHeightPreparationMachine.Processed c.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.height.K c.height.a c.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.height) start:=height.processed
 obtain ⟨last,nt,second,cheap,lp,cursor,sourceFinal,trueFinal,falseFinal,heap,scalar,scalarRegs,outputs,rootOrders,saved⟩:=
  UniformLocalDisabledHeightMachine.execution c.height FD FF FU FJ c.negative B n ha he x start
   (height.cursor.header.withPC _) (show UniformLocalDisabledHeightMachine.Args FD FF FU FJ start from ⟨fargs.rows,fargs.colors,fargs.palette,fargs.directory⟩) src done layout.heightLayout falseLayout trueBefore falseBudget
   (by omega) rfl hb
 have call:=UniformBoundedAssembly.boundedExecution_placed disabled_code
  (by rw [UniformLocalDisabledHeightMachine.program_length];omega) (by omega) second
 have callStart:placed 2114 start=setPC v 2114:=by cases v;rfl
 rw [callStart] at call
 let u:=setPC last 2307
 have stop:BoundedExecution program n x B u 1 u:=.halt call.final_bound (by simp [step,u,setPC,halt_at])
 have finalGenerated:UniformLocalReplayAssembly.Generated c.exponent A 6 u:=
  generated.transport (fun i hi=>heap i (lt_of_lt_of_le hi slotsBefore))
 have prefixFrame:UniformSeedRankCrossPreparation.PreservedFrame n v u:=by
  refine ⟨fun i hi=>heap i (by have h:=entry.originalDirectory;omega),
   fun i _=>congrFun scalar i,fun i lo hi=>saved i lo hi,outputs,rootOrders⟩
 have finalConjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=
  UniformLocalRectangleCoefficientMachine.conjugate_retained vc
   (fun i _=>congrFun scalar i)
   (fun i hi=>heap i (by have h:=entry.conjugateDirectory;omega))
 have finalSources:UniformMatchingConjugateLoadMachine.Sources c.exponent c.C c.negative c.constants dest
  (fun i:Fin (7*c.width)=>UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j c)
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val) u:=
  UniformConjugatePackedMatchingPreparation.sources_transport sources scalar
 refine ⟨u,t+nt+1,?_,?_,rfl,finalGenerated,sourceFinal.withPC,trueFinal,cursor.withPC,
  falseFinal,finalSources,prefixFrame.retained vr,finalConjugate,prefixFrame.protected.metadata vm,
  prefixFrame.protected.operands vo,outputs.trans out,rootOrders.trans roots⟩
 · simpa only [Nat.add_assoc] using placedFirst.executes (call.executes stop)
 · change t ≤ UniformLocalRectangleCoefficientMachine.runtimeBudget n j q original work+
    247*UniformLocalReplayAssembly.phasePrefix (8*(actual q original).exponent+6) 6+113 at bound
   dsimp only [runtimeBudget]
   change nt ≤ 4*(actual q original).exponent+34+(8*(actual q original).exponent+7)*
    (64*(actual q original).gates+200*(2*(actual q original).gates+1)^2+56) at cheap
   omega

end
end ExactFourierCircuits.UniformLocalRectanglePhaseBanks
