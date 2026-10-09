import UniformLocalRectangleCoefficientMachine
import UniformLocalReplayAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleReplayPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
namespace C
abbrev program := UniformLocalRectangleCoefficientMachine.program
abbrev nextParameters := UniformLocalRectangleCoefficientMachine.nextParameters
end C
namespace R
abbrev program := UniformLocalReplayAssembly.program
end R

def setup : List Op := [.literal 4231 0,.add 4205 1050 4231,.add 4206 4230 4231]
lemma setup_length : setup.length=3 := rfl
/-- Original/conjugate physical preparation, followed by the literal six-phase
slot printer. The height is copied from the producer, never supplied. -/
def program : Program := C.program.map (relocate 0 1851)++setup.map Op.code++
 R.program.map (relocate 1854 2113)++[.halt]
lemma program_length : program.length=2114 := by
 simp only [program,List.length_append,List.length_map,
  UniformLocalRectangleCoefficientMachine.program_length,setup_length,
  UniformLocalReplayAssembly.program_length,List.length_singleton]
attribute [local irreducible] UniformLocalRectangleCoefficientMachine.program UniformLocalReplayAssembly.program
lemma coefficient_code : CodeAt C.program program 0 1851 := by
 let rest:=setup.map Op.code++R.program.map (relocate 1854 2113)++[.halt]
 have eq:program=[]++C.program.map (relocate 0 1851)++rest:=by
  simp only [program,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] rest _ 0 1851 rfl
lemma setup_code : BlockAt setup program 1851 := by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment
  (C.program.map (relocate 0 1851)) (setup.map Op.code)
  (R.program.map (relocate 1854 2113)++[.halt]) i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_map,UniformLocalRectangleCoefficientMachine.program_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using lookup
lemma replay_code : CodeAt R.program program 1854 2113 := by
 let before:=C.program.map (relocate 0 1851)++setup.map Op.code
 have eq:program=before++R.program.map (relocate 1854 2113)++[.halt]:=by
  simp only [program,before,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before [.halt] _ 1854 2113 (by
  simp only [before,List.length_append,List.length_map,UniformLocalRectangleCoefficientMachine.program_length,setup_length])
lemma halt_at : program[2113]?=some .halt := by
 let before:=C.program.map (relocate 0 1851)++setup.map Op.code++R.program.map (relocate 1854 2113)
 have len:before.length=2113:=by
  simp only [before,List.length_append,List.length_map,UniformLocalRectangleCoefficientMachine.program_length,
   setup_length,UniformLocalReplayAssembly.program_length]
 change (before++[.halt])[2113]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

open UniformNewtonTableMachine (KeepsNat)
lemma relocate_keeps {q:ℕ} {i:Instruction} (b r:ℕ) (h:KeepsNat q i) : KeepsNat q (relocate b r i) := by
 cases i <;>exact h
lemma coefficient_keeps_slot : ∀i∈C.program,KeepsNat 4230 i := by
 intro i hi
 simp only [C.program,UniformLocalRectangleCoefficientMachine.program,List.mem_append,List.mem_map,List.mem_singleton] at hi
 rcases hi with ((⟨i,hi,rfl⟩|⟨o,ho,rfl⟩)|⟨i,hi,rfl⟩)|rfl
 · exact relocate_keeps _ _ (UniformLocalRectangleCoefficientMachine.original_keeps 4230 (by omega) (by simp) i hi)
 · simp only [UniformLocalRectangleCoefficientMachine.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp [Op.code,KeepsNat]
 · exact relocate_keeps _ _ (UniformConjugatePackedMatchingPreparation.spectrum_keeps 4230 (Or.inr (by omega)) i hi)
 · trivial
lemma replay_keeps (q:ℕ) (lo:q<4200) : ∀i∈R.program,KeepsNat q i := by
 intro i hi
 simp only [R.program,UniformLocalReplayAssembly.program,List.mem_append,List.mem_map,
  List.mem_flatMap,List.mem_singleton] at hi
 rcases hi with (⟨o,ho,rfl⟩|⟨j,_,i,hi,rfl⟩)|rfl
 · simp only [UniformLocalReplayAssembly.boot,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,KeepsNat];omega
 · apply relocate_keeps
   simp only [UniformLocalReplayAssembly.piece,List.mem_append,List.mem_map] at hi
   rcases hi with (⟨o,ho,rfl⟩|⟨ins,hin,rfl⟩)|⟨o,ho,rfl⟩
   · simp only [UniformLocalReplayAssembly.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
     rcases ho with rfl|rfl|rfl
     all_goals simp only [Op.code,KeepsNat];omega
   · exact relocate_keeps _ _ (UniformLocalReplaySlotMachine.keeps_nat q (Or.inl (by omega)) ins hin)
   · simp only [UniformLocalReplayAssembly.copy,List.mem_singleton] at ho
     subst o
     simp only [Op.code,KeepsNat];omega
 · trivial

noncomputable section
lemma setup_safe {B:ℕ} (s:State) (hs:WordBound B s) : readable setup s ∧ peak setup s ≤ B := by
 constructor
 · simp [setup,readable,Op.readable]
 · simp only [setup,peak,Op.peak,Op.apply,writeNat,next];simp
   exact ⟨hs.2.1 1050,hs.2.1 4230⟩
lemma setup_headers {K A:ℕ} (s:State) (hk:s.natReg 1050=K) (ha:s.natReg 4230=A) :
 (applyBlock setup s).natReg 4205=K ∧ (applyBlock setup s).natReg 4206=A := by
 simp [setup,applyBlock,Op.apply,writeNat,next,hk,ha]
lemma setup_frame {n:ℕ} (s:State) : UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock setup s) := by
 refine ⟨fun _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
 intro q lo hi
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_result {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedHeightPreparation.Config} {B:ℕ}
 {layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedHeightPreparation.parameters n j c) B}
 {s:State} (old:UniformSeedHeightPreparation.Result n j c B layout s) :
 UniformSeedHeightPreparation.Result n j c B layout (applyBlock setup s) := by
 have eq:∀q,1050 ≤ q → q ≤ 1079 → (applyBlock setup s).natReg q=s.natReg q:=by
  intro q lo hi;simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
 refine ⟨?_,old.cursor.transport_register eq,?_,?_,?_,?_,?_⟩
 · refine ⟨old.source.bank,old.source.directory,old.source.tape⟩
 · exact old.processed
 · exact old.positive
 · exact old.root
 · exact old.negative
 · exact old.constants

lemma result_replay {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (c:UniformSeedHeightPreparation.Config)
 (B A t:ℕ) (x:Fin n→ℂ) (s u:State) (layout:UniformSeedHeightPreparation.Layout n j c B)
 (old:UniformSeedHeightPreparation.Result n j c B (layout.replay hn j c B) s)
 (run:BoundedExecution R.program n x B s t u)
 (outside:UniformLocalReplayAssembly.Outside A c.exponent s u)
 (native:UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7) ≤ A) :
 UniformSeedHeightPreparation.Result n j c B (layout.replay hn j c B) u := by
 have scal:=UniformLocalReplayAssembly.execution_scalarFrame run
 have reg:∀q,1050 ≤ q → q ≤ 1079 → u.natReg q=s.natReg q:=by
  intro q lo hi
  exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (replay_keeps q (by omega))
 have nat:∀q,q<UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7) → u.natHeap q=s.natHeap q:=by
  intro q hq;exact outside q (Or.inl (lt_of_lt_of_le hq native))
 have gEq:(UniformRankCrossReplayPreparationMachine.cross
  (UniformSeedHeightPreparation.parameters n j c) (layout.replay hn j c B)).size=
  UniformCrossHeightPreparationMachine.gates c.height:=UniformRankCrossReplayPreparationMachine.cross_shape _ _
 have rowBefore:c.rows ≤ UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7):=by
  have hr:=layout.heightLayout.rows;have hc:=layout.heightLayout.colors;have hp:=layout.heightLayout.palette
  change c.rows+6*c.gates*(8*c.exponent+7) ≤ c.colors at hr
  change c.colors+2*c.gates*(8*c.exponent+7) ≤ c.palette at hc
  change c.palette+12 ≤ c.heightDirectory at hp
  change c.rows ≤ c.heightDirectory+3*(8*c.exponent+7)
  omega
 refine ⟨old.source.transport gEq layout.heightLayout (fun q hq=>nat q (lt_of_lt_of_le hq rowBefore)),
  old.cursor.transport_register reg,
  UniformLocalRectangleCoefficientMachine.processed_prefix c.height c.negative _ old.processed gEq layout.heightLayout nat,
  ?_,?_,?_,?_⟩
 · intro i;exact (congrFun scal.1 _).trans (old.positive i)
 · exact (congrFun scal.1 _).trans old.root
 · intro i hi;exact (congrFun scal.1 _).trans (old.negative i hi)
 · intro i hi;exact (congrFun scal.1 _).trans (old.constants i hi)

/-- Every six-phase control record is physically emitted after the real
coefficient producers; the later cache consumer receives no host phase list. -/
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
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let c:=UniformLocalRectangleBankMachine.geometry q original
 obtain ⟨v,t,first,bound,vp,new,height,sources,vr,vc,vm,vo,out,roots⟩:=
  UniformLocalRectangleCoefficientMachine.execution hn j D q original work dest B x s args nextArgs source
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
  finalSources,full.retained vr,finalConjugate,full.protected.metadata vm,full.protected.operands vo,?_,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using placedFirst.executes (install.executes (call.executes stop))
 · exact full.2.2.2.1.trans out
 · exact full.2.2.2.2.trans roots

end
end ExactFourierCircuits.UniformLocalRectangleReplayPreparation
