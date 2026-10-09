import UniformLocalRectangleBankMachine
import UniformConjugatePackedMatchingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleCoefficientMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
namespace O
abbrev c := UniformLocalRectangleBankMachine.geometry
end O
namespace C
abbrev Parameters := UniformRankCrossPreparationMachine.Parameters
abbrev Allocation := UniformConjugateRankSpectrumPreparation.Allocation
end C

/-- The next arena addresses are ordinary caller integers. Geometry and the
FFT exponent are read from the actual stored row and preceding producer. -/
def setup : List Op := [.literal 4215 0,.literal 4216 1,.literal 4217 2,
 .add 1821 4200 4215,.add 1820 4214 4215,.add 525 1050 4215,
 .add 490 4207 4215,.add 527 4208 4215,.add 528 4209 4215,.add 529 4210 4215,
 .add 563 4211 4215,.add 564 4212 4215,.add 675 4213 4215,
 .add 4204 4201 4217,.getNat 484 4204,.add 4204 4204 4216,
 .getNat 485 4204,.add 4204 4204 4216,.getNat 488 4204,
 .add 4204 4204 4216,.getNat 486 4204,.add 4204 4204 4216,.getNat 487 4204]
lemma setup_length : setup.length=23 := rfl
def program : Program :=
 UniformLocalRectangleBankMachine.program.map (relocate 0 1064)++setup.map Op.code++
 UniformConjugateRankSpectrumPreparation.program.map (relocate 1087 1850)++[.halt]
lemma program_length : program.length=1851 := by
 simp only [program,List.length_append,List.length_map,
  UniformLocalRectangleBankMachine.program_length,setup_length,
  UniformConjugateRankSpectrumPreparation.program_length,List.length_singleton]

attribute [local irreducible] UniformLocalRectangleBankMachine.program
 UniformConjugateRankSpectrumPreparation.program
lemma original_code : CodeAt UniformLocalRectangleBankMachine.program program 0 1064 := by
 let rest:=setup.map Op.code++UniformConjugateRankSpectrumPreparation.program.map (relocate 1087 1850)++[.halt]
 have eq:program=[]++UniformLocalRectangleBankMachine.program.map (relocate 0 1064)++rest:=by
  simp only [program,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] rest _ 0 1064 rfl
lemma setup_code : BlockAt setup program 1064 := by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformLocalRectangleBankMachine.program.map (relocate 0 1064)) (setup.map Op.code)
  (UniformConjugateRankSpectrumPreparation.program.map (relocate 1087 1850)++[.halt]) i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_map,UniformLocalRectangleBankMachine.program_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using lookup
lemma conjugate_code : CodeAt UniformConjugateRankSpectrumPreparation.program program 1087 1850 := by
 let before:=UniformLocalRectangleBankMachine.program.map (relocate 0 1064)++setup.map Op.code
 have eq:program=before++UniformConjugateRankSpectrumPreparation.program.map (relocate 1087 1850)++[.halt]:=by
  simp only [program,before,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before [.halt] _ 1087 1850 (by
  simp only [before,List.length_append,List.length_map,UniformLocalRectangleBankMachine.program_length,setup_length])
lemma halt_at : program[1850]?=some .halt := by
 let before:=UniformLocalRectangleBankMachine.program.map (relocate 0 1064)++setup.map Op.code++
  UniformConjugateRankSpectrumPreparation.program.map (relocate 1087 1850)
 have len:before.length=1850:=by
  simp only [before,List.length_append,List.length_map,UniformLocalRectangleBankMachine.program_length,
   setup_length,UniformConjugateRankSpectrumPreparation.program_length]
 change (before++[.halt])[1850]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
def nextParameters (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:C.Parameters) : C.Parameters :=
 UniformConjugateRankSpectrumPreparation.relocated
  (UniformSeedHeightPreparation.parameters n j (O.c q original)).base work
def addressRegister (work:C.Parameters) (dest:ℕ) : ℕ → ℕ
 | 4207=>work.S | 4208=>work.A | 4209=>work.d | 4210=>work.C
 | 4211=>work.conv | 4212=>work.tape | 4213=>work.depth | _=>dest
def NextArgs (work:C.Parameters) (dest:ℕ) (s:State) : Prop :=
 ∀r,4207 ≤ r → r ≤ 4214 → s.natReg r=addressRegister work dest r

/-- All previously prepared compact banks and directories lie before these
ordinary fresh arenas. This states placement, never their output values. -/
structure PrefixFresh (n:ℕ) (c:UniformSeedHeightPreparation.Config) : Prop where
 scalar : ∀base∈[c.S,c.A,c.C,c.negative,c.constants],
  UniformConjugateRankSpectrumPreparation.seedEnd n ≤ base
 nat : ∀base∈[c.d,c.conv,c.tape,c.depth,c.order,c.directory,c.rows,c.colors,c.palette,c.heightDirectory],
  UniformConjugateRankSpectrumPreparation.dirEnd n ≤ base

lemma outside_prefix {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedHeightPreparation.Config} {s u:State}
 (fresh:PrefixFresh n c) (frame:UniformSeedEdgeRetention.Height.Outside n j c s u) :
 (∀i,i<UniformConjugateRankSpectrumPreparation.seedEnd n → u.scalarHeap i=s.scalarHeap i) ∧
 (∀i,i<UniformConjugateRankSpectrumPreparation.dirEnd n → u.natHeap i=s.natHeap i) := by
 constructor
 · intro i hi
   apply frame.2 i
   all_goals apply Or.inl
   all_goals apply lt_of_lt_of_le hi
   all_goals apply fresh.scalar; simp
 · intro i hi
   apply frame.1 i
   all_goals apply Or.inl
   all_goals apply lt_of_lt_of_le hi
   all_goals apply fresh.nat; simp

lemma conjugate_retained {n:ℕ} {s u:State}
 (old:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (scalar:∀i,i<UniformConjugateRankSpectrumPreparation.seedEnd n → u.scalarHeap i=s.scalarHeap i)
 (nat:∀i,i<UniformConjugateRankSpectrumPreparation.dirEnd n → u.natHeap i=s.natHeap i) :
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u := by
 refine ⟨?_,?_,?_⟩
 · intro k hk q l
   exact (scalar _ (UniformAllAxisConjugatePreparation.compact_address_before k hk q l)).trans (old.coefficients k hk q l)
 · intro k hk
   exact (nat _ (by have:=k.isLt;unfold UniformConjugateRankSpectrumPreparation.dirEnd UniformConjugateRankSpectrumPreparation.O.axisCount;omega)).trans (old.address k hk)
 · intro k hk
   exact (nat _ (by have:=k.isLt;unfold UniformConjugateRankSpectrumPreparation.dirEnd UniformConjugateRankSpectrumPreparation.O.axisCount;omega)).trans (old.width k hk)

lemma setup_keeps (s:State) (r:ℕ)
 (notWrite:r ∉ [4215,4216,4217,1821,1820,525,490,527,528,529,563,564,675,4204,484,485,488,486,487]) :
 (applyBlock setup s).natReg r=s.natReg r := by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 intro o ho
 simp only [setup,List.mem_cons,List.not_mem_nil,or_false] at ho
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at notWrite
 rcases notWrite with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18⟩
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp [UniformSeedRankCrossPreparation.KeepsRegister,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18]

lemma setup_spec {n:ℕ} (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:C.Parameters) (dest:ℕ) (s:State)
 (axis:s.natReg 4200=j.val) (address:s.natReg 4201=D)
 (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (exponent:s.natReg 1050=(O.c q original).exponent)
 (master:s.natReg 104=UniformMasterRootMachine.order n) (args:NextArgs work dest s) :
 UniformConjugateRankSpectrumPreparation.Arguments n j (nextParameters n j q original work) dest (applyBlock setup s) := by
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h4:s.natHeap (D+4)=some q.split:=by simpa [Row.words] using source ⟨4,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 have ha:=args 4207 (by omega) (by omega);have hA:=args 4208 (by omega) (by omega)
 have hd:=args 4209 (by omega) (by omega);have hC:=args 4210 (by omega) (by omega)
 have hc:=args 4211 (by omega) (by omega);have ht:=args 4212 (by omega) (by omega)
 have hl:=args 4213 (by omega) (by omega);have hv:=args 4214 (by omega) (by omega)
 refine ⟨?_,?_,?_⟩
 · simp [setup,applyBlock,Op.apply,writeNat,next,hv,addressRegister]
 · simp [setup,applyBlock,Op.apply,writeNat,next,axis]
 · intro r hr h0 h1 h7 h8
   simp only [UniformRankCrossPreparationMachine.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp_all [setup,applyBlock,Op.apply,writeNat,next,Nat.add_assoc,
    nextParameters,UniformConjugateRankSpectrumPreparation.relocated,
    UniformConjugateRankSpectrumPreparation.selected,UniformRankCrossPreparationMachine.Parameters.register,
    O.c,UniformLocalRectangleBankMachine.geometry,UniformSeedHeightPreparation.parameters,
    UniformSeedRankCrossPreparation.parameters,UniformSeedHeightPreparation.Config.seed,
    UniformSeedHeightPreparation.Config.exponent,addressRegister]

lemma setup_safe {D B:ℕ} {q:Row} (s:State)
 (address:s.natReg 4201=D) (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (hs:WordBound B s) (rowBound:D+6 ≤ B) (_two:2 ≤ B) :
 readable setup s ∧ peak setup s ≤ B := by
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h4:s.natHeap (D+4)=some q.split:=by simpa [Row.words] using source ⟨4,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 have b2:=(hs.2.2.1 _ _ h2).2;have b3:=(hs.2.2.1 _ _ h3).2
 have b4:=(hs.2.2.1 _ _ h4).2;have b5:=(hs.2.2.1 _ _ h5).2
 have b6:=(hs.2.2.1 _ _ h6).2
 have bounds:∀r,s.natReg r ≤ B:=hs.2.1
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,address,
  Nat.add_assoc,h2,h3,h4,h5,h6]
 repeat' apply And.intro
 all_goals first | omega | exact bounds _

lemma original_keeps (r:ℕ) (lo:1230 ≤ r) (keep:r ∉ [4202,4203,4204,4205,4206]) :
 ∀ins∈UniformLocalRectangleBankMachine.program,UniformNewtonTableMachine.KeepsNat r ins := by
 intro ins hi
 simp only [UniformLocalRectangleBankMachine.program,List.mem_append,List.mem_map,List.mem_singleton] at hi
 rcases hi with (⟨o,ho,rfl⟩|⟨i,hi,rfl⟩)|rfl
 · simp only [UniformLocalRectangleBankMachine.install,List.mem_cons,List.not_mem_nil,or_false] at ho
   simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at keep
   rcases keep with ⟨h0,h1,h2,h3,h4⟩
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,UniformNewtonTableMachine.KeepsNat]
   all_goals omega
 · have k:=UniformSeedChunkPreparation.ceiling_keeps r lo i hi
   cases i <;>exact k
 · trivial

lemma cursor_setup {c:UniformCrossHeightPreparationMachine.Parameters} {d:ℕ} {s:State}
 (h:UniformCrossHeightPreparationMachine.Cursor c d s) :
 UniformCrossHeightPreparationMachine.Cursor c d (applyBlock setup s) := by
 rcases h with ⟨⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩,
  ⟨h13,h14,h15,h16,h17,h18,h19⟩,h20,h21,h22,h23,h24,h25,h26,h27,h28⟩
 constructor
 · constructor <;>rw [setup_keeps s _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)]
   all_goals assumption
 · constructor <;>rw [setup_keeps s _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)]
   all_goals assumption
 all_goals rw [setup_keeps s _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)]
 all_goals assumption

lemma result_setup {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedHeightPreparation.Config} {B:ℕ}
 {layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedHeightPreparation.parameters n j c) B}
 {s:State} (orig:UniformSeedHeightPreparation.Result n j c B layout s) :
 UniformSeedHeightPreparation.Result n j c B layout (applyBlock setup s) := by
 have nh:(applyBlock setup s).natHeap=s.natHeap:=by
  simp only [setup,applyBlock,Op.apply,writeNat,next]
 have sh:(applyBlock setup s).scalarHeap=s.scalarHeap:=by
  simp only [setup,applyBlock,Op.apply,writeNat,next]
 refine ⟨⟨?_,?_,?_⟩,cursor_setup orig.cursor,?_,?_,?_,?_,?_⟩
 · simpa only [UniformDAGBucketMachine.Bank,nh] using orig.source.bank
 · simpa only [UniformDAGBucketMachine.Directory,nh] using orig.source.directory
 · simpa only [UniformToeplitzCrossTopologyMachine.RowTable,nh] using orig.source.tape
 · simpa only [UniformCrossHeightPreparationMachine.Processed,UniformCrossHeightPreparationMachine.Slice,
   UniformCrossShearTableMachine.Table,UniformCrossHeightPreparationMachine.Record,nh] using orig.processed
 · simpa only [UniformKernelSpectrumMachine.Result,sh] using orig.positive
 · simpa only [sh] using orig.root
 · simpa only [UniformReplayCoefficientMachine.NegativeBank,sh] using orig.negative
 · simpa only [UniformReplayCoefficientMachine.Constants,sh] using orig.constants

lemma result_withPC {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedHeightPreparation.Config} {B pc:ℕ}
 {layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedHeightPreparation.parameters n j c) B}
 {s:State} (orig:UniformSeedHeightPreparation.Result n j c B layout s) :
 UniformSeedHeightPreparation.Result n j c B layout (setPC s pc) :=
 ⟨orig.source.withPC,orig.cursor.withPC,orig.processed,orig.positive,orig.root,orig.negative,orig.constants⟩

lemma setup_frame {n:ℕ} (s:State) :
 UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock setup s) := by
 refine ⟨fun _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
 intro r lo hi
 exact setup_keeps s r (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)

def installedState (s:State) : State := applyBlock setup s
lemma installedState_eq (s:State) : installedState s=applyBlock setup s := rfl
attribute [irreducible] installedState

lemma row_source_retained {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedHeightPreparation.Config} {D:ℕ} {q:Row} {s u:State}
 (source:UniformLocalRectangleBankMachine.RowSource D q s)
 (before:∀base∈[c.d,c.conv,c.tape,c.depth,c.order,c.directory,c.rows,c.colors,c.palette,c.heightDirectory],D+7 ≤ base)
 (frame:UniformSeedEdgeRetention.Height.Outside n j c s u) :
 UniformLocalRectangleBankMachine.RowSource D q u := by
 intro f
 apply Eq.trans _ (source f)
 apply frame.1
 all_goals apply Or.inl
 all_goals apply lt_of_lt_of_le (show D+f.val<D+7 by have:=f.isLt;omega)
 all_goals apply before; simp


open UniformCrossHeightPreparationMachine in
lemma processed_prefix {G:ℕ} (v:Parameters) (Z:ℕ)
 (p:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize v.K) v.e G) {s u:State}
 (old:Processed v Z p (height v) s) (hG:G=gates v) (layout:Layout v)
 (heap:∀i,i<recordBase v (height v) → u.natHeap i=s.natHeap i) :
 Processed v Z p (height v) u := by
 intro d hd
 rcases old d hd with ⟨table,colors,record⟩
 let W:=UniformCrossDepthReplayPreparation.bucket p v.enabled d
 have len:W.length ≤ 2*gates v:=by
  have h:=bucket_length p v.enabled d
  exact h.trans (Nat.mul_le_mul_left 2 hG.le)
 have rowEnd:= (rowBase_mono v (show d+1 ≤ height v by omega)).trans layout.rows
 have colorEnd:=(colorBase_mono v (show d+1 ≤ height v by omega)).trans layout.colors
 have colorsBefore:v.F ≤ v.U:=by
  have :=layout.colors
  unfold colorBase at this;omega
 have paletteBefore:v.U ≤ v.J:=by have :=layout.palette;omega
 have endBefore:v.J ≤ recordBase v (height v):=by unfold recordBase;omega
 have rowBound:∀i,i<W.length → ∀f,f<3 → rowBase v d+3*i+f<recordBase v (height v):=by
  intro i hi f hf
  rw [rowBase_succ] at rowEnd
  omega
 refine ⟨?_,?_,?_⟩
 · intro i hi
   rcases table i hi with ⟨a,b,c⟩
   exact ⟨(heap _ (rowBound i (by simpa [W] using hi) 0 (by omega))).trans a,
    (heap _ (rowBound i (by simpa [W] using hi) 1 (by omega))).trans b,
    (heap _ (rowBound i (by simpa [W] using hi) 2 (by omega))).trans c⟩
 · intro i
   have hi:i.val<W.length:=i.isLt
   have hb:colorBase v d+i.val<recordBase v (height v):=by
    rw [colorBase_succ] at colorEnd;omega
   exact (heap _ hb).trans (colors i)
 · rcases record with ⟨a,b,c⟩
   have rb:∀f,f<3 → recordBase v d+f<recordBase v (height v):=by
    intro f hf
    unfold recordBase
    omega
   exact ⟨(heap _ (rb 0 (by omega))).trans a,(heap _ (rb 1 (by omega))).trans b,
    (heap _ (rb 2 (by omega))).trans c⟩

lemma height_result_retained {n:ℕ} (hn:0<n) (j:Fin (axisCount n))
 (c:UniformSeedHeightPreparation.Config) (B:ℕ) (layout:UniformSeedHeightPreparation.Layout n j c B)
 (work:C.Parameters) (dest:ℕ) (s u:State)
 (orig:UniformSeedHeightPreparation.Result n j c B (layout.replay hn j c B) s)
 (allocation:C.Allocation n j (UniformConjugateRankSpectrumPreparation.relocated
  (UniformSeedHeightPreparation.parameters n j c).base work) dest B)
 (frame:UniformConjugateRankSpectrumPreparation.Frame (UniformConjugateRankSpectrumPreparation.relocated
  (UniformSeedHeightPreparation.parameters n j c).base work) dest s u)
 (before:∀base∈[work.d,work.conv,work.tape,work.depth],
  UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7) ≤ base)
 (positive:c.C+7*c.width+1 ≤ work.S) (negative:c.negative+7*c.width ≤ work.S)
 (constants:c.constants+6 ≤ work.S)
 (registers:∀i,1050 ≤ i → i ≤ 1079 → u.natReg i=s.natReg i) :
 UniformSeedHeightPreparation.Result n j c B (layout.replay hn j c B) u := by
 let endNat:=UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7)
 have nh:∀i,i<endNat → u.natHeap i=s.natHeap i:=by
  intro i hi
  apply frame.1 i
  all_goals apply Or.inl
  all_goals apply lt_of_lt_of_le hi
  all_goals apply before; simp [UniformConjugateRankSpectrumPreparation.relocated]
 have scalar:∀i,i<work.S → u.scalarHeap i=s.scalarHeap i:=fun i hi=>frame.scalar_before allocation i hi
 have geq:(UniformRankCrossReplayPreparationMachine.cross
  (UniformSeedHeightPreparation.parameters n j c) (layout.replay hn j c B)).size=
  UniformCrossHeightPreparationMachine.gates c.height:=
  UniformRankCrossReplayPreparationMachine.cross_shape _ _
 have colorsBefore:c.colors ≤ c.palette:=by
  have h:=layout.heightLayout.colors
  change c.colors+2*c.gates*(8*c.exponent+7) ≤ c.palette at h
  omega
 have paletteBefore:c.palette ≤ c.heightDirectory:=by have h:=layout.heightLayout.palette;change c.palette+12 ≤ c.heightDirectory at h;omega
 have rowsBefore:c.rows ≤ c.colors:=by
  have h:=layout.heightLayout.rows
  change c.rows+6*c.gates*(8*c.exponent+7) ≤ c.colors at h
  omega
 have nativeEnd:c.rows ≤ endNat:=by
  dsimp only [endNat]
  change c.rows ≤ c.heightDirectory+3*(8*c.exponent+7)
  omega
 refine ⟨orig.source.transport geq layout.heightLayout (fun i hi=>nh i (lt_of_lt_of_le hi nativeEnd)),
  orig.cursor.transport_register registers,?_,?_,?_,?_,?_⟩
 · exact processed_prefix c.height c.negative _ orig.processed geq layout.heightLayout nh
 · intro i
   exact (scalar _ (by have hi:=i.isLt;unfold UniformToeplitzCrossDAG.bankSize at hi;change _<c.width+6*c.width at hi;omega)).trans (orig.positive i)
 · exact (scalar _ (by omega)).trans orig.root
 · intro i hi
   exact (scalar _ (by omega)).trans (orig.negative i hi)
 · intro i hi
   exact (scalar _ (by omega)).trans (orig.constants i hi)

def runtimeBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (work:C.Parameters) : ℕ :=
 UniformSeedHeightPreparation.runtimeBudget n j (O.c q original)+
 UniformRankCrossPreparationMachine.runtimeBudget
  (UniformConjugateRankSpectrumPreparation.selected n j (nextParameters n j q original work))+
 91*(O.c q original).width+71

/-- A physically stored forest row drives both original and conjugate
coefficient preparation continuously. All later spectra and signed coefficient
sources are derived, while both compact seed banks and directories survive. -/
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
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
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
  finalFrame.protected.metadata metadataOut,finalFrame.protected.operands oper,?_,?_⟩
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

end
end ExactFourierCircuits.UniformLocalRectangleCoefficientMachine
