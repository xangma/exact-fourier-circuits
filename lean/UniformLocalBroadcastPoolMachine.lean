import UniformLocalStoredRequestCoverage
import UniformCrossBroadcastTableMachine
import UniformTranslatedMatchingRows
import UniformGlobalMatchingPoolPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalBroadcastPoolMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformLocalCacheChronology
namespace L
abbrev Coefficient:=UniformMatchingConjugateLoadMachine.Coefficient
end L

/-- Stored rectangle and stored slot are read physically. The actual gate
count comes from Height186 register1072; no count table is readied. -/
def boot : List Op := [.literal 4290 0,.literal 4291 1,.literal 4292 2,
 .add 4294 4237 4290,.getNat 4295 4294,.add 4294 4294 4291,.getNat 4296 4294,
 .add 4294 4294 4291,.getNat 264 4294,.add 4294 4294 4291,.getNat 262 4294,
 .add 4294 4294 4292,.getNat 263 4294,.add 4294 4294 4291,.getNat 261 4294,
 .add 265 1072 4290,.add 266 4238 4290,
 .add 4294 4245 4292,.getNat 4264 4294,.add 4294 4294 4292,.getNat 4265 4294]
def broadcastSetup : List Op := [.sub 4270 4291 4265,.mul 3100 264 4270,
 .add 3101 265 4290,.add 3102 263 4290,.add 3103 266 4290,
 .add 3104 4239 4290,.add 3105 1062 4264]
def translationSetup : List Op := [.add 4990 894 4290,.add 4991 4239 4290,
 .add 4992 4240 4290,.add 4993 4296 4290]
def poolSetup : List Op := [.add 2100 1060 4290,.add 2101 4246 4290,.add 2102 1062 4290,
 .add 2103 4247 4290,.add 2106 4242 4290,.add 2107 4243 4290,.add 2140 4240 4290,
 .add 4330 4241 4290,.add 4331 4248 4290]
lemma boot_length : boot.length=21:=rfl
lemma broadcastSetup_length : broadcastSetup.length=7:=rfl
lemma translationSetup_length : translationSetup.length=4:=rfl
lemma poolSetup_length : poolSetup.length=9:=rfl
def program : Program := boot.map Op.code++
 UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++broadcastSetup.map Op.code++
 UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
 UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code++
 UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
lemma program_length : program.length=241 := by
 simp only [program,List.length_append,List.length_map,boot_length,broadcastSetup_length,
  translationSetup_length,poolSetup_length,UniformBorrowedCoordinateMachine.program_length,
  UniformCrossBroadcastTableMachine.program_length,UniformTranslatedMatchingRows.program_length,
  UniformGlobalMatchingPoolPreparation.program_length,List.length_singleton]

noncomputable section
def SlotSource (A:ℕ) (slot:Slot) (s:State) : Prop :=
 ∀f:Fin 5,s.natHeap (A+f.val)=some (UniformLocalReplaySlotMachine.Slot.words slot)[f.val]
def count (q:Row) (slot:Slot) := q.a*(1-slot.color)
def signIndex (slot:Slot) : Fin 6 := ⟨UniformLocalReplaySlotMachine.bit slot.inverse,by
 cases slot.inverse <;> simp [UniformLocalReplaySlotMachine.bit]⟩
def borrowedValue (q:Row) (g:ℕ) (fit:g+q.e+q.a ≤ q.width) (j:ℕ) : ℕ :=
 if h:j<g then (UniformBorrowedCoordinateMachine.embedding q.width q.j0 q.e q.i0 q.a g fit ⟨j,h⟩).val else 0
def rawRows (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) :=
 UniformCrossBroadcastTableMachine.rowList (count q slot) g q.i0 (P+(signIndex slot).val) (borrowedValue q g fit)
def rows (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) :=
 (rawRows q slot g P fit).map (UniformTranslatedMatchingRows.translated q.offset)
def coefficients {R:ℕ} (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) :
 Fin (rows q slot g P fit).length→L.Coefficient R:=fun _=>.constant (signIndex slot)
lemma rawRows_length (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) :
 (rawRows q slot g P fit).length=count q slot := by simp only [rawRows,UniformCrossBroadcastTableMachine.rowList_length]
lemma rows_length (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) :
 (rows q slot g P fit).length=count q slot := by simp only [rows,List.length_map,rawRows_length]
lemma count_cases (q:Row) (slot:Slot) : count q slot=0 ∨ count q slot=q.a := by
 by_cases zero:slot.color=0
 · right;simp [count,zero]
 · left
   have h:1-slot.color=0:=by omega
   simp only [count,h,Nat.mul_zero]
lemma labels {R:ℕ} (q:Row) (slot:Slot) (g C T P:ℕ) (fit:g+q.e+q.a ≤ q.width) :
 ∀j:Fin (rows q slot g P fit).length,(rows q slot g P fit)[j.val].coefficient=
 UniformMatchingConjugateLoadMachine.address C T P (coefficients (R:=R) q slot g P fit j) := by
 intro j
 simp only [rows,rawRows,UniformCrossBroadcastTableMachine.rowList,List.getElem_map,
  UniformTranslatedMatchingRows.translated,coefficients,UniformMatchingConjugateLoadMachine.address]

lemma bounds (q:Row) (slot:Slot) (g P r:ℕ) (fit:g+q.e+q.a ≤ q.width)
 (ag:q.a ≤ g) (target:q.i0+q.a ≤ q.width) (extent:q.offset+q.width ≤ r) :
 UniformGlobalMatchingPoolPreparation.Bounds r (rows q slot g P fit) := by
 rcases count_cases q slot with zero|full
 · intro j;have h:j.val<0:=by simpa only [rows_length,zero] using j.isLt
   omega
 · intro j
   have ja:j.val<q.a:=by simpa only [rows_length,full] using j.isLt
   have bg:g-q.a+j.val<g:=by omega
   have br:borrowedValue q g fit (g-q.a+j.val)<q.width:=by
    simp only [borrowedValue,dite_eq_left bg]
    exact (UniformBorrowedCoordinateMachine.embedding q.width q.j0 q.e q.i0 q.a g fit ⟨_,bg⟩).isLt
   simp only [rows,rawRows,UniformCrossBroadcastTableMachine.rowList,List.getElem_map,List.getElem_finRange,
    UniformTranslatedMatchingRows.translated,full,Fin.val_cast]
   constructor <;>omega

lemma different (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g) :
 UniformGlobalMatchingPoolPreparation.Different (rows q slot g P fit) := by
 rcases count_cases q slot with zero|full
 · intro j;have h:j.val<0:=by simpa only [rows_length,zero] using j.isLt
   omega
 · intro j
   have ja:j.val<q.a:=by simpa only [rows_length,full] using j.isLt
   have bg:g-q.a+j.val<g:=by omega
   have eligible:=UniformBorrowedCoordinateMachine.embedding_eligible q.width q.j0 q.e q.i0 q.a g fit ⟨_,bg⟩
   unfold UniformBorrowedCoordinateMachine.Eligible at eligible
   simp only [rows,rawRows,UniformCrossBroadcastTableMachine.rowList,List.getElem_map,List.getElem_finRange,
    UniformTranslatedMatchingRows.translated,full,Fin.val_cast,borrowedValue,dite_eq_left bg]
   omega

lemma matching (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g) :
 UniformGlobalMatchingPoolPreparation.Matching (rows q slot g P fit) := by
 rcases count_cases q slot with zero|full
 · intro i;have h:i.val<0:=by simpa only [rows_length,zero] using i.isLt
   omega
 · intro i j different
   have ia:i.val<q.a:=by simpa only [rows_length,full] using i.isLt
   have ja:j.val<q.a:=by simpa only [rows_length,full] using j.isLt
   have ib:g-q.a+i.val<g:=by omega
   have jb:g-q.a+j.val<g:=by omega
   have ij:(⟨i.val,ia⟩:Fin q.a)≠⟨j.val,ja⟩:=by
    intro eq
    have vals:i.val=j.val:=congrArg (fun z:Fin q.a=>z.val) eq
    exact different (Fin.ext vals)
   have mat:=UniformCrossBroadcastTableMachine.actual_matching q.width q.j0 q.e q.i0 q.a g fit ag
    ⟨i.val,ia⟩ ⟨j.val,ja⟩ ij
   unfold UniformColoring.Conflict UniformColoring.Incident UniformCrossBroadcastTableMachine.actualEdges
    UniformCrossBroadcastTableMachine.outputBorrowed at mat
   dsimp only [Fin.val_mk] at mat
   simp only [rows,rawRows,UniformCrossBroadcastTableMachine.rowList,List.getElem_map,List.getElem_finRange,
    UniformTranslatedMatchingRows.translated,full,Fin.val_cast,
    borrowedValue,dite_eq_left ib,dite_eq_left jb]
   omega

lemma coefficient_value {R:ℕ} (K:ℕ) (bank:Fin R→ℂ) (slot:Slot) :
 UniformMatchingConjugateLoadMachine.value K bank (.constant (signIndex slot))=
 if slot.inverse then (-1:ℂ) else 1 := by
 cases h:slot.inverse <;>
  simp [UniformMatchingConjugateLoadMachine.value,signIndex,UniformLocalReplaySlotMachine.bit,
   UniformReplayCoefficientMachine.constant,h]

/-- All caller addresses are ordinary retained integers. No scalar leaves,
borrowed coordinates, row tables, counts, or factor lanes are supplied. -/
structure Args (D I Q T E pool mu bar C Z P V r g:ℕ) (s:State) : Prop where
 rectangle : s.natReg 4237=D
 slot : s.natReg 4245=I
 borrowed : s.natReg 4238=Q
 rawRows : s.natReg 4239=T
 translated : s.natReg 4240=E
 pool : s.natReg 4241=pool
 mu : s.natReg 4242=mu
 conjugateMu : s.natReg 4243=bar
 negative : s.natReg 4246=Z
 conjugates : s.natReg 4247=V
 radix : s.natReg 4248=r
 positive : s.natReg 1060=C
 constants : s.natReg 1062=P
 gates : s.natReg 1072=g

structure Booted (q:Row) (slot:Slot) (g Q:ℕ) (s:State) : Prop where
 zero : s.natReg 4290=0
 one : s.natReg 4291=1
 two : s.natReg 4292=2
 width : s.natReg 4295=q.width
 offset : s.natReg 4296=q.offset
 source : s.natReg 261=q.j0
 inputs : s.natReg 262=q.e
 target : s.natReg 263=q.i0
 outputs : s.natReg 264=q.a
 gates : s.natReg 265=g
 borrowed : s.natReg 266=Q
 inverse : s.natReg 4264=(signIndex slot).val
 color : s.natReg 4265=slot.color

lemma boot_spec (D I Q T E pool mu bar C Z P V r g:ℕ) (q:Row) (slot:Slot) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s) :
 Booted q slot g Q (applyBlock boot s) := by
 have h0:s.natHeap D=some q.width:=by simpa [Row.words] using source ⟨0,by decide⟩
 have h1:s.natHeap (D+1)=some q.offset:=by simpa [Row.words] using source ⟨1,by decide⟩
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 have i2:s.natHeap (I+2)=some (signIndex slot).val:=by
  simpa [UniformLocalReplaySlotMachine.Slot.words,signIndex] using record ⟨2,by decide⟩
 have i4:s.natHeap (I+4)=some slot.color:=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using record ⟨4,by decide⟩
 constructor <;>
  simp [boot,applyBlock,Op.apply,writeNat,next,args.rectangle,args.slot,args.borrowed,args.gates,
   Nat.add_assoc,h0,h1,h2,h3,h5,h6,i2,i4]

lemma boot_heap (s:State) : (applyBlock boot s).natHeap=s.natHeap:=by
 simp only [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_scalar (s:State) : (applyBlock boot s).scalarHeap=s.scalarHeap:=by
 simp only [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_keeps (s:State) (q:ℕ)
 (keep:q ∉ [4290,4291,4292,4294,4295,4296,264,262,263,261,265,266,4264,4265]) :
 (applyBlock boot s).natReg q=s.natReg q := by
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at keep
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_args (D I Q T E pool mu bar C Z P V r g:ℕ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s) :
 Args D I Q T E pool mu bar C Z P V r g (applyBlock boot s) := by
 rcases args with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
 constructor <;>
  rw [boot_keeps s _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)] <;>assumption

lemma boot_safe (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (bound:WordBound B s) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B) (_code:241 ≤ B) :
 readable boot s ∧ peak boot s ≤ B := by
 have h0:s.natHeap D=some q.width:=by simpa [Row.words] using source ⟨0,by decide⟩
 have h1:s.natHeap (D+1)=some q.offset:=by simpa [Row.words] using source ⟨1,by decide⟩
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 have i2:s.natHeap (I+2)=some (signIndex slot).val:=by
  simpa [UniformLocalReplaySlotMachine.Slot.words,signIndex] using record ⟨2,by decide⟩
 have i4:s.natHeap (I+4)=some slot.color:=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using record ⟨4,by decide⟩
 have b0:=(bound.2.2.1 _ _ h0).2;have b1:=(bound.2.2.1 _ _ h1).2
 have b2:=(bound.2.2.1 _ _ h2).2;have b3:=(bound.2.2.1 _ _ h3).2
 have b5:=(bound.2.2.1 _ _ h5).2;have b6:=(bound.2.2.1 _ _ h6).2
 have bi2:=(bound.2.2.1 _ _ i2).2;have bi4:=(bound.2.2.1 _ _ i4).2
 have bg:=bound.2.1 1072;have bq:=bound.2.1 4238
 constructor
 · simp [boot,readable,Op.readable,Op.apply,writeNat,next,args.rectangle,args.slot,Nat.add_assoc,
    h0,h1,h2,h3,h5,h6,i2,i4]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,args.rectangle,args.slot,Nat.add_assoc,
    h0,h1,h2,h3,h5,h6,i2,i4]
   repeat' apply And.intro
   all_goals omega

lemma Args.withPC {D I Q T E pool mu bar C Z P V r g pc:ℕ} {s:State}
 (h:Args D I Q T E pool mu bar C Z P V r g s) :
 Args D I Q T E pool mu bar C Z P V r g (setPC s pc):=by
 cases h;constructor <;>assumption
lemma Booted.withPC {q:Row} {slot:Slot} {g Q pc:ℕ} {s:State} (h:Booted q slot g Q s) :
 Booted q slot g Q (setPC s pc):=by cases h;constructor <;>assumption
lemma Args.transport {D I Q T E pool mu bar C Z P V r g:ℕ} {s u:State}
 (h:Args D I Q T E pool mu bar C Z P V r g s)
 (eq:∀k,k∈[4237,4245,4238,4239,4240,4241,4242,4243,4246,4247,4248,1060,1062,1072]→u.natReg k=s.natReg k) :
 Args D I Q T E pool mu bar C Z P V r g u := by
 rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
 constructor <;> rw [eq _ (by simp)] <;>assumption
lemma Booted.transport {q:Row} {slot:Slot} {g Q:ℕ} {s u:State} (h:Booted q slot g Q s)
 (eq:∀k,k∈[4290,4291,4292,4295,4296,261,262,263,264,265,266,4264,4265]→u.natReg k=s.natReg k) :
 Booted q slot g Q u := by
 rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
 constructor <;>rw [eq _ (by simp)] <;>assumption

lemma segment_block (before after:Program) (ops:List Op) (base:ℕ)
 (len:before.length=base) : BlockAt ops (before++ops.map Op.code++after) base := by
 intro i hi
 simpa only [len,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,List.append_assoc] using
  UniformAllAxisSeedPreparation.lookup_segment before (ops.map Op.code) after i (by simpa using hi)
attribute [local irreducible] UniformBorrowedCoordinateMachine.program
 UniformCrossBroadcastTableMachine.program UniformTranslatedMatchingRows.program
 UniformGlobalMatchingPoolPreparation.program
lemma boot_code : BlockAt boot program 0 := by
 let rest:=UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++broadcastSetup.map Op.code++
  UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code++
  UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=[]++boot.map Op.code++rest:=by simp only [program,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact segment_block [] rest boot 0 rfl
lemma borrowed_code : CodeAt UniformBorrowedCoordinateMachine.program program 21 38 := by
 let rest:=broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++
  translationSetup.map Op.code++UniformTranslatedMatchingRows.program.map (relocate 69 92)++
  poolSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++rest:=by
  simp only [program,rest,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code (boot.map Op.code) rest _ 21 38 (by
  simp only [List.length_map,boot_length])
lemma broadcastSetup_code : BlockAt broadcastSetup program 38 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)
 let rest:=UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code++
  UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=before++broadcastSetup.map Op.code++rest:=by simp only [program,before,rest,List.append_assoc]
 rw [eq]
 exact segment_block before rest _ 38 (by
  simp only [before,List.length_append,List.length_map,boot_length,UniformBorrowedCoordinateMachine.program_length])
lemma broadcast_code : CodeAt UniformCrossBroadcastTableMachine.program program 45 65 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++broadcastSetup.map Op.code
 let rest:=translationSetup.map Op.code++UniformTranslatedMatchingRows.program.map (relocate 69 92)++
  poolSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=before++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++rest:=by
  simp only [program,before,rest,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before rest _ 45 65 (by
  simp only [before,List.length_append,List.length_map,boot_length,
   UniformBorrowedCoordinateMachine.program_length,broadcastSetup_length])
lemma translationSetup_code : BlockAt translationSetup program 65 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++
  broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)
 let rest:=UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code++
  UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=before++translationSetup.map Op.code++rest:=by simp only [program,before,rest,List.append_assoc]
 rw [eq]
 exact segment_block before rest _ 65 (by
  simp only [before,List.length_append,List.length_map,boot_length,broadcastSetup_length,
   UniformBorrowedCoordinateMachine.program_length,UniformCrossBroadcastTableMachine.program_length])
lemma translation_code : CodeAt UniformTranslatedMatchingRows.program program 69 92 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++
  broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code
 let rest:=poolSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=before++UniformTranslatedMatchingRows.program.map (relocate 69 92)++rest:=by
  simp only [program,before,rest,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before rest _ 69 92 (by
  simp only [before,List.length_append,List.length_map,boot_length,broadcastSetup_length,translationSetup_length,
   UniformBorrowedCoordinateMachine.program_length,UniformCrossBroadcastTableMachine.program_length])
lemma poolSetup_code : BlockAt poolSetup program 92 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++
  broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 69 92)
 let rest:=UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]
 have eq:program=before++poolSetup.map Op.code++rest:=by simp only [program,before,rest,List.append_assoc]
 rw [eq]
 exact segment_block before rest _ 92 (by
  simp only [before,List.length_append,List.length_map,boot_length,broadcastSetup_length,translationSetup_length,
   UniformBorrowedCoordinateMachine.program_length,UniformCrossBroadcastTableMachine.program_length,
   UniformTranslatedMatchingRows.program_length])
lemma pool_code : CodeAt UniformGlobalMatchingPoolPreparation.program program 101 240 := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++
  broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code
 have eq:program=before++UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)++[.halt]:=by
  simp only [program,before,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before [.halt] _ 101 240 (by
  simp only [before,List.length_append,List.length_map,boot_length,broadcastSetup_length,translationSetup_length,
   poolSetup_length,UniformBorrowedCoordinateMachine.program_length,UniformCrossBroadcastTableMachine.program_length,
   UniformTranslatedMatchingRows.program_length])
lemma halt_at : program[240]?=some .halt := by
 let before:=boot.map Op.code++UniformBorrowedCoordinateMachine.program.map (relocate 21 38)++
  broadcastSetup.map Op.code++UniformCrossBroadcastTableMachine.program.map (relocate 45 65)++translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 69 92)++poolSetup.map Op.code++
  UniformGlobalMatchingPoolPreparation.program.map (relocate 101 240)
 have len:before.length=240:=by
  simp only [before,List.length_append,List.length_map,boot_length,broadcastSetup_length,translationSetup_length,
   poolSetup_length,UniformBorrowedCoordinateMachine.program_length,UniformCrossBroadcastTableMachine.program_length,
   UniformTranslatedMatchingRows.program_length,UniformGlobalMatchingPoolPreparation.program_length]
 change (before++[.halt])[240]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

def protectedRegisters : List ℕ := [4237,4245,4238,4239,4240,4241,4242,4243,4246,4247,4248,
 1060,1062,1072,4290,4291,4292,4295,4296,261,262,263,264,265,266,4264,4265]
def Stable (s u:State) : Prop := ∀q,q∈protectedRegisters→u.natReg q=s.natReg q
lemma Stable.args {D I Q T E pool mu bar C Z P V r g:ℕ} {s u:State}
 (stable:Stable s u) (args:Args D I Q T E pool mu bar C Z P V r g s) :
 Args D I Q T E pool mu bar C Z P V r g u:=args.transport (fun q hq=>stable q (by
  simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at *;omega))
lemma Stable.booted {q:Row} {slot:Slot} {g Q:ℕ} {s u:State}
 (stable:Stable s u) (h:Booted q slot g Q s) : Booted q slot g Q u:=h.transport (fun q hq=>stable q (by
  simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at *;omega))

lemma broadcastSetup_stable (s:State) : Stable s (applyBlock broadcastSetup s) := by
 intro q hq
 apply UniformSeedRankCrossPreparation.block_register_keeps
 intro o ho
 simp only [broadcastSetup,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [UniformSeedRankCrossPreparation.KeepsRegister]
 all_goals simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega
lemma translationSetup_stable (s:State) : Stable s (applyBlock translationSetup s) := by
 intro q hq
 apply UniformSeedRankCrossPreparation.block_register_keeps
 intro o ho
 simp only [translationSetup,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl
 all_goals simp only [UniformSeedRankCrossPreparation.KeepsRegister]
 all_goals simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega
lemma poolSetup_stable (s:State) : Stable s (applyBlock poolSetup s) := by
 intro q hq
 apply UniformSeedRankCrossPreparation.block_register_keeps
 intro o ho
 simp only [poolSetup,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only [UniformSeedRankCrossPreparation.KeepsRegister]
 all_goals simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega
lemma borrowed_stable {s u:State} (frame:UniformBorrowedCoordinateMachine.Frame s u) : Stable s u := by
 intro q hq
 exact frame.2.2.2.2 q (by simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega)
lemma broadcast_stable {s u:State} (frame:UniformCrossBroadcastTableMachine.Frame s u) : Stable s u := by
 intro q hq
 apply frame.2.2.2.2
 all_goals simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega
lemma translation_stable {s u:State} (frame:UniformTranslatedMatchingRows.Frame s u) : Stable s u := by
 intro q hq
 exact frame.2.2.2.2 q (by simp only [protectedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq;omega)

lemma broadcastSetup_header {D I Q T E pool mu bar C Z P V r g:ℕ} {q:Row} {slot:Slot} (s:State)
 (h:Booted q slot g Q s) (args:Args D I Q T E pool mu bar C Z P V r g s) :
 UniformCrossBroadcastTableMachine.Header (count q slot) g q.i0 Q T (P+(signIndex slot).val)
  (applyBlock broadcastSetup s) := by
 constructor <;>simp [broadcastSetup,applyBlock,Op.apply,writeNat,next,h.one,h.color,h.outputs,
  h.gates,h.target,h.borrowed,h.zero,h.inverse,args.rawRows,args.constants,count]
lemma broadcastSetup_safe {q:Row} {slot:Slot} {g Q P B:ℕ} (s:State)
 (h:Booted q slot g Q s) (pp:s.natReg 1062=P) (bound:WordBound B s) (cp:P+1 ≤ B) :
 readable broadcastSetup s ∧ peak broadcastSetup s ≤ B := by
 have le:count q slot ≤ q.a:=by
  unfold count
  exact (Nat.mul_le_mul_left q.a (show 1-slot.color ≤ 1 by omega)).trans_eq (Nat.mul_one _)
 have hp:(signIndex slot).val ≤ 1:=by
  cases hh:slot.inverse <;>simp [signIndex,UniformLocalReplaySlotMachine.bit,hh]
 have ba:=bound.2.1 264;rw [h.outputs] at ba
 have bg:=bound.2.1 265;rw [h.gates] at bg
 have bt:=bound.2.1 263;rw [h.target] at bt
 have bq:=bound.2.1 266;rw [h.borrowed] at bq
 have bd:=bound.2.1 4239
 constructor
 · simp [broadcastSetup,readable,Op.readable]
 · simp [broadcastSetup,peak,Op.peak,Op.apply,writeNat,next,h.one,h.color,h.outputs,h.gates,
    h.target,h.borrowed,h.zero,h.inverse,pp]
   dsimp only [count] at le
   repeat' apply And.intro
   all_goals omega
lemma translationSetup_safe (B:ℕ) (s:State) (h:s.natReg 4290=0) (bound:WordBound B s) :
 readable translationSetup s ∧ peak translationSetup s ≤ B := by
 constructor
 · simp [translationSetup,readable,Op.readable]
 · simp [translationSetup,peak,Op.peak,Op.apply,writeNat,next,h]
   exact ⟨bound.2.1 894,bound.2.1 4239,bound.2.1 4240,bound.2.1 4296⟩
lemma poolSetup_safe (B:ℕ) (s:State) (h:s.natReg 4290=0) (bound:WordBound B s) :
 readable poolSetup s ∧ peak poolSetup s ≤ B := by
 constructor
 · simp [poolSetup,readable,Op.readable]
 · simp [poolSetup,peak,Op.peak,Op.apply,writeNat,next,h]
   exact ⟨bound.2.1 1060,bound.2.1 4246,bound.2.1 1062,bound.2.1 4247,bound.2.1 4242,
    bound.2.1 4243,bound.2.1 4240,bound.2.1 4241,bound.2.1 4248⟩
lemma setup_heap (b:List Op) (hb:b∈[broadcastSetup,translationSetup,poolSetup]) (s:State) :
 (applyBlock b s).natHeap=s.natHeap ∧ (applyBlock b s).scalarHeap=s.scalarHeap ∧
 (applyBlock b s).scalarReg=s.scalarReg ∧ (applyBlock b s).outputs=s.outputs ∧
 (applyBlock b s).rootOrders=s.rootOrders := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 all_goals simp [broadcastSetup,translationSetup,poolSetup,applyBlock,Op.apply,writeNat,next]

lemma translationSetup_headers {D I Q T E pool mu bar C Z P V r g M:ℕ} {q:Row} {slot:Slot} (s:State)
 (h:Booted q slot g Q s) (args:Args D I Q T E pool mu bar C Z P V r g s) (hc:s.natReg 894=M) :
 (applyBlock translationSetup s).natReg 4990=M ∧ (applyBlock translationSetup s).natReg 4991=T ∧
 (applyBlock translationSetup s).natReg 4992=E ∧ (applyBlock translationSetup s).natReg 4993=q.offset := by
 simp [translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.offset,args.rawRows,args.translated,hc]
lemma poolSetup_args {D I Q T E pool mu bar C Z P V r g:ℕ} {q:Row} {slot:Slot} (s:State)
 (h:Booted q slot g Q s) (args:Args D I Q T E pool mu bar C Z P V r g s) :
 UniformMatchingConjugateLoadMachine.RowArgs C Z P V mu bar E ((applyBlock poolSetup s).natReg 2141)
  (applyBlock poolSetup s) ∧ (applyBlock poolSetup s).natReg 4330=pool ∧
 (applyBlock poolSetup s).natReg 4331=r := by
 refine ⟨?_,?_,?_⟩
 · constructor <;>simp [poolSetup,applyBlock,Op.apply,writeNat,next,h.zero,args.positive,args.negative,
    args.constants,args.conjugates,args.mu,args.conjugateMu,args.translated]
 · simp [poolSetup,applyBlock,Op.apply,writeNat,next,h.zero,args.pool]
 · simp [poolSetup,applyBlock,Op.apply,writeNat,next,h.zero,args.radix]

lemma raw_range (q:Row) (slot:Slot) (g P:ℕ) (fit:g+q.e+q.a ≤ q.width)
 (ag:q.a ≤ g) (target:q.i0+q.a ≤ q.width) :
 ∀row∈rawRows q slot g P fit,row.dst<q.width ∧ row.src<q.width := by
 have b:=bounds {q with offset:=0} slot g P q.width fit ag target (by simp)
 change UniformGlobalMatchingPoolPreparation.Bounds q.width
  ((rawRows q slot g P fit).map (UniformTranslatedMatchingRows.translated 0)) at b
 intro row hr
 obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hr
 simpa only [List.getElem_map,UniformTranslatedMatchingRows.translated,Nat.zero_add] using
  b ⟨i,by simpa only [List.length_map] using hi⟩

theorem boot_stage {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot)
 (x:Fin n→ℂ) (s:State) (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (_fit:g+q.e+q.a ≤ q.width) (_sourceEnd:q.j0+q.e ≤ q.width) (_targetEnd:q.i0+q.a ≤ q.width)
 (_width:q.width ≤ B) (_borrowedEnd:Q+g ≤ B) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B)
 (code:241 ≤ B) (pc:s.pc=0) (bound:WordBound B s) : ∃a,
 BoundedRuns program n x B s 21 a ∧ a.pc=21 ∧ Booted q slot g Q a ∧
 Args D I Q T E pool mu bar C Z P V r g a ∧ a.natHeap=s.natHeap ∧
 a.scalarHeap=s.scalarHeap ∧ a.outputs=s.outputs ∧ a.rootOrders=s.rootOrders := by
 have safe:=boot_safe D I Q T E pool mu bar C Z P V r g B q slot s args source record bound rowEnd slotEnd code
 have first:=block_runs boot program 0 n B x s boot_code pc bound (by rw [boot_length];omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=21:=by rw [applyBlock_pc,pc,boot_length]
 have ab:Booted q slot g Q a:=boot_spec D I Q T E pool mu bar C Z P V r g q slot s args source record
 have aa:=boot_args D I Q T E pool mu bar C Z P V r g s args
 refine ⟨a,?_,ap,ab,aa,boot_heap s,boot_scalar s,?_,?_⟩
 · simpa only [boot_length] using first
 · rfl
 · rfl

theorem borrowed_stage {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot)
 (x:Fin n→ℂ) (s:State) (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (fit:g+q.e+q.a ≤ q.width) (sourceEnd:q.j0+q.e ≤ q.width) (targetEnd:q.i0+q.a ≤ q.width)
 (width:q.width ≤ B) (borrowedEnd:Q+g ≤ B) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B)
 (code:241 ≤ B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedRuns program n x B s ticks u ∧ ticks ≤ 11*q.width+28 ∧ u.pc=38 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) u ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 obtain ⟨a,first,ap,ab,aa,aheap,ascalar,aout,aroot⟩:=
  boot_stage D I Q T E pool mu bar C Z P V r g B q slot x s args source record
   fit sourceEnd targetEnd width borrowedEnd rowEnd slotEnd code pc bound
 let ae:=setPC a 0
 have aw:=changePC_bound B a 0 first.final_bound (by omega)
 have bh:UniformBorrowedCoordinateMachine.Headers q.j0 q.e q.i0 q.a g Q ae:=
  ⟨ab.source,ab.inputs,ab.target,ab.outputs,ab.gates,ab.borrowed⟩
 obtain ⟨bt,b,borrowed,bcheap,bpc,bcount,filled,bframe,boutside⟩:=
  UniformBorrowedCoordinateMachine.execution n x q.width q.j0 q.e q.i0 q.a g Q B ae
   bh rfl aw (by omega) width (sourceEnd.trans width) (targetEnd.trans width) borrowedEnd fit
 have placedBorrowed:=UniformBoundedAssembly.boundedExecution_placed borrowed_code
  (by rw [UniformBorrowedCoordinateMachine.program_length];omega) (by omega) borrowed
 rw [UniformSeedRankCrossPreparation.placed_zero a 21 ap] at placedBorrowed

 let u:=setPC b 38
 have physical:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) u:=by
  intro j hj
  change b.natHeap (Q+j)=some (borrowedValue q g fit j)
  rw [borrowedValue,dite_eq_left hj]
  have jl:j<(UniformBorrowedCoordinateMachine.borrowed q.width q.j0 q.e q.i0 q.a g).length:=by
   rw [UniformBorrowedCoordinateMachine.borrowed_length _ _ _ _ _ _ fit];exact hj
  change b.natHeap (Q+j)=some ((UniformBorrowedCoordinateMachine.borrowed q.width q.j0 q.e q.i0 q.a g)[j]'jl)
  exact filled j jl
 refine ⟨u,21+bt,?_,by omega,rfl,((borrowed_stable bframe).booted ab.withPC).withPC,
  ((borrowed_stable bframe).args aa.withPC).withPC,physical,?_,bframe.1.trans ascalar,?_,?_⟩
 · simpa only [boot_length,u,setPC] using first.trans placedBorrowed
 · intro i hi;exact (boutside i (Or.inl hi)).trans (congrFun aheap i)
 · exact bframe.2.2.1.trans aout
 · exact bframe.2.2.2.1.trans aroot

theorem broadcast_stage {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ) (q:Row) (slot:Slot)
 (x:Fin n→ℂ) (s:State) (args:Args D I Q T E pool mu bar C Z P V r g s)
 (booted:Booted q slot g Q s) (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g)
 (physical:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) s)
 (borrowedEnd:Q+g ≤ T) (rawEnd:T+3*q.a ≤ B) (targetEnd:q.i0+q.a ≤ B)
 (cap:P+1 ≤ B) (code:241 ≤ B) (pc:s.pc=38) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (14*count q slot+14) u ∧ u.pc=65 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) u ∧ u.natReg 894=count q slot ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have safe:=broadcastSetup_safe s booted args.constants bound cap
 have setBroadcast:=block_runs broadcastSetup program 38 n B x s broadcastSetup_code pc
  bound (by rw [broadcastSetup_length];omega) safe.1 safe.2
 let c:=applyBlock broadcastSetup s
 have cp:c.pc=45:=by rw [applyBlock_pc,pc,broadcastSetup_length]
 have cb:Booted q slot g Q c:=(broadcastSetup_stable s).booted booted
 have ca:Args D I Q T E pool mu bar C Z P V r g c:=(broadcastSetup_stable s).args args
 have cnh: c.natHeap=s.natHeap:=(setup_heap broadcastSetup (by simp) s).1
 have phy:UniformCrossBroadcastTableMachine.Borrowed Q g (borrowedValue q g fit) c:=by
  intro j hj
  rw [cnh]
  simpa only [borrowedValue,dite_eq_left hj,UniformBorrowedCoordinateMachine.embedding] using
   physical j hj
 let ce:=setPC c 0
 have cw:=changePC_bound B c 0 setBroadcast.final_bound (by omega)
 have ch:UniformCrossBroadcastTableMachine.Header (count q slot) g q.i0 Q T (P+(signIndex slot).val) ce:=by
  have h:=broadcastSetup_header s booted args
  exact ⟨h.count,h.gates,h.target,h.borrowed,h.output,h.coefficient⟩
 obtain ⟨d,broadcast,printed,bretained,doutside,dframe,dc,dpc⟩:=
  UniformCrossBroadcastTableMachine.execution n B (count q slot) g q.i0 Q T (P+(signIndex slot).val)
   x (borrowedValue q g fit) ce ch rfl (mc.trans ag) phy
   borrowedEnd (by omega) (by omega) cw (by omega)
 have placedBroadcast:=UniformBoundedAssembly.boundedExecution_placed broadcast_code
  (by rw [UniformCrossBroadcastTableMachine.program_length];omega) (by omega) broadcast
 rw [UniformSeedRankCrossPreparation.placed_zero c 45 cp] at placedBroadcast

 let u:=setPC d 65
 have heaps:=setup_heap broadcastSetup (by simp) s
 refine ⟨u,?_,rfl,((broadcast_stable dframe).booted cb.withPC).withPC,((broadcast_stable dframe).args ca.withPC).withPC,
  UniformCrossBroadcastTableMachine.rows_table printed,dc,?_,dframe.1.trans heaps.2.1,
  dframe.2.2.1.trans heaps.2.2.2.1,dframe.2.2.2.1.trans heaps.2.2.2.2⟩
 · convert setBroadcast.trans placedBroadcast using 1 <;>try simp only [broadcastSetup_length,u,setPC] <;>omega
 · intro i hi;exact (doutside i (Or.inl (by omega))).trans (congrFun cnh i)

/-- Actual translated rows; this boundary keeps all earlier scalar banks. -/
theorem translation_stage {n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ)
 (q:Row) (slot:Slot) (x:Fin n→ℂ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s) (booted:Booted q slot g Q s)
 (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g) (targetEnd:q.i0+q.a ≤ q.width)
 (extent:q.offset+q.width ≤ B) (raw:UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) s)
 (counted:s.natReg 894=count q slot) (borrowedEnd:Q ≤ T) (rawEnd:T+3*q.a ≤ E)
 (tableEnd:E+3*q.a ≤ B) (code:241 ≤ B) (pc:s.pc=65) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (19*count q slot+9) u ∧ u.pc=92 ∧
 Booted q slot g Q u ∧ Args D I Q T E pool mu bar C Z P V r g u ∧
 UniformCrossShearTableMachine.Table E (rows q slot g P fit) u ∧ u.natReg 894=count q slot ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧ u.scalarHeap=s.scalarHeap ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have safe:=translationSetup_safe B s booted.zero bound
 have first:=block_runs translationSetup program 65 n B x s translationSetup_code pc bound
  (by rw [translationSetup_length];omega) safe.1 safe.2
 let e:=applyBlock translationSetup s
 have ep:e.pc=69:=by rw [applyBlock_pc,pc,translationSetup_length]
 have eb:Booted q slot g Q e:=(translationSetup_stable s).booted booted
 have ea:Args D I Q T E pool mu bar C Z P V r g e:=(translationSetup_stable s).args args
 have heaps:=setup_heap translationSetup (by simp) s
 have rawTable:UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) e:=by
  change UniformCrossShearTableMachine.Table T (rawRows q slot g P fit) (applyBlock translationSetup s)
  simpa only [UniformCrossShearTableMachine.Table,UniformCrossShearTableMachine.RowFields,heaps.1] using raw
 have th:=translationSetup_headers s booted args counted
 let ee:=setPC e 0
 have ew:=changePC_bound B e 0 first.final_bound (by omega)
 obtain ⟨f,run,table,rawRetained,frame,outside,fp⟩:=
  UniformTranslatedMatchingRows.execution n B T E q.offset q.width (rawRows q slot g P fit) x ee
   rfl (by simpa only [ee,setPC,e,rawRows_length] using th.1) th.2.1 th.2.2.1 th.2.2.2 rawTable
   (raw_range q slot g P fit ag targetEnd) (by rw [rawRows_length];omega)
   (by omega) (by rw [rawRows_length];omega) (by rw [rawRows_length];omega) extent ew
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed translation_code
  (by rw [UniformTranslatedMatchingRows.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero e 69 ep] at placedRun
 let u:=setPC f 92
 refine ⟨u,?_,rfl,((translation_stable frame).booted eb.withPC).withPC,
  ((translation_stable frame).args ea.withPC).withPC,table,?_,?_,frame.1.trans heaps.2.1,
  frame.2.2.1.trans heaps.2.2.2.1,frame.2.2.2.1.trans heaps.2.2.2.2⟩
 · convert first.trans placedRun using 1 <;>try simp only [translationSetup_length,rawRows_length,u,setPC] <;>omega
 · have ec:e.natReg 894=count q slot:=by
    simpa only [e,translationSetup,applyBlock,Op.apply,writeNat,next,Function.update_of_ne (by omega : 894≠4990),
     Function.update_of_ne (by omega : 894≠4991),Function.update_of_ne (by omega : 894≠4992),
     Function.update_of_ne (by omega : 894≠4993)] using counted
   exact (frame.2.2.2.2 894 (by omega)).trans ec
 · intro i hi;exact (outside i (Or.inl (by omega))).trans (congrFun heaps.1 i)

/-- The matching factors are prepared from actual rows and actual coefficients. -/
theorem pool_stage {R K n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ)
 (q:Row) (slot:Slot) (bank:Fin R→ℂ) (x:Fin n→ℂ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s) (booted:Booted q slot g Q s)
 (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g) (targetEnd:q.i0+q.a ≤ q.width)
 (extent:q.offset+q.width ≤ r) (table:UniformCrossShearTableMachine.Table E (rows q slot g P fit) s)
 (counted:s.natReg 894=count q slot)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C Z P V mu bar B)
 (low:6 ≤ mu) (fresh:bar<pool) (tableEnd:E+3*count q slot ≤ B) (poolEnd:pool+9*r ≤ B)
 (code:241 ≤ B) (pc:s.pc=92) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ 45*r+117*count q slot+23 ∧ u.pc=240 ∧
 UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r (rows q slot g P fit)
  bank (coefficients q slot g P fit) (rows q slot g P fit).length u ∧
 UniformCrossShearTableMachine.Table E (rows q slot g P fit) u ∧ u.natReg 894=count q slot ∧
 UniformMatchingConjugateLoadMachine.Sources K C Z P V bank u ∧ UniformHadamardPairMachine.Constants u ∧
 u.natHeap=s.natHeap ∧
 (∀i,(i<pool ∨ pool+9*r ≤ i)→i≠mu→i≠bar→u.scalarHeap i=s.scalarHeap i) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have safe:=poolSetup_safe B s booted.zero bound
 have first:=block_runs poolSetup program 92 n B x s poolSetup_code pc bound
  (by rw [poolSetup_length];omega) safe.1 safe.2
 let z:=applyBlock poolSetup s
 have zp:z.pc=101:=by rw [applyBlock_pc,pc,poolSetup_length]
 have heaps:=setup_heap poolSetup (by simp) s
 have zsources:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank z:=
  UniformConjugatePackedMatchingPreparation.sources_transport sources heaps.2.1
 have zconstants:UniformHadamardPairMachine.Constants z:=by
  change UniformHadamardPairMachine.Constants (applyBlock poolSetup s)
  simpa only [UniformHadamardPairMachine.Constants,heaps.2.1] using constants
 have ztable:UniformCrossShearTableMachine.Table E (rows q slot g P fit) z:=by
  change UniformCrossShearTableMachine.Table E (rows q slot g P fit) (applyBlock poolSetup s)
  simpa only [UniformCrossShearTableMachine.Table,UniformCrossShearTableMachine.RowFields,heaps.1] using table
 have zcount:z.natReg 894=(rows q slot g P fit).length:=by
  rw [rows_length]
  simpa [z,poolSetup,applyBlock,Op.apply,writeNat,next] using counted
 have ph:=poolSetup_args s booted args
 let ze:=setPC z 0
 have zw:=changePC_bound B z 0 first.final_bound (by omega)
 have rowArgs:UniformMatchingConjugateLoadMachine.RowArgs C Z P V mu bar E (ze.natReg 2141) ze:=
  ⟨ph.1.positive,ph.1.negative,ph.1.constants,ph.1.conjugates,ph.1.original,ph.1.conjugate,
   ph.1.rows,ph.1.index⟩
 have src:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank ze:=
  ⟨zsources.positive,zsources.negative,zsources.conjugate,zsources.constants⟩
 obtain ⟨last,pt,run,cheap,lpc,values,retSources,retConstants,retTable,nh,outs,roots,outside⟩:=
  UniformGlobalMatchingPoolPreparation.execution (rows q slot g P fit) (coefficients q slot g P fit)
   (labels q slot g C Z P fit) rowArgs src zconstants ztable zcount ph.2.1 ph.2.2
   (bounds q slot g P r fit ag targetEnd extent) (different q slot g P fit ag) (matching q slot g P fit ag)
   layout low fresh (by simpa only [rows_length] using tableEnd) poolEnd (by omega) x rfl zw
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed pool_code
  (by rw [UniformGlobalMatchingPoolPreparation.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero z 101 zp] at placedRun
 let u:=setPC last 240
 have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound (by
  simp [step,u,setPC,halt_at])
 have lastCount:u.natReg 894=count q slot:=by
  have keep:=UniformGlobalMatchingPoolPreparation.execution_nat run (q:=894) (by
   simp only [UniformGlobalMatchingPoolPreparation.natScratch,UniformGlobalMatchingScaleMachine.natScratch,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false];omega)
  exact keep.trans (by simpa only [rows_length,ze,setPC] using zcount)
 refine ⟨u,9+pt+1,?_,?_,rfl,⟨values.done,values.remaining,values.untouched⟩,retTable,lastCount,
  ⟨retSources.positive,retSources.negative,retSources.conjugate,retSources.constants⟩,retConstants,
  nh.trans heaps.1,?_,outs.trans heaps.2.2.2.1,roots.trans heaps.2.2.2.2⟩
 · simpa only [poolSetup_length,u,setPC,Nat.add_assoc] using first.executes (placedRun.executes stop)
 · rw [rows_length] at cheap;omega
 · intro i hi hm hb;exact (outside i hi hm hb).trans (congrFun heaps.2.1 i)

/-- One actual broadcast-cache preparation, from physically stored records. -/
theorem execution {R K n:ℕ} (D I Q T E pool mu bar C Z P V r g B:ℕ)
 (q:Row) (slot:Slot) (bank:Fin R→ℂ) (x:Fin n→ℂ) (s:State)
 (args:Args D I Q T E pool mu bar C Z P V r g s)
 (source:UniformLocalRectangleBankMachine.RowSource D q s) (record:SlotSource I slot s)
 (fit:g+q.e+q.a ≤ q.width) (ag:q.a ≤ g)
 (sourceEnd:q.j0+q.e ≤ q.width) (targetEnd:q.i0+q.a ≤ q.width)
 (extent:q.offset+q.width ≤ r)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C Z P V mu bar B)
 (low:6 ≤ mu) (fresh:bar<pool)
 (borrowedEnd:Q+g ≤ T) (rawEnd:T+3*q.a ≤ E) (tableEnd:E+3*q.a ≤ B)
 (poolEnd:pool+9*r ≤ B) (rowEnd:D+6 ≤ B) (slotEnd:I+4 ≤ B)
 (code:241 ≤ B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ 11*q.width+45*r+150*count q slot+74 ∧ u.pc=240 ∧
 UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r (rows q slot g P fit)
  bank (coefficients q slot g P fit) (rows q slot g P fit).length u ∧
 UniformCrossShearTableMachine.Table E (rows q slot g P fit) u ∧
 u.natReg 894=count q slot ∧ UniformMatchingConjugateLoadMachine.Sources K C Z P V bank u ∧
 UniformHadamardPairMachine.Constants u ∧
 (∀i,i<Q→u.natHeap i=s.natHeap i) ∧
 (∀i,(i<pool ∨ pool+9*r ≤ i)→i≠mu→i≠bar→u.scalarHeap i=s.scalarHeap i) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have mc:count q slot ≤ q.a:=by rcases count_cases q slot with z|eq <;>omega
 have width:q.width ≤ B:=by omega
 obtain ⟨a,firstTicks,first,cheapA,ap,ab,aa,physical,ah,ascalar,aout,aroot⟩:=
  borrowed_stage D I Q T E pool mu bar C Z P V r g B q slot x s args source record fit sourceEnd
   targetEnd width (by omega) rowEnd slotEnd code pc bound
 have cap:P+1 ≤ B:=by
  have:=layout.constantsBelow;have:=layout.conjugatesBelow;have:=layout.destinations;have:=layout.bound;omega
 obtain ⟨b,second,bp,bb,ba,raw,bc,bh,bscalar,bout,broot⟩:=
  broadcast_stage D I Q T E pool mu bar C Z P V r g B q slot x a aa ab fit ag physical
   borrowedEnd (by omega) (targetEnd.trans width) cap code ap first.final_bound
 obtain ⟨c,third,cp,cb,ca,table,cc,ch,cscalar,cout,croot⟩:=
  translation_stage D I Q T E pool mu bar C Z P V r g B q slot x b ba bb fit ag targetEnd
   (extent.trans (by omega)) raw bc (by omega) rawEnd tableEnd code bp second.final_bound
 have scalars:c.scalarHeap=s.scalarHeap:=cscalar.trans (bscalar.trans ascalar)
 have src:UniformMatchingConjugateLoadMachine.Sources K C Z P V bank c:=
  UniformConjugatePackedMatchingPreparation.sources_transport sources scalars
 have const:UniformHadamardPairMachine.Constants c:=by
  simpa only [UniformHadamardPairMachine.Constants,scalars] using constants
 obtain ⟨u,pt,last,cheapP,up,values,rowsOut,uc,srcOut,constOut,nh,outside,outs,roots⟩:=
  pool_stage D I Q T E pool mu bar C Z P V r g B q slot bank x c ca cb fit ag targetEnd extent table cc
   src const layout low fresh (by omega) poolEnd code cp third.final_bound
 refine ⟨u,firstTicks+(14*count q slot+14)+(19*count q slot+9)+pt,?_,by omega,up,values,rowsOut,uc,
  srcOut,constOut,?_,?_,outs.trans (cout.trans (bout.trans aout)),roots.trans (croot.trans (broot.trans aroot))⟩
 · exact ((first.trans second).trans third).executes last
 · intro i hi;exact (congrFun nh i).trans ((ch i hi).trans ((bh i hi).trans (ah i hi)))
 · intro i hi hm hb;exact (outside i hi hm hb).trans (congrFun scalars i)

end
end ExactFourierCircuits.UniformLocalBroadcastPoolMachine
