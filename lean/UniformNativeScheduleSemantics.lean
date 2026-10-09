import UniformFixedNetworkScheduleMachine
import UniformNativeCopiedInverse
import UniformBinarySpectatorCMachine
import UniformNativeScheduleMatrix

set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeScheduleSemantics
open OAI.ExactFourier UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformFixedCoefficientCodec
open UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open scoped BigOperators Kronecker
noncomputable section

/-- A typed view of the real finite metadata. It stores no matrix, callback,
or assumed child execution. Its erasure is the actual printer's record list. -/
inductive Instruction where
 | initial
 | boundary (a : Invocation)
 | macro (a : Invocation) (v : EncodedMacro (fixedBlock a).width seedWidth)
 | translation
 | exchange
 | padding

def instructions : List Instruction :=
 .initial :: (fixedInvocations.map (fun a =>
  .boundary a :: (encodedBlock a).map (.macro a))).flatten ++
 [.translation,.exchange,.padding]

def Instruction.record (q : ℕ) : Instruction → Record
 | .initial => ⟨6,q,seedWidth,(TripleSchedule.Global.size ExplicitSeedBudget.h),W,0,ExplicitSeedBudget.roleBits,0,[]⟩
 | .boundary a => blockBoundary q a
 | .macro a v => macroRecord q (fixedBlock a).embedding v
 | .translation => (rawTerminalRecords[0]'(by decide)).withColumns q
 | .exchange => (rawTerminalRecords[1]'(by decide)).withColumns q
 | .padding => (rawTerminalRecords[2]'(by decide)).withColumns q

lemma terminal_records (q : ℕ) :
 [.translation,.exchange,.padding].map (Instruction.record q)=terminalRecords q := rfl

/-- The typed chronology erases to every printed opcode, including both
marker classes and the final padding descriptor. -/
theorem records_actual (q : ℕ) : instructions.map (Instruction.record q)=scheduleRecords q := by
 rw [schedule_chronology]
 unfold instructions
 simp only [List.map_cons,List.map_append,List.map_flatten,List.map_map]
 change Instruction.record q .initial ::
  (fixedInvocations.map (fun a => ((.boundary a :: (encodedBlock a).map (.macro a)).map (Instruction.record q)))).flatten ++
  [.translation,.exchange,.padding].map (Instruction.record q)=_
 rw [terminal_records]
 congr 2
 apply congrArg List.flatten
 apply congrArg (fun f => fixedInvocations.map f)
 funext a
 simp only [List.map_cons,List.map_map,Instruction.record,blockRecords,Function.comp_def]

def activeEmbedding (q : ℕ) : Fin ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m)) ↪ Fin (W*2^(q*m)) :=
 Function.Embedding.inl.trans
  (PaddingWords.blockCoordinates (q*m)
    (PaddingWords.paddingRoles (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
      MasterBudget.seed_actual_padding)).toEmbedding
def paddingEmbedding (q : ℕ) : Fin ((2^ExplicitSeedBudget.roleBits-(TripleSchedule.Global.size ExplicitSeedBudget.h))*2^(q*m)) ↪ Fin (W*2^(q*m)) :=
 Function.Embedding.inr.trans
  (PaddingWords.blockCoordinates (q*m)
    (PaddingWords.paddingRoles (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
      MasterBudget.seed_actual_padding)).toEmbedding

def activeWord (q : ℕ) (T : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m)))) :
 List (WordStep C (W*2^(q*m))) :=
 TensorWords.embeddedWord (activeEmbedding q)
  (PaddingWords.canonicalNetworkWord (TripleSchedule.Global.size ExplicitSeedBudget.h) (q*m) T)

lemma activeWord_append (q : ℕ) (T U : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m)))) :
 activeWord q (T++U)=activeWord q T++activeWord q U := by
 simp only [activeWord,PaddingWords.canonicalNetworkWord,TypedKernelWords.relabelWord,
  TensorWords.embeddedWord,List.map_append]
lemma activeWord_flatten (q : ℕ)
 (Ts : List (List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m))))) :
 activeWord q Ts.flatten=(Ts.map (activeWord q)).flatten := by
 induction Ts with
 | nil => rfl
 | cons T Ts ih =>
  simp only [List.flatten_cons,activeWord_append,List.map_cons,ih]

def Instruction.word (q : ℕ) : Instruction → List (WordStep C (W*2^(q*m)))
 | .initial => []
 | .boundary _ => []
 | .macro a v => activeWord q
    (TripleSchedule.Global.liftWord (fixedBlock a).embedding ((decodeMacro v).compile q))
 | .translation => activeWord q
    [.monomial
      (TerminalWords.translationMatrix (TripleSchedule.Global.coordinates ExplicitSeedBudget.h)
        (TripleColumnAction.globalDirection q))
      (TerminalWords.translationMatrix_monomial _ _)]
 | .exchange => activeWord q
    [.monomial
      (TerminalWords.exchangeMatrix (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (q*m))
      (TerminalWords.exchangeMatrix_monomial _ _)]
 | .padding => TensorWords.embeddedWord (paddingEmbedding q)
    (PaddingWords.ordinaryCopiesWord (2^ExplicitSeedBudget.roleBits-(TripleSchedule.Global.size ExplicitSeedBudget.h)) (q*m))

def compile (q : ℕ) (is : List Instruction) : List (WordStep C (W*2^(q*m))) :=
 (is.map (Instruction.word q)).flatten

lemma lift_flatten {a R k : ℕ} (e : Fin a ↪ Fin R)
 (Ts : List (List (WordStep C (a*2^k)))) :
 TripleSchedule.Global.liftWord e Ts.flatten=
 (Ts.map (TripleSchedule.Global.liftWord e)).flatten := by
 simp only [TripleSchedule.Global.liftWord,TensorWords.embeddedWord,List.map_flatten]
 rfl

lemma macro_words {a : ℕ} (q : ℕ) (e : Fin a ↪ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
 (vs : List (EncodedMacro a m)) :
 (vs.map (fun v => activeWord q (TripleSchedule.Global.liftWord e ((decodeMacro v).compile q)))).flatten=
 activeWord q (TripleSchedule.Global.liftWord e (compileTape q (vs.map decodeMacro))) := by
 unfold compileTape
 rw [lift_flatten,activeWord_flatten]
 simp only [List.map_map,Function.comp_def]

/-- Opaque type boundaries retain the printer's decoded terms while exposing
one canonical dimension to the typed compiler. They perform no traversal. -/
def blockAtM (q : ℕ) (a : Invocation) : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m))) := decodedBlockWord q a
def masterAtM (q : ℕ) : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m))) := decodedMasterWord q
def correctionAtM (q : ℕ) : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m))) :=
 TerminalWords.correctionWord (TripleSchedule.Global.coordinates ExplicitSeedBudget.h)
  (TripleColumnAction.globalDirection q)
def correctedAtM (q : ℕ) : List (WordStep C ((TripleSchedule.Global.size ExplicitSeedBudget.h)*2^(q*m))) := decodedCorrectedWord q
lemma masterAtM_chronology (q : ℕ) : masterAtM q=(fixedInvocations.map (blockAtM q)).flatten := rfl
lemma correctedAtM_chronology (q : ℕ) : correctedAtM q=masterAtM q++correctionAtM q := rfl
lemma correctedAtM_actual (q : ℕ) : correctedAtM q=correctedWord q := decodedCorrectedWord_actual q

def paddedAtM (q : ℕ) : List (WordStep C (W*2^(q*m))) :=
 PaddingWords.fillWord (q*m)
  (PaddingWords.paddingRoles (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits MasterBudget.seed_actual_padding)
  (PaddingWords.canonicalNetworkWord (TripleSchedule.Global.size ExplicitSeedBudget.h) (q*m) (correctedAtM q))

lemma macro_block (q : ℕ) (a : Invocation) :
 compile q (.boundary a :: (encodedBlock a).map (.macro a))=
 activeWord q (blockAtM q a) := by
 simp only [compile,List.map_cons,Instruction.word,List.flatten_cons,List.nil_append,
  List.map_map,Function.comp_def]
 exact macro_words q (fixedBlock a).embedding (encodedBlock a)

lemma compile_cons (q : ℕ) (i : Instruction) (is : List Instruction) :
 compile q (i::is)=i.word q++compile q is := rfl
lemma compile_append (q : ℕ) (is js : List Instruction) :
 compile q (is++js)=compile q is++compile q js := by
 simp only [compile,List.map_append,List.flatten_append]
lemma compile_flatten (q : ℕ) (iss : List (List Instruction)) :
 compile q iss.flatten=(iss.map (compile q)).flatten := by
 induction iss with
 | nil => rfl
 | cons is iss ih =>
  change compile q (is++iss.flatten)=compile q is++(iss.map (compile q)).flatten
  rw [compile_append,ih]
lemma compile_terminal (q : ℕ) :
 compile q [.translation,.exchange,.padding]=
 activeWord q (correctionAtM q)++Instruction.word q .padding := by
 rw [compile_cons,compile_cons,compile_cons]
 change activeWord q [_]++(activeWord q [_]++(Instruction.word q .padding++[]))=_
 rw [List.append_nil,←List.append_assoc,←activeWord_append]
 rfl

/-- Compilation of each typed descriptor preserves the exact word chronology,
including translation before signed exchange and padding last. -/
theorem compile_actual (q : ℕ) : compile q instructions=paddedAtM q := by
 have blocks :
  compile q ((fixedInvocations.map (fun a => .boundary a :: (encodedBlock a).map (.macro a))).flatten)=
  activeWord q (masterAtM q) := by
  rw [compile_flatten]
  have fs :
   (fun a => compile q (.boundary a :: (encodedBlock a).map (.macro a)))=
   (fun a => activeWord q (blockAtM q a)) := by
   funext a
   exact macro_block q a
  simp only [List.map_map,Function.comp_def]
  rw [fs]
  rw [masterAtM_chronology,activeWord_flatten,List.map_map]
  rfl
 rw [instructions]
 change compile q (.initial :: (((fixedInvocations.map (fun a => .boundary a :: (encodedBlock a).map (.macro a))).flatten)++
  [.translation,.exchange,.padding]))=_
 rw [compile_cons]
 change []++compile q (((fixedInvocations.map (fun a => .boundary a :: (encodedBlock a).map (.macro a))).flatten)++
  [.translation,.exchange,.padding])=_
 rw [List.nil_append,compile_append,blocks,compile_terminal,←List.append_assoc,←activeWord_append]
 rw [←correctedAtM_chronology]
 rfl

theorem paddedAtM_actual (q : ℕ) : paddedAtM q=simultaneousWord q :=
 padding_congr MasterBudget.seed_actual_padding (correctedAtM q) (correctedWord q)
  (correctedAtM_actual q)

theorem compile_simultaneous (q : ℕ) : compile q instructions=simultaneousWord q :=
 (compile_actual q).trans (paddedAtM_actual q)

open UniformNativeScheduleMatrix

def semantic (q r : ℕ) (i : Instruction) :
 Matrix (Fin (W*2^(q*m+r))) (Fin (W*2^(q*m+r))) ℂ :=
 spectatorLift W (q*m) r (nativeMatrix W (q*m) (wordMatrix (i.word q)))

/-- Chronological interpretation, suitable for the actual record-loop induction.
This is algebra only; its hypotheses contain no alleged machine executions. -/
def interpret (q r : ℕ) (is : List Instruction)
 (X : Fin (W*2^(q*m+r))→ℂ) : Fin (W*2^(q*m+r))→ℂ :=
 is.foldl (fun Y i => (semantic q r i).mulVec Y) X

theorem interpret_compile (q r : ℕ) (is : List Instruction)
 (X : Fin (W*2^(q*m+r))→ℂ) : interpret q r is X=
 (spectatorLift W (q*m) r (nativeMatrix W (q*m) (wordMatrix (compile q is)))).mulVec X := by
 induction is generalizing X with
 | nil =>
  simp [interpret,compile,wordMatrix,nativeMatrix_one,spectatorLift_one]
 | cons i is ih =>
  change interpret q r is ((semantic q r i).mulVec X)=_
  rw [ih]
  simp only [compile,List.map_cons,List.flatten_cons,TypedKernelWords.wordMatrix_append,
    nativeMatrix_mul,spectatorLift_mul]
  rw [←Matrix.mulVec_mulVec]
  rfl

theorem interpret_actual (q r : ℕ) (X : Fin (W*2^(q*m+r))→ℂ) :
 interpret q r instructions X=
 (spectatorLift W (q*m) r
   (PaddingWords.copiesMatrix W (q*m) (physicalMatrix (q*m)))).mulVec X := by
 rw [interpret_compile,compile_simultaneous,simultaneousWord_matrix,native_copies]

/-- Every role and every high-bit spectator slice receives the physical low-bit
tensor, including arbitrary dirty auxiliary and padding arrays. -/
theorem interpret_array (q r : ℕ) (X : Fin W→Fin (2^(q*m+r))→ℂ)
 (i : Fin W) (s : Fin (2^r)) (z : Fin (2^(q*m))) :
 interpret q r instructions (RoleWords.arrayValues (q*m+r) X)
   (RoleWords.roleAddresses W (q*m+r) (i,(spectatorSplit (q*m) r).symm (s,z)))=
 (physicalMatrix (q*m)).mulVec
   (fun y => X i ((spectatorSplit (q*m) r).symm (s,y))) z := by
 rw [interpret_actual]
 exact spectator_copies_array W (q*m) r (physicalMatrix (q*m)) X i s z

end
end ExactFourierCircuits.UniformNativeScheduleSemantics
