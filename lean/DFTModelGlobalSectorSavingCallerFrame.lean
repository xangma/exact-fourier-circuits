import DFTModelGlobalSectorSavingReturn
import UniformRecursiveStaticNatFrame
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorSavingCallerFrame
namespace HeaderSafety
open UniformMachine UniformAssembly UniformSyntacticNatFrame
noncomputable section

def Safe (i : Instruction) : Prop := match natDst i with
 | none => True
 | some d => d<4530 ∨ 4534≤d
instance (i : Instruction) : Decidable (Safe i) := by unfold Safe;split <;>infer_instance
def SafeProgram (p : Program) : Prop := ∀i∈p,Safe i

lemma checked (p : Program) (h:p.all (fun i=>decide (Safe i))=true) : SafeProgram p :=
 fun i hi=>of_decide_eq_true ((List.all_eq_true.mp h) i hi)
lemma append_safe {p q : Program} (hp:SafeProgram p) (hq:SafeProgram q) : SafeProgram (p++q) := by
 intro i hi
 rcases List.mem_append.mp hi with h|h
 · exact hp i h
 · exact hq i h
lemma relocated_safe {p : Program} (hp:SafeProgram p) (base ret : ℕ) :
 SafeProgram (p.map (relocate base ret)) := by
 intro i hi
 obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
 simpa only [Safe,relocate_dst] using hp a ha
lemma halt_safe : SafeProgram [.halt] := checked _ (by decide)

lemma printer_boot_safe : SafeProgram (UniformFixedNetworkScheduleMachine.boot.map UniformTensorMonomialMachine.Op.code) :=
 checked _ (by decide)
lemma printer_cells_safe (data : List ℕ) :
 SafeProgram ((UniformFixedNetworkScheduleMachine.cells data).map UniformTensorMonomialMachine.Op.code) := by
 induction data with
 | nil=>intro i hi;simp [UniformFixedNetworkScheduleMachine.cells] at hi
 | cons v vs ih=>
  have head:SafeProgram (([UniformTensorMonomialMachine.Op.literal 2602 v,
   .putNat 2601 2602,.add 2601 2601 2603]).map UniformTensorMonomialMachine.Op.code):=
   checked _ (by rfl)
  simpa only [UniformFixedNetworkScheduleMachine.cells,List.map_append] using append_safe head ih
lemma printer_safe (data : List ℕ) : SafeProgram (UniformFixedNetworkScheduleMachine.program data) := by
 simpa only [UniformFixedNetworkScheduleMachine.program,List.map_append] using
  append_safe (append_safe printer_boot_safe (printer_cells_safe data)) halt_safe

lemma decoder_setup_safe : SafeProgram (UniformFixedNetworkLiteralDecoderMachine.setup.map UniformTensorMonomialMachine.Op.code) :=
 checked _ (by decide)
lemma decoder_patches_safe (rs : List UniformFixedNetworkScheduleMachine.Record) :
 SafeProgram ((UniformFixedNetworkLiteralDecoderMachine.patches rs).map UniformTensorMonomialMachine.Op.code) := by
 induction rs with
 | nil=>intro i hi;simp [UniformFixedNetworkLiteralDecoderMachine.patches] at hi
 | cons r rs ih=>
  have head:SafeProgram (([UniformTensorMonomialMachine.Op.putNat 2700 2599,
   .literal 2701 r.data.length,.add 2700 2700 2701]).map UniformTensorMonomialMachine.Op.code):=
   checked _ (by rfl)
  simpa only [UniformFixedNetworkLiteralDecoderMachine.patches,List.map_append] using append_safe head ih
lemma decoder_safe (rs : List UniformFixedNetworkScheduleMachine.Record) :
 SafeProgram (UniformFixedNetworkLiteralDecoderMachine.program rs) := by
 simpa only [UniformFixedNetworkLiteralDecoderMachine.program,UniformAssembly.embed,List.nil_append,List.length_nil,
  UniformFixedNetworkLiteralDecoderMachine.patchBlock,List.map_append] using
  append_safe (relocated_safe (printer_safe (UniformFixedNetworkScheduleMachine.serialize rs)) 0
   (UniformFixedNetworkLiteralDecoderMachine.continuation rs))
  (append_safe (append_safe decoder_setup_safe (decoder_patches_safe rs)) halt_safe)

lemma reflexive_apply {α β : Type*} (f : α→β) (a : α) : f a=f a := Eq.refl _
lemma fixed_program_eq : UniformFixedNetworkLiteralDecoderMachine.fixedProgram=
 UniformFixedNetworkLiteralDecoderMachine.program UniformFixedNetworkScheduleMachine.baseSchedule :=
 reflexive_apply UniformFixedNetworkLiteralDecoderMachine.program UniformFixedNetworkScheduleMachine.baseSchedule
lemma fixed_decoder_safe : SafeProgram UniformFixedNetworkLiteralDecoderMachine.fixedProgram :=
 Eq.mp (congrArg SafeProgram fixed_program_eq.symm)
  (decoder_safe UniformFixedNetworkScheduleMachine.baseSchedule)

namespace P
export UniformRecursiveSavingProgram (Part piece program order)
end P

lemma finite_piece_safe (a : P.Part) (seed:a≠.seedPrinter) (unit:a≠.unitPrinter) :
 SafeProgram (P.piece a) := by
 cases a <;> first | contradiction | exact checked _ (by decide +kernel)

lemma piece_safe (a : P.Part) : SafeProgram (P.piece a) := by
 by_cases seed:a=.seedPrinter
 · subst a
   exact relocated_safe fixed_decoder_safe _ _
 by_cases unit:a=.unitPrinter
 · subst a
   exact relocated_safe (printer_safe UniformRecursiveSavingProgram.unitRecord.data) _ _
 exact finite_piece_safe a seed unit

lemma program_safe : SafeProgram P.program := by
 intro i hi
 change i∈P.order.flatMap P.piece at hi
 obtain ⟨a,_,hi⟩:=List.mem_flatMap.mp hi
 exact piece_safe a i hi

lemma program_avoids (j : ℕ) (lo:4530≤j) (hi:j<4534) : Avoids P.program j := by
 intro i mem bad
 have h:=program_safe i mem
 rw [Safe,bad] at h
 omega

end
end HeaderSafety

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelAdmissibilityControl
open UniformMachine UniformAssembly UniformSyntacticNatFrame
open DFTModelGlobalSectorSaving DFTModelSectorTranspose
open DFTModelSavingNativeRoot
noncomputable section

/-- Exact original child bytecode preserves the four transpose header registers. -/
theorem header_after_root {n B ticks : ℕ} {x : Fin n→ℂ} {s u : State}
 (actual : BoundedExecution UniformRecursiveSavingProgram.program n x B s ticks u)
 {W : ℕ} {inverse : Bool} (g : Native.Geometry W inverse) (h : Native.Header g s) :
 Native.Header g u := by
 constructor
 · rw [boundedExecution_preserves (HeaderSafety.program_avoids 4530 (by omega) (by omega)) actual]
   exact h.volume
 · rw [boundedExecution_preserves (HeaderSafety.program_avoids 4531 (by omega) (by omega)) actual]
   exact h.native
 · rw [boundedExecution_preserves (HeaderSafety.program_avoids 4532 (by omega) (by omega)) actual]
   exact h.directory
 · rw [boundedExecution_preserves (HeaderSafety.program_avoids 4533 (by omega) (by omega)) actual]
   exact h.ordinal

/-- The real original setup writes only its scratch and child ABI fields. -/
theorem cursor_ready {M E F i : ℕ} {s : State}
 (h : UniformSameProgramSectorLoop.Cursor M E F i s) :
 UniformSameProgramSectorLoop.Cursor M E F i (ready s) := by
 constructor <;>simp [ready,UniformTensorMonomialMachine.setPC,UniformSameProgramSectorLoop.setup,
  UniformTensorMonomialMachine.applyBlock,UniformTensorMonomialMachine.Op.apply,
  writeNat,next,h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five]

/-- Every original sector-loop cursor register lies in the proved untouched interval. -/
theorem cursor_after_root {n B ticks M E F i : ℕ} {x : Fin n→ℂ} {s u : State}
 (actual : BoundedExecution UniformRecursiveSavingProgram.program n x B (ready s) ticks u)
 (h : UniformSameProgramSectorLoop.Cursor M E F i s) :
 UniformSameProgramSectorLoop.Cursor M E F i u := by
 have h0:=cursor_ready h
 constructor
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5890 (by omega)]
   exact h0.count
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5891 (by omega)]
   exact h0.one
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5892 (by omega)]
   exact h0.index
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5893 (by omega)]
   exact h0.directory
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5894 (by omega)]
   exact h0.fresh
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5895 (by omega)]
   exact h0.zero
 · rw [UniformRecursiveStaticNatFrame.bounded_execution_frame actual 5896 (by omega)]
   exact h0.five

/-- The existing root Nat-heap frame retains the five real directory cells.
The directory extent is an ordinary allocation obligation. -/
theorem batch_after_root {n B q A F K ticks E buffer i : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {input input0 output output0 : Fin W→Fin (2^q)→Scalar}
 (result : Result n B q A F K x s s0 u u0 ticks input input0 output output0)
 (st : UniformSectorPacking.BlockState)
 (row : UniformSectorBatchDirectoryMachine.BatchCell W E buffer i st s)
 (fit : E+5*(i+1)≤F) :
 UniformSectorBatchDirectoryMachine.BatchCell W E buffer i st u := by
 rcases row with ⟨h0,h1,h2,h3,h4⟩
 refine ⟨?_,?_,?_,?_,?_⟩
 · rw [result.natHeap _ (by omega)];exact h0
 · rw [result.natHeap _ (by omega)];exact h1
 · rw [result.natHeap _ (by omega)];exact h2
 · rw [result.natHeap _ (by omega)];exact h3
 · rw [result.natHeap _ (by omega)];exact h4

/-- Both actual runs retain a preexisting higher return bank. Its exact Scalar
flags and values come from the real entry cells, not a completed scatter premise. -/
theorem bank_after_root {n B q A F K ticks : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {input input0 output output0 : Fin W→Fin (2^q)→Scalar}
 (result : Result n B q A F K x s s0 u u0 ticks input input0 output output0)
 (g : Native.Geometry W true) (width : g.sector.width=2^q)
 (base : g.buffer+W*g.sector.start=A) (fit : g.native+W*g.volume≤F)
 (old : Tape Tagged.T)
 (cells : ∀r,r<W→∀j,j<g.volume→∃a a0,
   s.scalarHeap (g.native+r*g.volume+j)=some a ∧
   s0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
   old.look (r*g.volume+j) Tagged.blank=encodePaired a a0) :
 ∀r,r<W→∀j,j<g.volume→∃a a0,
   u.scalarHeap (g.native+r*g.volume+j)=some a ∧
   u0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
   old.look (r*g.volume+j) Tagged.blank=encodePaired a a0 := by
 have sep : g.buffer+W*g.volume≤g.native := g.separation
 have extent:=Nat.mul_le_mul_left W g.fit
 rw [width,Nat.mul_add] at extent
 have endChild : A+W*2^q≤g.native := by omega
 intro r hr j hj
 have role:=Nat.mul_le_mul_right g.volume (show r+1≤W by omega)
 have address : g.native+r*g.volume+j<g.native+W*g.volume := by nlinarith
 obtain ⟨a,a0,ha,ha0,encoded⟩:=cells r hr j hj
 refine ⟨a,a0,?_,?_,encoded⟩
 · rw [result.scalarHeap _ (by omega) (Or.inr (by omega))];exact ha
 · rw [result.scalarHeap0 _ (by omega) (Or.inr (by omega))];exact ha0

/-- Existing reverse34 receives readiness derived from real child-entry
metadata and untouched physical cells. No source header writes are inserted.
Installing that higher destination before the root remains an outer-caller task. -/
theorem scatter_from_entry {n B q A F K ticks : ℕ} {x : Fin n→ℂ}
 {s s0 u u0 : State}
 {input input0 output output0 : Fin W→Fin (2^q)→Scalar}
 (result : Result n B q A F K x s s0 u u0 ticks input input0 output output0)
 (g : Native.Geometry W true) (bound : g.B=B) (width : g.sector.width=2^q)
 (base : g.buffer+W*g.sector.start=A)
 (directoryFit : g.directory+5*(g.ordinal+1)≤F) (bankFit : g.native+W*g.volume≤F)
 (old : Tape Tagged.T) (header : Native.Header g s)
 (row : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (cells : ∀r,r<W→∀j,j<g.volume→∃a a0,
   s.scalarHeap (g.native+r*g.volume+j)=some a ∧
   s0.scalarHeap (g.native+r*g.volume+j)=some a0 ∧
   old.look (r*g.volume+j) Tagged.blank=encodePaired a a0) :
 ∃v v0,Returned g old (DFTModelRecursiveScalarSource.paired output output0) x u u0 v v0 := by
 have h:=header_after_root result.actual g header
 have cell:=batch_after_root result g.sector row directoryFit
 have bank:=bank_after_root result g width base bankFit old cells
 exact scatter_execution result g bound width base old h cell
   (fun r hr j hj _=>bank r hr j hj)

end
end ExactFourierCircuits.DFTModelGlobalSectorSavingCallerFrame
