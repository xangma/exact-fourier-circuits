import UniformSyntacticNatFrame
import UniformFixedNetworkLiteralDecoderMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelCallerPrinterSafety
open UniformMachine UniformAssembly UniformSyntacticNatFrame
noncomputable section

def Safe (i : Instruction) : Prop := match natDst i with
 | none => True
 | some d => d<6000 ∨ 6200≤d ∧d<6300
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

lemma safe_avoids {p : Program} (h:SafeProgram p) (j : ℕ)
 (kept:6000≤j ∧j<6200 ∨6300≤j) : Avoids p j := by
 intro i hi
 have hs:=h i hi
 intro bad
 rw [Safe,bad] at hs
 omega
end
end ExactFourierCircuits.UniformKernelCallerPrinterSafety
