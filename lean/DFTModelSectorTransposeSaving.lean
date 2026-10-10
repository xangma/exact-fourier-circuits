import DFTModelSectorTransposeProgram
import DFTModelSavingValidity
import DFTModelSavingPeakClosed

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a:
§4.2–4.3, Lemma 4.1 and Proposition 4.2, pp.19–20, invoke the
§2.6, Theorem 2.6, pp.11–12 tensor-power algorithm on each sector.
One complete role batch enters the same closed saving program once.
The readonly whole bank and sector geometry
are retained beside its compact result. Global sector metadata, native child
entry assembly and final whole-bank materialization remain separate. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean
noncomputable section

/-- The child is the actual closed saving AST, with no handler input. -/
def saving : Prog false (RawInput Tagged) (p (Context Tagged) (Ty.a Tagged)) :=
 .comp (argument Tagged)
  (.fork (.atom .fst) (.comp (.atom .snd) DFTModelSavingProgram.program))

attribute [local irreducible] argument DFTModelSavingProgram.program

theorem saving_value (q W V a : ℕ) (I : ℂ) (v : Tape Tagged.T) :
 (run saving ((q,I),((W,(V,a)),v))).val =
 ((((q,I),((W,(V,a)),v)),2^q),
  (run DFTModelSavingProgram.program
   ((q,I),gathered W V a (2^q) v Tagged.blank)).val) := by
 change ((run (argument Tagged) ((q,I),((W,(V,a)),v))).val.1,
  (run DFTModelSavingProgram.program
   (run (argument Tagged) ((q,I),((W,(V,a)),v))).val.2).val) = _
 rw [argument_value]

/-- All argument construction is charged; the child work occurs once. -/
theorem saving_work (q W V a : ℕ) (I : ℂ) (v : Tape Tagged.T) :
 (run saving ((q,I),((W,(V,a)),v))).work =
 61*(W*2^q)+8*q+74+
  (run DFTModelSavingProgram.program
   ((q,I),gathered W V a (2^q) v Tagged.blank)).work := by
 change (run (argument Tagged) ((q,I),((W,(V,a)),v))).work+
  (1+(1+(run DFTModelSavingProgram.program
   (run (argument Tagged) ((q,I),((W,(V,a)),v))).val.2).work+1)+1)+1 = _
 rw [argument_work,argument_value]
 dsimp only [Prod.snd]
 omega

theorem saving_valid (q W V a : ℕ) (I : ℂ) (v : Tape Tagged.T) :
 (run saving ((q,I),((W,(V,a)),v))).valid := by
 change (run (argument Tagged) ((q,I),((W,(V,a)),v))).valid ∧
  True ∧ (True ∧ (run DFTModelSavingProgram.program
   (run (argument Tagged) ((q,I),((W,(V,a)),v))).val.2).valid) ∧ True
 rw [argument_value]
 exact ⟨argument_valid _ _ _ _ _ _ _,trivial,
  ⟨trivial,DFTModelSavingValidity.program_valid _ _ _⟩,trivial⟩

theorem gathered_boolean (W V a T : ℕ) (v : Tape Tagged.T) (h : Boolean v) :
 Boolean (gathered W V a T v Tagged.blank) :=
 tab_boolean _ _ (fun _ _ => look_boolean h _)

/-- Actual full-role geometry supplies the closed child's polynomial peak;
neither a child action nor a child peak callback is a premise. -/
theorem saving_peak (q V a : ℕ) (I : ℂ) (v : Tape Tagged.T)
 (roles : 1 ≤ UniformBatching.width) (fit : a+2^q ≤ V) (before : Boolean v) :
 (run saving ((q,I),((UniformBatching.width,(V,a)),v))).peak ≤
 max (UniformBatching.width*V) (DFTModelSavingPeak.wholeCoeff*(2^q*2^q)) := by
 have outer := argument_peak Tagged q UniformBatching.width V a I v roles fit
 have child := DFTModelSavingPeak.program_peak_bound q I
  (gathered UniformBatching.width V a (2^q) v Tagged.blank) rfl
  (gathered_boolean _ _ _ _ _ before)
 simp only [saving,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
 change max (run (argument Tagged)
  ((q,I),((UniformBatching.width,(V,a)),v))).peak
  (run DFTModelSavingProgram.program
   (run (argument Tagged) ((q,I),((UniformBatching.width,(V,a)),v))).val.2).peak ≤ _
 rw [argument_value]
 exact max_le_max outer child

end
end ExactFourierCircuits.DFTModelSectorTranspose
