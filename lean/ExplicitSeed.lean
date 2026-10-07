import MasterBudget
import TripleColumnAction

set_option autoImplicit false

/- A closed witness assembled from the actual chronological network word.
   The column parameter remains symbolic in intermediate word and matrix types. -/
namespace ExactFourierCircuits.ExplicitSeed
open OAI.ExactFourier
noncomputable section

theorem h_large : 7 ≤ ExplicitSeedBudget.h := by
  norm_num [ExplicitSeedBudget.h]

def bits (f : ℕ) : ℕ := ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.h ^ 3

/-- The literal h=100 master, physical correction, canonicalization, padding and role axes. -/
def word (f : ℕ) : List (WordStep C (2 ^ bits f)) :=
  MasterBudget.actualSeedWord f h_large (TripleSchedule.Global.coordinates ExplicitSeedBudget.h)
    (TripleColumnAction.globalDirection f)

/-- Correctness is proved for every column count, on the same literal word used for the count. -/
theorem word_matrix (f : ℕ) : wordMatrix (word f) = tensorPower C (bits f) := by
  unfold word MasterBudget.actualSeedWord bits
  apply PaddingWords.extendedWord_matrix
  change wordMatrix (TripleSchedule.Global.masterWordColumns f h_large ++
      TerminalWords.correctionWord (TripleSchedule.Global.coordinates ExplicitSeedBudget.h)
        (TripleColumnAction.globalDirection f)) = _
  rw [TerminalWords.master_terminal_bridge_of_endpoint
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection f)
    (TripleSchedule.Global.masterWordColumns f h_large) (TripleColumnAction.endpoint f)
    (TripleSchedule.Global.masterWordColumns_packed_endpoint f h_large)
    (TripleColumnAction.corrected_stages_endpoint h_large f), MasterBudget.ordinaryWord_matrix]

theorem word_calls (f : ℕ) (hf : f = ExplicitSeedBudget.columns) :
    wordCalls (word f) = ExplicitSeedBudget.calls (f * ExplicitSeedBudget.h ^ 3) :=
  MasterBudget.actualSeedWord_calls f hf h_large
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection f)

theorem word_saves (f : ℕ) (hf : f = ExplicitSeedBudget.columns) :
    wordCalls (word f) < bits f * 2 ^ (bits f - 1) :=
  MasterBudget.actualSeedWord_saves f hf h_large
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection f)

theorem bits_eq (f : ℕ) (hf : f = ExplicitSeedBudget.columns) : bits f = ExplicitSeedBudget.bits := by
  unfold bits
  rw [← ExplicitSeedBudget.parameter_formulas.2.2.1, MasterBudget.seed_bits f hf]

theorem bits_at_least_two (f : ℕ) (hf : f = ExplicitSeedBudget.columns) : 2 ≤ bits f := by
  rw [bits_eq f hf]
  exact ExplicitSeedBudget.bits_at_least_two

/-- A closed existential seed, with no circuit-action or call-count hypotheses. -/
theorem witness : ∃ f : ℕ, f = ExplicitSeedBudget.columns ∧ 2 ≤ bits f ∧
    ∃ W : List (WordStep C (2 ^ bits f)), wordMatrix W = tensorPower C (bits f) ∧
      wordCalls W < bits f * 2 ^ (bits f - 1) :=
  ⟨ExplicitSeedBudget.columns, rfl, bits_at_least_two _ rfl, word _, word_matrix _, word_saves _ rfl⟩

theorem finiteWin_at_columns (f : ℕ) (hf : f = ExplicitSeedBudget.columns) : FiniteWinStatement :=
  ConstructiveBridge.finiteWin_of_word (bits_at_least_two f hf) (word f) (word_matrix f) (word_saves f hf)

/-- The explicit h=100 construction supplies the finite-win witness unconditionally. -/
theorem finiteWin : FiniteWinStatement := finiteWin_at_columns ExplicitSeedBudget.columns rfl

/-- Apply the upstream exact transfer to this constructed witness. -/
theorem main : MainStatement := win_to_fourier finiteWin

end
end ExactFourierCircuits.ExplicitSeed
