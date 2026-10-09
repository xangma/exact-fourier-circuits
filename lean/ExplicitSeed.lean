import MasterBudget
import TripleColumnAction

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.4, Proposition 2.4, PDF p. 10; Appendix A, Lemma A.1, p. 25 (net:finite-interface, syn:local-certificate).
This is a symbolic finite word and a proved existential finite win. Its matrix identity and count concern the same chronological word; this file alone is not a running uniform machine.
-/

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
/- Paper: Proposition 2.4, p. 10: terminal translations and signed exchange are corrected on every arbitrary physical role. Lemma A.1, p. 25 then pads roles and applies the 71 role axes. -/
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
/- Paper: Lemma A.1, p. 25, supplies the finite certificate. Companion Finite tensor savings and exact Fourier circuits, Definition 2.1 and (2.1), p. 6, define this finite-win interface. -/
theorem witness : ∃ f : ℕ, f = ExplicitSeedBudget.columns ∧ 2 ≤ bits f ∧
    ∃ W : List (WordStep C (2 ^ bits f)), wordMatrix W = tensorPower C (bits f) ∧
      wordCalls W < bits f * 2 ^ (bits f - 1) :=
  ⟨ExplicitSeedBudget.columns, rfl, bits_at_least_two _ rfl, word _, word_matrix _, word_saves _ rfl⟩

theorem finiteWin_at_columns (f : ℕ) (hf : f = ExplicitSeedBudget.columns) : FiniteWinStatement :=
  ConstructiveBridge.finiteWin_of_word (bits_at_least_two f hf) (word f) (word_matrix f) (word_saves f hf)

/-- The explicit h=100 construction supplies the finite-win witness unconditionally. -/
theorem finiteWin : FiniteWinStatement := finiteWin_at_columns ExplicitSeedBudget.columns rfl

/-- Apply the upstream exact transfer to this constructed witness. -/
/- Paper: Companion Finite tensor savings and exact Fourier circuits, §3, pp. 10–15: the upstream finite-win transfer is a nonuniform circuit-existence result. Uniform operational execution is established in separate modules. -/
theorem main : MainStatement := win_to_fourier finiteWin

end
end ExactFourierCircuits.ExplicitSeed
