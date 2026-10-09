import UniformRecursiveRootExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePreparedValues
open UniformMachine
noncomputable section

def Prepared {ι : Type*} (f : ι→Scalar) : Prop := ∀i,(f i).dependent=false
def Prepared2 {ι κ : Type*} (f : ι→κ→Scalar) : Prop := ∀i,Prepared (f i)

lemma axis {k : ℕ} (i : Fin k) (f : Fin (2^k)→Scalar) (h : Prepared f) :
 Prepared (UniformBinaryTensorCoordinates.axisAction k i f) := by
 intro z
 change (_ || _)=false
 rw [h _,h _]
 rfl

lemma axes {k : ℕ} (l : List (Fin k)) (f : Fin (2^k)→Scalar) (h : Prepared f) :
 Prepared (UniformBinaryTensorCoordinates.applyAxes k l f) := by
 induction l generalizing f with
 | nil => exact h
 | cons i l ih => exact ih _ (axis i f h)

lemma batch {k : ℕ} (f : Fin (2^k)→Scalar) (h : Prepared f) :
 Prepared (UniformBinaryBatchCMachine.transformed k f) := axes _ f h
lemma spectator {k b : ℕ} (f : Fin (2^k)→Scalar) (h : Prepared f) :
 Prepared (UniformBinarySpectatorCMachine.transformed k b f) := axes _ f h

lemma shear {R V : ℕ} (d source : Fin R) (c : ℂ) (f : Fin R→Fin V→Scalar)
 (h : Prepared2 f) : Prepared2 (UniformFixedNetworkShearChildMachine.shearValues d source c f) := by
 intro i j
 simp only [UniformFixedNetworkShearChildMachine.shearValues]
 split
 · change ((f d j).dependent || (f source j).dependent)=false
   rw [h d j,h source j]
   rfl
 · exact h i j

lemma exchange {R V : ℕ} (d source : Fin R) (f : Fin R→Fin V→Scalar)
 (h : Prepared2 f) : Prepared2 (UniformFixedNetworkExchangeChildMachine.values d source f) := by
 intro i j
 simp only [UniformFixedNetworkExchangeChildMachine.values]
 split
 · exact h source j
 · split
   · exact h d j
   · exact h i j

lemma exchanges {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
 (f : Fin R→Fin V→Scalar) (h : Prepared2 f) :
 Prepared2 (UniformNativeExchangeRecordMachine.actions ps f) := by
 induction ps generalizing f with
 | nil => exact h
 | cons p ps ih => exact ih _ (exchange p.first p.second f h)

lemma translation {R q w k : ℕ} (d : UniformNativeYRecordMachine.Direction R w)
 (f : Fin R→Fin (UniformResidualNativeTranslationMachine.volume k)→Scalar) (h : Prepared2 f) :
 Prepared2 (UniformNativeYRecordMachine.values q w k d f) := by
 intro i j
 simp only [UniformNativeYRecordMachine.values]
 split
 · exact h i _
 · exact h i j

lemma translations {R q w k : ℕ} (ds : List (UniformNativeYRecordMachine.Direction R w))
 (f : Fin R→Fin (UniformResidualNativeTranslationMachine.volume k)→Scalar) (h : Prepared2 f) :
 Prepared2 (UniformNativeYRecordMachine.actions q w k ds f) := by
 induction ds generalizing f with
 | nil => exact h
 | cons d ds ih => exact ih _ (translation d f h)

lemma selected {k q : ℕ} (qk : q≤k) (inv : Bool) (f : Fin (2^k)→Scalar)
 (h : Prepared f) : Prepared (UniformRecursiveResidualOutput.selected k q qk inv f) := by
 intro j
 unfold UniformRecursiveResidualOutput.selected
 split <;> exact h _
end
end ExactFourierCircuits.UniformRecursivePreparedValues
