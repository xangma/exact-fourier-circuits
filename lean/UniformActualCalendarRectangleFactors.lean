import UniformActualCalendarRectangleEvent
import UniformGlobalCalendarMatchingPhase

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleEvent
open UniformMachine UniformLocalFactorDispatchMachine
open UniformLocalCacheSlotConductorMachine
open UniformActualCalendarMatchingSource
open UniformGlobalMatchingScaleBankBridge
noncomputable section

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

/-- The actual selected typed coefficient in each real dispatcher branch. -/
def coefficients (i : Fin (printedRows c q slot l bl ha he).length) : ℂ:=
 if hb:slot.broadcast then (if slot.inverse then (-1:ℂ) else 1)
 else if hi:slot.inverse then
  UniformInverseMatchingFactorPreparation.selectedValue (Header.forward c q slot) l ha he bank
   ⟨i.val,by simpa only[printedRows,hb,Bool.false_eq_true,ite_false,hi,ite_true] using i.isLt⟩
 else
  UniformForwardMatchingFactorPreparation.selectedValue (Header.forward c q slot) l ha he bank
   ⟨i.val,by simpa only[printedRows,hb,Bool.false_eq_true,ite_false,hi] using i.isLt⟩

/-- Every actual cached lane has the matching word's native endpoint factors,
with1 on all coordinates not incident to its actual generated matching. -/
theorem values_native (lane : Fin 9) (i : Fin c.ambient) :
 values c q slot l bl ha he bank lane i=
 nativeFactor (edges c q slot l bl ha he) (coefficients c q slot l bl ha he bank) lane i.val:=by
 cases slot with
 | mk broadcast enabled inverse depth color=>
  cases broadcast <;>cases inverse <;>rfl

lemma values_nonzero (lane : Fin 9) (i : Fin c.ambient) :
 values c q slot l bl ha he bank lane i≠0:=by
 rw[values_native]
 exact UniformGlobalCalendarMatchingPhase.nativeFactor_nonzero _ _ _ _

lemma values_unused (lane : Fin 9) (i : Fin c.ambient)
 (unused : ∀j,¬UniformColoring.Incident (edges c q slot l bl ha he j) i.val) :
 values c q slot l bl ha he bank lane i=1:=by
 rw[values_native]
 exact nativeFactor_unused _ _ _ _ unused

end
end ExactFourierCircuits.UniformActualCalendarRectangleEvent
