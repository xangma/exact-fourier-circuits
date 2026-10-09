import UniformActualCalendarOccurrences
import UniformActualCalendarBroadcastCodes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleEvent
open UniformMachine UniformLocalFactorDispatchMachine UniformLocalCacheSlotConductorMachine
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def occurrences := UniformActualCalendarOccurrences.actual
 (edges c q slot l bl ha he) (coefficients c q slot l bl ha he bank)

lemma constant_occurrences (rows : List UniformInPlaceMachine.Row) (mu : ℂ) :
 List.ofFn (fun i:Fin rows.length=>((rows.get i).dst,(rows.get i).src,mu))=
 rows.map (fun row=>(row.dst,row.src,mu)):=by
 have eq:=congrArg (List.map (fun row:UniformInPlaceMachine.Row=>(row.dst,row.src,mu))) (List.ofFn_get rows)
 simpa only[List.map_ofFn,Function.comp_def] using eq

lemma occurrences_forward (broadcast : slot.broadcast=false) (inverse : slot.inverse=false) :
 occurrences c q slot l bl ha he bank=
 UniformActualCalendarForwardCodes.occurrences (Header.forward c q slot) l ha he bank:=by
 cases slot with
 | mk b e i d color=>cases b <;>cases i <;>cases broadcast <;>cases inverse;rfl

lemma occurrences_inverse (broadcast : slot.broadcast=false) (inverse : slot.inverse=true) :
 occurrences c q slot l bl ha he bank=
 UniformActualCalendarInverseCodes.occurrences (Header.forward c q slot) l ha he bank:=by
 cases slot with
 | mk b e i d color=>cases b <;>cases i <;>cases broadcast <;>cases inverse;rfl

lemma occurrences_broadcast (broadcast : slot.broadcast=true) :
 occurrences c q slot l bl ha he bank=
 UniformActualCalendarBroadcastCodes.occurrences q slot c.gates c.height.P bl.capacity:=by
 cases slot with
 | mk b e i d color=>
   cases b <;>cases broadcast
   cases i <;>
    simp only[occurrences,UniformActualCalendarOccurrences.actual,edges,coefficients,
     printedRows,UniformGlobalMatchingScaleBankBridge.rowEdges,
     UniformActualCalendarBroadcastCodes.occurrences,
     Bool.false_eq_true,ite_false,ite_true,dite_true,dite_false]
   all_goals exact constant_occurrences _ _

end
end ExactFourierCircuits.UniformActualCalendarRectangleEvent
