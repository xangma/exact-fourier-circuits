import UniformActualCalendarWitnessSlots
import UniformLocalRectangleCacheBindings

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBroadcastSlots
open UniformReplayPrint UniformToeplitzChunkWord UniformDAGLayers UniformLocalCacheChronology
open UniformActualCalendarTypedSlots UniformActualCalendarBroadcastCodes
open UniformLocalFactorDispatchMachine (BroadcastLayout)
open UniformLocalCacheSlotConductorMachine (SlotWitness)
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row) (slot : Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)

lemma actual_gates {original : UniformSeedHeightPreparation.Config} {D A dest FD FF FU FJ : ℕ}
 (binding : UniformLocalRectangleCacheBindings.Bindings c q original D A dest FD FF FU FJ) :
 c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height:=by
 rw[binding.gates]
 simp only[Header.forward,UniformLocalCacheSlotHeaderMachine.forward,
  UniformLocalCacheSlotHeaderMachine.selectedHeight,UniformCrossHeightPreparationMachine.gates,
  UniformCrossHeightPreparationMachine.widthOf,binding.height,
  UniformLocalRectangleCacheBindings.P.actual,UniformLocalRectanglePhaseBanks.actual,
  UniformLocalRectangleBankMachine.geometry,
  UniformSeedHeightPreparation.Config.height,UniformSeedHeightPreparation.Config.gates,
  UniformSeedHeightPreparation.Config.width]

def codes := entries (R:=UniformToeplitzCrossDAG.bankSize c.height.K) q slot c.gates bl.outputCount

theorem normal (gates : c.gates=UniformCrossHeightPreparationMachine.gates
  (Header.forward c q slot).chunk.height) (broadcast : slot.broadcast=true) (H : ℕ) :
 slotCodes c q slot H ha he=if slot.inverse then (codes c q slot bl).reverse else codes c q slot bl:=by
 have eq:=layer_entries c.height.K q.a q.e ha he q rfl rfl slot H broadcast
 have size: (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he).size=c.gates:=
  (UniformActualCalendarWitnessSlots.size c q slot ha he).trans gates.symm
 simpa only[slotCodes,codes,size] using eq

include ha he in
theorem stored {j : ℕ} (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) : ∀code∈codes c q slot bl,Stored q.e c.gates q.a code:=by
 have st:=UniformActualCalendarWitnessSlots.stored c q slot ha he h
 rw[normal c q slot bl ha he gates broadcast,←gates] at st
 cases inverse:slot.inverse <;>simp only[inverse,Bool.false_eq_true,ite_false,ite_true] at st
 · exact st
 · intro code hc;exact st code (List.mem_reverse.mpr hc)

include ha he in
theorem matching {j : ℕ} (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) : UniformDAGLayers.Matching (codes c q slot bl):=by
 have hm:=UniformActualCalendarWitnessSlots.matching c q slot ha he h
 rw[normal c q slot bl ha he gates broadcast] at hm
 cases inverse:slot.inverse <;>simp only[inverse,Bool.false_eq_true,ite_false,ite_true] at hm
 · exact hm
 · have back:=hm.reverse
   rw[List.reverse_reverse] at back
   exact back.imp (fun h=>⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩)

end
end ExactFourierCircuits.UniformActualCalendarBroadcastSlots
