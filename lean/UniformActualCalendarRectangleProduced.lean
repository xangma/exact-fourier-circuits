import UniformActualCalendarRegistry
import UniformActualCalendarRectangleSnapshot
import UniformLocalCacheSlotGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleProduced
open UniformMachine UniformActualCalendarRegistry
open UniformLocalCacheSlotConductorMachine
open UniformLocalFactorDispatchMachine (BroadcastLayout)
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf c.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf c.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)
 (positive : 2≤c.ambient) (j : ℕ) (s : State)

/-- Exact witnesses retained by the real finite rectangle cache loop. -/
structure Data where
 slot : UniformLocalCacheChronology.Slot
 witness : SlotWitness c.height.K j slot
 layout : UniformForwardMatchingFactorPreparation.Layout (Header.forward (Cursor.shifted c j) q slot) B
 broadcast : BroadcastLayout (Cursor.shifted c j) q B
 contents : Contents (Cursor.shifted c j) q slot layout broadcast ha he bank positive s

theorem of_cached (actual : Cached (B:=B) c q ha he bank positive j s) :
 Nonempty (Data (B:=B) c q ha he bank positive j s):=by
 obtain ⟨slot,witness,l,bl,contents⟩:=actual
 exact ⟨⟨slot,witness,l,bl,contents⟩⟩

def phase (elapsed : ℕ) : UniformGlobalMatchingScaleMachine.Phase:=
 UniformGlobalMatchingScaleMachine.phases.get
  ⟨elapsed%28,by rw[UniformGlobalMatchingScaleMachine.phases_length];exact Nat.mod_lt _ (by decide)⟩

def Data.event (data : Data (B:=B) c q ha he bank positive j s) (elapsed : ℕ) : UniformGlobalCalendarDispatch.Event:=
 UniformActualCalendarRectangleEvent.actualEvent (Cursor.shifted c j) q data.slot data.layout
  data.broadcast ha he bank elapsed (phase elapsed)

/-- Genuine Cached contents construct the selector's event factory. -/
def Data.produced {O T : ℕ} (data : Data (B:=B) c q ha he bank positive j s)
 (kind : c.kind=0) (entry : (Cursor.shifted c j).cacheDirectory+7≤T)
 (pool : (Cursor.shifted c j).pool+9*c.ambient≤O)
 (permutation : (Cursor.shifted c j).cachePermutation+c.ambient≤T) (radix : c.ambient≤B) :
 Produced c.ambient O T B (Cursor.shifted c j).cacheDirectory (Cursor.shifted c j).time 0 s:=by
 refine ⟨data.event c q ha he bank positive j s,?_,?_,?_⟩
 · intro elapsed;rfl
 · intro elapsed;rfl
 · intro elapsed bound
   have below:elapsed<28:=by simpa only[UniformGlobalCalendarSelector.duration,ite_true] using bound
   have cache:=UniformActualCalendarRectangleEvent.ordinary_cached (Cursor.shifted c j) q data.slot
    data.layout data.broadcast ha he bank elapsed below s positive data.contents kind entry pool permutation radix
   change UniformGlobalCalendarDispatch.CachedEvent c.ambient O T B _ s at cache
   simpa only[Data.event,phase,Nat.mod_eq_of_lt below] using cache

end
end ExactFourierCircuits.UniformActualCalendarRectangleProduced
