import UniformCanonicalSelectedPhase

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalPairPhase
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformLocalFourierLayers
open UniformWorkspacePlanner UniformBalancedToeplitz UniformLocalRectangleDescriptors
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry
open UniformCanonicalRectanglePhase UniformCanonicalSelectedPhase
open UniformCalendarRenderTick UniformCalendarRenderPlan
open UniformGlobalCalendarMatchingPhase UniformGlobalMatchingScaleMachine
open UniformLocalCacheSlotConductorMachine (SlotWitness)

theorem pairSource_interval (v : ℕ) (hv : 0<selected v)
 (j : Fin (chunkCount (v/2) (selected v)))
 (bound : j.val*selected v+UniformBalancedToeplitz.size (v/2) (selected v) j≤v) :
 pairSource v hv j=UniformChunkPortMachine.intervalEmbedding v (j.val*selected v)
  (UniformBalancedToeplitz.size (v/2) (selected v) j) bound:=by
 ext i
 rfl

theorem pairTarget_interval (v : ℕ) (hv : 0<selected v)
 (i : Fin (chunkCount (v-v/2) (selected v)))
 (bound : v/2+i.val*selected v+UniformBalancedToeplitz.size (v-v/2) (selected v) i≤v) :
 pairTarget v hv i=UniformChunkPortMachine.intervalEmbedding v (v/2+i.val*selected v)
  (UniformBalancedToeplitz.size (v-v/2) (selected v) i) bound:=by
 ext j
 change v/2+(i.val*selected v+j.val)=(v/2+i.val*selected v)+j.val
 omega

theorem selected_congr {v a e : ℕ} (hv : 0<selected v)
 (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
 (s1 s2 : Fin e↪Fin v) (t1 t2 : Fin a↪Fin v)
 (h1 : ∀i j,s1 i≠t1 j) (h2 : ∀i j,s2 i≠t2 j)
 (hs : s1=s2) (ht : t1=t2)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e))→ℂ) :
 selectedSchedule hv ha he s1 t1 h1 bank=selectedSchedule hv ha he s2 t2 h2 bank:=by
 subst s2
 subst t2
 rfl

variable (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n))
 (v o : ℕ) (hv : 0<selected v)
 (indices : Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v)))
 (k time : ℕ) (slot : UniformLocalCacheChronology.Slot) {B : ℕ}

abbrev pairRow:=row v o (selected v) indices.1.val indices.2.val
abbrev pairContext:=context constants n axisIndex (pairRow v o indices) k time

variable
 (ha : (pairRow v o indices).a≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot).chunk.height)
 (he : (pairRow v o indices).e≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot).chunk.height)
 (l : UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot) B)

/-- The allocated producer's canonical placement and rank bank produce exactly
this genuine pair piece's normal rendered schedule. -/
theorem pair_chunkRender (f : PowerSeries ℂ) :
 chunkRender (pairContext constants n axisIndex v o indices k time) (pairRow v o indices)
  slot ha he l (size_pos _ _ hv _) (rowBank (pairRow v o indices) f)=
 pairSchedule v hv f indices:=by
 rw[chunkRender_selected constants n axisIndex (pairRow v o indices) k time slot ha he l hv
  (size_mem _ _ indices.1) (size_mem _ _ indices.2)]
 apply selected_congr
 · exact (pairSource_interval v hv indices.2 l.chunk.sourceRange).symm
 · exact (pairTarget_interval v hv indices.1 l.chunk.targetRange).symm

/-- No local rendered matrix premise remains: actual slot chronology, the
actual rank bank, and the pair's printed placement determine this tick. -/
theorem pair_piece_phase_tick (f : PowerSeries ℂ) {j : ℕ}
 (h : SlotWitness (pairContext constants n axisIndex v o indices k time).height.K j slot)
 (p : Fin 28) :
 (phaseSnapshot (rowBank (pairRow v o indices) f)
  (typedSlot (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot
   (8*(pairContext constants n axisIndex v o indices k time).height.K+6) l ha he (size_pos _ _ hv _)
   (stored _ _ _ ha he h))
  (typedSlot_matching _ _ _ _ l ha he (size_pos _ _ hv _) (stored _ _ _ ha he h)
   (matching _ _ _ ha he h))
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick (pairPiece v hv o f indices).layers (28*j+p.val):=by
 have phase:=chunk_slot_tick (pairContext constants n axisIndex v o indices k time) (pairRow v o indices)
  slot ha he l (size_pos _ _ hv _) (rowBank (pairRow v o indices) f) h p
 have render:=pair_chunkRender constants n axisIndex v o hv indices k time slot ha he l f
 exact phase.trans (congrArg (fun L=>tick L (28*j+p.val)) render)

end
end ExactFourierCircuits.UniformCanonicalPairPhase
