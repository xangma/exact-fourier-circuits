import UniformCanonicalRectanglePhase
import UniformCanonicalCacheSlotContext
import UniformCalendarRenderPlan

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalSelectedPhase
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformReplayPrint UniformLocalFourierLayers
open UniformWorkspacePlanner UniformBalancedToeplitz UniformLocalRectangleDescriptors
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry
open UniformCanonicalRectanglePhase
open UniformCalendarRenderTick

/-- The producer's actual rank kernels use the same coefficients as the normal
ragged rectangle render. -/
def rowBank (q : Row) (f : PowerSeries ℂ) : Fin (UniformToeplitzCrossDAG.bankSize (exponent q.a q.e))→ℂ:=
 UniformToeplitzCrossDAG.sharedBank (exponent q.a q.e)
  (UniformToeplitzCrossDAG.rankKernels (exponent q.a q.e) q.a q.e
   (fun i j=>ToeplitzLayers.cross q.split (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹)
    (q.i0+i) (q.j0+j))
   (fun i=>-PowerSeries.coeff (q.i0+i-q.split) f)
   (fun j=>PowerSeries.coeff (q.split-(q.j0+j)) f⁻¹))

lemma castPlacement_fit {e g h a v : ℕ} (eq : g=h)
 (source : Fin e↪Fin v) (target : Fin a↪Fin v) (separated : ∀i j,source i≠target j)
 (fitg : g+a+e≤v) (fith : h+a+e≤v) :
 castPlacement eq (placementOfFit source target separated fitg)=
 placementOfFit source target separated fith:=by
 subst h
 rfl

variable (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n))
 (q : Row) (k time : ℕ) (slot : UniformLocalCacheChronology.Slot) {B : ℕ}
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (context constants n axisIndex q k time) q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (context constants n axisIndex q k time) q slot).chunk.height)
 (l : UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (context constants n axisIndex q k time) q slot) B)

lemma normalPlacement_fit :
 normalPlacement (context constants n axisIndex q k time) q slot ha he l=
 placementOfFit (g:=(dag (context constants n axisIndex q k time) q slot ha he).size)
  (UniformChunkPortMachine.intervalEmbedding q.width q.j0 q.e l.chunk.sourceRange)
  (UniformChunkPortMachine.intervalEmbedding q.width q.i0 q.a l.chunk.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated l.chunk.sourceRange l.chunk.targetRange l.chunk.separated)
  (by
   rw[UniformActualCalendarWitnessSlots.size]
   have fit:=l.chunk.capacity
   change UniformCrossHeightPreparationMachine.gates
    (Header.forward (context constants n axisIndex q k time) q slot).chunk.height+q.e+q.a≤q.width at fit
   omega):=by
 unfold normalPlacement placement
 exact castPlacement_fit _ _ _ _ _ _

/-- All placement and DAG data are fixed by the canonical allocated context;
no coefficient action or rendered output is assumed. -/
theorem chunkRender_selected (hv : 0<selected q.width)
 (qa : q.a∈chunkSizes (q.width-q.width/2) (selected q.width))
 (qe : q.e∈chunkSizes (q.width/2) (selected q.width)) (f : PowerSeries ℂ) :
 chunkRender (context constants n axisIndex q k time) q slot ha he l
  (chunk_pos hv qe) (rowBank q f)=
 selectedSchedule hv qa qe
  (UniformChunkPortMachine.intervalEmbedding q.width q.j0 q.e l.chunk.sourceRange)
  (UniformChunkPortMachine.intervalEmbedding q.width q.i0 q.a l.chunk.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated l.chunk.sourceRange l.chunk.targetRange l.chunk.separated)
  (rowBank q f):=by
 unfold chunkRender
 rw[normalPlacement_fit]
 rfl

/-- Exact scalar-bank identity for the actual seed-height rank producer. -/
theorem rowBank_producer (f : PowerSeries ℂ) :
 rowBank q f=UniformToeplitzCrossDAG.sharedBank
  (UniformSeedRankCrossPreparation.parameters n axisIndex (UniformJointCacheWorkspace.original n q).seed).base.K
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedRankCrossPreparation.parameters n axisIndex (UniformJointCacheWorkspace.original n q).seed).base
   (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹)):=rfl

end
end ExactFourierCircuits.UniformCanonicalSelectedPhase
