import UniformActualCalendarRectangleAtomResult
import UniformActualCalendarNodeAtomResult
import UniformCalendarNativeRootAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarAtomsResult
noncomputable section
open OAI.ExactFourier UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents UniformLocalCacheTreeMachine
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformCalendarRefinementActive UniformCalendarActualAtoms
open UniformGlobalCalendarUnion UniformGlobalCalendarGeometry UniformLocalCacheTiming UniformLocalFourierLayers UniformCalendarNativePieces
open UniformCalendarIntervalPartition UniformActualCalendarRectanglePhaseResult UniformCalendarAtomCollapse

attribute [local irreducible] Nat.add Nat.mul of_actual

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{R N:ℕ}
 {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:State}
 (g:Geometry constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N)
 (all:∀i (hi:i<(UniformAxisCacheRequestSource.requests visits).length),
  Complete constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N g i hi s)
 (forest:Contents p visits A positive s)(facts:Facts p visits)(hn:0<n)
 {O T:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤T)
 (radixRoom:radix n axisIndex≤envelope constants n)(sameRadix:p.radix=radix n axisIndex)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*UniformDirectLeafForestModel.demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*UniformDirectLeafForestModel.demand visits≤T)

/-- The actual native1/28 refinement is dispatched by its genuine macro kind.
Both branches consume only produced cache contents and their active interval. -/
def result (t:ℕ)(a:ActiveAtom (preparationEvents visits) (pieces n (preparationEvents visits)) t)
 (fit:Event.low ((preparationEvents visits).get a.val.1).event+
  Event.width ((preparationEvents visits).get a.val.1).event≤radix n axisIndex)
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta (radix n axisIndex)))≠0}
 (L:List (Layer (Event.width ((preparationEvents visits).get a.val.1).event)))
 (actual:Core (NewtonFourier.invH (zeta (radix n axisIndex))) hf
  ((preparationEvents visits).get a.val.1).event L):
 Result
  ((of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
   (UniformCalendarRefinementActive.order n (preparationEvents visits) a.val).val
   (t-((preparationEvents visits).get a.val.1).start-
    prefixDuration (pieces n (preparationEvents visits) a.val.1) a.val.2.val))
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex)
   (Event.low ((preparationEvents visits).get a.val.1).event)
   (Event.width ((preparationEvents visits).get a.val.1).event) fit)
  L (t-((preparationEvents visits).get a.val.1).start):=by
 rcases a with ⟨⟨index,slot⟩,active⟩
 generalize h:((UniformCalendarPreparationIndices.order visits).symm index)=code
 have eq:index=UniformCalendarPreparationIndices.order visits code:=by
  calc
   index=UniformCalendarPreparationIndices.order visits ((UniformCalendarPreparationIndices.order visits).symm index):=
    ((UniformCalendarPreparationIndices.order visits).apply_symm_apply index).symm
   _=UniformCalendarPreparationIndices.order visits code:=congrArg _ h
 subst index
 cases code with
 | inl i=>
  exact UniformActualCalendarRectangleAtomResult.result g all forest facts hn scalarRoom natRoom radixRoom
   sameRadix entry pool nat t i slot active fit L actual
 | inr pair=>
  rcases pair with ⟨i,j⟩
  exact UniformActualCalendarNodeAtomResult.result g all forest facts hn scalarRoom natRoom radixRoom
   sameRadix entry pool nat t i j slot active fit L actual

end
end ExactFourierCircuits.UniformActualCalendarAtomsResult
