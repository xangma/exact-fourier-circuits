import UniformFinalClockOverhead
import UniformFinalAxisPrinted

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalAxisCost
noncomputable section
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation UniformJointCacheAllocation
open UniformFinalClockOverhead
open UniformActualGlobalConstants (constants)

def prep (n:ℕ)(j:Fin (axisCount n)):ℕ:=
 UniformFourierAxisOperationalCases.budget (radix n j)
  (UniformAxisCacheForestEntry.rectangleCount constants n j)
  (UniformFinalAxisCacheBundle.nodes constants n j)

def selected {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (g:ℕ)(j:Fin (axisCount n)):ℕ:=(UniformFinalAxisPrinted.events hn cache g j).length

def axisCost {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (g:ℕ)(j:Fin (axisCount n)):ℕ:=
 prep n j+66*radix n j+233+selected hn cache g j*(9*radix n j+48)

/-- The genuine389 scan count and selected count are independently bounded
by actual retained cache capacity; no count/cost premise is supplied. -/
lemma bound {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (g:ℕ)(j:Fin (axisCount n)):
 axisCost hn cache g j≤axisScanBudget (radix n j):=by
 have counts:=UniformFinalAxisCacheSource.of_contents (cache j)
 have selected:=UniformFinalAxisPrinted.capacity hn cache g j
 apply axis_scan_bound (radix n j) (prep n j)
  (UniformCanonicalAxisCost.selected hn cache g j)
  (UniformAxisCacheForestEntry.rectangleCount constants n j+
   UniformCacheRangeSelector.total (UniformFinalAxisCacheBundle.nodes constants n j))
  (UniformFinalAxisCacheBundle.nodes constants n j).length
 · unfold prep UniformFourierAxisOperationalCases.budget
   omega
 · exact selected
 · exact counts.countFit
 · exact counts.nodesFit

end
end ExactFourierCircuits.UniformCanonicalAxisCost
