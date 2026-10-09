import UniformFinalAxisSuffix
import UniformCalendarActionPosition
import UniformFourierAxisCanonicalActionFactory
import UniformFourierAxisCommonBounds

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisPrinted
open UniformMachine UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformActualGlobalConstants (constants)
open UniformCalendarPrintedPrefix
noncomputable section

def treeEvents {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)
 (i:Fin (axisCount n)):=
 (UniformFinalAxisCacheBundle.reference constants n hn i (cache i)).events

def events {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)
 (g:ℕ)(i:Fin (axisCount n)):=
 UniformFourierAxisCommonResult.events constants n g i (treeEvents hn cache i)

def action {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)
 (g:ℕ)(i:Fin (axisCount n)):
 UniformCalendarAxisAction.Action (radix n i) (events hn cache g i)
  (UniformReflectedFourierCalendar.specified (radix n i) g).matrix:=
 UniformFourierAxisCanonicalActionFactory.action constants n hn i (cache i) g

def position {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)
 (g:ℕ)(i:Fin (axisCount n)):= (action hn cache g i).position

lemma capacity {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)
 (g:ℕ)(i:Fin (axisCount n)):
 (events hn cache g i).length≤UniformJointCacheExtent.capacity (radix n i):=
 UniformFourierAxisCommonBounds.reference_events_length (cache i)

lemma banks {n g:ℕ}{hn:0<n}{original s v u:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (j:Fin (axisCount n)){x:Fin n→ℂ}
 (actual:UniformFourierAxisCommonResult.Result constants n g j (treeEvents hn cache j) x s v)
 (out:UniformFinalAxisSuffix.Output hn j (treeEvents hn cache j) x s v actual u):
 AxisBanks hn (events hn cache g) (position hn cache g) j u:=by
 have pos:(UniformFinalAxisSuffix.selectedAction actual).position=(action hn cache g j).position:=
  UniformCalendarActionPosition.unique (UniformFinalAxisSuffix.selectedAction actual) (action hn cache g j)
 have axis:UniformFinalAxisSuffix.physicalAxis hn actual=
  physical hn (events hn cache g) (position hn cache g) j:=by
  exact congrArg (fun p:(Σ _:Fin (callTotal (radix n j) (events hn cache g j)),Fin 2) ↪ Fin (radix n j)=>
   UniformMatchingAxisTableMachine.physicalAxis (radix n j) (UniformFourierAxisWorkspace.axis constants n j).widths
    (UniformFourierAxisWorkspace.axis constants n j).permutation (UniformMatchingKernelAmbient.edges p)
    (UniformMatchingKernelAmbient.matching p) (UniformMatchingKernelAmbient.range p)
    (UniformFourierAxisGeometry.geometry constants hn j).radix) pos
 exact ⟨axis ▸ out.row,axis ▸ out.widths,axis ▸ out.permutations,out.directoryCells,out.pool⟩

end
end ExactFourierCircuits.UniformFinalAxisPrinted
