import UniformProducedCalendarMatrix
import UniformCalendarAxisAction
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§3.5, proof of Proposition 3.1, PDF pp. 17–18, especially (3.12)–(3.14); §4.3, Proposition 4.2 proof, p. 20 (`loc:three-kernel`, `loc:nonzero-shear`, `loc:nonzero-split`).

The common fixed C/diagonal word is represented by ordered calendar events. A local `Action` supplies both the dispatch order and matrix identity; the complete clock constructs this input from its retained cache, rather than assuming a desired Fourier output.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedCalendarAction
open UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
noncomputable section

def family {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (M:∀i,Matrix (Fin (radix n i)) (Fin (radix n i)) ℂ)
 (actual:∀i,UniformCalendarAxisAction.Action (radix n i) (es i) (M i)):
 UniformProducedAllAxisGeometry.Family n:=
 UniformProducedCalendarFamily.family hn es (fun i=>(actual i).position)

lemma rows {n:ℕ} (es:Fin (axisCount n)→List Event)
 (M:∀i,Matrix (Fin (radix n i)) (Fin (radix n i)) ℂ)
 (actual:∀i,UniformCalendarAxisAction.Action (radix n i) (es i) (M i)) (i:Fin (axisCount n)):
 allRows (radix n i) (es i)=List.ofFn (fun j:Fin (callTotal (radix n i) (es i))=>
  (((actual i).position ⟨j,0⟩).val,((actual i).position ⟨j,1⟩).val)):=
 (actual i).rows

/-- A genuine common389 Action on each axis closes the exact local matrix
premise of the actual physical K-to147 consumer, with its real workspace banks. -/
theorem local_matrices {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(UniformSynchronizedLayers.localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (radix n i) (es i)
  (UniformSynchronizedLayers.slot (UniformSynchronizedLayers.localSchedules n i) (length i) t).matrix):
 let f:=family hn es
  (fun i=>(UniformSynchronizedLayers.slot (UniformSynchronizedLayers.localSchedules n i) (length i) t).matrix) actual
 ∀i,Matrix.reindex (finCongr (UniformProducedAllAxisGeometry.shape f i))
  (finCongr (UniformProducedAllAxisGeometry.shape f i))
  (Matrix.diagonal (UniformProducedAllAxisAlignment.factors f i)*
   UniformMatchingKernelGeometry.localKernel
    ((UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).get i))=
  (UniformSynchronizedLayers.slot
   (UniformSynchronizedLayers.localSchedules n (UniformProducedAllAxisGeometry.index f i))
   (length (UniformProducedAllAxisGeometry.index f i)) t).matrix:=
 UniformProducedCalendarMatrix.local_matrices hn es (fun i=>(actual i).position) length t (fun i=>(actual i).matrix)
end
end ExactFourierCircuits.UniformProducedCalendarAction
