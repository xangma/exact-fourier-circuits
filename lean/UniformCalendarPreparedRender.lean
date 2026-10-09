import UniformCalendarPreparationOrder
import UniformReflectedCalendarSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPreparedRender
noncomputable section
open OAI.ExactFourier TypedKernelWords UniformLayerSnapshot UniformBalancedToeplitz
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformGlobalCalendarUnion
open UniformCalendarRenderSnapshot UniformGlobalCalendarDispatch UniformCalendarPreparationOrder

abbrev Sources {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed start (ofPlan P o)) t) :=
  LocalSources r es (renderFamily P o start t f hf) (treeEmbedding P o start t r extent) events

theorem render_matrix {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed start (ofPlan P o)) t)
    (h : Sources P o start t r extent f hf es events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
    if start≤t then Embedded.matrix (rootEmbedding v o r extent)
      (UniformCalendarRenderTick.tick (UniformLocalFourierLayers.render P f hf) (t-start)) else 1 := by
  rw [UniformCalendarPreparationOrder.matrix h]
  exact treeSnapshot_renderFamily P o start t r extent f hf

abbrev AxisSources {r : ℕ} (P : Plan r) (t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan P 0)) t) :=
  Sources P 0 0 t r (by omega) f hf es events

theorem axis_matrix {r : ℕ} (P : Plan r) (t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan P 0)) t)
    (h : AxisSources P t f hf es events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformAllAxisCalendarTensor.axisSnapshot P f hf t).matrix :=
  UniformCalendarPreparationOrder.matrix h

theorem axis_diagonal {r : ℕ} (P : Plan r) (t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan P 0)) t)
    (h : AxisSources P t f hf es events) (x : Fin r) :
    foldValues es (fun _ => 1) x.val =
      (UniformAllAxisCalendarTensor.axisSnapshot P f hf t).diagonal x :=
  foldValues_diagonal h x

/-- The upper epoch reuses forward cached sources at the reflected clock.
The source's ordinary elapsed and local call enumeration remain unchanged. -/
theorem reflected_matrix {r : ℕ} (left right d : Fin r → ℂ)
    (hl : ∀ i,left i≠0) (hr : ∀ i,right i≠0) (hd : ∀ i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (g : ℕ) (positive : 0<g) (upper : g≤(UniformLocalFourierLayers.toeplitz r f hf).length)
    (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan (plan r) 0))
      ((UniformLocalFourierLayers.toeplitz r f hf).length-g))
    (h : AxisSources (plan r) ((UniformLocalFourierLayers.toeplitz r f hf).length-g) f hf es events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformReflectedFourierCalendar.full left right d hl hr hd f hf g).matrix := by
  rw [UniformReflectedCalendarSource.upper_source left right d hl hr hd f hf g positive upper]
  exact axis_matrix (plan r) _ f hf es events h

theorem reflected_diagonal {r : ℕ} (left right d : Fin r → ℂ)
    (hl : ∀ i,left i≠0) (hr : ∀ i,right i≠0) (hd : ∀ i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (g : ℕ) (positive : 0<g) (upper : g≤(UniformLocalFourierLayers.toeplitz r f hf).length)
    (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan (plan r) 0))
      ((UniformLocalFourierLayers.toeplitz r f hf).length-g))
    (h : AxisSources (plan r) ((UniformLocalFourierLayers.toeplitz r f hf).length-g) f hf es events)
    (x : Fin r) :
    foldValues es (fun _ => 1) x.val =
      (UniformReflectedFourierCalendar.full left right d hl hr hd f hf g).diagonal x := by
  rw [UniformReflectedCalendarSource.upper_source left right d hl hr hd f hf g positive upper]
  exact axis_diagonal (plan r) _ f hf es events h x

theorem forward_matrix {r : ℕ} (left right d : Fin r → ℂ)
    (hl : ∀ i,left i≠0) (hr : ∀ i,right i≠0) (hd : ∀ i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (active : t<(UniformLocalFourierLayers.toeplitz r f hf).length)
    (es : List UniformGlobalCalendarDispatch.Event)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan (plan r) 0)) t)
    (h : AxisSources (plan r) t f hf es events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformReflectedFourierCalendar.full left right d hl hr hd f hf
        ((UniformLocalFourierLayers.toeplitz r f hf).length+4+t)).matrix := by
  rw [UniformReflectedCalendarSource.forward_source left right d hl hr hd f hf t active]
  exact axis_matrix (plan r) t f hf es events h

end
end ExactFourierCircuits.UniformCalendarPreparedRender
