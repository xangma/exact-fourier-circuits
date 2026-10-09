import UniformCalendarExplicitLocalFamily

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarExplicitPreparedRender
noncomputable section
open OAI.ExactFourier TypedKernelWords UniformLayerSnapshot UniformBalancedToeplitz
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformGlobalCalendarUnion
open UniformCalendarRenderSnapshot UniformGlobalCalendarDispatch UniformCalendarPreparationOrder
open UniformCalendarRenderPieces UniformCalendarRenderPlan UniformCalendarRenderPosition
open UniformCalendarExplicitLocalFamily

abbrev Sources {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed start (ofPlan P o)) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed start (ofPlan P o)) t) :=
  LocalSources r es (fun i => S i) (treeEmbedding P o start t r extent) events

/-- Explicit local phases are compared only by matrix with the actual local
render, leaving their finite call indices and ordered endpoints explicit. -/
theorem render_matrix {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed start (ofPlan P o)) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed start (ofPlan P o)) t)
    (phase : ∀ i,(S i).matrix=(renderFamily P o start t f hf i).matrix)
    (h : Sources P o start t r extent es S events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
    if start≤t then Embedded.matrix (rootEmbedding v o r extent)
      (UniformCalendarRenderTick.tick (UniformLocalFourierLayers.render P f hf) (t-start)) else 1 := by
  rw [UniformCalendarPreparationOrder.matrix h]
  have same := family_matrix S (renderFamily P o start t f hf)
    (treeEmbedding P o start t r extent) phase
  exact same.trans (treeSnapshot_renderFamily P o start t r extent f hf)

/-- A generated explicit family transports the genuine calendar's descriptors. -/
def generatedFamily {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (S : Family ((calendar P o start f hf).map Piece.descriptor) t) :
    Family (treeTimed start (ofPlan P o)) t :=
  transport (calendar P o start f hf) (treeTimed start (ofPlan P o))
    (descriptors P o start f hf) t S

lemma generated_agreement {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (S : Family ((calendar P o start f hf).map Piece.descriptor) t)
    (phase : ∀ i,(S i).matrix=localPhaseMatrix (calendar P o start f hf) t i) :
    ∀ i,(generatedFamily P o start t f hf S i).matrix=(renderFamily P o start t f hf i).matrix :=
  transport_agreement (calendar P o start f hf) (treeTimed start (ofPlan P o))
    (descriptors P o start f hf) t S phase

/-- Only each actual local rendered tick is needed; no global output matrix or
call order for a classical choice appears in the inputs. -/
theorem generated_matrix {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family ((calendar P o start f hf).map Piece.descriptor) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed start (ofPlan P o)) t)
    (phase : ∀ i,(S i).matrix=localPhaseMatrix (calendar P o start f hf) t i)
    (h : Sources P o start t r extent es (generatedFamily P o start t f hf S) events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
    if start≤t then Embedded.matrix (rootEmbedding v o r extent)
      (UniformCalendarRenderTick.tick (UniformLocalFourierLayers.render P f hf) (t-start)) else 1 :=
  render_matrix P o start t r extent f hf es _ events
    (generated_agreement P o start t f hf S phase) h

abbrev AxisSources {r : ℕ} (P : Plan r) (t : ℕ)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed 0 (ofPlan P 0)) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan P 0)) t) :=
  Sources P 0 0 t r (by omega) es S events

theorem axis_matrix {r : ℕ} (P : Plan r) (t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed 0 (ofPlan P 0)) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan P 0)) t)
    (phase : ∀ i,(S i).matrix=(renderFamily P 0 0 t f hf i).matrix)
    (h : AxisSources P t es S events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformAllAxisCalendarTensor.axisSnapshot P f hf t).matrix := by
  rw [UniformCalendarPreparationOrder.matrix h]
  exact family_matrix S (renderFamily P 0 0 t f hf) (treeEmbedding P 0 0 t r (by omega)) phase

/-- Reflected forward cached phases implement the original upper epoch without
requiring their explicit call enumeration to equal a classically chosen one. -/
theorem reflected_matrix {r : ℕ} (left right d : Fin r → ℂ)
    (hl : ∀ i,left i≠0) (hr : ∀ i,right i≠0) (hd : ∀ i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (g : ℕ) (positive : 0<g) (upper : g≤(UniformLocalFourierLayers.toeplitz r f hf).length)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed 0 (ofPlan (plan r) 0)) ((UniformLocalFourierLayers.toeplitz r f hf).length-g))
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan (plan r) 0))
      ((UniformLocalFourierLayers.toeplitz r f hf).length-g))
    (phase : ∀ i,(S i).matrix=(renderFamily (plan r) 0 0
      ((UniformLocalFourierLayers.toeplitz r f hf).length-g) f hf i).matrix)
    (h : AxisSources (plan r) ((UniformLocalFourierLayers.toeplitz r f hf).length-g) es S events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformReflectedFourierCalendar.full left right d hl hr hd f hf g).matrix := by
  rw [UniformReflectedCalendarSource.upper_source left right d hl hr hd f hf g positive upper]
  exact axis_matrix (plan r) _ f hf es S events phase h

theorem forward_matrix {r : ℕ} (left right d : Fin r → ℂ)
    (hl : ∀ i,left i≠0) (hr : ∀ i,right i≠0) (hd : ∀ i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (active : t<(UniformLocalFourierLayers.toeplitz r f hf).length)
    (es : List UniformGlobalCalendarDispatch.Event)
    (S : Family (treeTimed 0 (ofPlan (plan r) 0)) t)
    (events : Fin es.length ≃ ActiveIndex (treeTimed 0 (ofPlan (plan r) 0)) t)
    (phase : ∀ i,(S i).matrix=(renderFamily (plan r) 0 0 t f hf i).matrix)
    (h : AxisSources (plan r) t es S events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (UniformReflectedFourierCalendar.full left right d hl hr hd f hf
        ((UniformLocalFourierLayers.toeplitz r f hf).length+4+t)).matrix := by
  rw [UniformReflectedCalendarSource.forward_source left right d hl hr hd f hf t active]
  exact axis_matrix (plan r) t f hf es S events phase h

/-- Every axis contributes its independently generated active phases at the
same tick; mixed phases require no common local slot or compiler alignment. -/
theorem tensor_render_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    {r : ι → ℕ} {T : ℕ} (P : ∀ i,Plan (r i)) (f : ∀ _i : ι,PowerSeries ℂ)
    (hf : ∀ i,PowerSeries.constantCoeff (f i)≠0)
    (length : ∀ i,(UniformLocalFourierLayers.render (P i) (f i) (hf i)).length≤T) (t : Fin T)
    (es : ι → List UniformGlobalCalendarDispatch.Event)
    (S : ∀ i,Family (treeTimed 0 (ofPlan (P i) 0)) t.val)
    (events : ∀ i,Fin (es i).length ≃ ActiveIndex (treeTimed 0 (ofPlan (P i) 0)) t.val)
    (phase : ∀ i j,(S i j).matrix=(renderFamily (P i) 0 0 t.val (f i) (hf i) j).matrix)
    (h : ∀ i,AxisSources (P i) t.val (es i) (S i) (events i)) :
    PiTensor.matrix (fun i =>
      Matrix.diagonal (fun x : Fin (r i) => foldValues (es i) (fun _ => 1) x.val) *
        Embedded.matrix (position (h i))
          (Matrix.blockDiagonal' (fun _ : Fin (callTotal (r i) (es i)) => C))) =
      UniformSynchronizedLayers.tensorSlot
        (fun i => UniformLocalFourierLayers.render (P i) (f i) (hf i)) length t := by
  calc
    _ = PiTensor.matrix (fun i => (UniformAllAxisCalendarTensor.axisSnapshot (P i) (f i) (hf i) t.val).matrix) := by
      apply congrArg PiTensor.matrix
      funext i
      exact axis_matrix (P i) t.val (f i) (hf i) (es i) (S i) (events i) (phase i) (h i)
    _ = _ := UniformAllAxisCalendarTensor.tensor_calendar P f hf length t

end
end ExactFourierCircuits.UniformCalendarExplicitPreparedRender
