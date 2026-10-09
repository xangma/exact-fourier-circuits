import UniformActualCalendarLocalSources
import UniformCalendarExplicitPreparedRender

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarExplicitSourceTransport
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformActualCalendarLocalSources
open UniformGlobalCalendarDispatch UniformCalendarPreparationOrder

lemma reindex_diagonal {a b r:ℕ}(S:Snapshot (Fin a))(e:Fin a≃Fin b)(band:Fin b↪Fin r):
 ((S.reindex e).embed band).diagonal=(S.embed (e.toEmbedding.trans band)).diagonal:=by
 funext x
 change Embedded.matrix band
  (Matrix.diagonal (fun y=>Embedded.matrix e.toEmbedding (Matrix.diagonal S.diagonal) y y)) x x=_
 rw[←UniformLayerRestriction.embedded_diagonal]
 exact congrArg (fun M=>M x x) (Embedded.matrix_comp e.toEmbedding band (Matrix.diagonal S.diagonal))

/-- Width casts preserve the same explicit ordered calls and actual lane
sources, with no comparison to a classically chosen call orientation. -/
def reindex {a b r:ℕ}{event:Event}{S:Snapshot (Fin a)}{band:Fin a↪Fin r}
 (h:Source event S band)(e:Fin a≃Fin b)(target:Fin b↪Fin r)
 (compatible:e.toEmbedding.trans target=band):Source event (S.reindex e) target where
 calls:=h.calls
 records:=by
  intro j
  change event.records j.val=
   (((e.toEmbedding.trans target) (S.calls.position ⟨h.calls j,0⟩)).val,
    ((e.toEmbedding.trans target) (S.calls.position ⟨h.calls j,1⟩)).val)
  rw[compatible]
  exact h.records j
 factor:=by
  intro x
  rw[reindex_diagonal,compatible]
  exact h.factor x

/-- Assemble elementary event sources without constraining their preparation
order or local occurrence enumeration. -/
def family {σ:Type}[Fintype σ][DecidableEq σ]{v:σ→ℕ}{r:ℕ}
 (es:List Event)(S:∀i,Snapshot (Fin (v i)))
 (band:(Σi,Fin (v i))↪Fin r)(events:Fin es.length≃σ)
 (actual:∀i,Source (es.get i) (S (events i)) ((Embedded.sigmaIn (events i)).trans band)):
 LocalSources r es S band events where
 calls:=fun i=>(actual i).calls
 records:=fun i j=>(actual i).records j
 factor:=fun i x=>(actual i).factor x

end
end ExactFourierCircuits.UniformCalendarExplicitSourceTransport
