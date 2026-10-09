import UniformCalendarExplicitSourceTransport
import UniformCalendarAxisAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPulledSourceAction
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformCalendarPreparationOrder
open UniformCalendarRenderUnion UniformGlobalCalendarUnion UniformGlobalCalendarDispatch
open UniformCalendarAxisAction
open scoped BigOperators

variable {σ:Type}[Fintype σ][DecidableEq σ]{v:σ→ℕ}{r:ℕ}

def pullBand {es:List Event}(events:Fin es.length≃σ)(band:(Σi,Fin (v i))↪Fin r):
 (Σi:Fin es.length,Fin (v (events i)))↪Fin r:=
 (Equiv.sigmaCongrLeft events).toEmbedding.trans band

omit [Fintype σ] [DecidableEq σ] in
lemma pullBand_event {es:List Event}(events:Fin es.length≃σ)(band:(Σi,Fin (v i))↪Fin r)
 (i:Fin es.length):
 (Embedded.sigmaIn i).trans (pullBand events band)=(Embedded.sigmaIn (events i)).trans band:=by
 ext j
 rfl

lemma pulled_matrix {es:List Event}(events:Fin es.length≃σ)(band:(Σi,Fin (v i))↪Fin r)
 (S:∀i:Fin es.length,Snapshot (Fin (v (events i))))(T:∀i:σ,Snapshot (Fin (v i)))
 (phase:∀i,(S i).matrix=(T (events i)).matrix):
 (union S (pullBand events band)).matrix=(union T band).matrix:=by
 change ((UniformGlobalCalendarUnion.Snapshot.family S).embed (pullBand events band)).matrix=
  ((UniformGlobalCalendarUnion.Snapshot.family T).embed band).matrix
 rw[Snapshot.embed_matrix,Snapshot.embed_matrix,
  UniformGlobalCalendarUnion.Snapshot.family_matrix,UniformGlobalCalendarUnion.Snapshot.family_matrix,
  embedded_blocks_perturbations,embedded_blocks_perturbations]
 simp_rw[pullBand_event,phase]
 exact congrArg (fun M=>1+M) (Equiv.sum_comp events
  (fun i=>Embedded.matrix ((Embedded.sigmaIn i).trans band) (T i).matrix-1))

/-- Event order is the literal preparation order. Local phase agreement and
actual elementary sources suffice to transport its physical matrix. -/
def action {es:List Event}(events:Fin es.length≃σ)(band:(Σi,Fin (v i))↪Fin r)
 (S:∀i:Fin es.length,Snapshot (Fin (v (events i))))(T:∀i:σ,Snapshot (Fin (v i)))
 (actual:∀i,UniformActualCalendarLocalSources.Source (es.get i) (S i)
  ((Embedded.sigmaIn (events i)).trans band))
 (phase:∀i,(S i).matrix=(T (events i)).matrix):Action r es (union T band).matrix:=by
 let sources:LocalSources r es S (pullBand events band) (Equiv.refl _):=
  UniformCalendarExplicitSourceTransport.family es S (pullBand events band) (Equiv.refl _)
   (fun i=>by rw[pullBand_event];exact actual i)
 exact UniformCalendarAxisAction.congr (of_sources sources) (pulled_matrix events band S T phase)

end
end ExactFourierCircuits.UniformCalendarPulledSourceAction
