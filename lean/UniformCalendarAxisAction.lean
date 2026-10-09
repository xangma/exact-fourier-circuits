import UniformCalendarPreparationOrder

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarAxisAction
noncomputable section
open OAI.ExactFourier UniformGlobalCalendarDispatch UniformCalendarPreparationOrder

/-- The common semantic result consumed by the real physical-axis printer.
Its injection follows the exact dispatcher's preparation order. -/
structure Action (r:ℕ)(es:List Event)(M:Matrix (Fin r) (Fin r) ℂ) where
 position:(Σ _:Fin (callTotal r es),Fin 2)↪Fin r
 rows:allRows r es=List.ofFn (fun i:Fin (callTotal r es)=>
  ((position ⟨i,0⟩).val,(position ⟨i,1⟩).val))
 matrix:Matrix.diagonal (fun x:Fin r=>foldValues es (fun _=>1) x.val)*
  Embedded.matrix position (Matrix.blockDiagonal' (fun _:Fin (callTotal r es)=>C))=M

def of_sources {σ:Type}[Fintype σ][DecidableEq σ]{v:σ→ℕ}{r:ℕ}{es:List Event}
 {S:∀i,UniformLayerSnapshot.Snapshot (Fin (v i))}{band:(Σi,Fin (v i))↪Fin r}
 {events:Fin es.length≃σ}(actual:LocalSources r es S band events):
 Action r es (union S band).matrix:=
 ⟨UniformCalendarPreparationOrder.position actual,allRows_position actual,
  UniformCalendarPreparationOrder.matrix actual⟩

def congr {r:ℕ}{es:List Event}{M N:Matrix (Fin r) (Fin r) ℂ}
 (actual:Action r es M)(eq:M=N):Action r es N:=
 ⟨actual.position,actual.rows,actual.matrix.trans eq⟩

end
end ExactFourierCircuits.UniformCalendarAxisAction
