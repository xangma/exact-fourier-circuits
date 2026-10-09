import UniformActualCalendarNativeFactor
import UniformActualCalendarMatchingSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarLocalSources
open OAI.ExactFourier UniformReplayPrint UniformToeplitzChunkWord UniformLayerSnapshot
open UniformGlobalCalendarDispatch UniformGlobalMatchingScaleMachine
open UniformGlobalMatchingScaleBankBridge UniformGlobalCalendarMatchingPhase
noncomputable section

/-- A single real event's elementary lane and ordered-call correspondence.
The all-event union is proved separately from these local facts. -/
structure Source {r v : ℕ} (e : Event) (S : Snapshot (Fin v)) (band : Fin v ↪ Fin r) where
 calls : Fin (callCount r e) ≃ S.calls.index
 records : ∀j,e.records j.val=
  ((band (S.calls.position ⟨calls j,0⟩)).val,(band (S.calls.position ⟨calls j,1⟩)).val)
 factor : ∀x:Fin r,phaseFactor e.phase e.factor x.val=(S.embed band).diagonal x

/-- Native factors and real ordered endpoint records imply the exact local
snapshot correspondence, for any occurrence enumeration. -/
def matching {r v R M D elapsed pool P kind : ℕ}
 (E : Fin M→UniformColoring.Edge) (mu : Fin M→ℂ)
 (hmE : UniformMatchingAxisTableMachine.Matching E) (capacity : M≤r)
 (bank : Fin R→ℂ) (W : List (ShearCode (Fin v) R)) (hm : Matching W)
 (band : Fin v ↪ Fin r) (order : Fin M ≃ Fin W.length)
 (left : ∀j,(E j).left=(band (W.get (order j)).dst).val)
 (right : ∀j,(E j).right=(band (W.get (order j)).src).val)
 (coefficient : ∀j,mu j=(W.get (order j)).coefficient.eval bank) (p : Phase) :
 Source (UniformActualCalendarMatchingSource.event (r:=r) D elapsed pool P kind p
   (fun lane (i:Fin r)=>nativeFactor E mu lane i.val) E)
  (phaseSnapshot bank W hm p) band:=by
 cases p with
 | diagonal lane=>
   refine ⟨Equiv.refl (Fin 0),?_,?_⟩
   · intro j;exact Fin.elim0 j
   · intro x
     change (if h:x.val<r then nativeFactor E mu lane (⟨x.val,h⟩:Fin r).val else 1)=
      Embedded.matrix band
       (Matrix.diagonal (fun i:Fin v=>nativeFactor (edges W) (coefficients bank W) lane i.val)) x x
     rw[dite_eq_left x.isLt]
     exact UniformActualCalendarNativeFactor.embedded E mu hmE bank W hm band order left right coefficient lane x
 | kernel=>
   have count:r-(r-M)=M:=by omega
   let callOrder : Fin (r-(r-M)) ≃ Fin W.length := (finCongr count).trans order
   refine ⟨callOrder,?_,?_⟩
   · intro j
     change UniformActualCalendarMatchingSource.endpoints E j.val=
      ((band (W.get (callOrder j)).dst).val,(band (W.get (callOrder j)).src).val)
     have bound:j.val<M:=by
      have jj:j.val<r-(r-M):=j.isLt
      omega
     rw[UniformActualCalendarMatchingSource.endpoints_at E j.val bound]
     exact Prod.ext (left ⟨j.val,bound⟩) (right ⟨j.val,bound⟩)
   · intro x
     change (1:ℂ)=Embedded.matrix band (Matrix.diagonal (fun _ : Fin v=>(1:ℂ))) x x
     rw[Matrix.diagonal_one,Embedded.matrix_one,Matrix.one_apply_eq]

end
end ExactFourierCircuits.UniformActualCalendarLocalSources
