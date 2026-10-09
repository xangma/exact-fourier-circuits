import UniformActualCalendarPackedCodes
import UniformGlobalCalendarMatchingPhase

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNativeFactor
open OAI.ExactFourier UniformReplayPrint UniformToeplitzChunkWord
open UniformGlobalMatchingScaleBankBridge UniformGlobalCalendarMatchingPhase
noncomputable section

/-- Equality of the real factor bank with an embedded matching diagonal
follows from its enumerated endpoints and selected coefficients. -/
theorem embedded {r v R M : ℕ} (E : Fin M→UniformColoring.Edge) (mu : Fin M→ℂ)
 (matching : UniformMatchingAxisTableMachine.Matching E)
 (bank : Fin R→ℂ) (W : List (ShearCode (Fin v) R)) (hm : Matching W)
 (band : Fin v ↪ Fin r) (order : Fin M ≃ Fin W.length)
 (left : ∀j,(E j).left=(band (W.get (order j)).dst).val)
 (right : ∀j,(E j).right=(band (W.get (order j)).src).val)
 (coefficient : ∀j,mu j=(W.get (order j)).coefficient.eval bank)
 (lane : Fin 9) (x : Fin r) :
 nativeFactor E mu lane x.val=
 Embedded.matrix band
  (Matrix.diagonal (fun i:Fin v=>nativeFactor (edges W) (coefficients bank W) lane i.val)) x x:=by
 by_cases inside:x∈Set.range band
 · obtain ⟨y,rfl⟩:=inside
   rw[Embedded.matrix_on,Matrix.diagonal_apply_eq]
   by_cases incident:∃j,UniformColoring.Incident (E j) (band y).val
   · obtain ⟨j,hj|hj⟩:=incident
     · have eq:y=(W.get (order j)).dst:=band.injective (Fin.ext (hj.symm.trans (left j)))
       rw[eq,←left j,nativeFactor_left E mu matching lane j,coefficient j]
       exact (nativeFactor_left (edges W) (coefficients bank W) (edges_matching W hm) lane (order j)).symm
     · have eq:y=(W.get (order j)).src:=band.injective (Fin.ext (hj.symm.trans (right j)))
       rw[eq,←right j,nativeFactor_right E mu matching lane j,coefficient j]
       exact (nativeFactor_right (edges W) (coefficients bank W) (edges_matching W hm) lane (order j)).symm
   · rw[nativeFactor_unused E mu lane (band y).val (by intro j hj;exact incident ⟨j,hj⟩)]
     symm
     apply nativeFactor_unused
     intro j hj
     apply incident
     refine ⟨order.symm j,?_⟩
     rcases hj with eq|eq
     · left
       rw[left,Equiv.apply_symm_apply]
       exact congrArg (fun z:Fin v=>(band z).val) (Fin.ext eq)
     · right
       rw[right,Equiv.apply_symm_apply]
       exact congrArg (fun z:Fin v=>(band z).val) (Fin.ext eq)
 · rw[Embedded.matrix_off_row _ _ _ _ inside,ite_eq_left rfl]
   apply nativeFactor_unused
   intro j hj
   apply inside
   rcases hj with eq|eq
   · exact ⟨(W.get (order j)).dst,Fin.ext ((left j).symm.trans eq)⟩
   · exact ⟨(W.get (order j)).src,Fin.ext ((right j).symm.trans eq)⟩

end
end ExactFourierCircuits.UniformActualCalendarNativeFactor
