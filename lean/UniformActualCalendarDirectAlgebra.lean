import UniformActualCalendarDirectProduced
import UniformCanonicalDirectPhase

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectAlgebra
open OAI.ExactFourier UniformLayerSnapshot UniformLayerRestriction UniformGlobalMatchingScaleBankBridge
open UniformGlobalMatchingScaleMachine UniformCanonicalDirectPhase
noncomputable section

lemma scale_factor {v r:ℕ} (band:Fin v↪Fin r)(i:Fin v)(mu:ℂ)(x:Fin r):
 (if x.val=(band i).val then mu else 1)=
 Embedded.matrix band (Matrix.diagonal (fun j=>if j=i then mu else 1)) x x:=by
 by_cases inside:x∈Set.range band
 · obtain ⟨y,rfl⟩:=inside
   rw[Embedded.matrix_on,Matrix.diagonal_apply_eq]
   have equality : (band y).val=(band i).val ↔ y=i:=
    ⟨fun eq=>band.injective (Fin.ext eq),fun eq=>congrArg (fun z:Fin v=>(band z).val) eq⟩
   simp only[equality]
 · rw[Embedded.matrix_off_row _ _ _ _ inside,ite_eq_left rfl]
   rw[ite_eq_right (by intro eq;exact inside ⟨i,Fin.ext eq.symm⟩)]

lemma singleton_factor {r M:ℕ}(E:Fin M→UniformColoring.Edge)(matching:UniformMatchingAxisTableMachine.Matching E)
 (one:M=1)(e:Fin 2↪Fin r)(left:∀j,(E j).left=(e 0).val)(right:∀j,(E j).right=(e 1).val)
 (mu:ℂ)(lane:Fin 9)(x:Fin r):
 nativeFactor E (fun _=>mu) lane x.val=Embedded.matrix e (Matrix.diagonal (factor mu lane)) x x:=by
 let j:Fin M:=⟨0,by omega⟩
 by_cases inside:x∈Set.range e
 · obtain ⟨side,rfl⟩:=inside
   rw[Embedded.matrix_on,Matrix.diagonal_apply_eq]
   fin_cases side
   · change nativeFactor E (fun _=>mu) lane (e 0).val=factor mu lane 0
     rw[←left j,nativeFactor_left E (fun _=>mu) matching lane j]
   · change nativeFactor E (fun _=>mu) lane (e 1).val=factor mu lane 1
     rw[←right j,nativeFactor_right E (fun _=>mu) matching lane j]
 · rw[Embedded.matrix_off_row _ _ _ _ inside,ite_eq_left rfl]
   apply nativeFactor_unused
   intro j incident
   rcases incident with eq|eq
   · exact inside ⟨0,Fin.ext ((left j).symm.trans eq)⟩
   · exact inside ⟨1,Fin.ext ((right j).symm.trans eq)⟩

lemma embedded_diagonal_comp {a b c:Type}[Fintype a][Fintype b][Fintype c]
 [DecidableEq a][DecidableEq b][DecidableEq c]
 (e:a↪b)(f:b↪c)(d:a→ℂ):
 Embedded.matrix f (Matrix.diagonal (fun x=>Embedded.matrix e (Matrix.diagonal d) x x))=
 Embedded.matrix (e.trans f) (Matrix.diagonal d):=by
 rw[←embedded_diagonal,Embedded.matrix_comp]

end
end ExactFourierCircuits.UniformActualCalendarDirectAlgebra
