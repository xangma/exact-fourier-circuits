import UniformActualCalendarDirectAlgebra
import UniformActualCalendarLocalSources

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectSource
open OAI.ExactFourier UniformMachine UniformLayerSnapshot UniformActualCalendarLocalSources
open UniformGlobalCalendarDispatch UniformGlobalMatchingScaleMachine UniformGlobalMatchingScaleBankBridge
open UniformCanonicalDirectPhase UniformActualCalendarDirectAlgebra UniformDirectLeafCacheReader
open UniformDirectLeafCacheSemanticExecution UniformActualCalendarDirectEvent
noncomputable section

variable {r:ℕ}{c:Config}{q:UniformTransposeDescriptorMachine.Record}{mu:ℂ}{positive:2≤r}{s:State}

def embed_source {u v:ℕ}(event:Event)(S:Snapshot (Fin u))(a:Fin u↪Fin v)(b:Fin v↪Fin r)
 (h:UniformActualCalendarLocalSources.Source event S (a.trans b)):
 UniformActualCalendarLocalSources.Source event (S.embed a) b:=by
 refine ⟨h.calls,h.records,?_⟩
 intro x
 change phaseFactor event.phase event.factor x.val=
  Embedded.matrix b (Matrix.diagonal (fun y=>Embedded.matrix a (Matrix.diagonal S.diagonal) y y)) x x
 rw[embedded_diagonal_comp]
 exact h.factor x

def pair_source (res:SemanticResult c r q mu positive s)(shear:q.kind=1)
 (e:Fin 2↪Fin r)(left:q.dest=(e 0).val)(right:q.source=(e 1).val)(elapsed:ℕ)(p:Phase):
 UniformActualCalendarLocalSources.Source (actualEvent res elapsed p) (pairPhase mu p) e:=by
 have count:res.count=1:=by rw[res.count_eq,shear];rfl
 cases p with
 | diagonal lane=>
  refine ⟨Equiv.refl (Fin 0),?_,?_⟩
  · intro j;exact Fin.elim0 j
  · intro x
    change (if hx:x.val<r then values res lane ⟨x.val,hx⟩ else 1)=
     Embedded.matrix e (Matrix.diagonal (UniformGlobalMatchingScaleMachine.factor mu lane)) x x
    rw[dite_eq_left x.isLt]
    simp only[values,shear,show ¬(1:ℕ)=0 by omega,ite_false]
    exact singleton_factor res.edges res.matching count e
     (fun j=>(res.endpoints j).1.trans left) (fun j=>(res.endpoints j).2.trans right) mu lane x
 | kernel=>
  have total:r-(r-res.count)=1:=by have:=positive;omega
  refine ⟨finCongr total,?_,?_⟩
  · intro j
    change UniformActualCalendarMatchingSource.endpoints res.edges j.val=((e 0).val,(e 1).val)
    have bound:j.val<res.count:=by
     have jj:j.val<r-(r-res.count):=j.isLt
     omega
    rw[UniformActualCalendarMatchingSource.endpoints_at _ _ bound]
    exact Prod.ext ((res.endpoints ⟨j.val,bound⟩).1.trans left) ((res.endpoints ⟨j.val,bound⟩).2.trans right)
  · intro x
    change (1:ℂ)=Embedded.matrix e (Matrix.diagonal (fun _ : Fin 2=>(1:ℂ))) x x
    rw[Matrix.diagonal_one,Embedded.matrix_one,Matrix.one_apply_eq]

def scale_source {v:ℕ}(res:SemanticResult c r q mu positive s)(scale:q.kind=0)
 (band:Fin v↪Fin r)(i:Fin v)(dest:q.dest=(band i).val)(nonzero:mu≠0)(elapsed:ℕ):
 UniformActualCalendarLocalSources.Source (actualEvent res elapsed (.diagonal 0))
  (Snapshot.ofDiagonal (fun j=>if j=i then mu else 1)
    (fun j=>by split_ifs;exact nonzero;exact one_ne_zero)) band:=by
 refine ⟨Equiv.refl (Fin 0),?_,?_⟩
 · intro j;exact Fin.elim0 j
 · intro x
   change (if hx:x.val<r then values res 0 ⟨x.val,hx⟩ else 1)=
    Embedded.matrix band (Matrix.diagonal (fun j=>if j=i then mu else 1)) x x
   rw[dite_eq_left x.isLt]
   simp only[values,scale,ite_true,UniformDirectLeafCacheScale.Value,Fin.val_zero,true_and,dest]
   exact scale_factor band i mu x

end
end ExactFourierCircuits.UniformActualCalendarDirectSource
