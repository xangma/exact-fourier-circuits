import UniformActualCalendarDirectSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectSource
open OAI.ExactFourier UniformMachine UniformLayerSnapshot UniformActualCalendarLocalSources
open UniformGlobalCalendarDispatch UniformGlobalMatchingScaleMachine UniformDirectToeplitz
open UniformCanonicalDirectPhase UniformDirectLeafCacheReader UniformDirectLeafCacheSemanticExecution
open UniformActualCalendarDirectEvent
noncomputable section

def operationValue {v:ℕ}(h:Fin v→ℂ)(hv:0<v):Operation v→ℂ
 | .scale _=>h ⟨0,hv⟩
 | .shear i j=>coefficient h i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩

/-- Actual descriptor endpoints and the retained scalar identity identify the
explicit direct-render phase; no output or action hypothesis is used. -/
def operation_source {r v:ℕ}{c:Config}{q:UniformTransposeDescriptorMachine.Record}{mu:ℂ}
 {positive:2≤r}{s:State}(res:SemanticResult c r q mu positive s)
 (h:Fin v→ℂ)(hv:0<v)(h0:h ⟨0,hv⟩≠0)(op:Operation v)(o K elapsed:ℕ)
 (band:Fin v↪Fin r)(coordinates:∀i,(band i).val=o+i.val)
 (descriptor:q=UniformTransposeDescriptorMachine.ofOperation o K op)
 (value:mu=operationValue h hv op):
 UniformActualCalendarLocalSources.Source (UniformActualCalendarDirectProduced.event res elapsed)
  (operationPhase h hv h0 op elapsed) band:=by
 cases op with
 | scale i=>
  have scale:q.kind=0:=by rw[descriptor];rfl
  have dest:q.dest=(band i).val:=by rw[descriptor];exact (coordinates i).symm
  have nz:mu≠0:=by rw[value];exact h0
  have result:=scale_source res scale band i dest nz elapsed
  have phaseEq:phase q elapsed=.diagonal 0:=by simp only[phase,scale,ite_true]
  change UniformActualCalendarLocalSources.Source (actualEvent res elapsed (phase q elapsed)) _ band
  rw[phaseEq]
  have snapshot:operationPhase h hv h0 (.scale i) elapsed=
   Snapshot.ofDiagonal (fun j=>if j=i then mu else 1)
    (fun j=>by split_ifs;exact nz;exact one_ne_zero):=by
   change scalePhase h hv h0 i=_
   simp only[value,operationValue,scalePhase]
  rw[snapshot]
  exact result
 | shear i j=>
  let source:Fin v:=⟨j.val,Nat.lt_trans j.isLt i.isLt⟩
  have ne:i≠source:=by
   intro eq
   have val:i.val=j.val:=congrArg Fin.val eq
   exact (ne_of_lt j.isLt) val.symm
  let pair:=Embedded.pair i source ne
  have shear:q.kind=1:=by rw[descriptor];rfl
  have left:q.dest=((pair.trans band) 0).val:=by
   change q.dest=(band i).val
   rw[descriptor]
   exact (coordinates i).symm
  have right:q.source=((pair.trans band) 1).val:=by
   change q.source=(band source).val
   rw[descriptor]
   exact (coordinates source).symm
  let p:=phase q elapsed
  have result:=embed_source (actualEvent res elapsed p) (pairPhase mu p) pair band
   (pair_source res shear (pair.trans band) left right elapsed p)
  have snapshot:operationPhase h hv h0 (.shear i j) elapsed=(pairPhase mu p).embed pair:=by
   have phaseEq:p=phases.get ⟨elapsed%28,by rw[phases_length];exact Nat.mod_lt _ (by decide)⟩:=by
    simp only[p,phase,shear,show ¬(1:ℕ)=0 by omega,ite_false]
   rw[phaseEq,value]
   rfl
  change UniformActualCalendarLocalSources.Source (actualEvent res elapsed p) _ band
  rw[snapshot]
  exact result

end
end ExactFourierCircuits.UniformActualCalendarDirectSource
