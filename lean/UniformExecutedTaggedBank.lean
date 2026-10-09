import UniformConditionalKernelNumeric
set_option autoImplicit false
namespace ExactFourierCircuits.UniformExecutedTaggedBank
open UniformMachine
noncomputable section
/-- Proof-level projection of tags already present in an executed physical
bank. This definition performs no machine write or host data replacement. -/
def values (A V:ℕ) (s:State) (r j:ℕ):Scalar:=(s.scalarHeap (A+r*V+j)).getD Scalar.zero
lemma present {A V:ℕ} {s:State} {r j:ℕ} {z:ℂ}
 (h:(s.scalarHeap (A+r*V+j)).map Scalar.value=some z):
 s.scalarHeap (A+r*V+j)=some (values A V s r j):=by
 unfold values
 cases hs:s.scalarHeap (A+r*V+j) with
 | none=>simp only[hs,Option.map_none] at h;contradiction
 | some a=>rfl
lemma value {A V:ℕ} {s:State} {r j:ℕ} {z:ℂ}
 (h:(s.scalarHeap (A+r*V+j)).map Scalar.value=some z):
 (values A V s r j).value=z:=by
 have hp:=present h
 rw[hp] at h
 exact Option.some.inj h
lemma source {W:ℕ} (g:UniformGlobalTensorDiagonalMachine.Geometry W) (s:State)
 (v:ℕ→Fin g.volume→ℂ)
 (h:∀r,r<W→∀j:Fin g.volume,(s.scalarHeap (g.source+r*g.volume+j.val)).map Scalar.value=some (v r j)):
 UniformGlobalTensorDiagonalMachine.Source g (values g.source g.volume s) s:=by
 intro r hr j hj
 exact present (h r hr ⟨j,hj⟩)
end
end ExactFourierCircuits.UniformExecutedTaggedBank
