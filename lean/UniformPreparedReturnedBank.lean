import UniformGlobalTickReturnedBank
import UniformPreparedKernelAnyExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedReturnedBank
open UniformMachine UniformKernelDiagonalBanks
noncomputable section

lemma present {A V:ℕ} {s:State} {r j:ℕ}
 (tag:(s.scalarHeap (A+r*V+j)).map Scalar.dependent=some false):
 s.scalarHeap (A+r*V+j)=some (UniformExecutedTaggedBank.values A V s r j):=by
 unfold UniformExecutedTaggedBank.values
 cases q:s.scalarHeap (A+r*V+j) with
 | none=>simp[q] at tag
 | some z=>rfl

/-- A real collectively prepared output is the exact tagged source of the next
tick, including its stored false flags. No replacement bank is synthesized. -/
theorem source_and_prepared {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (sourceEq:g.packing.source=d.tensor.source) (s:State)
 (tags:∀r,r<W→∀j:Fin d.packing.volume,
  (s.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.dependent=some false):
 UniformGlobalRolePackingMachine.Source g.packing (UniformGlobalTickReturnedBank.values g s) s ∧
 (∀r,r<W→∀j:Fin g.packing.volume,(UniformGlobalTickReturnedBank.values g s r j).dependent=false):=by
 have volume:g.packing.volume=d.tensor.volume:=links.volume.trans d.volume
 have actual (r:ℕ) (hr:r<W) (j:Fin g.packing.volume):
  (s.scalarHeap (g.packing.source+r*g.packing.volume+j.val)).map Scalar.dependent=some false:=by
  simpa only[sourceEq,volume,finCongr_apply,Fin.val_cast] using tags r hr (finCongr links.volume j)
 exact ⟨fun r hr j=>present (actual r hr j),
  fun r hr j=>UniformPreparedKernelAnyExecution.projected_false (actual r hr j)⟩
end
end ExactFourierCircuits.UniformPreparedReturnedBank
