import UniformGlobalClockTickExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTickReturnedBank
open UniformMachine UniformKernelDiagonalBanks
noncomputable section
attribute [local irreducible] Nat.add

/-- Projection of actual stored result tags, used as the next clock's input.
It allocates nothing and writes no replacement data. -/
def values {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (s:State)
 (r:ℕ) (j:Fin g.packing.volume):Scalar:=
 UniformExecutedTaggedBank.values g.packing.source g.packing.volume s r j.val

lemma source_and_value {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (sourceEq:g.packing.source=d.tensor.source)
 (v:ℕ→Fin g.packing.volume→Scalar) (s:State)
 (produced:∀r,r < W→∀j:Fin d.packing.volume,
  (s.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v r j)):
 UniformGlobalRolePackingMachine.Source g.packing (values g s) s ∧
 (∀r,r < W→∀j:Fin g.packing.volume,(values g s r j).value=
  UniformDiagonalReturnNumeric.multiplier d (finCongr links.volume j)*
   kernelValue g d links v r (finCongr links.volume j)):=by
 have volume:g.packing.volume=d.tensor.volume:=links.volume.trans d.volume
 have actual (r:ℕ) (hr:r < W) (j:Fin g.packing.volume):
  (s.scalarHeap (g.packing.source+r*g.packing.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d (finCongr links.volume j)*
    kernelValue g d links v r (finCongr links.volume j)):=by
  simpa only[sourceEq,volume,finCongr_apply,Fin.val_cast] using produced r hr (finCongr links.volume j)
 exact ⟨fun r hr j=>UniformExecutedTaggedBank.present (actual r hr j),
  fun r hr j=>UniformExecutedTaggedBank.value (actual r hr j)⟩
end
end ExactFourierCircuits.UniformGlobalTickReturnedBank
