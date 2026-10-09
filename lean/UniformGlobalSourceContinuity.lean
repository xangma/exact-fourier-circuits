import UniformGlobalTickReturnedBank
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalSourceContinuity
open UniformMachine UniformKernelDiagonalBanks
noncomputable section

/-- Reprinting the next clock's physical axes changes the geometry record,
but the actual source tags stay in the common source/volume bank. -/
theorem source {W F R F' R':ℕ} (g:Kernel (W:=W) (F:=F) (R:=R))
 (h:Kernel (W:=W) (F:=F') (R:=R')) (s:State)
 (sameSource:h.packing.source=g.packing.source) (sameVolume:h.packing.volume=g.packing.volume)
 (ready:UniformGlobalRolePackingMachine.Source g.packing (UniformGlobalTickReturnedBank.values g s) s):
 UniformGlobalRolePackingMachine.Source h.packing (UniformGlobalTickReturnedBank.values h s) s:=by
 intro r hr j
 have old:=ready r hr (finCongr sameVolume j)
 simpa only[UniformGlobalTickReturnedBank.values,UniformExecutedTaggedBank.values,
  sameSource,sameVolume,finCongr_apply,Fin.val_cast] using old

lemma values {W F R F' R':ℕ} (g:Kernel (W:=W) (F:=F) (R:=R))
 (h:Kernel (W:=W) (F:=F') (R:=R')) (s:State)
 (sameSource:h.packing.source=g.packing.source) (sameVolume:h.packing.volume=g.packing.volume)
 (r:ℕ) (j:Fin h.packing.volume):
 UniformGlobalTickReturnedBank.values h s r j=
 UniformGlobalTickReturnedBank.values g s r (finCongr sameVolume j):=by
 simp only[UniformGlobalTickReturnedBank.values,UniformExecutedTaggedBank.values,
  sameSource,sameVolume,finCongr_apply,Fin.val_cast]
end
end ExactFourierCircuits.UniformGlobalSourceContinuity
