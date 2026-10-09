import UniformFinalClockOuterCore

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOuterRetention
open UniformMachine
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants

lemma Frame.movement {n:ℕ}{s u:State}(hn:0<n)(h:UniformFinalMovementFrame.Frame n s u):
 Frame n s u:=by
 refine ⟨h.low hn,h.cache_heaps hn,?_,?_,?_,h.outputs,h.roots⟩
 · intro j;exact congrFun h.natHeap _
 · intro j;exact congrFun h.natHeap _
 · intro q hq
   by_cases lo:q<200
   · exact h.saved q (by unfold RequiredNat at hq;omega) (by unfold RequiredNat at hq;omega)
   · exact h.high q (by omega) (by unfold RequiredNat at hq;omega) (by unfold RequiredNat at hq;omega)

/-- The actual role loader rewrites 7300. Its returned storage equation, not
a syntactic nonwrite claim, closes that one field. -/
lemma Frame.role_of_storage {n:ℕ}{s u:State}(hn:0<n)(h:UniformFinalRoleExecution.Frame n s u)
 (storage:u.natReg 7300=s.natReg 7300):Frame n s u:=by
 refine ⟨h.low hn,h.cache_heaps hn,?_,?_,?_,h.outputs,h.roots⟩
 · intro j;exact congrFun h.natHeap _
 · intro j;exact congrFun h.natHeap _
 · intro q hq
   by_cases eq:q=7300
   · subst q;exact storage
   · exact h.natReg q
      (by unfold UniformFinalRoleExecution.R.Protected;unfold RequiredNat at hq;omega)
      (by unfold UniformFinalRoleExecution.H.Changed;unfold RequiredNat at hq;omega)

lemma Frame.role_of_table {n:ℕ}{x:Fin n→ℂ}{s u:State}(hn:0<n)
 (h:UniformFinalRoleExecution.Frame n s u)(old:UniformFinalPhysicalTablePrefix.Result n x s)
 (storage:u.natReg 7300=UniformKernelSpectrumStorage.base c n):Frame n s u:=
 role_of_storage hn h (storage.trans old.tableArgs.storage.symm)

lemma Spectrum.role {n:ℕ}{s u:State}(hn:0<n)(h:UniformFinalRoleExecution.Frame n s u):Spectrum n s u:=
 h.spectrum hn

end
end ExactFourierCircuits.UniformFinalClockOuterRetention
