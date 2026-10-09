import UniformFinalClockOuterDerivations
import UniformFinalClockOuterTable
import UniformFinalClockRuntime

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockOuterRetention
open UniformMachine
noncomputable section

/-- The two restored arena endpoints are execution postconditions. The other
runtime fields follow from the minimal retained-register predicate. -/
lemma Frame.runtime_transport {n:ℕ}{s u:State}(h:Frame n s u)
 (old:UniformFinalClockRuntime.Runtime n s)
 (natEnd:u.natReg 6819=s.natReg 6819)(scalarEnd:u.natReg 6821=s.natReg 6821):
 UniformFinalClockRuntime.Runtime n u:=by
 apply old.transport
 intro q hq
 by_cases a:q=6819
 · subst q;exact natEnd
 by_cases b:q=6821
 · subst q;exact scalarEnd
 exact h.natReg q (by unfold UniformFinalClockRuntime.Kept at hq;unfold RequiredNat;omega)

lemma Frame.movement_runtime {n:ℕ}{s u:State}(hn:0<n)
 (h:UniformFinalMovementFrame.Frame n s u)(old:UniformFinalClockRuntime.Runtime n s):
 UniformFinalClockRuntime.Runtime n u:=
 (Frame.movement hn h).runtime_transport old
 (h.high _ (by omega) (by omega) (by omega))
 (h.high _ (by omega) (by omega) (by omega))

lemma Frame.role_runtime {n:ℕ}{s u:State}(h:UniformFinalRoleExecution.Frame n s u)
 (old:UniformFinalClockRuntime.Runtime n s):UniformFinalClockRuntime.Runtime n u:=old.role h

lemma Spectrum.trans {n:ℕ}{s u v:State}(a:Spectrum n s u)(b:Spectrum n u v):Spectrum n s v:=
 fun j=>(b j).trans (a j)

lemma Spectrum.withPC {n:ℕ}{s u:State}(h:Spectrum n s u)(p:ℕ):Spectrum n s {u with pc:=p}:=h
lemma Spectrum.beforePC {n:ℕ}{s u:State}(h:Spectrum n s u)(p:ℕ):Spectrum n {s with pc:=p} u:=h

end
end ExactFourierCircuits.UniformFinalClockOuterRetention
