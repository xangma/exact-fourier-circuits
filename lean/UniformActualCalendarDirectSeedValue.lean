import UniformActualCalendarDirectOperationSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectSource
open OAI.ExactFourier UniformDirectToeplitz UniformDirectLeafCacheSource
noncomputable section

def seedCoefficients (omega:ℂ)(v:ℕ):Fin v→ℂ:=
 fun i=>UniformLocalSeedTableMachine.seedValue omega 3 i.val

lemma seedCoefficients_invH (omega:ℂ)(v:ℕ):
 seedCoefficients omega v=fun i:Fin v=>PowerSeries.coeff i.val (NewtonFourier.invH omega):=by
 funext i
 norm_num [seedCoefficients,UniformLocalSeedTableMachine.seedValue,NewtonFourier.invH,PowerSeries.coeff_mk]


/-- Actual descriptor coefficient addresses select the exact lane3 value of
its genuine scale/shear, including both native subtraction operations. -/
lemma mu_ofOperation (r v o K:ℕ)(hv:0<v)(op:Operation v):
 mu r K (UniformTransposeDescriptorMachine.ofOperation o K op)=
 operationValue (seedCoefficients (zeta r) v) hv op:=by
 cases op with
 | scale i=>
  change UniformLocalSeedTableMachine.seedValue (zeta r) 3 (K-K)=_
  rw[Nat.sub_self]
  rfl
 | shear i j=>
  change UniformLocalSeedTableMachine.seedValue (zeta r) 3 (K+(i.val-j.val)-K)=_
  rw[show K+(i.val-j.val)-K=i.val-j.val by omega]
  rfl

lemma mu_invH_ofOperation (r v o K:ℕ)(hv:0<v)(op:Operation v):
 mu r K (UniformTransposeDescriptorMachine.ofOperation o K op)=
 operationValue (fun i:Fin v=>PowerSeries.coeff i.val (NewtonFourier.invH (zeta r))) hv op:=by
 rw[←seedCoefficients_invH]
 exact mu_ofOperation r v o K hv op

lemma invH_zero (r v:ℕ)(hv:0<v):
 (fun i:Fin v=>PowerSeries.coeff i.val (NewtonFourier.invH (zeta r))) ⟨0,hv⟩≠0:=by
 change PowerSeries.coeff 0 (NewtonFourier.invH (zeta r))≠0
 rw[PowerSeries.coeff_zero_eq_constantCoeff,NewtonFourier.invH_constant]
 exact one_ne_zero

open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheSemanticExecution

def seed_operation_source {r v:ℕ}{c:Config}{positive:2≤r}{s:State}(o K elapsed:ℕ)(hv:0<v)
 (op:Operation v)
 (res:SemanticResult c r (UniformTransposeDescriptorMachine.ofOperation o K op)
  (mu r K (UniformTransposeDescriptorMachine.ofOperation o K op)) positive s)
 (band:Fin v↪Fin r)(coordinates:∀i,(band i).val=o+i.val):
 UniformActualCalendarLocalSources.Source (UniformActualCalendarDirectProduced.event res elapsed)
  (UniformCanonicalDirectPhase.operationPhase
   (fun i:Fin v=>PowerSeries.coeff i.val (NewtonFourier.invH (zeta r))) hv (invH_zero r v hv) op elapsed) band:=
 operation_source res _ hv (invH_zero r v hv) op o K elapsed band coordinates rfl
  (mu_invH_ofOperation r v o K hv op)

end
end ExactFourierCircuits.UniformActualCalendarDirectSource
