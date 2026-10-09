import UniformFinalCRTMovement

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCRTRoleSource
open UniformMachine UniformFinalNumericJoin UniformFinalMovementFrame
noncomputable section

def values {L:ℕ}(v:ℕ→Fin L→Scalar)(alpha beta:Fin L≃Fin L)(r:ℕ)(j:Fin L):Scalar:=
 if r=0 then v 0 (beta.symm (alpha j)) else v r j

/-- CRT movement preserves the remaining W roles. The temporary standard
bank is placed after the whole role bank, not just after role0. -/
theorem execution {n W L S T AP BI B:ℕ}(x:Fin n→ℂ)(v:ℕ→Fin L→Scalar)
 (alpha beta:Fin L≃Fin L)(s:State)(pc:s.pc=0)
 (roles:0<W)(width:s.natReg 103=L)(source:s.natReg 6026=S)(target:s.natReg 6025=T)
 (alphaHeader:s.natReg 7310=AP)(inverseHeader:s.natReg 7311=BI)
 (input:UniformRolePointwiseMachine.Source W L S v s)
 (alphaBank:UniformGlobalNatPreparation.PermutationBank L AP s.natHeap alpha)
 (inverseBank:UniformGlobalNatPreparation.PermutationBank L BI s.natHeap beta.symm)
 (disjoint:UniformPermutationMachine.Disjoint S T L)(afterRoles:S+W*L≤T)
 (sourceFit:S+L≤B)(targetFit:T+L≤B)(alphaFit:AP+L≤B)(inverseFit:BI+L≤B)
 (beforeS:Q n≤S)(beforeT:Q n≤T)(code:34≤B)(wb:WordBound B s):
 ∃u,BoundedExecution UniformPhysicalCRTConsumerMachine.program n x B s (18*L+18) u∧
 UniformRolePointwiseMachine.Source W L S (values v alpha beta) u∧
 (∀j:Fin L,u.scalarHeap (S+j.val)=s.scalarHeap (S+(beta.symm (alpha j)).val))∧
 (∀j:Fin L,u.scalarHeap (T+j.val)=s.scalarHeap (S+(beta.symm j).val))∧
 Frame n s u∧
 (∀a,(a<S∨S+L≤a)→(a<T∨T+L≤a)→u.scalarHeap a=s.scalarHeap a)∧
 UniformPhysicalCRTConsumerMachine.Frame s u∧u.pc=33:=by
 have numeric:NumericValues S (fun j=>(v 0 j).value) s:=by
  intro j
  simpa only[Nat.zero_mul,Nat.add_zero,Option.map_some] using
   congrArg (Option.map Scalar.value) (input 0 roles j)
 obtain ⟨u,run,reindex,standard,_,_,frame,outside,raw,upc⟩:=UniformFinalCRTMovement.execution
  x (fun j=>(v 0 j).value) alpha beta s pc width source target alphaHeader inverseHeader
  numeric alphaBank inverseBank disjoint sourceFit targetFit alphaFit inverseFit
  beforeS beforeT code wb
 refine ⟨u,run,?_,reindex,standard,frame,outside,raw,upc⟩
 intro r hr j
 by_cases zero:r=0
 · subst r
   simpa only[Nat.zero_mul,Nat.add_zero,values,ite_true] using
    (reindex j).trans (by simpa only[Nat.zero_mul,Nat.add_zero] using input 0 roles (beta.symm (alpha j)))
 · have lower:L≤r*L:=by
    simpa only[Nat.one_mul] using Nat.mul_le_mul_right L (show 1≤r by omega)
   have upper:(r+1)*L≤W*L:=Nat.mul_le_mul_right L (by omega)
   rw[Nat.add_mul,Nat.one_mul] at upper
   rw[outside _ (Or.inr (by omega)) (Or.inl (by have:=j.isLt;omega))]
   simpa only[values,zero,ite_false] using input r hr j

end
end ExactFourierCircuits.UniformFinalCRTRoleSource
