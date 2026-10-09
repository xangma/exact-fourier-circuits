import UniformFinalPointwiseExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCRTMovement
open UniformMachine UniformFinalNumericJoin UniformFinalMovementFrame
noncomputable section

/-- Both real gathers consume the independent AP and inverse-BP banks.
This does not assume that AP and BP are inverses. -/
theorem execution {n L S T AP BI B:ℕ}(x:Fin n→ℂ)(f:Fin L→ℂ)
 (alpha beta:Fin L≃Fin L)(s:State)(pc:s.pc=0)
 (width:s.natReg 103=L)(source:s.natReg 6026=S)(target:s.natReg 6025=T)
 (alphaHeader:s.natReg 7310=AP)(inverseHeader:s.natReg 7311=BI)
 (input:NumericValues S f s)
 (alphaBank:UniformGlobalNatPreparation.PermutationBank L AP s.natHeap alpha)
 (inverseBank:UniformGlobalNatPreparation.PermutationBank L BI s.natHeap beta.symm)
 (disjoint:UniformPermutationMachine.Disjoint S T L)
 (sourceFit:S+L≤B)(targetFit:T+L≤B)(alphaFit:AP+L≤B)(inverseFit:BI+L≤B)
 (beforeS:Q n≤S)(beforeT:Q n≤T)(code:34≤B)(wb:WordBound B s):
 ∃u,BoundedExecution UniformPhysicalCRTConsumerMachine.program n x B s (18*L+18) u∧
 (∀j:Fin L,u.scalarHeap (S+j.val)=s.scalarHeap (S+(beta.symm (alpha j)).val))∧
 (∀j:Fin L,u.scalarHeap (T+j.val)=s.scalarHeap (S+(beta.symm j).val))∧
 NumericValues S (fun j=>f (beta.symm (alpha j))) u∧
 NumericValues T (fun j=>f (beta.symm j)) u∧
 Frame n s u∧
 (∀a,(a<S∨S+L≤a)→(a<T∨T+L≤a)→u.scalarHeap a=s.scalarHeap a)∧
 UniformPhysicalCRTConsumerMachine.Frame s u∧u.pc=33:=by
 obtain ⟨u,run,upc,values,standard,outside,frame⟩:=UniformPhysicalCRTConsumerMachine.execution
  n B L S T AP BI x (scalars L S s) alpha beta.symm s pc width source target
  alphaHeader inverseHeader (numeric_present input) alphaBank inverseBank disjoint
  sourceFit targetFit alphaFit inverseFit code wb
 have reindex:∀j:Fin L,u.scalarHeap (S+j.val)=s.scalarHeap (S+(beta.symm (alpha j)).val):=by
  intro j;exact (values j).trans (numeric_present input _).symm
 have toStandard:∀j:Fin L,u.scalarHeap (T+j.val)=s.scalarHeap (S+(beta.symm j).val):=by
  intro j;exact (standard j).trans (numeric_present input _).symm
 refine ⟨u,run,reindex,toStandard,?_,?_,UniformFinalMovementFrame.Frame.crt beforeS beforeT outside frame,outside,frame,upc⟩
 · intro j
   rw[reindex j]
   exact input _
 · intro j
   rw[toStandard j]
   exact input _

end
end ExactFourierCircuits.UniformFinalCRTMovement
