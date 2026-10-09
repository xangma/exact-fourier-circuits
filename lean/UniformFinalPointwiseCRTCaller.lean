import UniformFinalCRTRoleSource
import UniformFinalMovementGeometry

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPointwiseCRTCaller
open UniformMachine UniformFinalNumericJoin UniformFinalMovementFrame UniformSequentialExecution
noncomputable section

/-- Two actual charged helpers with one genuine intermediate state. No
interphase headers or source arrays are installed outside the program. -/
theorem execution {n W L S T AP BI B:ℕ}(x:Fin n→ℂ)(v:ℕ→Fin L→Scalar)
 (y:Fin L→ℂ)(alpha beta:Fin L≃Fin L)(s:State)(pc:s.pc=0)
 (roles:0<W)(width:s.natReg 103=L)(source:s.natReg 6026=S)(target:s.natReg 6025=T)
 (alphaHeader:s.natReg 7310=AP)(inverseHeader:s.natReg 7311=BI)(kernel:s.natReg 7300=Q n)
 (input:UniformRolePointwiseMachine.Source W L S v s)
 (prepared:∀j:Fin L,s.scalarHeap (Q n+j.val)=some (UniformPairMachine.prepared (y j)))
 (alphaBank:UniformGlobalNatPreparation.PermutationBank L AP s.natHeap alpha)
 (inverseBank:UniformGlobalNatPreparation.PermutationBank L BI s.natHeap beta.symm)
 (separate:Q n+L≤S)(disjoint:UniformPermutationMachine.Disjoint S T L)
 (afterRoles:S+W*L≤T)(extent:S+W*L≤B)(targetFit:T+L≤B)
 (kernelFit:Q n+L≤B)(alphaFit:AP+L≤B)(inverseFit:BI+L≤B)
 (beforeT:Q n≤T)(code:64≤B)(wb:WordBound B s):
 ∃p u,LocalStages n B x [UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]
  s ((9*L+9)+(18*L+18)) u∧
 NumericValues S (fun j=>(v 0 j).value*y j) p∧
 (∀j:Fin L,u.scalarHeap (S+j.val)=p.scalarHeap (S+(beta.symm (alpha j)).val))∧
 (∀j:Fin L,u.scalarHeap (T+j.val)=p.scalarHeap (S+(beta.symm j).val))∧
 UniformRolePointwiseMachine.Source W L S
  (UniformFinalCRTRoleSource.values (UniformRolePointwiseMachine.multiplied v y) alpha beta) u∧
 (∀j:Fin L,u.scalarHeap (Q n+j.val)=some (UniformPairMachine.prepared (y j)))∧
 Frame n s u∧u.pc=33:=by
 obtain ⟨p,first,pSource,numeric,pKernel,pFrame,_raw,_ppc⟩:=UniformFinalPointwiseExecution.execution
  x v y s roles input prepared width source kernel separate kernelFit extent code pc wb
 let e:State:={p with pc:=0}
 have ewb:WordBound B e:=changePC_bound B p 0 first.final_bound (by omega)
 have pWidth:e.natReg 103=L:=(pFrame.saved _ (by omega) (by omega)).trans width
 have pSourceHeader:e.natReg 6026=S:=(pFrame.high _ (by omega) (by omega) (by omega)).trans source
 have pTarget:e.natReg 6025=T:=(pFrame.high _ (by omega) (by omega) (by omega)).trans target
 have pAlpha:e.natReg 7310=AP:=(pFrame.high _ (by omega) (by omega) (by omega)).trans alphaHeader
 have pInverse:e.natReg 7311=BI:=(pFrame.high _ (by omega) (by omega) (by omega)).trans inverseHeader
 have aBank:UniformGlobalNatPreparation.PermutationBank L AP e.natHeap alpha:=by
  change UniformGlobalNatPreparation.PermutationBank L AP p.natHeap alpha
  rw[pFrame.natHeap];exact alphaBank
 have bBank:UniformGlobalNatPreparation.PermutationBank L BI e.natHeap beta.symm:=by
  change UniformGlobalNatPreparation.PermutationBank L BI p.natHeap beta.symm
  rw[pFrame.natHeap];exact inverseBank
 have one:L≤W*L:=by
  simpa only[Nat.one_mul] using Nat.mul_le_mul_right L (show 1≤W by omega)
 obtain ⟨u,second,uSource,reindex,standard,uFrame,outside,_raw2,upc⟩:=UniformFinalCRTRoleSource.execution
  x (UniformRolePointwiseMachine.multiplied v y) alpha beta e rfl roles pWidth pSourceHeader pTarget
  pAlpha pInverse pSource aBank bBank disjoint afterRoles (by omega) targetFit alphaFit inverseFit
  (by omega) beforeT (by omega) ewb
 have rawFrame:Frame n p u:=
  ⟨uFrame.natHeap,uFrame.scalar,uFrame.saved,uFrame.high,uFrame.outputs,uFrame.roots⟩
 have start:{s with pc:=0}=s:=by rw[←pc]
 have firstReset:BoundedExecution UniformRolePointwiseMachine.program n x B {s with pc:=0} (9*L+9) p:=by
  rw[start];exact first
 have stages:=LocalStages.cons firstReset
  (LocalStages.cons second (LocalStages.nil u second.final_bound))
 refine ⟨p,u,?_,numeric,reindex,standard,uSource,?_,pFrame.trans rawFrame,upc⟩
 · simpa only[Nat.add_zero] using stages
 · intro j
   exact (outside _ (Or.inl (by have:=j.isLt;omega))
    (Or.inl (by have:=j.isLt;omega))).trans (pKernel j)

end
end ExactFourierCircuits.UniformFinalPointwiseCRTCaller
