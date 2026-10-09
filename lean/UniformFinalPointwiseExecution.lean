import UniformFinalPreparedSpectrumSave
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPointwiseExecution
open UniformMachine UniformFinalNumericJoin UniformFinalMovementFrame
noncomputable section
namespace P
export UniformRolePointwiseMachine (Source multiplied)
end P

/-- The actual guarded multiply uses the saved prepared spectrum and leaves
every other role and every source coefficient unchanged. -/
theorem execution {n W L S B:ℕ}(x:Fin n→ℂ)(v:ℕ→Fin L→Scalar)(y:Fin L→ℂ)(s:State)
 (roles:0<W)(input:P.Source W L S v s)
 (prepared:∀j:Fin L,s.scalarHeap (Q n+j.val)=some (UniformPairMachine.prepared (y j)))
 (width:s.natReg 103=L)(base:s.natReg 6026=S)(kernel:s.natReg 7300=Q n)
 (separate:Q n+L≤S)(kernelFit:Q n+L≤B)(extent:S+W*L≤B)
 (code:64≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution UniformRolePointwiseMachine.program n x B s (9*L+9) u∧
 P.Source W L S (P.multiplied v y) u∧
 NumericValues S (fun j=>(v 0 j).value*y j) u∧
 (∀j,u.scalarHeap (Q n+j.val)=some (UniformPairMachine.prepared (y j)))∧
 Frame n s u∧UniformRolePointwiseMachine.Frame S L s u∧u.pc=16:=by
 obtain ⟨u,run,values,frame,upc⟩:=UniformRolePointwiseMachine.execution x v y s
  roles input prepared width base kernel (Or.inr separate) kernelFit extent code pc wb
 refine ⟨u,run,values,?_,?_,UniformFinalMovementFrame.Frame.pointwise (by omega) frame,frame,upc⟩
 · intro j
   have h:=congrArg (Option.map Scalar.value) (values 0 roles j)
   simpa only[Nat.zero_mul,Nat.add_zero,UniformRolePointwiseMachine.multiplied,
    ite_true,UniformChirpPointwiseMachine.productScalar,Option.map_some] using h
 · intro j
   exact (frame.scalar _ (Or.inl (by have:=j.isLt;omega))).trans (prepared j)

end
end ExactFourierCircuits.UniformFinalPointwiseExecution
