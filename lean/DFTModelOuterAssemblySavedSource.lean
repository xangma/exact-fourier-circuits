import DFTModelOuterAssemblySavedProgram
import UniformSequentialExecution
import UniformFinalOuterHeaders

set_option autoImplicit false

/-! Exact source outer stages 10, 11, 12. The first clock's prepared role-1
bank remains an entry contract. Every copy, original header operation and
role-loader operation below is executed and charged. -/
namespace ExactFourierCircuits.DFTModelOuterAssemblySaved
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformNatBlockMachine UniformSequentialAssembly UniformSequentialExecution
noncomputable section
attribute [local irreducible] applyBlock UniformFinalOuterHeaders.roleArgs
  UniformKernelSpectrumCopy.program UniformRoleInputMachine.program

def stages (W : ℕ) : List Program := [UniformKernelSpectrumCopy.program,
  natProgram (UniformFinalOuterHeaders.roleArgs W false),UniformRoleInputMachine.program]

structure Entry (W V S Q I K A B : ℕ) (v : Fin V → Scalar) (k y : Fin V → ℂ)
    (a : Fin V ≃ Fin V) (s : State) : Prop where
  roles : 2≤W
  rolesFit : W≤B
  width : s.natReg 103=V
  base : s.natReg 6026=S
  storage : s.natReg 7300=Q
  alpha : s.natReg 7310=A
  storageAddress : Q=S-V
  kernelAddress : K=s.natReg 102+7+s.natReg 101*2+V
  inputAddress : I=K+V+1
  inputSource : ∀j : Fin V, s.scalarHeap (I+j.val)=some (v j)
  kernelSource : ∀j : Fin V, s.scalarHeap (K+j.val)=some (UniformPairMachine.prepared (k j))
  spectrumSource : ∀j : Fin V, s.scalarHeap (S+V+j.val)=some (UniformPairMachine.prepared (y j))
  alphaSource : UniformGlobalNatPreparation.PermutationBank V A s.natHeap a
  inputBefore : I+V≤Q
  kernelBefore : K+V≤Q
  separate : Q+V≤S
  extent : S+W*V≤B
  tableFit : A+V≤B
  code : 76≤B
  low : s.natReg 105+12*s.natReg 102+4*s.natReg 101+4*V+100≤B
  wordBound : WordBound B s

structure Result (W V S Q : ℕ) (v : Fin V → Scalar) (k y : Fin V → ℂ)
    (a : Fin V ≃ Fin V) (u : State) : Prop where
  roles : ∀i : Fin W, ∀j : Fin V, u.scalarHeap (S+i.val*V+j.val)=some
    (UniformRoleInputMachine.roleValue v (fun j => UniformPairMachine.prepared (k j)) a i.val j)
  saved : ∀j : Fin V, u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))
  storage : u.natReg 7300=Q
  width : u.natReg 103=V
  base : u.natReg 6026=S
  pc : u.pc=41

theorem execution {n W V S Q I K A B : ℕ} (x : Fin n → ℂ)
    (v : Fin V → Scalar) (k y : Fin V → ℂ) (a : Fin V ≃ Fin V)
    (s : State) (entry : Entry W V S Q I K A B v k y a s) :
    ∃u, LocalStages n B x (stages W) s
      ((7*V+9)+19+(5*(W*V)+16*V+24)) u ∧ Result W V S Q v k y a u := by
  let e : State := {s with pc:=0}
  have ewb : WordBound B e := changePC_bound _ s 0 entry.wordBound (by omega)
  have two : 2*V≤W*V := Nat.mul_le_mul_right V entry.roles
  obtain ⟨c,copy,copied,copyFrame,copyPC⟩ := UniformKernelSpectrumCopy.execution
    x (fun j => UniformPairMachine.prepared (y j)) e entry.spectrumSource entry.width
    entry.base entry.storage (by have h:=entry.separate;omega)
    (by have h:=entry.extent;omega) (by have h:=entry.separate;have h':=entry.extent;omega)
    (by have h:=entry.code;omega) rfl ewb
  have copyReg (q : ℕ) (hq : ¬UniformKernelSpectrumCopy.Changed q) :
      c.natReg q=s.natReg q := copyFrame.natReg q hq
  have cWidth : c.natReg 103=V := (copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)).trans entry.width
  have cBase : c.natReg 6026=S := (copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)).trans entry.base
  have cAlpha : c.natReg 7310=A := (copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)).trans entry.alpha
  have c101 : c.natReg 101=s.natReg 101 := copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)
  have c102 : c.natReg 102=s.natReg 102 := copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)
  have c105 : c.natReg 105=s.natReg 105 := copyReg _ (by unfold UniformKernelSpectrumCopy.Changed;omega)
  let d : State := {c with pc:=0}
  have dwb : WordBound B d := changePC_bound _ c 0 copy.final_bound (by omega)
  have safe := UniformFinalOuterHeaders.roleArgs_safe W false d B entry.rolesFit
    (by change c.natReg 6026≤B;exact copy.final_bound.2.1 _)
    (by change c.natReg 7310≤B;exact copy.final_bound.2.1 _)
    (by change c.natReg 105+12*c.natReg 102+4*c.natReg 101+4*c.natReg 103+100≤B
        rw [c105,c102,c101,cWidth];exact entry.low)
  have header := nat_execution (UniformFinalOuterHeaders.roleArgs W false) x d rfl dwb
    (by simp only [UniformFinalOuterHeaders.roleArgs_length,Bool.false_eq_true,ite_false]
        have h:=entry.code;omega) safe.1 safe.2
  let h := applyBlock (UniformFinalOuterHeaders.roleArgs W false) d
  have hFrame := UniformFinalOuterHeaders.roleArgs_frame W false d
  have hHeap : h.scalarHeap=c.scalarHeap := hFrame.2.1
  have hNat : h.natHeap=s.natHeap := hFrame.1.trans copyFrame.natHeap
  have args : DFTModelOuterAssemblyRole.Entry W V S I K A B v k a {h with pc:=0} := by
    refine ⟨rfl,entry.roles,UniformFinalOuterHeaders.raw_roles W false d,?_,?_,?_,?_,?_,?_,?_,?_,
      ?_,?_,entry.extent,entry.tableFit,by have h:=entry.code;omega,
      changePC_bound _ h 0 header.final_bound (by omega)⟩
    · exact (UniformFinalOuterHeaders.raw_volume W false d).trans cWidth
    · exact (UniformFinalOuterHeaders.raw_source W false d).trans cBase
    · rw [UniformFinalOuterHeaders.raw_input]
      change c.natReg 102+7+c.natReg 101*2+c.natReg 103+c.natReg 103+1=I
      rw [c102,c101,cWidth,entry.inputAddress,entry.kernelAddress]
    · rw [UniformFinalOuterHeaders.raw_kernel]
      change c.natReg 102+7+c.natReg 101*2+c.natReg 103=K
      rw [c102,c101,cWidth,entry.kernelAddress]
    · exact (UniformFinalOuterHeaders.raw_alpha W false d).trans cAlpha
    · intro j
      change h.scalarHeap (I+j.val)=some (v j)
      rw [hHeap]
      exact (copyFrame.scalar _ (Or.inl (by have hj:=j.isLt;have fit:=entry.inputBefore;omega))).trans (entry.inputSource j)
    · intro j
      change h.scalarHeap (K+j.val)=some (UniformPairMachine.prepared (k j))
      rw [hHeap]
      exact (copyFrame.scalar _ (Or.inl (by have hj:=j.isLt;have fit:=entry.kernelBefore;omega))).trans (entry.kernelSource j)
    · change UniformGlobalNatPreparation.PermutationBank V A h.natHeap a
      rw [hNat]
      exact entry.alphaSource
    · have h:=entry.inputBefore;have h':=entry.separate;omega
    · have h:=entry.kernelBefore;have h':=entry.separate;omega
  obtain ⟨u,load,pcu,loaded,out,loadFrame⟩ := args.execution x
  have localRun : LocalStages n B x (stages W) s
      ((7*V+9)+19+(5*(W*V)+16*V+24)) u := by
    have head : BoundedExecution (natProgram (UniformFinalOuterHeaders.roleArgs W false)) n x B
        {c with pc:=0} 19 h := by
      simpa only [UniformFinalOuterHeaders.roleArgs_length,Bool.false_eq_true,ite_false] using header
    have tail : LocalStages n B x [UniformRoleInputMachine.program] h (5*(W*V)+16*V+24) u := by
      simpa only [Nat.add_zero] using LocalStages.cons load (LocalStages.nil u load.final_bound)
    have rest := LocalStages.cons head tail
    simpa only [stages,Nat.add_assoc] using LocalStages.cons copy rest
  refine ⟨u,localRun,⟨loaded,?_,?_,?_,?_,pcu⟩⟩
  · intro j
    exact (out _ (Or.inl (by have hj:=j.isLt;have fit:=entry.separate;omega))).trans
      ((congrFun hHeap _).trans (copied j))
  · have frame := loadFrame.natReg 7300 (by unfold UniformRoleInputMachine.Protected;omega)
    change u.natReg 7300=Q
    rw [frame,UniformFinalOuterHeaders.raw_storage]
    change c.natReg 6026-c.natReg 103=Q
    rw [cBase,cWidth,entry.storageAddress]
  · exact (loadFrame.natReg 103 (by unfold UniformRoleInputMachine.Protected;omega)).trans
      ((hFrame.2.2.2.2.2 103 (by unfold UniformFinalOuterHeaders.Changed;omega)).trans cWidth)
  · exact (loadFrame.natReg 6026 (by unfold UniformRoleInputMachine.Protected;omega)).trans
      ((hFrame.2.2.2.2.2 6026 (by unfold UniformFinalOuterHeaders.Changed;omega)).trans cBase)

end
end ExactFourierCircuits.DFTModelOuterAssemblySaved
