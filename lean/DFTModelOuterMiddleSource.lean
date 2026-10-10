import DFTModelOuterMiddleProgram
import UniformSequentialExecution

set_option autoImplicit false

/-! Original outer stages15–16, with genuine stage14 clock source and saved
prepared spectrum as entry obligations. Every actual pointwise instruction
and both physical gathers are constructed and charged at the same states. -/
namespace ExactFourierCircuits.DFTModelOuterMiddle
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformSequentialExecution UniformSequentialAssembly
noncomputable section
attribute [local irreducible] UniformRolePointwiseMachine.program UniformPhysicalCRTConsumerMachine.program

def stages : List Program := [UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]

structure Entry (W V S T Q AP BI B : ℕ) (v : ℕ → Fin V → Scalar) (y : Fin V → ℂ)
    (alpha betaInverse : Fin V ≃ Fin V) (s : State) : Prop where
  roles : 0<W
  width : s.natReg 103=V
  sourceBase : s.natReg 6026=S
  targetBase : s.natReg 6025=T
  kernelBase : s.natReg 7300=Q
  alphaBase : s.natReg 7310=AP
  betaBase : s.natReg 7311=BI
  source : UniformRolePointwiseMachine.Source W V S v s
  prepared : ∀j : Fin V, s.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))
  alphaTable : UniformGlobalNatPreparation.PermutationBank V AP s.natHeap alpha
  betaTable : UniformGlobalNatPreparation.PermutationBank V BI s.natHeap betaInverse
  sourceTarget : S+W*V≤T ∨ T+V≤S
  sourceKernel : S+W*V≤Q ∨ Q+V≤S
  kernelTarget : Q+V≤T ∨ T+V≤Q
  extent : S+W*V≤B
  targetFit : T+V≤B
  kernelFit : Q+V≤B
  alphaFit : AP+V≤B
  betaFit : BI+V≤B
  code : 64≤B
  wordBound : WordBound B s

def product {V : ℕ} (v : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (j : Fin V) : Scalar :=
  UniformChirpPointwiseMachine.productScalar (v 0 j) (y j)

structure Result (W V S T Q : ℕ) (v : ℕ → Fin V → Scalar) (y : Fin V → ℂ)
    (alpha betaInverse : Fin V ≃ Fin V) (u : State) : Prop where
  source : ∀j : Fin V, u.scalarHeap (S+j.val)=some (product v y (betaInverse (alpha j)))
  target : ∀j : Fin V, u.scalarHeap (T+j.val)=some (product v y (betaInverse j))
  spectators : ∀r,0<r → r<W → ∀j : Fin V, u.scalarHeap (S+r*V+j.val)=some (v r j)
  prepared : ∀j : Fin V, u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))
  width : u.natReg 103=V
  sourceBase : u.natReg 6026=S
  targetBase : u.natReg 6025=T
  kernelBase : u.natReg 7300=Q
  pc : u.pc=33

theorem execution {n W V S T Q AP BI B : ℕ} (x : Fin n → ℂ)
    (v : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha betaInverse : Fin V ≃ Fin V)
    (s : State) (entry : Entry W V S T Q AP BI B v y alpha betaInverse s) :
    ∃u, LocalStages n B x stages s (27*V+27) u ∧ Result W V S T Q v y alpha betaInverse u := by
  let e : State := {s with pc:=0}
  have ewb : WordBound B e := changePC_bound _ s 0 entry.wordBound (by omega)
  have one : V≤W*V := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤W by have h:=entry.roles;omega)
  have sepKernel : S+V≤Q ∨ Q+V≤S := by
    rcases entry.sourceKernel with h|h
    · exact Or.inl (by omega)
    · exact Or.inr h
  obtain ⟨m,multiply,values,mulFrame,mpc⟩ := UniformRolePointwiseMachine.execution x v y e
    entry.roles entry.source entry.prepared entry.width entry.sourceBase entry.kernelBase
    sepKernel entry.kernelFit entry.extent entry.code rfl ewb
  have reg (q : ℕ) (hq : ¬UniformRolePointwiseMachine.Changed q) : m.natReg q=s.natReg q :=
    mulFrame.natReg q hq
  have width : m.natReg 103=V := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.width
  have base : m.natReg 6026=S := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.sourceBase
  have targetBase : m.natReg 6025=T := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.targetBase
  have ap : m.natReg 7310=AP := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.alphaBase
  have bi : m.natReg 7311=BI := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.betaBase
  have kernelBase : m.natReg 7300=Q := (reg _ (by unfold UniformRolePointwiseMachine.Changed;omega)).trans entry.kernelBase
  let d : State := {m with pc:=0}
  have source : ∀j : Fin V, d.scalarHeap (S+j.val)=some (product v y j) := by
    intro j
    simpa only [d,product,UniformRolePointwiseMachine.multiplied,ite_true,Nat.zero_mul,Nat.add_zero]
      using values 0 entry.roles j
  have disjoint : UniformPermutationMachine.Disjoint S T V := by
    rcases entry.sourceTarget with h|h
    · exact Or.inl (by omega)
    · exact Or.inr h
  obtain ⟨u,crt,upc,sourceOut,targetOut,outside,crtFrame⟩ := UniformPhysicalCRTConsumerMachine.execution
    n B V S T AP BI x (product v y) alpha betaInverse d rfl width base targetBase ap bi source
    (by change UniformGlobalNatPreparation.PermutationBank V AP m.natHeap alpha
        rw [mulFrame.natHeap];exact entry.alphaTable)
    (by change UniformGlobalNatPreparation.PermutationBank V BI m.natHeap betaInverse
        rw [mulFrame.natHeap];exact entry.betaTable)
    disjoint (by have h:=entry.extent;omega) entry.targetFit entry.alphaFit entry.betaFit
    (by have h:=entry.code;omega) (changePC_bound _ m 0 multiply.final_bound (by omega))
  have native : LocalStages n B x stages s (27*V+27) u := by
    have tail : LocalStages n B x [UniformPhysicalCRTConsumerMachine.program] m (18*V+18) u := by
      simpa only [Nat.add_zero] using LocalStages.cons crt (LocalStages.nil u crt.final_bound)
    have joined : LocalStages n B x stages s ((9*V+9)+(18*V+18)) u := LocalStages.cons multiply tail
    have time : (9*V+9)+(18*V+18)=27*V+27 := by omega
    rw [time] at joined
    exact joined
  refine ⟨u,native,⟨sourceOut,targetOut,?_,?_,?_,?_,?_,?_,upc⟩⟩
  · intro r hr hrW j
    have lower : V≤r*V := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤r by omega)
    have upper : r*V+j.val<W*V := by
      have h := Nat.mul_le_mul_right V (show r+1≤W by omega)
      have hj:=j.isLt
      simp only [Nat.add_mul,Nat.one_mul] at h
      omega
    have outT : S+r*V+j.val<T ∨ T+V≤S+r*V+j.val := by
      rcases entry.sourceTarget with h|h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact (outside _ (Or.inr (by omega)) outT).trans
      (by simpa [d,UniformRolePointwiseMachine.multiplied,show r≠0 by omega] using values r hrW j)
  · intro j
    have outS : Q+j.val<S ∨ S+V≤Q+j.val := by
      rcases entry.sourceKernel with h|h
      · exact Or.inr (by omega)
      · exact Or.inl (by have hj:=j.isLt;omega)
    have outT : Q+j.val<T ∨ T+V≤Q+j.val := by
      rcases entry.kernelTarget with h|h
      · exact Or.inl (by have hj:=j.isLt;omega)
      · exact Or.inr (by omega)
    exact (outside _ outS outT).trans ((mulFrame.scalar _ outS).trans (entry.prepared j))
  · exact (crtFrame.natReg 103 (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans width
  · exact (crtFrame.natReg 6026 (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans base
  · exact (crtFrame.natReg 6025 (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans targetBase
  · exact (crtFrame.natReg 7300 (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans kernelBase

end
end ExactFourierCircuits.DFTModelOuterMiddle
