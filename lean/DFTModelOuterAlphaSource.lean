import DFTModelOuterAlphaProgram
import UniformRolePointwiseMachine
import UniformSequentialExecution

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterAlpha
open UniformMachine UniformSequentialExecution
noncomputable section
attribute [local irreducible] UniformPhysicalCRTConsumerMachine.alphaProgram

def stages : List Program := [UniformPhysicalCRTConsumerMachine.alphaProgram]

/-- Padded input7312 and saved spectrum7300 have distinct source contracts.
Only the first V cells of the loaded role bank6026 are written. -/
structure Entry (W V K S Q AP B : ℕ) (f : Fin V → Scalar)
    (roles : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha : Fin V ≃ Fin V) (s : State) : Prop where
  positiveRoles : 0<W
  width : s.natReg 103=V
  paddedBase : s.natReg 7312=K
  roleBase : s.natReg 6026=S
  savedBase : s.natReg 7300=Q
  alphaBase : s.natReg 7310=AP
  padded : ∀j : Fin V, s.scalarHeap (K+j.val)=some (f j)
  loadedRoles : UniformRolePointwiseMachine.Source W V S roles s
  preparedSaved : ∀j : Fin V,s.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))
  alphaTable : UniformGlobalNatPreparation.PermutationBank V AP s.natHeap alpha
  paddedSeparate : UniformPermutationMachine.Disjoint K S V
  savedSeparate : Q+V≤S ∨ S+V≤Q
  paddedFit : K+V≤B
  extent : S+W*V≤B
  savedFit : Q+V≤B
  alphaFit : AP+V≤B
  code : 18≤B
  wordBound : WordBound B s

structure Result (W V K S Q : ℕ) (f : Fin V → Scalar)
    (roles : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha : Fin V ≃ Fin V)
    (s u : State) : Prop where
  target : ∀j : Fin V,u.scalarHeap (S+j.val)=some (f (alpha j))
  padded : ∀j : Fin V,u.scalarHeap (K+j.val)=some (f j)
  spectators : ∀r,0<r → r<W → ∀j : Fin V,u.scalarHeap (S+r*V+j.val)=some (roles r j)
  preparedSaved : ∀j : Fin V,u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (y j))
  outside : UniformPermutationMachine.Outside S V s.scalarHeap u
  frame : UniformPhysicalCRTConsumerMachine.Frame s u
  pc : u.pc=17

theorem execution {n W V K S Q AP B : ℕ} (x : Fin n → ℂ) (f : Fin V → Scalar)
    (roles : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha : Fin V ≃ Fin V) (s : State)
    (entry : Entry W V K S Q AP B f roles y alpha s) :
    ∃u, LocalStages n B x stages s (9*V+10) u ∧ Result W V K S Q f roles y alpha s u := by
  let e : State := {s with pc:=0}
  have ewb : WordBound B e := changePC_bound _ s 0 entry.wordBound (by omega)
  have one : V≤W*V := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right V
      (show 1≤W by have h:=entry.positiveRoles;omega)
  obtain ⟨u,actual,pc,target,padded,outside,frame⟩ := UniformPhysicalCRTConsumerMachine.alpha_execution
    n B V K S AP x f alpha e rfl entry.width entry.paddedBase entry.roleBase entry.alphaBase
    entry.padded entry.alphaTable entry.paddedSeparate entry.paddedFit
    (by have h:=entry.extent;omega) entry.alphaFit entry.code ewb
  have native : LocalStages n B x stages s (9*V+10) u := by
    change LocalStages n B x [UniformPhysicalCRTConsumerMachine.alphaProgram] s (9*V+10) u
    simpa only [Nat.add_zero] using LocalStages.cons actual (LocalStages.nil u actual.final_bound)
  have finalFrame : UniformPhysicalCRTConsumerMachine.Frame s u :=
    ⟨frame.natHeap,frame.outputs,frame.roots,frame.natReg,frame.scalarReg⟩
  refine ⟨u,native,⟨target,padded,?_,?_,outside,finalFrame,pc⟩⟩
  · intro r hr hrW j
    have lower : V≤r*V := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤r by omega)
    exact (outside _ (Or.inr (by omega))).trans (entry.loadedRoles r hrW j)
  · intro j
    have out : Q+j.val<S ∨ S+V≤Q+j.val := by
      rcases entry.savedSeparate with h|h
      · exact Or.inl (by have hj:=j.isLt;omega)
      · exact Or.inr (by omega)
    exact (outside _ out).trans (entry.preparedSaved j)

end
end ExactFourierCircuits.DFTModelOuterAlpha
