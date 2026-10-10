import DFTModelCacheTraversalProgram
import DFTModelCacheDescriptorNodeBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node finish

theorem attach_valid (s : StateT.T) : (run attach s).valid := by
  have h:=DFTModelCacheDescriptor.node_valid (run headArg s).val.1 (run headArg s).val.2
  change True ∧ ((run head s).valid ∧
    ((run headArg s).valid ∧ (run DFTModelCacheDescriptor.node (run headArg s).val).valid) ∧ True) ∧ True
  exact ⟨trivial,⟨indexCode_valid head (by decide) () s,
    ⟨indexCode_valid headArg (by decide) () s,h⟩,trivial⟩,trivial⟩

theorem step_valid (s : StateT.T) : (run step s).valid := by
  change (True ∧ True) ∧ (if s.1.len=0 then run (.atom .id : Prog false StateT StateT) s else
    run (.comp attach finish) s).valid
  refine ⟨⟨trivial,trivial⟩,?_⟩
  split_ifs
  · trivial
  · exact ⟨attach_valid s,finish_valid _⟩

theorem body_valid (r o i : ℕ) (s : StateT.T) : (run body ((r,o),(i,s))).valid :=
  ⟨⟨trivial,trivial⟩,step_valid s⟩

theorem program_valid (r o : ℕ) : (run program (r,o)).valid := by
  change ((run count (r,o)).valid ∧ (run start (r,o)).valid ∧ (ticks r o (run count (r,o)).val).valid) ∧ True
  exact ⟨⟨indexCode_valid count (by decide) () (r,o),
    indexCode_valid start (by decide) () (r,o),
    steps_valid _ _ (fun i s=>body_valid r o i s) _⟩,trivial⟩

end
end ExactFourierCircuits.DFTModelCacheTraversal
