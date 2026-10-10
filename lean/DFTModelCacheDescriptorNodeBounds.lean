import DFTModelCacheDescriptorNode
import DFTModelCacheDescriptorSearchBounds
import DFTModelCacheDescriptorRowsBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] selected rectangleRows rowCell nodeRows nodeSeed

theorem emptyRows_valid (v o b : ℕ) : (run emptyRows ((v,o),b)).valid := by
  change True ∧ (Bill.tab 0 Row7.blank (fun h=>run rowCell (((v,o),b),h))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr ?_⟩
  intro i hi
  omega

theorem emptyRows_work (v o b : ℕ) : (run emptyRows ((v,o),b)).work=4 := rfl

theorem nodeRows_valid (v o b : ℕ) : (run nodeRows ((v,o),b)).valid := by
  have he:=emptyRows_valid v o b
  have hr:=rectangleRows_valid v o b
  dsimp only [run] at he hr
  rw [nodeRows]
  dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  split_ifs <;> simp_all

theorem nodeRows_work (v o b : ℕ) :
    (run nodeRows ((v,o),b)).work≤1200*(v+1)^2+20 := by
  have he:=emptyRows_work v o b
  dsimp only [run] at he
  by_cases hz : b=0
  · subst b
    rw [nodeRows]
    dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    split_ifs <;> simp_all
  · have hr:=rectangleRows_work v o b (by omega)
    dsimp only [run] at hr
    rw [nodeRows]
    dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    split_ifs <;> simp_all
    all_goals omega

theorem node_valid (v o : ℕ) : (run node (v,o)).valid := by
  have hs:=selected_valid v
  have hr:=nodeRows_valid v o (UniformWorkspacePlanner.selected v)
  rw [node]
  change (run nodeSeed (v,o)).valid ∧ (True ∧ (run nodeRows (run nodeSeed (v,o)).val).valid ∧ True)
  rw [nodeSeed_value]
  have seed : (run nodeSeed (v,o)).valid := by
    rw [nodeSeed]
    change True ∧ (True ∧ (run selected v).valid) ∧ True
    exact ⟨trivial,⟨trivial,hs⟩,trivial⟩
  exact ⟨seed,trivial,hr,trivial⟩

theorem node_work (v o : ℕ) : (run node (v,o)).work≤4000*(v+1)^4 := by
  have hs:=selected_work v
  have hr:=nodeRows_work v o (UniformWorkspacePlanner.selected v)
  have seed : (run nodeSeed (v,o)).work=(run selected v).work+4 := by
    rw [nodeSeed]
    change 1+(1+(run selected v).work+1)+1=_
    omega
  rw [node]
  change (run nodeSeed (v,o)).work+(1+(run nodeRows (run nodeSeed (v,o)).val).work+1)+1≤_
  rw [nodeSeed_value,seed]
  have hpow : (v+1)^2≤(v+1)^4 := by
    calc
      _ ≤ ((v+1)^2)^2 := Nat.le_self_pow (by decide : (2:ℕ)≠0) _
      _ = _ := by ring
  have hone:=Nat.one_le_pow 4 (v+1) (by omega)
  omega

end
end ExactFourierCircuits.DFTModelCacheDescriptor
