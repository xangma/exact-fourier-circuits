import DFTModelCacheDescriptorRows
import DFTModelCacheDescriptorFitsBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targets sources)
noncomputable section

attribute [local irreducible] pairSizes sourceCount targetCount rowCoordinates rowA rowE rowI0 rowJ0

theorem rowCoordinates_value (v o b h : ℕ) :
    (run rowCoordinates (((v,o),b),h)).val=((v,b),(h/sources v b,h%sources v b)) := by
  rw [rowCoordinates]
  change ((v,b),(h/(run sourceCount (v,b)).val,h%(run sourceCount (v,b)).val))=_
  rw [sourceCount_value]

theorem rowCoordinates_valid (v o b h : ℕ) : (run rowCoordinates (((v,o),b),h)).valid := by
  have hs:=(counts_valid v b).2
  dsimp only [run] at hs
  rw [rowCoordinates]
  dsimp only [rowV,rowB,rowI,rowJ,rowsPair,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true]
  exact ⟨hs,hs⟩

theorem rowA_valid (v o b h : ℕ) : (run rowA (((v,o),b),h)).valid := by
  rw [rowA]
  change (run rowCoordinates (((v,o),b),h)).valid ∧
    (run pairSizes (run rowCoordinates (((v,o),b),h)).val).valid ∧ True
  rw [rowCoordinates_value]
  exact ⟨rowCoordinates_valid _ _ _ _,pairSizes_valid _ _ _ _,trivial⟩

theorem rowE_valid (v o b h : ℕ) : (run rowE (((v,o),b),h)).valid := by
  rw [rowE]
  change (run rowCoordinates (((v,o),b),h)).valid ∧
    (run pairSizes (run rowCoordinates (((v,o),b),h)).val).valid ∧ True
  rw [rowCoordinates_value]
  exact ⟨rowCoordinates_valid _ _ _ _,pairSizes_valid _ _ _ _,trivial⟩

theorem rowSmall_valid (v o b h : ℕ) :
    (run rowSplit (((v,o),b),h)).valid ∧ (run rowI0 (((v,o),b),h)).valid ∧
      (run rowJ0 (((v,o),b),h)).valid := by
  have hs:=(counts_valid v b).2
  dsimp only [run] at hs
  rw [rowSplit,rowI0,rowJ0]
  dsimp only [rowSplit,rowV,rowI,rowJ,rowB,rowsPair,split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true]
  exact ⟨hs,hs⟩

theorem rowCell_valid (v o b h : ℕ) : (run rowCell (((v,o),b),h)).valid := by
  have ha:=rowA_valid v o b h
  have he:=rowE_valid v o b h
  have hs:=rowSmall_valid v o b h
  dsimp only [run] at ha he hs
  simp only [rowCell,rowV,rowO,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,and_true]
  exact ⟨ha,he,hs⟩

theorem rowCount_valid (v o b : ℕ) : (run rowCount ((v,o),b)).valid := by
  simp only [rowCount,rowsPair,targetCount,sourceCount,chunks,target,split,nat,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  trivial

theorem rowCoordinates_work (v o b h : ℕ) : (run rowCoordinates (((v,o),b),h)).work≤100 := by
  have hs:=(counts_work v b).2
  dsimp only [run] at hs
  rw [rowCoordinates]
  dsimp only [rowV,rowB,rowI,rowJ,rowsPair,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  rw [hs]
  norm_num

theorem rowAE_work (v o b h : ℕ) :
    (run rowA (((v,o),b),h)).work≤223 ∧ (run rowE (((v,o),b),h)).work≤223 := by
  have hc:=rowCoordinates_work v o b h
  have hp:=(pairSizes_work v b (h/sources v b) (h%sources v b))
  have hp' : (run pairSizes (run rowCoordinates (((v,o),b),h)).val).work≤120 := by
    rw [rowCoordinates_value];exact hp
  rw [rowA,rowE]
  change ((run rowCoordinates (((v,o),b),h)).work+((run pairSizes (run rowCoordinates (((v,o),b),h)).val).work+1+1)+1≤223) ∧ _
  constructor <;> change (run rowCoordinates (((v,o),b),h)).work+((run pairSizes (run rowCoordinates (((v,o),b),h)).val).work+1+1)+1≤223 <;> omega

theorem rowSmall_work (v o b h : ℕ) :
    (run rowSplit (((v,o),b),h)).work≤20 ∧ (run rowI0 (((v,o),b),h)).work≤100 ∧
      (run rowJ0 (((v,o),b),h)).work≤100 := by
  have hs:=(counts_work v b).2
  dsimp only [run] at hs
  rw [rowSplit,rowI0,rowJ0]
  dsimp only [rowSplit,rowV,rowI,rowJ,rowB,rowsPair,split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  rw [hs]
  norm_num

theorem rowCell_work (v o b h : ℕ) : (run rowCell (((v,o),b),h)).work≤1000 := by
  have hae:=rowAE_work v o b h
  have hs:=rowSmall_work v o b h
  dsimp only [run] at hae hs
  rw [rowCell]
  dsimp only [rowV,rowO,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega


theorem rowCount_work (v o b : ℕ) : (run rowCount ((v,o),b)).work≤100 := by
  simp only [rowCount,rowsPair,targetCount,sourceCount,chunks,target,split,nat,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  norm_num

theorem rectangleRows_valid (v o b : ℕ) : (run rectangleRows ((v,o),b)).valid := by
  change (run rowCount ((v,o),b)).valid ∧
    (Bill.tab (run rowCount ((v,o),b)).val Row7.blank (fun h=>run rowCell (((v,o),b),h))).valid
  exact ⟨rowCount_valid _ _ _,(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr (fun h _=>rowCell_valid _ _ _ _)⟩

theorem rectangleRows_work (v o b : ℕ) (hb : 0<b) :
    (run rectangleRows ((v,o),b)).work≤1200*(v+1)^2 := by
  change (run rowCount ((v,o),b)).work+
    (Bill.tab (run rowCount ((v,o),b)).val Row7.blank (fun h=>run rowCell (((v,o),b),h))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work,rowCount_value]
  have hc:=rowCount_work v o b
  have ht:=UniformWorkspaceSearchMachine.targets_bound (v:=v) hb
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  have hm:=Nat.mul_le_mul ht hs
  have sum:=Finset.sum_le_sum (s:=Finset.range (targets v b*sources v b)) (fun h _=>rowCell_work v o b h)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  nlinarith

end
end ExactFourierCircuits.DFTModelCacheDescriptor
