import DFTModelCacheDescriptorFits
import DFTModelCacheDescriptorAmountBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targetWidth sourceWidth targets sources targetSize sourceSize pairAmount)
noncomputable section
attribute [local irreducible] amount pairSizes badPair sourceTerm sourceBad allBad
attribute [local irreducible] targetCount sourceCount

theorem pairSizes_valid (v b i j : ℕ) : (run pairSizes ((v,b),(i,j))).valid := by
  simp only [pairSizes,targetPart,sourcePart,minimum,pairB,pairV,pairI,pairJ,
    target,split,nat,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  trivial

theorem badPair_valid (v b i j : ℕ) : (run badPair ((v,b),(i,j))).valid := by
  have hv:=pairSizes_valid v b i j
  have ha:=amount_valid (targetSize v b i) (sourceSize v b j)
  have hh : (run amount (run pairSizes ((v,b),(i,j))).val).valid := by
    rw [pairSizes_value];exact ha
  rw [badPair]
  dsimp only [nat,pairV,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true]
  exact ⟨hv,hh⟩

theorem counts_valid (v b : ℕ) :
    (run targetCount (v,b)).valid ∧ (run sourceCount (v,b)).valid := by
  simp [targetCount,sourceCount,chunks,target,split,nat,
    Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem sourceTerm_valid (v b i j : ℕ) : (run sourceTerm (((v,b),i),j)).valid := by
  rw [sourceTerm]
  dsimp only [sourceRepack,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true]
  exact badPair_valid v b i j

theorem sourceBad_valid (v b i : ℕ) : (run sourceBad ((v,b),i)).valid := by
  rw [sourceBad]
  apply sumProgram_valid
  · exact ⟨trivial,(counts_valid v b).2⟩
  · intro j _
    exact sourceTerm_valid v b i j

theorem allBad_valid (v b : ℕ) : (run allBad (v,b)).valid := by
  rw [allBad]
  exact sumProgram_valid _ _ _ (counts_valid v b).1 (fun i _=>sourceBad_valid v b i)

/-- Even failed candidates are physically checked; the checker is total integer
syntax.  No division-by-zero interpretation is used in the accepted b>0 domain. -/
theorem badPair_bound (v b i j : ℕ) : (run badPair ((v,b),(i,j))).val≤1 := by
  rw [badPair_value]
  split_ifs <;> decide

theorem pairSizes_work (v b i j : ℕ) : (run pairSizes ((v,b),(i,j))).work≤120 := by
  rw [pairSizes]
  dsimp only [targetPart,sourcePart,minimum,pairB,pairV,pairI,pairJ,
    target,split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  norm_num

theorem badPair_work (v b i j : ℕ) :
    (run badPair ((v,b),(i,j))).work≤100*(targetSize v b i+sourceSize v b j+1)+127 := by
  have h1:=pairSizes_work v b i j
  have h2:=amount_work_bound (targetSize v b i) (sourceSize v b j)
  have h2' : (run amount (run pairSizes ((v,b),(i,j))).val).work≤
      100*(targetSize v b i+sourceSize v b j+1) := by rw [pairSizes_value];exact h2
  rw [badPair]
  change 3+((run pairSizes ((v,b),(i,j))).work+
    (run amount (run pairSizes ((v,b),(i,j))).val).work+1)+3≤_
  omega

theorem sourceTerm_work (v b i j : ℕ) :
    (run sourceTerm (((v,b),i),j)).work≤100*(targetSize v b i+sourceSize v b j+1)+137 := by
  rw [sourceTerm]
  change 9+(run badPair ((v,b),(i,j))).work+1≤_
  have h:=badPair_work v b i j
  omega

theorem counts_work (v b : ℕ) :
    (run targetCount (v,b)).work=23 ∧ (run sourceCount (v,b)).work=19 := by
  simp [targetCount,sourceCount,chunks,target,split,nat,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem allBad_work (v b : ℕ) (hb : 0<b) :
    (run allBad (v,b)).work≤1000*(v+1)^3 := by
  have ht:=UniformWorkspaceSearchMachine.targets_bound (v:=v) hb
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  have inner : ∀i,(run sourceBad ((v,b),i)).work≤
      24+13*sources v b+sources v b*(200*v+237) := by
    intro i
    rw [sourceBad,sumProgram_work]
    have count : run (.comp (.atom .fst) sourceCount : Prog false SourceInput w) ((v,b),i)=
      (run sourceCount (v,b)).pay 2 0 := by
        simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,
          Nat.add_comm]
        omega
    rw [count]
    dsimp only [Bill.pay]
    rw [sourceCount_value,(counts_work v b).2]
    have term : ∀j,(run sourceTerm (((v,b),i),j)).work≤200*v+237 := by
      intro j
      have h:=sourceTerm_work v b i j
      have ha : targetSize v b i≤v := (min_le_right _ _).trans ((Nat.sub_le _ _).trans (show targetWidth v≤v from Nat.sub_le _ _))
      have he : sourceSize v b j≤v := (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.div_le_self _ _))
      omega
    have sum := Finset.sum_le_sum (s:=Finset.range (sources v b))
      (fun j _=>term j)
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
    omega
  rw [allBad,sumProgram_work,targetCount_value,(counts_work v b).1]
  have sum:=Finset.sum_le_sum (s:=Finset.range (targets v b)) (fun i _=>inner i)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  have hm := Nat.mul_le_mul ht hs
  have h3 := Nat.mul_le_mul ht (le_refl (24+13*v+v*(200*v+237)))
  have hi : 24+13*sources v b+sources v b*(200*v+237)≤24+13*v+v*(200*v+237) := by nlinarith
  have hh:=Nat.mul_le_mul_left (targets v b) hi
  nlinarith

end
end ExactFourierCircuits.DFTModelCacheDescriptor
