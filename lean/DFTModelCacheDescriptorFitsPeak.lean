import DFTModelCacheDescriptorFitsBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targetWidth sourceWidth targets sources targetSize sourceSize)
noncomputable section
attribute [local irreducible] amount pairSizes badPair sourceTerm sourceBad allBad
attribute [local irreducible] targetCount sourceCount

theorem pairSizes_peak (v b i j : ℕ) (hb : b≤v) (hi : i≤v) (hj : j≤v) :
    (run pairSizes ((v,b),(i,j))).peak≤10*(v+1)^2 := by
  have him:=Nat.mul_le_mul hi hb
  have hjm:=Nat.mul_le_mul hj hb
  have hd:=Nat.div_le_self v 2
  have hbase : v≤10*(v+1)^2 := by nlinarith
  have hmul : v*v≤10*(v+1)^2 := by nlinarith
  have htwo : 2≤10*(v+1)^2 := by nlinarith
  rw [pairSizes]
  dsimp only [targetPart,sourcePart,minimum,pairB,pairV,pairI,pairJ,
    target,split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [max_le_iff]
  omega

theorem badPair_peak (v b i j : ℕ) (hb : b≤v) (hi : i≤v) (hj : j≤v) :
    (run badPair ((v,b),(i,j))).peak≤4000*(v+1)^2 := by
  have h1:=pairSizes_peak v b i j hb hi hj
  have h2:=amount_peak (targetSize v b i) (sourceSize v b j)
  have ha : targetSize v b i≤v := (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have he : sourceSize v b j≤v := (min_le_right _ _).trans ((Nat.sub_le _ _).trans (Nat.div_le_self _ _))
  have ham : (run amount (run pairSizes ((v,b),(i,j))).val).peak≤1000*(targetSize v b i+sourceSize v b j+1)^2 := by
    rw [pairSizes_value];exact h2
  have ham' : (run amount (run pairSizes ((v,b),(i,j))).val).peak≤4000*(v+1)^2 := by
    have hpow:=Nat.pow_le_pow_left (show targetSize v b i+sourceSize v b j+1≤2*(v+1) from by omega) 2
    nlinarith
  have hbase : 1≤4000*(v+1)^2 := by nlinarith
  have h1' : (run pairSizes ((v,b),(i,j))).peak≤4000*(v+1)^2 := by nlinarith
  dsimp only [run] at h1' ham'
  rw [badPair]
  dsimp only [nat,pairV,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [max_le_iff]
  split_ifs <;> omega

theorem counts_peak (v b : ℕ) (hb : b≤v) :
    (run targetCount (v,b)).peak≤4*(v+1) ∧ (run sourceCount (v,b)).peak≤4*(v+1) := by
  have hd:=Nat.div_le_self v 2
  have hdt:=Nat.div_le_self (v-v/2+b-1) b
  have hds:=Nat.div_le_self (v/2+b-1) b
  simp only [targetCount,sourceCount,chunks,target,split,nat,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_le_iff]
  omega

theorem sourceTerm_peak (v b i j : ℕ) (hb : b≤v) (hi : i≤v) (hj : j≤v) :
    (run sourceTerm (((v,b),i),j)).peak≤4000*(v+1)^2 := by
  have h:=badPair_peak v b i j hb hi hj
  simpa only [sourceTerm,sourceRepack,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero] using h

theorem sourceBad_bound (v b i : ℕ) : (run sourceBad ((v,b),i)).val≤ sources v b := by
  rw [sourceBad,sumProgram_value]
  change (∑j∈Finset.range (run sourceCount (v,b)).val,
    (run sourceTerm (((v,b),i),j)).val)≤_
  rw [sourceCount_value]
  calc
    _ ≤ ∑_j∈Finset.range (sources v b),1 := by
      apply Finset.sum_le_sum
      intro j _
      rw [sourceTerm_value]
      split_ifs <;> decide
    _ = _ := by simp

theorem sourceBad_peak (v b i : ℕ) (hb : 0<b) (hbv : b≤v) (hi : i≤v) :
    (run sourceBad ((v,b),i)).peak≤4000*(v+1)^2 := by
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  have count : (run (.comp (.atom .fst) sourceCount : Prog false SourceInput w) ((v,b),i)).val=sources v b :=
    sourceCount_value v b
  have cp : (run (.comp (.atom .fst) sourceCount : Prog false SourceInput w) ((v,b),i)).peak≤4*(v+1) := by
    simpa only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero] using (counts_peak v b hbv).2
  rw [sourceBad]
  have h:=sumProgram_peak (.comp (.atom .fst) sourceCount) sourceTerm ((v,b),i) 1 (4000*(v+1)^2)
    (by intro j _; rw [sourceTerm_value];split_ifs <;> decide)
    (by
      intro j hj
      have hj' : j<sources v b := by simpa only [count] using hj
      exact sourceTerm_peak v b i j hbv hi ((Nat.le_of_lt hj').trans hs))
  rw [count] at h
  have hm : sources v b*1≤4000*(v+1)^2 := by nlinarith
  exact h.trans (by simp only [max_le_iff];exact ⟨by nlinarith,by nlinarith,le_refl _,hm⟩)

theorem allBad_peak (v b : ℕ) (hb : 0<b) (hbv : b≤v) :
    (run allBad (v,b)).peak≤4000*(v+1)^2 := by
  have ht:=UniformWorkspaceSearchMachine.targets_bound (v:=v) hb
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  rw [allBad]
  have h:=sumProgram_peak targetCount sourceBad (v,b) (sources v b) (4000*(v+1)^2)
    (fun i _=>sourceBad_bound v b i)
    (by
      intro i hi
      have hi' : i<targets v b := (targetCount_value v b) ▸ hi
      exact sourceBad_peak v b i hb hbv ((Nat.le_of_lt hi').trans ht))
  rw [targetCount_value] at h
  have cp:=(counts_peak v b hbv).1
  have hm:=Nat.mul_le_mul ht hs
  exact h.trans (by simp only [max_le_iff];exact ⟨by nlinarith,by nlinarith,le_refl _,by nlinarith⟩)

end
end ExactFourierCircuits.DFTModelCacheDescriptor
