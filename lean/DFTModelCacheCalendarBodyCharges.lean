import DFTModelCacheCalendarCharges

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node prepare direct finish leftInput rightInput

theorem code_comp_work {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r t u)
    (h : Handler r) (x : s.T) : (Code.run (.comp f g) h x).work=
      (Code.run f h x).work+(Code.run g h (Code.run f h x).val).work+1 := rfl

theorem code_fork_work {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r s u)
    (h : Handler r) (x : s.T) : (Code.run (.fork f g) h x).work=
      (Code.run f h x).work+(Code.run g h x).work+1 := rfl

theorem code_ifz_work {r : Port} {s t : Ty} (q : Code false r s w) (f g : Code false r s t)
    (h : Handler r) (x : s.T) : (Code.run (.ifz q f g) h x).work=
      (Code.run q h x).work+
      (if (Code.run q h x).val=0 then (Code.run f h x).work else (Code.run g h x).work)+1 := by
  change (Code.run q h x).work+(if (Code.run q h x).val=0 then Code.run f h x else Code.run g h x).work+1=_
  split_ifs <;>rfl

theorem splitCode_work (h : Handler RecPort) (nf : NodeFrame.T) :
    (splitCode.run h nf).work≤
      (h (nf.1.1/2,(nf.1.2.1,nf.1.2.2))).work+
      (h (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2))).work+
      (run finish (nf,((h (nf.1.1/2,(nf.1.2.1,nf.1.2.2))).val,
        (h (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2))).val))).work+65 := by
  rw [splitCode,code_comp_work,code_fork_work,code_fork_work,code_comp_work,code_comp_work]
  have l:(run leftInput nf).work=19:=by rw [leftInput];rfl
  have r:(run rightInput nf).work=35:=by rw [rightInput];rfl
  change 1+(((run leftInput nf).work+1)+((h (run leftInput nf).val).work+1)+1+
    (((run rightInput nf).work+1)+((h (run rightInput nf).val).work+1)+1)+1)+1+
    ((run finish (nf,((h (run leftInput nf).val).val,(h (run rightInput nf).val).val))).work+1)+1≤_
  rw [l,r,leftInput_value,rightInput_value]
  omega

theorem branch_work (h : Handler RecPort) (v o t b : ℕ) (L : Tape Row7.T) :
    (branch.run h ((v,(o,t)),(b,L))).work≤
      if v<2 ∨ b=0 then (run direct (v,(o,t))).work+16
      else (splitCode.run h ((v,(o,t)),(b,L))).work+13 := by
  rw [branch,code_ifz_work]
  have cmp:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,L))).val=
    if v<2 then 1 else 0:=rfl
  have cw:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,L))).work=8:=rfl
  have dw:(directCode.run h ((v,(o,t)),(b,L))).work=(run direct (v,(o,t))).work+3:=by
    change 1+((run direct (v,(o,t))).work+1)+1=_
    omega
  rw [cmp,cw]
  by_cases hv:v<2
  · simp only [hv,ite_true,Nat.one_ne_zero,ite_false,true_or,dw]
    omega
  · simp only [hv,ite_false,ite_true,false_or]
    rw [code_ifz_work]
    have sv:(Code.run (.comp (.atom .snd) (.atom .fst) : Code false RecPort NodeFrame w) h ((v,(o,t)),(b,L))).val=b:=rfl
    have sw:(Code.run (.comp (.atom .snd) (.atom .fst) : Code false RecPort NodeFrame w) h ((v,(o,t)),(b,L))).work=3:=rfl
    rw [sv,sw,dw]
    split_ifs <;>omega

theorem body_direct_work (h : Handler RecPort) (v o t : ℕ) (hd:v<2 ∨ selected v=0) :
    (body.run h (v,(o,t))).work≤(run DFTModelCacheDescriptor.node (v,o)).work+150 := by
  have hb:=branch_work h v o t (selected v)
    (ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode))
  rw [ite_eq_left hd] at hb
  have hdw:=direct_work v o t
  rw [body,code_comp_work]
  change ((run prepare (v,(o,t))).work+1)+_+1≤_
  rw [code_import_value,prepare_value,prepare_work]
  omega

theorem body_split_work (h : Handler RecPort) (v o t : ℕ) (hd:¬(v<2 ∨ selected v=0)) :
    (body.run h (v,(o,t))).work≤(run DFTModelCacheDescriptor.node (v,o)).work+
      (h (v/2,(o,t))).work+(h (v-v/2,(o+v/2,t))).work+
      (run finish (((v,(o,t)),(selected v,ofList ((rows v o (selected v)).map rectangleEncode))),
        ((h (v/2,(o,t))).val,(h (v-v/2,(o+v/2,t))).val))).work+100 := by
  have hb:=branch_work h v o t (selected v)
    (ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode))
  rw [ite_eq_right hd] at hb
  have hs:=splitCode_work h
    ((v,(o,t)),(selected v,ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode)))
  simp only [currentRows,hd,ite_false] at hb hs
  rw [body,code_comp_work]
  change ((run prepare (v,(o,t))).work+1)+_+1≤_
  rw [code_import_value,prepare_value,prepare_work]
  simp only [currentRows,hd,ite_false]
  omega

end
end ExactFourierCircuits.DFTModelCacheCalendar
