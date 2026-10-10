import DFTModelCacheSelectedPhysicalRowsNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelRecursiveScalarCore
open DFTModelCacheHeight (straight_work straightWork)
open scoped BigOperators
noncomputable section
attribute [local irreducible] borrowed borrowedArgs mapper prepare program
 DFTModelCacheColorSelection.program

theorem tab_work_bound {s t:Ty} (n:Prog false s w) (b:Prog false (p s w) t)
 (x:s.T) (C:ℕ) (hb:∀j,(run b (x,j)).work≤C) :
 (run (.tab n b) x).work≤(run n x).work+5+(4+C)*(run n x).val := by
 have sum:(∑j∈Finset.range (run n x).val,(run b (x,j)).work)≤(run n x).val*C := by
  calc
   _≤∑_j∈Finset.range (run n x).val,C:=Finset.sum_le_sum (fun j _=>hb j)
   _=_:=by simp
 change (run n x).work+(Bill.tab (run n x).val t.blank (fun j=>run b (x,j))).work+1≤_
 rw [ModelEquivalenceInterpreter.tab_work]
 nlinarith

theorem candidate_work (x:Candidate.T) : (run candidate x).work≤100 :=
 (straight_work candidate (by with_unfolding_all decide) () x).trans (by with_unfolding_all decide)
theorem eligible_work (x:Candidate.T) : (run eligible x).work≤500 :=
 (straight_work eligible (by with_unfolding_all decide) () x).trans (by with_unfolding_all decide)
theorem mapRow_work (x:Cell.T) : (run mapRow x).work≤2000 :=
 (straight_work mapRow (by with_unfolding_all decide) () x).trans (by with_unfolding_all decide)

theorem borrowedArgs_work (x:Geometry.T) : (run borrowedArgs x).work≤1000*(x.1+1) := by
 have c:=tab_work_bound radix candidate x 100 (fun j=>candidate_work (x,j))
 have e:=tab_work_bound radix eligible x 500 (fun j=>eligible_work (x,j))
 change (run (.tab radix candidate) x).work≤1+5+(4+100)*x.1 at c
 change (run (.tab radix eligible) x).work≤1+5+(4+500)*x.1 at e
 rw [borrowedArgs,fork_run,fork_run]
 change 1+((run (.tab radix candidate) x).work+(run (.tab radix eligible) x).work+1)+1≤_
 omega

theorem borrowedArgs_length (x:Geometry.T) : (run borrowedArgs x).val.2.1.len=x.1 := by
 rcases x with ⟨v,s,e,t,a,g⟩
 change (run borrowedArgs (geom v s e t a g)).val.2.1.len=v
 rw [borrowedArgs_value]
 rfl

theorem borrowed_work (x:Geometry.T) :
 (run borrowed x).work≤1000*(x.1+1)+DFTModelCacheColorSelection.workBudget x.1+1 := by
 have a:=borrowedArgs_work x
 have b:=DFTModelCacheColorSelection.program_work (run borrowedArgs x).val
 rw [borrowedArgs_length] at b
 rw [borrowed,comp_run]
 change (run borrowedArgs x).work+(run DFTModelCacheColorSelection.program (run borrowedArgs x).val).work+1≤_
 omega

theorem mapper_work (x:Ready.T) : (run mapper x).work≤10+2004*x.1.2.len := by
 have count:run (.comp rows (.atom .len)) x=⟨x.1.2.len,5,x.1.2.len,True⟩:=by
  simp [rows,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
 have h:=tab_work_bound (.comp rows (.atom .len)) mapRow x 2000 (fun j=>mapRow_work (x,j))
 rw [count] at h
 rw [mapper]
 exact h

def workBudget (v M:ℕ) : ℕ :=
 1000*(v+1)+DFTModelCacheColorSelection.workBudget v+2004*M+16

/-- Work depends on the genuine physical axis radix and selected occurrence
count, never on coefficient addresses or scalar heap bases. -/
theorem program_work (x:Input.T) : (run program x).work≤workBudget x.1.1 x.2.len := by
 have borrow:=borrowed_work x.1
 have prep: (run prepare x).work=(run borrowed x.1).work+4 := by
  rw [prepare,DFTModelCacheColorRebase.retained_comp_run]
  change 1+(run borrowed x.1).work+3=_
  omega
 have maps:=mapper_work (x,(run borrowed x.1).val)
 change (run mapper (x,(run borrowed x.1).val)).work≤10+2004*x.2.len at maps
 rw [program,comp_run]
 change (run prepare x).work+(run mapper (run prepare x).val).work+1≤_
 rw [prep,prepare_value]
 unfold workBudget
 omega

theorem workBudget_polynomial (v M:ℕ) : workBudget v M≤5000*(v+M+1)^2 := by
 have selected:=DFTModelCacheColorSelection.workBudget_polynomial v
 have monotone:(v+1)^2≤(v+M+1)^2:=Nat.pow_le_pow_left (by omega) 2
 have positive:1≤v+M+1:=by omega
 have square:v+M+1≤(v+M+1)^2:=by nlinarith
 unfold workBudget
 nlinarith

theorem program_work_polynomial (x:Input.T) :
 (run program x).work≤5000*(x.1.1+x.2.len+1)^2 :=
 (program_work x).trans (workBudget_polynomial _ _)

theorem program_valid (x:Input.T) : (run program x).valid :=
 DFTModelCacheTraversal.indexCode_valid program (by with_unfolding_all decide) () x

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
