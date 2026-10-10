import DFTModelCacheBucketProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
open DFTModelCacheDAGDepth (nat)
attribute [local irreducible] accepts

theorem replacement_bound (x:Input.T) (l q i:ℕ) (s:State.T):
    (run replacement ((x,(l,q)),(i,s))).valid ∧
    (run replacement ((x,(l,q)),(i,s))).work ≤ 30 ∧
    (run replacement ((x,(l,q)),(i,s))).peak ≤ 1 := by
  by_cases h:s.1<q <;>by_cases hr:q<s.1 <;>
    simp [replacement,ordinal,current,query,index,value,equal,nat,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay,h,hr]

attribute [local irreducible] replacement

theorem step_run (x:Input.T) (l q i:ℕ) (s:State.T):
    run step ((x,(l,q)),(i,s))=
      if depthValue x i=l then
        ⟨(s.1+1,(run replacement ((x,(l,q)),(i,s))).val),
          52+(run replacement ((x,(l,q)),(i,s))).work,
          max (x.1+1+i) (max (s.1+1) (run replacement ((x,(l,q)),(i,s))).peak),
          (run replacement ((x,(l,q)),(i,s))).valid⟩
      else ⟨s,36+(if depthValue x i<l then 3 else 9),x.1+1+i,True⟩ := by
  rw [step]
  change ((run accepts ((x,(l,q)),(i,s))).pass
    (fun z=>if z=0 then run current ((x,(l,q)),(i,s)) else
      run (.fork (nat .add ordinal (.atom (.lit 1))) replacement) ((x,(l,q)),(i,s)))).pay 1 0=_
  rw [accepts_run]
  by_cases h:depthValue x i=l
  · simp only [h,ite_true,lt_self_iff_false,ite_false]
    simp [nat,ordinal,current,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
    omega
  · simp [h,current,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    omega

theorem step_bound (x:Input.T) (l q i:ℕ) (s:State.T):
    (run step ((x,(l,q)),(i,s))).valid ∧
    (run step ((x,(l,q)),(i,s))).work ≤ 82 ∧
    (run step ((x,(l,q)),(i,s))).peak ≤ max (x.1+1+i) (s.1+1) := by
  have hr:=replacement_bound x l q i s
  rw [step_run]
  split_ifs <;>dsimp only [Bill.valid,Bill.work,Bill.peak] <;>exact ⟨by tauto,by omega,by omega⟩

theorem advance_count (d:ℕ→ℕ) (l q i:ℕ) (s:State.T):
    (advance d l q i s).1 ≤ s.1+1 := by
  unfold advance
  split_ifs <;>simp

theorem advance_value (d:ℕ→ℕ) (l q i:ℕ) (s:State.T):
    (advance d l q i s).2 ≤ max s.2 i := by
  unfold advance
  split_ifs <;>simp

end
end ExactFourierCircuits.DFTModelCacheBucket
