import DFTModelGlobalSectorPreparationAxis

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

def findList : List ℕ → ℕ → Found.T
 | [],_ => (0,0)
 | a::as,j => if j<a then (a,j) else findList as (j-a)

theorem findValue_model (as : List ℕ) (i j : ℕ) (ws : Tape ℕ)
 (read:∀l,l<as.length→ws.look (i+l) 0=as[l]?.getD 0) :
 findValue as.length i j ws=findList as j := by
 induction as generalizing i j with
 | nil => rfl
 | cons a as ih =>
  have h0:=read 0 (by simp)
  simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at h0
  have ht:∀l,l<as.length→ws.look ((i+1)+l) 0=as[l]?.getD 0 := by
   intro l hl
   have h:=read (l+1) (by simp;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  simp only [List.length_cons,findValue,h0,findList]
  split_ifs <;> simp_all

theorem findList_decode (as : List ℕ) (j : Fin as.sum) :
 findList as j.val=
   (as.get (UniformSectorPacking.blockDecode as j).1,
     (UniformSectorPacking.blockDecode as j).2.val) := by
 induction as with
 | nil => exact Fin.elim0 j
 | cons a as ih =>
  by_cases h:j.val<a
  · have hd : UniformSectorPacking.blockDecode (a::as) j=⟨0,⟨j.val,h⟩⟩ := by
     rw [UniformSectorPacking.blockDecode,dite_eq_left h]
    rw [hd]
    simp [findList,h]
  · rw [findList,ite_eq_right h,UniformSectorPacking.blockDecode,dite_eq_right h]
    exact ih ⟨j.val-a,by have hj:=j.isLt;change j.val<a+as.sum at hj;omega⟩

theorem sumValue_model (as : List ℕ) (i : ℕ) (ws : Tape ℕ)
 (read:∀l,l<as.length→ws.look (i+l) 0=as[l]?.getD 0) :
 sumValue as.length i ws=as.sum := by
 induction as generalizing i with
 | nil => rfl
 | cons a as ih =>
  have h0:=read 0 (by simp)
  simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at h0
  have ht:∀l,l<as.length→ws.look ((i+1)+l) 0=as[l]?.getD 0 := by
   intro l hl
   have h:=read (l+1) (by simp;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  simp only [List.length_cons,sumValue,h0,List.sum_cons]
  rw [ih (i+1) ht]

theorem sumValue_take (as : List ℕ) (j : ℕ) (bound:j≤as.length) :
 sumValue j 0 (ofList as)=(as.take j).sum := by
 have len:(as.take j).length=j := by simp [List.length_take,bound]
 conv_lhs => rw [←len]
 apply sumValue_model
 intro l hl
 rw [Nat.zero_add,ofList_look]
 have hlj:l<j := by omega
 simp [hlj]

def encodeAxis (a : UniformSectorPacking.Axis) : Axis.T :=
 (a.widths.sum,(ofList a.widths,ofList (List.ofFn (fun j=> (a.originalPermutation j).val))))

theorem localBlock_native (a : UniformSectorPacking.Axis) (b : Fin a.widths.length) :
 localBlockValue (encodeAxis a) b.val=
   (if a.widths.get b=2 then 1 else 0,
     (a.widths.get b,UniformTraversal.blockBefore a.widths b)) := by
 have hw:=a.widths_one_two (a.widths.get b) (List.get_mem _ _)
 have look:(ofList a.widths).look b.val 0=a.widths.get b := by
  simp [ofList,Tape.look,b.isLt]
 unfold localBlockValue encodeAxis
 rw [look,sumValue_take _ _ b.isLt.le]
 change (a.widths.get b-1,(a.widths.get b,(a.widths.take b.val).sum))=_
 apply Prod.ext
 · rcases hw with hw|hw <;> rw [hw] <;> norm_num
 · rfl

theorem localDigit_native (a : UniformSectorPacking.Axis) (j : Fin a.widths.sum) :
 localDigitValue (encodeAxis a) j.val=
   let b:=UniformSectorPacking.blockDecode a.widths j
   (a.widths.get b.1,(UniformTraversal.blockBefore a.widths b.1,
      (b.2.val,(a.originalPermutation j).val))) := by
 have hf:findValue a.widths.length 0 j.val (ofList a.widths)=
   (a.widths.get (UniformSectorPacking.blockDecode a.widths j).1,
    (UniformSectorPacking.blockDecode a.widths j).2.val) := by
  rw [findValue_model a.widths 0 j.val (ofList a.widths)
    (by intro l hl;rw [Nat.zero_add,ofList_look])]
  exact findList_decode a.widths j
 have hp:(ofList (List.ofFn (fun j=>(a.originalPermutation j).val))).look j.val 0=
     (a.originalPermutation j).val := by
  simp [ofList,Tape.look,j.isLt]
 have he:=congrArg Fin.val (UniformSectorPacking.blockEncode_decode a.widths j)
 change UniformTraversal.blockBefore a.widths (UniformSectorPacking.blockDecode a.widths j).1+
   (UniformSectorPacking.blockDecode a.widths j).2.val=j.val at he
 unfold localDigitValue encodeAxis
 change (let z:=findValue a.widths.length 0 j.val (ofList a.widths)
   ;(z.1,(j.val-z.2,(z.2,_))))=_
 rw [hf,hp]
 dsimp only
 congr 2
 omega

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
