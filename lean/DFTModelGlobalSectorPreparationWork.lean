import DFTModelGlobalSectorPreparationBounds
import DFTModelGlobalSectorPreparationCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

def volume (as : List Axis.T) : ℕ := (as.map Prod.fst).prod
def blocks (as : List Axis.T) : ℕ := (as.map (fun a=>a.2.1.len)).prod
def localWork (as : List Axis.T) : ℕ := (as.map (fun a=>(a.1+1)^2)).sum
def suffixWork : List Axis.T → ℕ
 | []=>0
 | a::as=>suffixWork as+volume (a::as)

theorem listTables_lengths (as : List Axis.T) :
 (listTables as).1=volume as ∧ (listTables as).2.1.len=blocks as ∧
 (listTables as).2.2.len=volume as := by
 induction as with
 | nil=>simp [listTables,baseValue,volume,blocks,Tape.tab]
 | cons a as ih=>simp [listTables,expandedValue,preparedAxisValue,Tape.tab,volume,blocks,ih]

theorem blocks_le_volume (as : List Axis.T) (shape:∀a∈as,a.2.1.len≤a.1) :
 blocks as≤volume as := by
 induction as with
 | nil=>rfl
 | cons a as ih=>
  change a.2.1.len*blocks as≤a.1*volume as
  exact Nat.mul_le_mul (shape a (by simp)) (ih (fun x hx=>shape x (by simp [hx])))

theorem suffixWork_le (as : List Axis.T) (two:∀a∈as,2≤a.1) :
 suffixWork as≤2*volume as := by
 induction as with
 | nil=>simp [suffixWork,volume]
 | cons a as ih=>
  have ha:=two a (by simp)
  have ht:=ih (fun x hx=>two x (by simp [hx]))
  change suffixWork as+a.1*volume as≤2*(a.1*volume as)
  have hm:=Nat.mul_le_mul_right (volume as) ha
  omega

attribute [local irreducible] prepareAxis expand body base

theorem depth_work (as : List Axis.T) (i : ℕ) (axes : Tape Axis.T)
 (read:∀l,l<as.length→axes.look (i+l) Axis.blank=as[l]?.getD Axis.blank)
 (shape:∀a∈as,a.2.1.len≤a.1) :
 (depthRun (run base) body.run as.length (i,axes)).work≤
 32+200*localWork as+2008*suffixWork as+68*as.length := by
 induction as generalizing i with
 | nil=>
  change (run base (i,axes)).work+1≤32
  rw [base_work]
 | cons a as ih=>
  have h0:=read 0 (by simp)
  simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at h0
  have ht:∀l,l<as.length→axes.look ((i+1)+l) Axis.blank=as[l]?.getD Axis.blank := by
   intro l hl
   have hh:=read (l+1) (by simp;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have hs:∀x∈as,x.2.1.len≤x.1:=fun x hx=>shape x (by simp [hx])
  have hb:=ih (i+1) ht hs
  have hp:=prepareAxis_work a (shape a (by simp))
  have he:=expand_work (preparedAxisValue a) (listTables as)
  have hl:=listTables_lengths as
  have hh:=blocks_le_volume as hs
  have hbmul:=Nat.mul_le_mul (shape a (by simp)) hh
  simp only [List.length_cons,depthRun,Bill.pay]
  rw [body_work,h0,prepareAxis_value,depth_value,tableValue_model as (i+1) axes ht]
  change (run expand (preparedAxisValue a,listTables as)).work≤
    1004*(a.2.1.len*(listTables as).2.1.len+a.1*(listTables as).2.2.len)+47 at he
  rw [hl.2.1,hl.2.2] at he
  change _≤32+200*((a.1+1)^2+localWork as)+
    2008*(suffixWork as+a.1*volume as)+68*(as.length+1)
  change (run prepareAxis a).work+
    (depthRun (run base) body.run as.length (i+1,axes)).work+
    (run expand (preparedAxisValue a,listTables as)).work+20+1≤_
  omega

theorem program_work (as : List Axis.T) (shape:∀a∈as,a.2.1.len≤a.1)
 (two:∀a∈as,2≤a.1) :
 (run program (ofList as)).work≤5000*(volume as+as.length+localWork as+1) := by
 have hd:=depth_work as 0 (ofList as) (by intro l hl;rw [Nat.zero_add,ofList_look]) shape
 have hs:=suffixWork_le as two
 have hl:=listTables_lengths as
 change (run tables (ofList as)).work+(run finalize (run tables (ofList as)).val).work+1≤_
 rw [tables_value,tableValue_ofList,finalize_work,hl.1,hl.2.2]
 have ht:(run tables (ofList as)).work=
   (depthRun (run base) body.run as.length (0,ofList as)).work+7 := by
   change 5+((depthRun (run base) body.run as.length (0,ofList as)).work+1)+1=_
   omega
 rw [ht]
 omega

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
