import DFTModelGlobalSectorPreparationRun
import DFTModelGlobalSectorPreparationLocalCorrect
import DFTModelNativeSectorRecurrenceAddresses

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

theorem tab_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
 Tape.tab n f=ofList (List.ofFn (fun j : Fin n=>f j.val)) := by
 apply tape_ext _ _ (f 0) (by simp [Tape.tab,ofList])
 intro j hj
 change j<n at hj
 simp [Tape.tab,Tape.look,ofList,hj]

theorem tab_cartesian {α : Type} (n m : ℕ) (g : ℕ → α)
 (f : Fin n → Fin m → α) (h:∀i j,g (i.val*m+j.val)=f i j) :
 Tape.tab (n*m) g=ofList ((List.finRange n).flatMap
   (fun i=>List.ofFn (fun j : Fin m=>f i j))) := by
 rw [tab_ofFn,List.ofFn_mul]
 change ofList _=ofList (((List.finRange n).map _).flatten)
 rw [←List.ofFn_eq_map]
 congr 2
 apply congrArg List.ofFn
 funext i
 apply congrArg List.ofFn
 funext j
 exact h i j

def listTables : List Axis.T → Tables.T
 | []=>baseValue
 | a::as=>expandedValue (preparedAxisValue a) (listTables as)

theorem tableValue_model (as : List Axis.T) (i : ℕ) (axes : Tape Axis.T)
 (read:∀l,l<as.length→axes.look (i+l) Axis.blank=as[l]?.getD Axis.blank) :
 tableValue as.length i axes=listTables as := by
 induction as generalizing i with
 | nil=>rfl
 | cons a as ih=>
  have h0:=read 0 (by simp)
  simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at h0
  have ht:∀l,l<as.length→axes.look ((i+1)+l) Axis.blank=as[l]?.getD Axis.blank := by
   intro l hl
   have hh:=read (l+1) (by simp;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  simp only [List.length_cons,tableValue,listTables,h0]
  rw [ih (i+1) ht]

theorem tableValue_ofList (as : List Axis.T) :
 tableValue (ofList as).len 0 (ofList as)=listTables as := by
 apply tableValue_model
 intro l hl
 rw [Nat.zero_add,ofList_look]

def encodeSector (s : UniformSectorPacking.BlockState) : Sector.T := (s.pairs,(s.width,s.start))
def nativeTables (as : List UniformSectorPacking.Axis) : Tables.T :=
 ((UniformSectorPacking.radices as).prod,
   (ofList ((UniformSectorPacking.sectorStates as).map encodeSector),
     ofList (DFTModelNativeSectorRecurrence.addressRows as)))

theorem nativeTables_nil : nativeTables []=baseValue := by
 apply Prod.ext (by rfl)
 apply Prod.ext
 · change ofList [(0,(1,0))]=Tape.tab 1 (fun _=>(0,(1,0)))
   rw [tab_ofFn];rfl
 · change ofList [(1,(0,(0,0)))]=Tape.tab 1 (fun _=>(1,(0,(0,0))))
   rw [tab_ofFn];rfl

theorem nativeTables_cons (a : UniformSectorPacking.Axis)
 (as : List UniformSectorPacking.Axis) :
 expandedValue (preparedAxisValue (encodeAxis a)) (nativeTables as)=nativeTables (a::as) := by
 have lb:(preparedAxisValue (encodeAxis a)).2.1.len=a.widths.length:=rfl
 have ld:(preparedAxisValue (encodeAxis a)).1=a.widths.sum:=rfl
 have ts:(nativeTables as).2.1.len=(UniformSectorPacking.sectorStates as).length:=by
   simp [nativeTables,ofList]
 have ta:(nativeTables as).2.2.len=(DFTModelNativeSectorRecurrence.addressRows as).length:=rfl
 apply Prod.ext (by rfl)
 apply Prod.ext
 · change Tape.tab (_*_) (sectorCellValue (preparedAxisValue (encodeAxis a)) (nativeTables as))=
      ofList ((UniformSectorPacking.sectorStates (a::as)).map encodeSector)
   rw [lb,ts,DFTModelNativeSectorRecurrence.sectorStates_cons,List.map_flatMap]
   rw [tab_cartesian a.widths.length (UniformSectorPacking.sectorStates as).length _
     (fun b j=>encodeSector (DFTModelNativeSectorRecurrence.extendSector a as b
       ((UniformSectorPacking.sectorStates as).get j)))]
   · congr 1
     apply congrArg (fun f=>(List.finRange a.widths.length).flatMap f)
     funext b
     change List.ofFn ((encodeSector ∘ DFTModelNativeSectorRecurrence.extendSector a as b) ∘ (UniformSectorPacking.sectorStates as).get)=_
     rw [←List.map_ofFn,List.ofFn_get,List.map_map]
   · intro b j
     have hj:=j.isLt
     have hd:(b.val*(UniformSectorPacking.sectorStates as).length+j.val)/
       (UniformSectorPacking.sectorStates as).length=b.val := by
       rw [Nat.mul_comm b.val _,Nat.mul_add_div (by omega),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
     have hr:(b.val*(UniformSectorPacking.sectorStates as).length+j.val)%
       (UniformSectorPacking.sectorStates as).length=j.val := by
       simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
     have hl:(preparedAxisValue (encodeAxis a)).2.1.look b.val (0,(0,0))=
       localBlockValue (encodeAxis a) b.val := Tape.look_of_lt _ _ b.isLt
     have hu:(nativeTables as).2.1.look j.val (0,(0,0))=
       encodeSector ((UniformSectorPacking.sectorStates as).get j) := by
       simp [nativeTables,ofList,Tape.look,j.isLt]
     unfold sectorCellValue
     rw [ts,hd,hr,hl,hu,localBlock_native]
     rfl
 · change Tape.tab (_*_) (addressCellValue (preparedAxisValue (encodeAxis a)) (nativeTables as))=
      ofList (DFTModelNativeSectorRecurrence.addressRows (a::as))
   rw [ld,ta,DFTModelNativeSectorRecurrence.addressRows_cons]
   rw [tab_cartesian a.widths.sum (DFTModelNativeSectorRecurrence.addressRows as).length _
     (fun j i=>DFTModelNativeSectorRecurrence.extendAddress a as j
       ((DFTModelNativeSectorRecurrence.addressRows as).get i))]
   · congr 1
     apply congrArg (fun f=>(List.finRange a.widths.sum).flatMap f)
     funext j
     change List.ofFn (DFTModelNativeSectorRecurrence.extendAddress a as j ∘ (DFTModelNativeSectorRecurrence.addressRows as).get)=_
     rw [←List.map_ofFn,List.ofFn_get]
   · intro j i
     have hi:=i.isLt
     have hd:(j.val*(DFTModelNativeSectorRecurrence.addressRows as).length+i.val)/
       (DFTModelNativeSectorRecurrence.addressRows as).length=j.val := by
       rw [Nat.mul_comm j.val _,Nat.mul_add_div (by omega),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
     have hr:(j.val*(DFTModelNativeSectorRecurrence.addressRows as).length+i.val)%
       (DFTModelNativeSectorRecurrence.addressRows as).length=i.val := by
       simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
     have hl:(preparedAxisValue (encodeAxis a)).2.2.look j.val (0,(0,(0,0)))=
       localDigitValue (encodeAxis a) j.val := Tape.look_of_lt _ _ j.isLt
     have hu:(nativeTables as).2.2.look i.val (0,(0,(0,0)))=
       (DFTModelNativeSectorRecurrence.addressRows as).get i := by
       simp [nativeTables,ofList,Tape.look,i.isLt]
     unfold addressCellValue
     rw [ta,hd,hr,hl,hu,localDigit_native]
     rfl

theorem listTables_native (as : List UniformSectorPacking.Axis) :
 listTables (as.map encodeAxis)=nativeTables as := by
 induction as with
 | nil=>exact nativeTables_nil.symm
 | cons a as ih=>simpa only [List.map_cons,listTables,ih] using nativeTables_cons a as

theorem tables_native (as : List UniformSectorPacking.Axis) :
 (run tables (ofList (as.map encodeAxis))).val=nativeTables as := by
 rw [tables_value,tableValue_ofList,listTables_native]

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
