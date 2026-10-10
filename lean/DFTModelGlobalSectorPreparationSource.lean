import DFTModelGlobalSectorPreparationCorrect
import DFTModelGlobalSectorPreparationBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

theorem sow_length {α : Type} (n m : ℕ) (z : α) (f : ℕ→ℕ×α) :
 (Tape.sow n m z f).len=n := DFTModelCRT.sow_iter_len n m z f

theorem sow_unique {α : Type} (n m i j : ℕ) (z : α) (f : ℕ→ℕ×α)
 (hi : i < m) (hj : j < n) (hit : (f i).1 = j)
 (unique : ∀ k, k < m → k ≠ i → (f k).1 ≠ j) :
 (Tape.sow n m z f).look j z=(f i).2 := by
 induction m with
 | zero=>omega
 | succ m ih=>
  change ((Tape.sow n m z f).set (f m).1 (f m).2).look j z=_
  by_cases last:i=m
  · subst i
    simp only [Tape.look,Tape.set,sow_length,hj,↓reduceDIte,hit,↓reduceIte]
  · have neq:j≠(f m).1:=Ne.symm (unique m (by omega) (Ne.symm last))
    have old:=ih (by omega) (fun k hk hki=>unique k (by omega) hki)
    simpa only [Tape.look,Tape.set,sow_length,hj,↓reduceDIte,neq,↓reduceIte] using old

theorem sow_equiv {α : Type} {V : ℕ} (e : Equiv.Perm (Fin V)) (g : Fin V→α)
 (f : ℕ→ℕ×α) (read:∀i : Fin V,f i.val=((e i).val,g i)) (z : α) (j : Fin V) :
 (Tape.sow V V z f).look j.val z=g (e.symm j) := by
 have h:=sow_unique V V (e.symm j).val j.val z f (e.symm j).isLt j.isLt
 apply (h ?_ ?_).trans
 · rw [read]
 · rw [read];simp
 · intro k hk ne eq
   rw [read ⟨k,hk⟩] at eq
   have he:e ⟨k,hk⟩=j:=Fin.ext eq
   have hi:(⟨k,hk⟩:Fin V)=e.symm j:=(Equiv.eq_symm_apply e).2 he
   exact ne (congrArg Fin.val hi)

theorem addressPair_native (as : List UniformSectorPacking.Axis)
 (i : Fin (UniformSectorPacking.radices as).prod) :
 addressPair (nativeTables as) i.val=
   ((DFTModelNativeSectorRecurrence.packedAddressEquiv as i).val,
    (DFTModelNativeSectorRecurrence.originalAddressEquiv as i).val) := by
 have hp:=DFTModelNativeSectorRecurrence.packedAddress_value as i
 have ho:=DFTModelNativeSectorRecurrence.originalAddress_value as i
 simp only [addressPair,nativeTables,DFTModelNativeSectorRecurrence.addressRows,
   ofList,Tape.look,List.length_ofFn,i.isLt,↓reduceDIte,List.getElem_ofFn]
 exact Prod.ext hp.symm ho.symm

/-- Packing is original→packed; the gather table is the inverse, packed→original. -/
theorem program_native (as : List UniformSectorPacking.Axis) :
 let u:=(run program (ofList (as.map encodeAxis))).val
 u.1=(UniformSectorPacking.radices as).prod ∧
 u.2.1.len=(UniformSectorPacking.radices as).prod ∧
 u.2.2.1.len=(UniformSectorPacking.radices as).prod ∧
 (∀j : Fin (UniformSectorPacking.radices as).prod,
   u.2.1.look j.val 0=(UniformSectorPacking.packingPermutation as j).val) ∧
 (∀j : Fin (UniformSectorPacking.radices as).prod,
   u.2.2.1.look j.val 0=(UniformSectorPacking.unpackingPermutation as j).val) ∧
 u.2.2.2=ofList ((UniformSectorPacking.sectorStates as).map encodeSector) := by
 rw [program_value,tableValue_ofList,listTables_native]
 dsimp only [finalizedValue,nativeTables]
 simp only [ofList,DFTModelNativeSectorRecurrence.addressRows_length]
 refine ⟨trivial,sow_length _ _ _ _,sow_length _ _ _ _,?_,?_,trivial⟩
 · intro j
   change (Tape.sow _ _ 0 (fun i=>(addressPair (nativeTables as) i).swap)).look j.val 0=_
   rw [sow_equiv (DFTModelNativeSectorRecurrence.originalAddressEquiv as)
     (fun i=>(DFTModelNativeSectorRecurrence.packedAddressEquiv as i).val)
     _ (fun i=>by rw [addressPair_native];rfl)]
   exact (congrArg Fin.val (DFTModelNativeSectorRecurrence.packingAddress as
     ((DFTModelNativeSectorRecurrence.originalAddressEquiv as).symm j))).symm.trans
       (by simp)
 · intro j
   change (Tape.sow _ _ 0 (addressPair (nativeTables as))).look j.val 0=_
   rw [sow_equiv (DFTModelNativeSectorRecurrence.packedAddressEquiv as)
     (fun i=>(DFTModelNativeSectorRecurrence.originalAddressEquiv as i).val)
     _ (fun i=>addressPair_native as i)]
   exact (congrArg Fin.val (DFTModelNativeSectorRecurrence.unpackingAddress as
     ((DFTModelNativeSectorRecurrence.packedAddressEquiv as).symm j))).symm.trans
       (by simp)

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
