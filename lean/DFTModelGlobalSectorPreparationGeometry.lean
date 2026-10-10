import DFTModelGlobalSectorPreparationCorrect
import DFTModelGlobalSectorPreparationLocalPeak
import DFTModelGlobalSectorPreparationWork

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

structure TablesBound (t : Tables.T) (R : ℕ) : Prop where
 volume:t.1≤R
 blocks:t.2.1.len≤R
 addresses:t.2.2.len≤R
 sector:∀j,let s:=t.2.1.look j (0,(0,0));s.1≤R ∧ s.2.1≤R ∧ s.2.2≤R
 address:∀j,let s:=t.2.2.look j (0,(0,(0,0)));s.1≤R ∧ s.2.1≤R ∧ s.2.2.1≤R ∧ s.2.2.2≤R

theorem sector_geometry (as : List UniformSectorPacking.Axis)
 (b : UniformSectorPacking.BlockChoices as) :
 (UniformSectorPacking.sectorRadices as b).prod≤(UniformSectorPacking.radices as).prod ∧
 UniformSectorPacking.sectorStart as b≤(UniformSectorPacking.radices as).prod := by
 have hw:=Fintype.card_le_of_injective (UniformSectorPacking.sectorCoordinate as b)
   (UniformSectorPacking.sectorCoordinate_injective as b)
 simp only [Fintype.card_fin] at hw
 have hz:0<(UniformSectorPacking.sectorRadices as b).prod:=UniformSectorPacking.sectorProduct_pos as b
 have hs:=(UniformSectorPacking.sectorCoordinate as b ⟨0,hz⟩).isLt
 rw [UniformSectorPacking.sectorCoordinate_value] at hs
 exact ⟨hw,by omega⟩

theorem native_volume_pos (as : List UniformSectorPacking.Axis) :
 0<(UniformSectorPacking.radices as).prod := by
 induction as with
 | nil=>simp
 | cons a as ih=>change 0<a.widths.sum*(UniformSectorPacking.radices as).prod
                 exact Nat.mul_pos (by have h:=a.radix_two;omega) ih

theorem native_axes_le_volume (as : List UniformSectorPacking.Axis) :
 as.length≤(UniformSectorPacking.radices as).prod := by
 induction as with
 | nil=>simp
 | cons a as ih=>
  have ht:=native_volume_pos as
  have ha:=a.radix_two
  change as.length+1≤a.widths.sum*(UniformSectorPacking.radices as).prod
  have hm:=Nat.mul_le_mul_right (UniformSectorPacking.radices as).prod ha
  omega

theorem native_tables_bound (as : List UniformSectorPacking.Axis) :
 TablesBound (nativeTables as) (UniformSectorPacking.radices as).prod := by
 have hcounts:(UniformSectorPacking.sectorStates as).length≤(UniformSectorPacking.radices as).prod := by
  have hb:=blocks_le_volume (as.map encodeAxis) (by
    intro x hx
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx
    exact native_blocks_bound a)
  simpa [UniformSectorPacking.sectorStates,UniformSectorPacking.sectorWidths_length,
    volume,blocks,encodeAxis,ofList,List.map_map,Function.comp_def] using hb
 refine ⟨le_rfl,?_,?_,?_,?_⟩
 · simpa [nativeTables,ofList] using hcounts
 · simp [nativeTables,ofList,DFTModelNativeSectorRecurrence.addressRows_length]
 · intro j
   by_cases hj:j<(UniformSectorPacking.sectorStates as).length
   · have hj':j<(UniformSectorPacking.sectorWidths as).length:=by
       simpa only [UniformSectorPacking.sectorStates,List.length_ofFn] using hj
     let b:=(UniformSectorPacking.sectorIndexEquiv as).symm ⟨j,hj'⟩
     have hg:=sector_geometry as b
     have hp:=UniformSectorPacking.sectorPairCount_le as b
     have ha:=native_axes_le_volume as
     have look:(nativeTables as).2.1.look j (0,(0,0))=
       encodeSector (UniformSectorPacking.expectedBlockState as b):=by
       simp [nativeTables,ofList,UniformSectorPacking.sectorStates,Tape.look,hj',b]
     rw [look]
     exact ⟨le_trans hp ha,hg.1,hg.2⟩
   · simp [nativeTables,ofList,Tape.look,hj]
 · intro j
   by_cases hj:j<(UniformSectorPacking.radices as).prod
   · let x:=DFTModelNativeSectorRecurrence.addressPositionEquiv as ⟨j,hj⟩
     have hg:=sector_geometry as x.1
     have hp:=(UniformSectorPacking.packedEquiv as x).isLt
     rw [UniformSectorPacking.packedEquiv_value] at hp
     have ho:=(UniformSectorPacking.originalEquiv as x).isLt
     simp only [nativeTables,ofList,Tape.look,DFTModelNativeSectorRecurrence.addressRows,
       List.length_ofFn,hj,↓reduceDIte,List.getElem_ofFn,
       DFTModelNativeSectorRecurrence.addressValue]
     change (UniformSectorPacking.sectorRadices as x.1).prod≤_ ∧
       UniformSectorPacking.sectorStart as x.1≤_ ∧
       UniformTraversal.encode (UniformSectorPacking.sectorRadices as x.1) x.2≤_ ∧
       (UniformSectorPacking.originalEquiv as x).val≤_
     exact ⟨hg.1,hg.2,by omega,ho.le⟩
   · simp [nativeTables,ofList,Tape.look,DFTModelNativeSectorRecurrence.addressRows,
       List.length_ofFn,hj]

theorem prepared_axis_bound (a : UniformSectorPacking.Axis) :
 TablesBound (preparedAxisValue (encodeAxis a)) a.widths.sum := by
 have hb:=native_blocks_bound a
 refine ⟨le_rfl,hb,le_rfl,?_,?_⟩
 · intro j
   by_cases hj:j<a.widths.length
   · have look:(preparedAxisValue (encodeAxis a)).2.1.look j (0,(0,0))=
       localBlockValue (encodeAxis a) j:=Tape.look_of_lt _ _ hj
     rw [look,localBlock_native a ⟨j,hj⟩]
     have hw:=list_get_le_sum a.widths ⟨j,hj⟩
     have hs:=sum_take_le a.widths j
     have ha:=a.radix_two
     simp only [UniformTraversal.blockBefore]
     exact ⟨by split_ifs; exact le_trans (by decide : 1≤2) ha; exact Nat.zero_le _,hw,hs⟩
   · change _≤_ ∧ _≤_ ∧ _≤_
     simp [preparedAxisValue,encodeAxis,Tape.look,Tape.tab,ofList,hj]
 · intro j
   by_cases hj:j<a.widths.sum
   · have h: (preparedAxisValue (encodeAxis a)).2.2.look j (0,(0,(0,0)))=
       localDigitValue (encodeAxis a) j:=Tape.look_of_lt _ _ hj
     rw [h,localDigit_native a ⟨j,hj⟩]
     have hw:=list_get_le_sum a.widths (UniformSectorPacking.blockDecode a.widths ⟨j,hj⟩).1
     have hs:=sum_take_le a.widths (UniformSectorPacking.blockDecode a.widths ⟨j,hj⟩).1.val
     have ht:=(UniformSectorPacking.blockDecode a.widths ⟨j,hj⟩).2.isLt
     have ho:=(a.originalPermutation ⟨j,hj⟩).isLt
     simp only [UniformTraversal.blockBefore]
     exact ⟨hw,hs,le_trans ht.le hw,ho.le⟩
   · simp [preparedAxisValue,encodeAxis,Tape.look,Tape.tab,hj]

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
