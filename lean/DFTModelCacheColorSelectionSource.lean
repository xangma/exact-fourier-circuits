import DFTModelCacheColorSelectionBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorSelection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section

/-- Indexed selection preserves chronology and distinct occurrences, including
identical physical rows and zero coefficient addresses. -/
def indices (x:Input.T) : List ℕ := (List.range x.2.1.len).filter (fun j=>decide (accepts x j))

theorem indices_mem (x:Input.T) (j:ℕ) : j∈indices x ↔ j<x.2.1.len ∧ accepts x j := by
 simp [indices]

theorem rowsPrefix_map (x:Input.T) (l:ℕ) :
 rowsPrefix x l=((List.range l).filter (fun j=>decide (accepts x j))).map (rowValue x) := by
 unfold rowsPrefix
 induction List.range l with
 | nil=>rfl
 | cons j js ih=>
   by_cases h:accepts x j <;>simp [h,ih]

theorem indices_length (x:Input.T) : (indices x).length=(run program x).val.len := by
 rw [program_value,rowsPrefix_map]
 simp only [Tape.tab,List.length_map]
 rfl

def originalIndex (x:Input.T) (i:Fin (indices x).length) : Fin x.2.1.len :=
 ⟨(indices x)[i.val],((indices_mem x _).mp (List.getElem_mem i.isLt)).1⟩

theorem originalIndex_accepts (x:Input.T) (i:Fin (indices x).length) :
 accepts x (originalIndex x i).val :=
 ((indices_mem x _).mp (List.getElem_mem i.isLt)).2

/-- Every accepted original occurrence appears; filtering does not collapse duplicates. -/
theorem originalIndex_complete (x:Input.T) (j:ℕ) (hj:j<x.2.1.len) (hc:accepts x j) :
 ∃i:Fin (indices x).length,(originalIndex x i).val=j := by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ((indices_mem x j).mpr ⟨hj,hc⟩)
 exact ⟨⟨i,hi⟩,eq⟩

theorem originalIndex_injective (x:Input.T) : Function.Injective (originalIndex x) := by
 intro i j same
 apply Fin.ext
 exact ((List.nodup_range.filter _).getElem_inj).mp (congrArg Fin.val same)

/-- Every output row is the exact original physical Row3 occurrence. -/
theorem selected_row (x:Input.T) (i:Fin (indices x).length) :
 (run program x).val.look i.val Row.blank=x.2.1.look (originalIndex x i).val Row.blank := by
 rw [program_value,rowsPrefix_map]
 have hi:i.val<(((List.range x.2.1.len).filter (fun j=>decide (accepts x j))).map (rowValue x)).length := by
  simpa only [List.length_map,indices] using i.isLt
 rw [Tape.look_of_lt (Tape.tab _ _) Row.blank hi]
 change ((List.map (rowValue x) (List.filter (fun j=>decide (accepts x j)) (List.range x.2.1.len)))[i.val]?.getD Row.blank)=_
 simp only [List.getElem?_eq_getElem hi,Option.getD_some,List.getElem_map]
 rfl

def selectedEdges {M:ℕ} (x:Input.T) (E:Fin M→Edge) (length:x.2.1.len=M) :
 Fin (indices x).length→Edge := fun i=>E (Fin.cast length (originalIndex x i))

/-- A proper computed color class is a matching on the SAME original physical
endpoints. Its physical radix is an independent explicit caller parameter. -/
theorem selected_matching {M:ℕ} (c r:ℕ) (z:Tape Row.T) (colors:Tape ℕ)
 (E:Fin M→Edge) (rows:DFTModelCacheColor.Rows E z) (range:InRange r E)
 (proper:∀i j:Fin M,i≠j→colors.look i.val 0=colors.look j.val 0→¬Conflict (E i) (E j)) :
 let x:Input.T := (c,(z,colors))
 DFTModelCacheMatchingNat.Rows (selectedEdges x E rows.length) (run program x).val ∧
 Matching (selectedEdges x E rows.length) ∧ InRange r (selectedEdges x E rows.length) := by
 dsimp only
 let x:Input.T := (c,(z,colors))
 let pick:Fin (indices x).length→Fin M := fun i=>Fin.cast rows.length (originalIndex x i)
 have injective:Function.Injective pick := by
  intro i j h
  apply originalIndex_injective x
  apply Fin.ext
  exact congrArg (fun k:Fin M=>k.val) h
 refine ⟨⟨(indices_length x).symm,?_⟩,?_,?_⟩
 · intro i
   change ((run program x).val.look i.val Row.blank).1=(E (pick i)).left ∧
    ((run program x).val.look i.val Row.blank).2.1=(E (pick i)).right
   rw [selected_row x i]
   exact rows.endpoints (pick i)
 · intro i j different
   apply proper (pick i) (pick j) (fun h=>different (injective h))
   exact (originalIndex_accepts x i).trans (originalIndex_accepts x j).symm
 · intro i
   exact range (pick i)

end
end ExactFourierCircuits.DFTModelCacheColorSelection
