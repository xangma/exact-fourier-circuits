import DFTModelSectorMapProgram
import DFTModelSectorMapReader

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformSectorPacking
noncomputable section

attribute [local irreducible] program powers DFTModelSectorMapCarry.program
 DFTModelSectorMapBits.pack DFTModelSectorMapBits.highTable sparse

theorem program_length (V : ℕ) (d : Tape (ℕ×ℕ)) : (run program (V,d)).val.len=V := by
 rw [program_value];rfl

theorem program_sector {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 (i j : ℕ) (hi : i<d.len) (start : (d.look i (0,0)).1≤j)
 (inside : j<(d.look i (0,0)).1+(d.look i (0,0)).2) :
 (run program (V,d)).val.look j Cell.blank=
 (i+1,((d.look i (0,0)).2,j-(d.look i (0,0)).1)) := by
 have hj:j<V:=(inside.trans_le (g.fit i hi))
 rw [program_value]
 simp only [Tape.look,Tape.tab,hj,↓reduceDIte]
 have h:=chosen_sector g (DFTModelSectorMapParameters.blockBits V) j i
  (DFTModelSectorMapParameters.blockBits_pos V) hj hi start inside
  (powerTable V) (carryTable V d)
  (fun k hk=>powers_lookup _ _ hk)
  (fun c hc=>DFTModelSectorMapCarry.program_cut _ _ d g.starts_ordered c hc)
 change mapped d j (chosen _ j _ _ _ _ _)=_
 change chosen (DFTModelSectorMapParameters.blockBits V) j (marks V d) (packedTable V d) (highTable V) (powerTable V) (carryTable V d)=i+1 at h
 rw [h]
 exact mapped_sector d i j start inside

theorem program_gap {V : ℕ} {d : Tape (ℕ×ℕ)} (j : ℕ) (hj:j<V)
 (gap:∀i,i<d.len→¬((d.look i (0,0)).1≤j ∧j<(d.look i (0,0)).1+(d.look i (0,0)).2)) :
 (run program (V,d)).val.look j Cell.blank=(0,(0,0)) := by
 rw [program_value]
 simp only [Tape.look,Tape.tab,hj,↓reduceDIte]
 exact mapped_gap d j _ gap

theorem program_native_sector {W E A : ℕ} (axes : List Axis) (s : UniformMachine.State)
 (table:∀i (hi:i<(sectorStates axes).length),
  UniformSectorBatchDirectoryMachine.BatchCell W E A i ((sectorStates axes)[i]'hi) s)
 (i j : ℕ) (hi:i<(sectorStates axes).length) (hj:j<((sectorStates axes)[i]'hi).width) :
 (run program ((radices axes).prod,nativeReadback E (sectorStates axes).length s)).val.look
 (((sectorStates axes)[i]'hi).start+j) Cell.blank=
 (i+1,(((sectorStates axes)[i]'hi).width,j)) := by
 have enc:=native_encoded (sectorStates axes) s table
 have geo:=canonical_geometry axes _ enc
 have row:=enc.2 i hi
 have h:=program_sector geo i (((sectorStates axes)[i]'hi).start+j)
  (by rw [enc.1];exact hi) (by rw [row];simp) (by rw [row];dsimp;omega)
 rw [row] at h
 simpa using h

theorem program_reader_sector {V : ℕ} {d : Tape (ℕ×ℕ)} (g : Geometry V d)
 (t : Ty) (i r j : ℕ) (hi:i<d.len) (hj:j<(d.look i (0,0)).2)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (reader t) ((V,((run program (V,d)).val,(patches,old))),r*V+(d.look i (0,0)).1+j)).val=
 (patches.look i (Tape.empty t.T)).look (r*(d.look i (0,0)).2+j) t.blank := by
 rw [reader_value]
 apply overlay_sector t V i _ _ r j _ patches old (g.fit i hi) hj
 have result:=program_sector g i ((d.look i (0,0)).1+j) hi (by omega) (by omega)
 simpa [Cell,Ty.blank] using result

end
end ExactFourierCircuits.DFTModelSectorMap
