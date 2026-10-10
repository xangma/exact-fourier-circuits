import DFTModelSectorMaterializationProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMaterialization
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] program joinedTape joined DFTModelSectorMap.program

theorem program_lookup (t : Ty) (W V j : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) (hj:j<W*V) :
 (run (program t) (W,(V,(m,(patches,old))))).val.look j t.blank=
 DFTModelSectorMap.overlay V j m patches old t.blank := by
 rw [program_value]
 simp [Tape.look,Tape.tab,hj]

theorem program_sector (t : Ty) (W V i a width role j : ℕ)
 (m : Tape DFTModelSectorMap.Cell.T) (patches : Tape (Tape t.T)) (old : Tape t.T)
 (fit:a+width≤V) (hr:role<W) (inside:j<width)
 (mapped:m.look (a+j) (0,(0,0))=(i+1,(width,j))) :
 (run (program t) (W,(V,(m,(patches,old))))).val.look (role*V+a+j) t.blank=
 (patches.look i (Tape.empty t.T)).look (role*width+j) t.blank := by
 have hj:role*V+a+j<W*V:=by nlinarith
 rw [program_lookup t W V _ m patches old hj]
 exact DFTModelSectorMap.overlay_sector t V i a width role j m patches old fit inside mapped

theorem program_spectator (t : Ty) (W V role j : ℕ)
 (m : Tape DFTModelSectorMap.Cell.T) (patches : Tape (Tape t.T)) (old : Tape t.T)
 (hr:role<W) (coord:j<V) (mapped:(m.look j (0,(0,0))).1=0) :
 (run (program t) (W,(V,(m,(patches,old))))).val.look (role*V+j) t.blank=
 old.look (role*V+j) t.blank := by
 have hj:role*V+j<W*V:=by nlinarith
 rw [program_lookup t W V _ m patches old hj]
 exact DFTModelSectorMap.overlay_spectator t V role j m patches old coord mapped

theorem joined_value (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).val=
 ((W,((V,d),(patches,old))),
  (run (program t) (W,(V,((run DFTModelSectorMap.program (V,d)).val,(patches,old))))).val) := by
 rw [joined_run,joinedTape_run];rfl

theorem joined_length (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (joined t) (W,((V,d),(patches,old)))).val.2.len=W*V := by
 rw [joined_value];exact program_length _ _ _ _ _ _

theorem joined_sector (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)}
 (g:DFTModelSectorMap.Geometry V d) (i role j : ℕ)
 (patches : Tape (Tape t.T)) (old : Tape t.T)
 (hi:i<d.len) (hr:role<W) (hj:j<(d.look i (0,0)).2) :
 (run (joined t) (W,((V,d),(patches,old)))).val.2.look
 (role*V+(d.look i (0,0)).1+j) t.blank=
 (patches.look i (Tape.empty t.T)).look (role*(d.look i (0,0)).2+j) t.blank := by
 rw [joined_value]
 apply program_sector t W V i _ _ role j _ patches old (g.fit i hi) hr hj
 have h:=DFTModelSectorMap.program_sector g i ((d.look i (0,0)).1+j) hi (by omega) (by omega)
 simpa [DFTModelSectorMap.Cell,Ty.blank] using h

theorem joined_spectator (t : Ty) {W V : ℕ} {d : Tape (ℕ×ℕ)} (role j : ℕ)
 (patches : Tape (Tape t.T)) (old : Tape t.T) (hr:role<W) (hj:j<V)
 (gap:∀i,i<d.len→¬((d.look i (0,0)).1≤j ∧j<(d.look i (0,0)).1+(d.look i (0,0)).2)) :
 (run (joined t) (W,((V,d),(patches,old)))).val.2.look (role*V+j) t.blank=
 old.look (role*V+j) t.blank := by
 rw [joined_value]
 apply program_spectator t W V role j _ patches old hr hj
 have h:=DFTModelSectorMap.program_gap j hj gap
 simpa [DFTModelSectorMap.Cell,Ty.blank] using congrArg Prod.fst h

/-- Whole-bank equality requires explicit complete source cells; no native
execution or child output equality is fabricated by the materializer. -/
theorem program_eq_of_cells (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old target : Tape t.T) (length:target.len=W*V)
 (cells:∀j,j<W*V→DFTModelSectorMap.overlay V j m patches old t.blank=target.look j t.blank) :
 (run (program t) (W,(V,(m,(patches,old))))).val=target := by
 rw [program_value]
 cases target with
 | mk L f=>
  dsimp only at length
  subst L
  dsimp only [Tape.tab]
  congr 1;funext j
  simpa [Tape.look,j.isLt] using cells j.val j.isLt

end
end ExactFourierCircuits.DFTModelSectorMaterialization
