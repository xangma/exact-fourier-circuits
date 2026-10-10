import DFTModelSectorMapCore

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

/-- Readonly old bank, compact child tapes, and the produced sector map. -/
abbrev ReadContext (t : Ty) := p w (p (Ty.a Cell) (p (Ty.a (Ty.a t)) (Ty.a t)))
abbrev ReadInput (t : Ty) := p (ReadContext t) w
abbrev BoundRead (t : Ty) := p (ReadInput t) Cell

def mapCell (t : Ty) : Prog false (ReadInput t) Cell :=
 .comp (.fork
  (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
  (binary .mod (.atom .snd) (.comp (.atom .fst) (.atom .fst)))) (.atom .look)

def readOld (t : Ty) : Prog false (BoundRead t) t :=
 .comp (.fork
  (.comp (.atom .fst) (.comp (.atom .fst)
   (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
  (.comp (.atom .fst) (.atom .snd))) (.atom .look)

def patchOrdinal (t : Ty) : Prog false (BoundRead t) w :=
 binary .sub (.comp (.atom .snd) (.atom .fst)) (.atom (.lit 1))
def patchOffset (t : Ty) : Prog false (BoundRead t) w :=
 binary .add
  (binary .mul
   (binary .div (.comp (.atom .fst) (.atom .snd))
    (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))))
   (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
  (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def readPatch (t : Ty) : Prog false (BoundRead t) t :=
 .comp (.fork
  (.comp (.fork
   (.comp (.atom .fst) (.comp (.atom .fst)
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))))
   (patchOrdinal t)) (.atom .look))
  (patchOffset t)) (.atom .look)
def readSelected (t : Ty) : Prog false (BoundRead t) t :=
 .ifz (.comp (.atom .snd) (.atom .fst)) (readOld t) (readPatch t)
def reader (t : Ty) : Prog false (ReadInput t) t :=
 .comp (.fork (.atom .id) (mapCell t)) (readSelected t)

def overlay {α : Type} (V j : ℕ) (m : Tape (ℕ×(ℕ×ℕ)))
 (patches : Tape (Tape α)) (old : Tape α) (z : α) : α :=
 let c:=m.look (j%V) (0,(0,0))
 if c.1=0 then old.look j z else
 (patches.look (c.1-1) (Tape.empty α)).look ((j/V)*c.2.1+c.2.2) z

theorem mapCell_run (t : Ty) (V j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (mapCell t) ((V,(m,(patches,old))),j)=
 ⟨m.look (j%V) Cell.blank,15,j%V,True⟩ := by
 simp [mapCell,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem reader_value (t : Ty) (V j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (reader t) ((V,(m,(patches,old))),j)).val=overlay V j m patches old t.blank := by
 simp only [reader,mapCell,readSelected,readOld,readPatch,patchOrdinal,patchOffset,
  binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:(m.look (j%V) (0,(0,0))).1=0 <;>
  simp [overlay,Cell,Ty.blank,h]

theorem reader_valid (t : Ty) (V j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (reader t) ((V,(m,(patches,old))),j)).valid := by
 simp only [reader,mapCell,readSelected,readOld,readPatch,patchOrdinal,patchOffset,
  binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:(m.look (j%V) Cell.blank).1=0 <;> simp [h]

theorem reader_work (t : Ty) (V j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (reader t) ((V,(m,(patches,old))),j)).work≤100 := by
 simp only [reader,mapCell,readSelected,readOld,readPatch,patchOrdinal,patchOffset,
  binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:(m.look (j%V) Cell.blank).1=0 <;> norm_num [h]

theorem reader_peak (t : Ty) (V j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (reader t) ((V,(m,(patches,old))),j)).peak ≤
 j+(m.look (j%V) Cell.blank).1+(j/V)*(m.look (j%V) Cell.blank).2.1+
 (m.look (j%V) Cell.blank).2.2+2 := by
 have hm:=Nat.mod_le j V
 have hd:=Nat.div_le_self j V
 have hs:=Nat.sub_le (m.look (j%V) Cell.blank).1 1
 simp only [reader,mapCell,readSelected,readOld,readPatch,patchOrdinal,patchOffset,
  binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:(m.look (j%V) Cell.blank).1=0 <;> simp only [h,↓reduceIte] <;> omega

/-- Exact native compact layout: role-major inside each returned child patch. -/
theorem overlay_sector (t : Ty) (V i a T r j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T)
 (fit:a+T≤V) (inside:j<T)
 (mapped:m.look (a+j) (0,(0,0))=(i+1,(T,j))) :
 overlay V (r*V+a+j) m patches old t.blank=
 (patches.look i (Tape.empty t.T)).look (r*T+j) t.blank := by
 have vp:0<V:=by omega
 have coordinate:a+j<V:=by omega
 have rem:(r*V+a+j)%V=a+j:=by
  rw [Nat.add_assoc,Nat.mul_comm r V,Nat.mul_add_mod,Nat.mod_eq_of_lt coordinate]
 have div:(r*V+a+j)/V=r:=by
  rw [Nat.add_assoc,Nat.mul_comm r V,Nat.mul_add_div vp,Nat.div_eq_of_lt coordinate,Nat.add_zero]
 simp [overlay,rem,div,mapped]

theorem overlay_spectator (t : Ty) (V r j : ℕ) (m : Tape Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T)
 (coord:j<V) (mapped:(m.look j (0,(0,0))).1=0) :
 overlay V (r*V+j) m patches old t.blank=old.look (r*V+j) t.blank := by
 have rem:(r*V+j)%V=j:=by
  rw [Nat.mul_comm r V,Nat.mul_add_mod,Nat.mod_eq_of_lt coord]
 simp [overlay,rem,mapped]

end
end ExactFourierCircuits.DFTModelSectorMap
