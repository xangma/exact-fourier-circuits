import DFTModelSectorTransposeCore

set_option autoImplicit false

/-! A compact patch has a genuine constant-work typed reader. The readonly
parent supplies every spectator; global assembly must materialize once, after
all sectors, using a produced direct sector map. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section
abbrev ReadInput (t : Ty) := p (Patch t) w
def readVolume (t : Ty) : Prog false (ReadInput t) w :=
 .comp (.atom .fst) (.comp (.atom .fst) (volume t))
def readStart (t : Ty) : Prog false (ReadInput t) w :=
 .comp (.atom .fst) (.comp (.atom .fst) (start t))
def readWidth (t : Ty) : Prog false (ReadInput t) w :=
 .comp (.atom .fst) (.comp (.atom .fst) (width t))
def readPosition (t : Ty) : Prog false (ReadInput t) w :=
 binary .mod (.atom .snd) (readVolume t)
def readDelta (t : Ty) : Prog false (ReadInput t) w :=
 binary .sub (readPosition t) (readStart t)
def readIndex (t : Ty) : Prog false (ReadInput t) w :=
 binary .add (binary .mul (binary .div (.atom .snd) (readVolume t))
  (readWidth t)) (readDelta t)
def readOld (t : Ty) : Prog false (ReadInput t) t :=
 .comp (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))
  (.atom .snd)) (.atom .look)
def readFresh (t : Ty) : Prog false (ReadInput t) t :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (readIndex t)) (.atom .look)
def reader (t : Ty) : Prog false (ReadInput t) t :=
 .ifz (binary .lt (readPosition t) (readStart t))
  (.ifz (binary .lt (readDelta t) (readWidth t)) (readOld t) (readFresh t))
  (readOld t)
def overlay {α : Type} (V a T j : ℕ) (v b : Tape α) (z : α) : α :=
 if j%V<a then v.look j z else
 if j%V-a<T then b.look ((j/V)*T+(j%V-a)) z else v.look j z

theorem reader_value (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) :
 (run (reader t) ((((W,(V,(a,T))),v),b),j)).val = overlay V a T j v b t.blank := by
 simp only [reader,readOld,readFresh,readIndex,readPosition,readDelta,
  readVolume,readStart,readWidth,volume,start,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases before : j%V<a
 · simp [before,overlay]
 · by_cases inside : j%V-a<T <;>simp [before,inside,overlay]

theorem reader_valid (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) :
 (run (reader t) ((((W,(V,(a,T))),v),b),j)).valid := by
 simp only [reader,readOld,readFresh,readIndex,readPosition,readDelta,
  readVolume,readStart,readWidth,volume,start,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h : j%V<a <;>by_cases h' : j%V-a<T <;>simp [h,h']

theorem reader_work (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) :
 (run (reader t) ((((W,(V,(a,T))),v),b),j)).work ≤ 133 := by
 simp only [reader,readOld,readFresh,readIndex,readPosition,readDelta,
  readVolume,readStart,readWidth,volume,start,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h : j%V<a <;>by_cases h' : j%V-a<T <;>norm_num [h,h']

theorem reader_peak (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) :
 (run (reader t) ((((W,(V,(a,T))),v),b),j)).peak ≤ (j+1)*(T+1)+1 := by
 have div : j/V≤j := Nat.div_le_self _ _
 have mod : j%V≤j := Nat.mod_le _ _
 have delta : j%V-a≤j := (Nat.sub_le _ _).trans mod
 have product : j/V*T≤j*T := Nat.mul_le_mul_right T div
 simp only [reader,readOld,readFresh,readIndex,readPosition,readDelta,
  readVolume,readStart,readWidth,volume,start,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]
 have jb : j≤(j+1)*(T+1)+1 := by nlinarith
 have db : j/V≤(j+1)*(T+1)+1 := div.trans jb
 have mb : j%V≤(j+1)*(T+1)+1 := mod.trans jb
 have ib : j/V*T+(j%V-a)≤(j+1)*(T+1)+1 := by nlinarith
 have one : 1≤(j+1)*(T+1)+1 := by omega
 by_cases h : j%V<a <;>by_cases h' : j%V-a<T <;>simp [h,h',db,mb,ib,one]

theorem overlay_sector (t : Ty) (V a T r j : ℕ) (v b : Tape t.T)
 (fit : a+T≤V) (inside : j<T) :
 overlay V a T (r*V+a+j) v b t.blank = b.look (r*T+j) t.blank := by
 have vp : 0<V := by omega
 have coordinate : a+j<V := by omega
 have rem : (r*V+a+j)%V=a+j := by
  rw [Nat.add_assoc,Nat.mul_comm r V,Nat.mul_add_mod,Nat.mod_eq_of_lt coordinate]
 have div : (r*V+a+j)/V=r := by
  rw [Nat.add_assoc,Nat.mul_comm r V,Nat.mul_add_div vp,Nat.div_eq_of_lt coordinate,Nat.add_zero]
 simp [overlay,rem,div,inside]

theorem overlay_spectator (t : Ty) (V a T r j : ℕ) (v b : Tape t.T)
 (coord : j<V) (outside : j<a ∨ a+T≤j) :
 overlay V a T (r*V+j) v b t.blank = v.look (r*V+j) t.blank := by
 have rem : (r*V+j)%V=j := by rw [Nat.mul_comm r V,Nat.mul_add_mod,Nat.mod_eq_of_lt coord]
 rcases outside with before|after
 · simp [overlay,rem,before]
 · have no : ¬j-a<T := by omega
   simp [overlay,rem,no]

end
end ExactFourierCircuits.DFTModelSectorTranspose
