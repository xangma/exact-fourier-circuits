import DFTModelResidualCore

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section

/-- A raw ordered sector interval: (packed start, width). -/
abbrev Row := p w w
abbrev Input := p w (Ty.a Row)
abbrev Cell := p w (p w w)

def volume : Prog false Input w := .atom .fst
def count : Prog false Input w := .comp (.atom .snd) (.atom .len)
def row : Prog false (p Input w) Row :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def rowStart : Prog false (p Input w) w := .comp row (.atom .fst)
def rowWidth : Prog false (p Input w) w := .comp row (.atom .snd)
def stampIndex : Prog false (p Input w) w :=
 .ifz rowWidth (.comp (.atom .fst) volume) rowStart
def stampCell : Prog false (p Input w) (p w w) :=
 .fork stampIndex (binary .add (.atom .snd) (.atom (.lit 1)))

/-- One fresh output allocation. Each actual row contributes one charged write.
Empty rows target the out-of-range index V and therefore make no mark. -/
def sparse : Prog false Input (Ty.a w) := .sow volume count stampCell

def stamp (V : ℕ) (d : Tape (ℕ×ℕ)) (i : ℕ) : ℕ×ℕ :=
 let st := d.look i (0,0)
 (if st.2=0 then V else st.1, i+1)

theorem row_run (V i : ℕ) (d : Tape (ℕ×ℕ)) :
 run row ((V,d),i)=⟨d.look i (0,0),7,0,True⟩ := by
 simp [row,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Row,Ty.blank]

theorem stampCell_run (V i : ℕ) (d : Tape (ℕ×ℕ)) :
 run stampCell ((V,d),i)=
 ⟨stamp V d i,if (d.look i (0,0)).2=0 then 19 else 25,
  i+1,True⟩ := by
 simp only [stampCell,stampIndex,rowWidth,rowStart,row,volume,binary,
  run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h : (d.look i (0,0)).2=0 <;>
  simp [h,stamp,Row,Ty.blank,Nat.add_comm]

attribute [local irreducible] stampCell

def constructed {α : Type} (n : ℕ) (z : α) (f : ℕ→Bill (ℕ×α)) (m : ℕ) : Bill (Tape α) :=
 Bill.steps (Tape.tab n (fun _=>z))
  (fun i v=>(f i).pass (fun s=>Bill.one (v.set s.1 s.2))) m

theorem constructed_value {α : Type} (n : ℕ) (z : α) (f : ℕ→Bill (ℕ×α)) (m : ℕ) :
 (constructed n z f m).val=Tape.sow n m z (fun i=>(f i).val) := by
 induction m with
 | zero=>rfl
 | succ m ih=>
  change ((constructed n z f m).val.set (f m).val.1 (f m).val.2)=_
  rw [ih];rfl

theorem constructed_work {α : Type} (n : ℕ) (z : α) (f : ℕ→Bill (ℕ×α)) (m : ℕ) :
 (constructed n z f m).work=1+2*m+∑i∈Finset.range m,(f i).work := by
 induction m with
 | zero=>simp [constructed,Bill.steps,Bill.one]
 | succ m ih=>
  change (constructed n z f m).work+(f m).work+1+1=_
  rw [ih,Finset.sum_range_succ];omega

theorem constructed_valid {α : Type} (n : ℕ) (z : α) (f : ℕ→Bill (ℕ×α)) (m : ℕ) :
 (constructed n z f m).valid ↔ ∀i < m,(f i).valid := by
 induction m with
 | zero=>simp [constructed,Bill.steps,Bill.one]
 | succ m ih=>
  change ((constructed n z f m).valid∧((f m).valid∧True))↔_
  simp only [and_true]
  rw [ih]
  constructor
  · rintro ⟨old,last⟩ i hi
    by_cases h:i=m
    · simpa [h] using last
    · exact old i (by omega)
  · intro h;exact ⟨fun i hi=>h i (by omega),h m (by omega)⟩

theorem constructed_peak {α : Type} (n : ℕ) (z : α) (f : ℕ→Bill (ℕ×α)) (m : ℕ) :
 (constructed n z f m).peak=max m ((Finset.range m).sup (fun i=>(f i).peak)) := by
 induction m with
 | zero=>simp [constructed,Bill.steps,Bill.one]
 | succ m ih=>
  change max (max (constructed n z f m).peak (max (f m).peak 0)) (m+1)=_
  rw [ih,Finset.range_add_one,Finset.sup_insert]
  simp only [max_zero]
  omega

theorem sparse_value (V : ℕ) (d : Tape (ℕ×ℕ)) :
 (run sparse (V,d)).val=Tape.sow V d.len 0 (stamp V d) := by
 change (Bill.sow V d.len 0 (fun i=>run stampCell ((V,d),i))).val=_
 change (constructed V 0 (fun i=>run stampCell ((V,d),i)) d.len).val=_
 rw [constructed_value]
 exact congrArg (Tape.sow V d.len 0) (funext (fun i=>congrArg Bill.val (stampCell_run V i d)))

theorem sparse_valid (V : ℕ) (d : Tape (ℕ×ℕ)) : (run sparse (V,d)).valid := by
 have h : (constructed V 0 (fun i=>run stampCell ((V,d),i)) d.len).valid := by
  apply (constructed_valid _ _ _ _).2
  intro i _;rw [stampCell_run];trivial
 simpa only [sparse,volume,count,run,Code.run,Atom.run,Bill.one,Bill.word,
  Bill.pass,Bill.pay,Bill.sow,constructed,Ty.blank,true_and] using h

theorem sparse_work (V : ℕ) (d : Tape (ℕ×ℕ)) :
 (run sparse (V,d)).work≤V+27*d.len+7 := by
 change 1+(3+((constructed V 0 (fun i=>run stampCell ((V,d),i)) d.len).work+(1+V)))+1≤_
 rw [constructed_work]
 have h : (∑i∈Finset.range d.len,(run stampCell ((V,d),i)).work)≤25*d.len := by
  calc
   _≤∑i∈Finset.range d.len,25 := by
    apply Finset.sum_le_sum;intro i _;rw [stampCell_run];dsimp only [Bill.work];split_ifs <;>omega
   _=25*d.len := by simp [Nat.mul_comm]
 omega

theorem sparse_peak (V : ℕ) (d : Tape (ℕ×ℕ)) :
 (run sparse (V,d)).peak ≤ max V d.len := by
 have h : (constructed V 0 (fun i=>run stampCell ((V,d),i)) d.len).peak ≤ max V d.len := by
  rw [constructed_peak]
  apply max_le (le_max_right _ _)
  apply Finset.sup_le
  intro i hi
  rw [stampCell_run]
  dsimp only [Bill.peak]
  have h:=Finset.mem_range.mp hi
  omega
 dsimp only [constructed] at h
 simp only [run,Bill.pass,Bill.one,max_zero] at h
 simp only [sparse,volume,count,run,Code.run,Atom.run,Bill.one,Bill.word,
  Bill.pass,Bill.pay,Bill.sow,Ty.blank,zero_max,max_zero]
 exact max_le (le_max_right _ _) (max_le h (le_max_left _ _))

end
end ExactFourierCircuits.DFTModelSectorMap
