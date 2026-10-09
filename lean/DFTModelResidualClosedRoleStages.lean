import DFTModelResidualClosedMovement
import DFTModelResidualPeakSyntax

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualClosedRoleStages
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open DFTModelResidualClosedBasis (Meta)
noncomputable section

abbrev Input (t:Ty) := p Meta (p w (Ty.a t))
abbrev Addressed (t:Ty) := p (Input t) (Ty.a w)
abbrev Context (t:Ty) := p (Input t) (p (Ty.a w) (Ty.a t))
abbrev ReplaceInput (t:Ty) := p (Input t) (Ty.a t)

def sliceCell (t:Ty) : Prog false (p (Addressed t) w) t := .comp (.fork
  (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))))
  (binary .add (binary .mul
    (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))))
    (.comp (.atom .fst) (.comp (.atom .snd) (.atom .len)))) (.atom .snd))) (.atom .look)
def slice (t:Ty) : Prog false (Addressed t) (Ty.a t) := .tab
  (.comp (.atom .snd) (.atom .len)) (sliceCell t)

def oldTape (t:Ty) : Prog false (p (ReplaceInput t) w) (Ty.a t) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
def newTape (t:Ty) : Prog false (p (ReplaceInput t) w) (Ty.a t) :=
  .comp (.atom .fst) (.atom .snd)
def role (t:Ty) : Prog false (p (ReplaceInput t) w) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
def width (t:Ty) : Prog false (p (ReplaceInput t) w) w := .comp (newTape t) (.atom .len)
def start (t:Ty) : Prog false (p (ReplaceInput t) w) w := binary .mul (role t) (width t)
def oldRead (t:Ty) : Prog false (p (ReplaceInput t) w) t :=
  .comp (.fork (oldTape t) (.atom .snd)) (.atom .look)
def newRead (t:Ty) : Prog false (p (ReplaceInput t) w) t := .comp
  (.fork (newTape t) (binary .sub (.atom .snd) (start t))) (.atom .look)
def replaceCell (t:Ty) : Prog false (p (ReplaceInput t) w) t :=
  .ifz (binary .lt (.atom .snd) (start t))
    (.ifz (binary .lt (.atom .snd) (binary .add (start t) (width t))) (oldRead t) (newRead t))
    (oldRead t)
def replace (t:Ty) : Prog false (ReplaceInput t) (Ty.a t) := .tab
  (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .len)))) (replaceCell t)

theorem sliceCell_run (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (p:Tape ℕ) (j:ℕ) :
    run (sliceCell t) (((ctx,(a,bank)),p),j)=
      ⟨bank.look (a*p.len+j) t.blank,29,max (a*p.len+j) (max (a*p.len) p.len),True⟩ := by
  simp [sliceCell,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    max_comm,max_left_comm]

theorem slice_value (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (p:Tape ℕ) :
    (run (slice t) ((ctx,(a,bank)),p)).val=Tape.tab p.len (fun j=>bank.look (a*p.len+j) t.blank) := by
  change (Bill.tab p.len t.blank (fun j=>run (sliceCell t) (((ctx,(a,bank)),p),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab p.len) (funext (fun j=>congrArg Bill.val (sliceCell_run t ctx a bank p j)))

theorem slice_work (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (p:Tape ℕ) :
    (run (slice t) ((ctx,(a,bank)),p)).work=33*p.len+6 := by
  change 3+(Bill.tab p.len t.blank (fun j=>run (sliceCell t) (((ctx,(a,bank)),p),j))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have cells:(fun j=>(run (sliceCell t) (((ctx,(a,bank)),p),j)).work)=(fun _=>29) := by
    funext j;exact congrArg Bill.work (sliceCell_run t ctx a bank p j)
  rw [cells]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem replaceCell_value (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:ℕ) :
    (run (replaceCell t) (((ctx,(a,old)),next),j)).val=
      if a*next.len ≤ j ∧ j<a*next.len+next.len then next.look (j-a*next.len) t.blank else old.look j t.blank := by
  by_cases low:j<a*next.len <;> by_cases high:j<a*next.len+next.len <;>
    simp [replaceCell,oldRead,newRead,oldTape,newTape,start,role,width,binary,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,low,high]

theorem replaceCell_work (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:ℕ) :
    (run (replaceCell t) (((ctx,(a,old)),next),j)).work ≤ 100 := by
  by_cases low:j<a*next.len <;> by_cases high:j<a*next.len+next.len <;>
    simp [replaceCell,oldRead,newRead,oldTape,newTape,start,role,width,binary,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,low,high]

theorem replace_value (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) :
    (run (replace t) ((ctx,(a,old)),next)).val=Tape.tab old.len (fun j=>
      if a*next.len ≤ j ∧ j<a*next.len+next.len then next.look (j-a*next.len) t.blank else old.look j t.blank) := by
  change (Bill.tab old.len t.blank (fun j=>run (replaceCell t) (((ctx,(a,old)),next),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab old.len) (funext (replaceCell_value t ctx a old next))

theorem replace_work (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) :
    (run (replace t) ((ctx,(a,old)),next)).work ≤ 104*old.len+10 := by
  change 7+(Bill.tab old.len t.blank (fun j=>run (replaceCell t) (((ctx,(a,old)),next),j))).work+1 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have cells:(∑j∈Finset.range old.len,(run (replaceCell t) (((ctx,(a,old)),next),j)).work) ≤ old.len*100 := by
    calc
      _ ≤ ∑_j∈Finset.range old.len,100 := Finset.sum_le_sum (fun j _=>replaceCell_work t ctx a old next j)
      _=_ := by simp
  omega


theorem slice_valid (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (p:Tape ℕ) :
    (run (slice t) ((ctx,(a,bank)),p)).valid := by
  have h:(Bill.tab p.len t.blank (fun j=>run (sliceCell t) (((ctx,(a,bank)),p),j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>by rw [sliceCell_run];trivial)
  exact ⟨⟨trivial,trivial⟩,h⟩

theorem slice_peak (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (p:Tape ℕ) :
    (run (slice t) ((ctx,(a,bank)),p)).peak ≤ a*p.len+p.len := by
  change max (max (max (max 0 p.len) 0) (Bill.tab p.len t.blank
    (fun j=>run (sliceCell t) (((ctx,(a,bank)),p),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have cells:(Finset.range p.len).sup
      (fun j=>(run (sliceCell t) (((ctx,(a,bank)),p),j)).peak) ≤ a*p.len+p.len := by
    apply Finset.sup_le
    intro j hj
    rw [sliceCell_run]
    have jl:=Finset.mem_range.mp hj
    dsimp only [Bill.peak]
    omega
  omega

theorem replaceCell_valid (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:ℕ) :
    (run (replaceCell t) (((ctx,(a,old)),next),j)).valid := by
  by_cases low:j<a*next.len <;> by_cases high:j<a*next.len+next.len <;>
    simp [replaceCell,oldRead,newRead,oldTape,newTape,start,role,width,binary,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,low,high]

theorem replace_valid (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) :
    (run (replace t) ((ctx,(a,old)),next)).valid := by
  have h:(Bill.tab old.len t.blank (fun j=>run (replaceCell t) (((ctx,(a,old)),next),j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>replaceCell_valid t ctx a old next j)
  exact ⟨⟨trivial,⟨trivial,⟨trivial,trivial⟩⟩⟩,h⟩

theorem replaceCell_peak (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:ℕ) (hj:j<old.len) :
    (run (replaceCell t) (((ctx,(a,old)),next),j)).peak ≤ a*next.len+next.len+old.len+1 := by
  have sub:=Nat.sub_le j (a*next.len)
  by_cases low:j<a*next.len <;> by_cases high:j<a*next.len+next.len <;>
    simp only [replaceCell,oldRead,newRead,oldTape,newTape,start,role,width,binary,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,low,high,
      ↓reduceIte,one_ne_zero,max_le_iff]
  all_goals repeat' apply And.intro
  all_goals omega

attribute [local irreducible] replaceCell

theorem replace_peak (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) :
    (run (replace t) ((ctx,(a,old)),next)).peak ≤ a*next.len+next.len+old.len+1 := by
  have lengthRun:run (show Prog false (ReplaceInput t) w from
      .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .len))))
      ((ctx,(a,old)),next)=⟨old.len,7,old.len,True⟩ := by
    simp [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rw [replace,DFTModelResidualPeakSyntax.tab,lengthRun]
  dsimp only [Bill.peak,Bill.val]

  have cells:(Finset.range old.len).sup
      (fun j=>(run (replaceCell t) (((ctx,(a,old)),next),j)).peak) ≤ a*next.len+next.len+old.len+1 :=
    Finset.sup_le (fun j hj=>replaceCell_peak t ctx a old next j (Finset.mem_range.mp hj))
  omega

theorem replace_len (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) :
    (run (replace t) ((ctx,(a,old)),next)).val.len=old.len := by rw [replace_value];rfl

theorem replace_inside (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:Fin next.len)
    (room:a*next.len+j.val<old.len) :
    (run (replace t) ((ctx,(a,old)),next)).val.look (a*next.len+j.val) t.blank=next.look j.val t.blank := by
  rw [replace_value]
  have inside:a*next.len ≤ a*next.len+j.val ∧ a*next.len+j.val<a*next.len+next.len := by
    have h:=j.isLt;omega
  simp [Tape.look,Tape.tab,room,inside,j.isLt]

theorem replace_outside (t:Ty) (ctx:Meta.T) (a:ℕ) (old next:Tape t.T) (j:Fin old.len)
    (outside:¬(a*next.len ≤ j.val ∧ j.val<a*next.len+next.len)) :
    (run (replace t) ((ctx,(a,old)),next)).val.look j.val t.blank=old.look j.val t.blank := by
  rw [replace_value]
  simp only [Tape.look,Tape.tab,j.isLt,↓reduceDIte,outside,↓reduceIte]

end
end ExactFourierCircuits.DFTModelResidualClosedRoleStages
