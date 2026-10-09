import DFTModelResidualAddressProof

set_option autoImplicit false

/-! Actual typed gather and inverse scatter of complete elements. In particular
one Tagged element carries both affine channels and its conservative tag. -/
namespace ExactFourierCircuits.DFTModelResidualMovement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input (t : Ty) := p (Ty.a w) (Ty.a t)
def length (t : Ty) : Prog false (Input t) w := .comp (.atom .fst) (.atom .len)
def address (t : Ty) : Prog false (p (Input t) w) w :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) (.atom .look)
def datum (t : Ty) : Prog false (p (Input t) w) t :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def gatherCell (t : Ty) : Prog false (p (Input t) w) t :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (address t)) (.atom .look)
def scatterCell (t : Ty) : Prog false (p (Input t) w) (p w t) := .fork (address t) (datum t)
def gather (t : Ty) : Prog false (Input t) (Ty.a t) := .tab (length t) (gatherCell t)
/-- This is a scatter: source i is written to destination addresses[i]. -/
def scatter (t : Ty) : Prog false (Input t) (Ty.a t) :=
  .sow (length t) (length t) (scatterCell t)

theorem gatherCell_run (t : Ty) (p : Tape ℕ) (v : Tape t.T) (j : ℕ) :
    run (gatherCell t) ((p,v),j)=⟨v.look (p.look j 0) t.blank,13,0,True⟩ := by
  simp [gatherCell,address,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem scatterCell_run (t : Ty) (p : Tape ℕ) (v : Tape t.T) (j : ℕ) :
    run (scatterCell t) ((p,v),j)=⟨(p.look j 0,v.look j t.blank),15,0,True⟩ := by
  simp [scatterCell,address,datum,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem gather_value (t : Ty) (p : Tape ℕ) (v : Tape t.T) :
    (run (gather t) (p,v)).val=Tape.tab p.len (fun j=>v.look (p.look j 0) t.blank) := by
  change (Bill.tab p.len t.blank (fun j=>run (gatherCell t) ((p,v),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab p.len) (funext (fun j=>congrArg Bill.val (gatherCell_run t p v j)))

theorem gather_work (t : Ty) (p : Tape ℕ) (v : Tape t.T) :
    (run (gather t) (p,v)).work=17*p.len+6 := by
  change 3+(Bill.tab p.len t.blank (fun j=>run (gatherCell t) ((p,v),j))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hf : (fun j=>(run (gatherCell t) ((p,v),j)).work)=(fun _=>13) := by
    funext j;exact congrArg Bill.work (gatherCell_run t p v j)
  rw [hf]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem gather_peak (t : Ty) (p : Tape ℕ) (v : Tape t.T) :
    (run (gather t) (p,v)).peak=p.len := by
  change max (max (max (max 0 p.len) 0) (Bill.tab p.len t.blank
    (fun j=>run (gatherCell t) ((p,v),j))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hf : (fun j=>(run (gatherCell t) ((p,v),j)).peak)=(fun _=>0) := by
    funext j;exact congrArg Bill.peak (gatherCell_run t p v j)
  rw [hf]
  simp

theorem gather_valid (t : Ty) (p : Tape ℕ) (v : Tape t.T) : (run (gather t) (p,v)).valid := by
  have h : (Bill.tab p.len t.blank (fun j=>run (gatherCell t) ((p,v),j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>by rw [gatherCell_run];trivial)
  exact ⟨⟨trivial,trivial⟩,h⟩

def scatterSteps (t : Ty) (p : Tape ℕ) (v : Tape t.T) (m : ℕ) : Bill (Tape t.T) :=
  Bill.steps (Tape.tab p.len (fun _=>t.blank))
    (fun j old=>(run (scatterCell t) ((p,v),j)).pass
      (fun pair=>Bill.one (old.set pair.1 pair.2))) m

theorem scatterSteps_work (t : Ty) (p : Tape ℕ) (v : Tape t.T) (m : ℕ) :
    (scatterSteps t p v m).work=17*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (scatterSteps t p v m).work+(run (scatterCell t) ((p,v),m)).work+1+1=_
    rw [scatterCell_run,ih]
    dsimp only [Bill.work]
    omega

theorem scatterSteps_peak (t : Ty) (p : Tape ℕ) (v : Tape t.T) (m : ℕ) :
    (scatterSteps t p v m).peak=m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change max (max (scatterSteps t p v m).peak
      (max (run (scatterCell t) ((p,v),m)).peak 0)) (m+1)=_
    rw [scatterCell_run,ih]
    dsimp only [Bill.peak]
    omega

theorem scatterSteps_valid (t : Ty) (p : Tape ℕ) (v : Tape t.T) (m : ℕ) :
    (scatterSteps t p v m).valid := by
  induction m with
  | zero => trivial
  | succ m ih =>
    change (scatterSteps t p v m).valid ∧ ((run (scatterCell t) ((p,v),m)).valid ∧ True)
    rw [scatterCell_run]
    exact ⟨ih,trivial,trivial⟩

theorem scatter_work (t : Ty) (p : Tape ℕ) (v : Tape t.T) :
    (run (scatter t) (p,v)).work=18*p.len+9 := by
  change 3+(3+((scatterSteps t p v p.len).work+(1+p.len)))+1=_
  rw [scatterSteps_work]
  omega

theorem scatter_peak (t : Ty) (p : Tape ℕ) (v : Tape t.T) :
    (run (scatter t) (p,v)).peak=p.len := by
  change max (max (max (max 0 p.len) 0) (max (max (max 0 p.len) 0)
    (max (scatterSteps t p v p.len).peak p.len))) 0 = _
  rw [scatterSteps_peak]
  omega

theorem scatter_valid (t : Ty) (p : Tape ℕ) (v : Tape t.T) : (run (scatter t) (p,v)).valid := by
  change (True ∧ True) ∧ (True ∧ True) ∧ (scatterSteps t p v p.len).valid
  exact ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩,scatterSteps_valid _ _ _ _⟩

theorem scatterSteps_len (t : Ty) (p : Tape ℕ) (v : Tape t.T) (m : ℕ) :
    (scatterSteps t p v m).val.len=p.len := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

theorem scatterSteps_look (t : Ty) {L : ℕ} (phi : Fin L≃Fin L) (p : Tape ℕ) (v : Tape t.T)
    (plen : p.len=L) (table : ∀j:Fin L,p.look j.val 0=(phi j).val)
    (m : ℕ) (hm : m≤L) (j : Fin L) :
    (scatterSteps t p v m).val.look (phi j).val t.blank =
      if j.val < m then v.look j.val t.blank else t.blank := by
  induction m with
  | zero => simp [scatterSteps,Bill.steps,Bill.one,Tape.look,Tape.tab,plen,(phi j).isLt]
  | succ m ih =>
    have ml:m<L:=by omega
    let i : Fin L:=⟨m,ml⟩
    have len:=scatterSteps_len t p v m
    change ((scatterSteps t p v m).val.set
      (run (scatterCell t) ((p,v),m)).val.1
      (run (scatterCell t) ((p,v),m)).val.2).look (phi j).val t.blank=_
    rw [scatterCell_run]
    change ((scatterSteps t p v m).val.set (p.look m 0) (v.look m t.blank)).look (phi j).val t.blank=_
    rw [show p.look m 0=(phi i).val from table i]
    by_cases eq:j=i
    · subst j
      simp [Tape.look,Tape.set,len,plen,(phi i).isLt,i]
    · have ne:(phi j).val≠(phi i).val := by
        intro h;exact eq (phi.injective (Fin.ext h))
      have old : ((scatterSteps t p v m).val.set (phi i).val
          (v.look m t.blank)).look (phi j).val t.blank=
          (scatterSteps t p v m).val.look (phi j).val t.blank := by
        simp [Tape.look,Tape.set,len,plen,(phi j).isLt,ne]
      rw [old,ih (by omega)]
      have jm:j.val≠m:=by intro he;exact eq (Fin.ext he)
      have hiff:(j.val < m+1)↔j.val < m:=by omega
      simp only [hiff]

/-- Inverse-coordinate semantics, proved for the literal `sow`; this is
not forward gather reused under a misleading name. -/
theorem scatter_value (t : Ty) {L : ℕ} (phi : Fin L≃Fin L) (p : Tape ℕ) (v : Tape t.T)
    (plen : p.len=L) (table : ∀j:Fin L,p.look j.val 0=(phi j).val) (j : Fin L) :
    (run (scatter t) (p,v)).val.look (phi j).val t.blank=v.look j.val t.blank := by
  exact (scatterSteps_look t phi p v plen table p.len (by omega) j).trans
    (ite_eq_left (by simpa only [plen] using j.isLt))

end
end ExactFourierCircuits.DFTModelResidualMovement
