import DFTModelResidualCore
import DFTModelAffineCore

set_option autoImplicit false

/-! Charged compact sector movement. Geometry is (roles, volume, start, width).
The fresh patch has roles*width cells. The published parent tape is readonly. -/
namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section
abbrev Geometry := p w (p w (p w w))
abbrev Input (t : Ty) := p Geometry (Ty.a t)
abbrev Patch (t : Ty) := p (Input t) (Ty.a t)
def roles (t : Ty) : Prog false (Input t) w := .comp (.atom .fst) (.atom .fst)
def volume (t : Ty) : Prog false (Input t) w :=
 .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def start (t : Ty) : Prog false (Input t) w :=
 .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def width (t : Ty) : Prog false (Input t) w :=
 .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def size (t : Ty) : Prog false (Input t) w := binary .mul (roles t) (width t)
def sourceIndex (t : Ty) : Prog false (p (Input t) w) w :=
 binary .add
  (binary .add
   (binary .mul (binary .div (.atom .snd) (.comp (.atom .fst) (width t)))
    (.comp (.atom .fst) (volume t)))
   (.comp (.atom .fst) (start t)))
  (binary .mod (.atom .snd) (.comp (.atom .fst) (width t)))
def gatherCell (t : Ty) : Prog false (p (Input t) w) t :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (sourceIndex t)) (.atom .look)
def gather (t : Ty) : Prog false (Input t) (Ty.a t) := .tab (size t) (gatherCell t)
def scatterCell (t : Ty) : Prog false (p (Patch t) w) t :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
/-- Reverse movement builds only a compact patch; spectators stay readonly. -/
def scatter (t : Ty) : Prog false (Patch t) (Patch t) :=
 .fork (.atom .fst) (.tab (.comp (.atom .fst) (size t)) (scatterCell t))

def gathered {α : Type} (W V a T : ℕ) (v : Tape α) (z : α) : Tape α :=
 Tape.tab (W*T) (fun j => v.look ((j/T)*V+a+j%T) z)

theorem size_run (t : Ty) (W V a T : ℕ) (v : Tape t.T) :
 run (size t) ((W,(V,(a,T))),v) = ⟨W*T,13,W*T,True⟩ := by
 simp [size,roles,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem sourceIndex_run (t : Ty) (W V a T j : ℕ) (v : Tape t.T) :
 run (sourceIndex t) (((W,(V,(a,T))),v),j) =
 ⟨(j/T)*V+a+j%T,51,max (j/T) (max ((j/T)*V) (max ((j/T)*V+a)
  (max (j%T) ((j/T)*V+a+j%T)))),True⟩ := by
 simp [sourceIndex,volume,start,width,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word, max_left_comm, max_comm]
 omega

theorem gatherCell_run (t : Ty) (W V a T j : ℕ) (v : Tape t.T) :
 run (gatherCell t) (((W,(V,(a,T))),v),j) =
 ⟨v.look ((j/T)*V+a+j%T) t.blank,57,
  max (j/T) (max ((j/T)*V) (max ((j/T)*V+a)
  (max (j%T) ((j/T)*V+a+j%T)))),True⟩ := by
 simp only [gatherCell,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [show Code.run (sourceIndex t) () (((W,(V,(a,T))),v),j)=_ from sourceIndex_run t W V a T j v]
 simp

theorem gather_value (t : Ty) (W V a T : ℕ) (v : Tape t.T) :
 (run (gather t) ((W,(V,(a,T))),v)).val = gathered W V a T v t.blank := by
 change (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
  (fun j => run (gatherCell t) (((W,(V,(a,T))),v),j))).val = _
 rw [size_run,ModelEquivalenceInterpreter.tab_value]
 exact congrArg (Tape.tab (W*T)) (funext (fun j => congrArg Bill.val (gatherCell_run t W V a T j v)))

theorem gather_work (t : Ty) (W V a T : ℕ) (v : Tape t.T) :
 (run (gather t) ((W,(V,(a,T))),v)).work = 61*(W*T)+16 := by
 change (run (size t) ((W,(V,(a,T))),v)).work+
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (gatherCell t) (((W,(V,(a,T))),v),j))).work+1 = _
 rw [size_run,ModelEquivalenceInterpreter.tab_work]
 have hf : (fun j => (run (gatherCell t) (((W,(V,(a,T))),v),j)).work) = fun _ => 57 := by
  funext j; exact congrArg Bill.work (gatherCell_run t W V a T j v)
 rw [hf]
 simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
 omega

theorem gather_valid (t : Ty) (W V a T : ℕ) (v : Tape t.T) :
 (run (gather t) ((W,(V,(a,T))),v)).valid := by
 change (run (size t) ((W,(V,(a,T))),v)).valid ∧
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (gatherCell t) (((W,(V,(a,T))),v),j))).valid
 rw [size_run]
 refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
 intro j _; rw [gatherCell_run]; trivial

theorem gather_length (t : Ty) (W V a T : ℕ) (v : Tape t.T) :
 (run (gather t) ((W,(V,(a,T))),v)).val.len = W*T := by
 rw [gather_value]; rfl

theorem gather_lookup (t : Ty) (W V a T r j : ℕ) (v : Tape t.T)
 (hr : r<W) (hj : j<T) :
 (run (gather t) ((W,(V,(a,T))),v)).val.look (r*T+j) t.blank =
 v.look (r*V+a+j) t.blank := by
 have pos : 0<T := by omega
 have small : r*T+j<W*T := by nlinarith
 rw [gather_value]
 simp [gathered,Tape.look,Tape.tab,small,Nat.add_div,pos,
  Nat.add_mod,Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj,Nat.not_le.mpr hj]

theorem scatterCell_run (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) :
 run (scatterCell t) ((((W,(V,(a,T))),v),b),j) =
 ⟨b.look j t.blank,7,0,True⟩ := by
 simp [scatterCell,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem scatter_value (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).val =
 (((W,(V,(a,T))),v),Tape.tab (W*T) (fun j => b.look j t.blank)) := by
 change (_, (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
  (fun j => run (scatterCell t) ((((W,(V,(a,T))),v),b),j))).val) = _
 rw [size_run,ModelEquivalenceInterpreter.tab_value]
 rfl

theorem scatter_work (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).work = 11*(W*T)+20 := by
 change 1+((1+(run (size t) ((W,(V,(a,T))),v)).work+1)+
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (scatterCell t) ((((W,(V,(a,T))),v),b),j))).work+1)+1 = _
 rw [size_run,ModelEquivalenceInterpreter.tab_work]
 have hf : (fun j => (run (scatterCell t) ((((W,(V,(a,T))),v),b),j)).work) = fun _ => 7 := by
  funext j; exact congrArg Bill.work (scatterCell_run t W V a T j v b)
 rw [hf]
 simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
 omega

theorem scatter_valid (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).valid := by
 change True ∧ ((True ∧ (run (size t) ((W,(V,(a,T))),v)).valid) ∧
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (scatterCell t) ((((W,(V,(a,T))),v),b),j))).valid) ∧ True
 rw [size_run]
 refine ⟨trivial,⟨⟨trivial,trivial⟩,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩,trivial⟩
 intro j _; rw [scatterCell_run]; trivial

theorem scatter_peak (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).peak = W*T := by
 simp only [scatter,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
 change max (run (size t) ((W,(V,(a,T))),v)).peak
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (scatterCell t) ((((W,(V,(a,T))),v),b),j))).peak = _
 rw [size_run,ModelEquivalenceInterpreter.tab_peak]
 have hf : (fun j => (run (scatterCell t) ((((W,(V,(a,T))),v),b),j)).peak) = fun _ => 0 := by
  funext j; exact congrArg Bill.peak (scatterCell_run t W V a T j v b)
 rw [hf]
 simp

end
end ExactFourierCircuits.DFTModelSectorTranspose
