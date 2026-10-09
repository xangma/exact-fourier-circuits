import DFTModelResidualBasisGeometry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualClosedBasis
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open BinaryFrames UniformBinaryXorCoordinates
noncomputable section

/-- Ordinary q, native width, spectator count, and original raw direction cells. -/
abbrev Meta := p w (p w (p w (Ty.a w)))
abbrev Prepared := p Meta (p w w)

def direction : Prog false Meta DFTModelResidualBasisMask.Input := .fork
  (.comp (.atom .snd) (.atom .fst))
  (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def prepare : Prog false Meta Prepared := .fork (.atom .id) (.fork
  (.comp direction DFTModelResidualBasisMask.program)
  (.comp direction DFTModelResidualBasisPivot.program))
def format : Prog false Prepared DFTModelResidualBasisImages.Params := .fork
  (.comp (.atom .fst) (.atom .fst)) (.fork
    (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))) (.fork
      (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
      (.atom .snd)))
def parameters : Prog false Meta DFTModelResidualBasisImages.Params := .comp prepare format
def program : Prog false Meta (Ty.a w) := .comp parameters DFTModelResidualBasisImages.program

attribute [local irreducible] DFTModelResidualBasisMask.program DFTModelResidualBasisPivot.program
  DFTModelResidualBasisImages.program

theorem direction_run (q m r : ℕ) (v : Tape ℕ) :
    run direction (q,(m,(r,v)))=⟨(m,v),9,0,True⟩ := by
  simp [direction,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem format_run (q m r a p : ℕ) (v : Tape ℕ) :
    run format ((q,(m,(r,v))),(a,p))=⟨(q,(m,(r,(a,p)))),19,0,True⟩ := by
  simp [format,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem parameters_value (q m r : ℕ) (v : Tape ℕ) :
    (run parameters (q,(m,(r,v)))).val=
      (q,(m,(r,((run DFTModelResidualBasisMask.program (m,v)).val,
        (run DFTModelResidualBasisPivot.program (m,v)).val)))) := by
  simp [parameters,prepare,direction,format,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]

theorem parameters_work (q m r : ℕ) (v : Tape ℕ) :
    (run parameters (q,(m,(r,v)))).work ≤ 60*m+60 := by
  have mask:=DFTModelResidualBasisMask.program_work m v
  have pivot:=DFTModelResidualBasisPivot.program_work m v
  simp only [parameters,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    direction,format]
  change (Code.run DFTModelResidualBasisMask.program () (m,v)).work=36*m+8 at mask
  change (Code.run DFTModelResidualBasisPivot.program () (m,v)).work ≤ 24*m+4 at pivot
  omega

theorem parameters_peak (q m r : ℕ) (v : Tape ℕ)
    (binary : ∀i,i < m → v.look i 0 < 2) :
    (run parameters (q,(m,(r,v)))).peak ≤ 2^m+m+2 := by
  have mask:=DFTModelResidualBasisMask.program_peak m v binary
  have pivot:=DFTModelResidualBasisPivot.program_peak m v
  have pos:=Nat.two_pow_pos m
  simp only [parameters,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    direction,format,max_le_iff]
  change (Code.run DFTModelResidualBasisMask.program () (m,v)).peak ≤ 2^m+2 at mask
  change (Code.run DFTModelResidualBasisPivot.program () (m,v)).peak ≤ m+1 at pivot
  repeat' apply And.intro
  all_goals omega

theorem parameters_valid (q m r : ℕ) (v : Tape ℕ) :
    (run parameters (q,(m,(r,v)))).valid := by
  have mask:=DFTModelResidualBasisMask.program_valid m v
  have pivot:=DFTModelResidualBasisPivot.program_valid m v
  simp only [parameters,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    direction,format,and_true,true_and]
  simpa only [run] using And.intro mask pivot

/-- The pivot and mask are obtained from charged original-direction reads.
The resulting tape is exactly the concrete native permutation's unit images. -/
theorem source_images (q w r : ℕ) (v : Vec (Fin (w+1))) (raw : Tape ℕ)
    (source : ∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero : v≠0) :
    ∃p:Fin (w+1),∃hp:v p=1,
      (run parameters (q,(w+1,(r,raw)))).val=
        (q,(w+1,(r,((encode v).val,p.val)))) ∧
      ∀i:Fin (q*(w+1)+r),(run program (q,(w+1,(r,raw)))).val.look i.val 0=
        (DFTModelResidualBasisGeometry.permutation q w r v p hp (encode (unit i))).val := by
  have binary:∀i,i < w+1 → raw.look i 0 < 2 := by
    intro i hi
    rw [source ⟨i,hi⟩]
    exact (v ⟨i,hi⟩).isLt
  have nz:∃i,i < w+1 ∧ raw.look i 0=1 := by
    by_contra no
    apply nonzero
    funext i
    have bit:=binary i.val i.isLt
    have notone:raw.look i.val 0≠1 := by intro h;exact no ⟨i.val,i.isLt,h⟩
    apply ZMod.val_injective
    change (v i).val=0
    rw [←source i]
    omega
  obtain ⟨pivot,hp,point,_before,actual⟩:=DFTModelResidualBasisPivot.program_finds (w+1) raw binary nz
  let p:Fin (w+1):=⟨pivot,hp⟩
  have vp:v p=1 := by
    apply ZMod.val_injective
    change (v p).val=1
    rw [←source p]
    exact point
  have parameter:(run parameters (q,(w+1,(r,raw)))).val=
      (q,(w+1,(r,((encode v).val,p.val)))) := by
    rw [parameters_value,DFTModelResidualBasisMask.source_value (w+1) v raw source,actual]
  refine ⟨p,vp,parameter,?_⟩
  intro i
  change (run DFTModelResidualBasisImages.program (run parameters (q,(w+1,(r,raw)))).val).val.look i.val 0=_
  rw [parameter]
  exact DFTModelResidualBasisGeometry.program_images q w r v p vp i

end
end ExactFourierCircuits.DFTModelResidualClosedBasis
