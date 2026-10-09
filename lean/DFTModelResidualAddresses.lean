import DFTModelResidualBlockXor
import UniformResidualExtendedPermutation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualAddresses
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Params := p w (p w (p (Ty.a w) (Ty.a w)))
abbrev GrowInput := p (p Params w) (Ty.a w)
abbrev CellInput := p GrowInput w
abbrev Input := p w Params

def parameters (q m : ℕ) (images : Tape ℕ) : Params.T :=
  (m,(2^q,((run DFTModelResidualTable.program q).val,images)))
def context : Prog false CellInput Params :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def old : Prog false CellInput (Ty.a w) := .comp (.atom .fst) (.atom .snd)
def length : Prog false CellInput w := .comp old (.atom .len)
def image : Prog false CellInput w := .comp (.fork
  (.comp context (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
  (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))) (.atom .look)
def mask : Prog false CellInput w :=
  .ifz (binary .lt (.atom .snd) length) image (.atom (.lit 0))
def oldRead : Prog false CellInput w := .comp (.fork old
  (binary .mod (.atom .snd) length)) (.atom .look)
def argument : Prog false CellInput DFTModelResidualBlockXor.Input :=
  .fork (.comp context (.atom .fst))
    (.fork (.comp context (.comp (.atom .snd) (.atom .fst)))
      (.fork (.comp context (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
        (.fork oldRead mask)))
def cell : Prog false CellInput w := .comp argument DFTModelResidualBlockXor.program

def grow : Prog false GrowInput (Ty.a w) := .tab
  (binary .mul (.comp (.atom .snd) (.atom .len)) (.atom (.lit 2))) cell

def initial : Prog false Input (Ty.a w) := .tab (.atom (.lit 1)) (.atom (.lit 0))
def body : Prog false (p Input (p w (Ty.a w))) (Ty.a w) :=
  .comp (.fork (.fork (.comp (.atom .fst) (.atom .snd))
    (.comp (.atom .snd) (.atom .fst))) (.comp (.atom .snd) (.atom .snd))) grow
/-- Growing lengths are 1,2,4,...; each address is constructed a constant
number of times, with m lookup blocks per toggle, never q bit steps per address. -/
def program : Prog false Input (Ty.a w) := .loop (.atom .fst) initial body

 theorem cell_value (q m h : ℕ) (images v : Tape ℕ) (j : ℕ)
    (hv : 0<v.len) (small : ∀i,i<v.len→v.look i 0<2^(q*m))
    (im : images.look h 0<2^(q*m)) :
    (run cell (((parameters q m images,h),v),j)).val =
      v.look (j%v.len) 0 ^^^ (if j<v.len then 0 else images.look h 0) := by
  have arg : (run argument (((parameters q m images,h),v),j)).val =
      DFTModelResidualBlockXor.input q m (v.look (j%v.len) 0)
        (if j<v.len then 0 else images.look h 0) := by
    by_cases hj : j<v.len <;>
      simp [argument,context,oldRead,old,length,mask,image,parameters,
        DFTModelResidualBlockXor.input,binary,run,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,hj]
  change (run DFTModelResidualBlockXor.program
    (run argument (((parameters q m images,h),v),j)).val).val = _
  rw [arg]
  apply DFTModelResidualBlockXor.program_value
  · exact small _ (Nat.mod_lt j hv)
  · split_ifs
    · exact Nat.two_pow_pos _
    · exact im

theorem cell_work (m N h : ℕ) (table images v : Tape ℕ) (j : ℕ) :
    (run cell ((((m,(N,(table,images))),h),v),j)).work ≤ 120*m+92 := by
  have argVal : (run argument ((((m,(N,(table,images))),h),v),j)).val.1=m := by
    simp [argument,context,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  have argWork : (run argument ((((m,(N,(table,images))),h),v),j)).work ≤ 75 := by
    by_cases hj : j<v.len <;>
      simp [argument,context,oldRead,old,length,mask,image,binary,run,Code.run,
        Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hj]
  change (run argument ((((m,(N,(table,images))),h),v),j)).work+
    (run DFTModelResidualBlockXor.program
      (run argument ((((m,(N,(table,images))),h),v),j)).val).work+1 ≤ _
  rw [DFTModelResidualBlockXor.program_work,argVal]
  omega

theorem cell_valid (x : CellInput.T) : (run cell x).valid := by
  have h : (run argument x).valid := by
    rcases x with ⟨⟨⟨⟨m,N,table,images⟩,h⟩,v⟩,j⟩
    by_cases hj : j<v.len <;>
      simp [argument,context,oldRead,old,length,mask,image,binary,run,Code.run,
        Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hj]
  exact ⟨h,DFTModelResidualBlockXor.program_valid _⟩

def grown (image : ℕ→ℕ) (h : ℕ) (v : Tape ℕ) : Tape ℕ :=
  Tape.tab (2*v.len) (fun j => v.look (j%v.len) 0 ^^^ (if j<v.len then 0 else image h))

theorem grow_value (q m h : ℕ) (images v : Tape ℕ)
    (hv : 0<v.len) (small : ∀i,i<v.len→v.look i 0<2^(q*m))
    (im : images.look h 0<2^(q*m)) :
    (run grow ((parameters q m images,h),v)).val = grown (fun i=>images.look i 0) h v := by
  change (Bill.tab (v.len*2) w.blank (fun j=>run cell (((parameters q m images,h),v),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  have hf : (fun j => (run cell (((parameters q m images,h),v),j)).val)=
      (fun j => v.look (j%v.len) 0 ^^^ (if j<v.len then 0 else images.look h 0)) := by
    funext j;exact cell_value _ _ _ _ _ _ hv small im
  rw [hf]
  simp only [grown,Nat.mul_comm]

theorem grow_work (m N h : ℕ) (table images v : Tape ℕ) :
    (run grow (((m,(N,(table,images))),h),v)).work ≤ (120*m+96)*(2*v.len)+10 := by
  change 7+(Bill.tab (v.len*2) w.blank
    (fun j=>run cell ((((m,(N,(table,images))),h),v),j))).work+1 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j∈Finset.range (v.len*2),
      (run cell ((((m,(N,(table,images))),h),v),j)).work) ≤ (v.len*2)*(120*m+92) := by
    calc
      _ ≤ ∑_j∈Finset.range (v.len*2),(120*m+92) := Finset.sum_le_sum (fun j _=>cell_work m N h table images v j)
      _ = _ := by simp
  nlinarith

theorem grow_valid (x : GrowInput.T) : (run grow x).valid := by
  rcases x with ⟨⟨⟨m,N,table,images⟩,h⟩,v⟩
  have good : (Bill.tab (v.len*2) w.blank
      (fun j=>run cell ((((m,(N,(table,images))),h),v),j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun _ _=>cell_valid _)
  simpa only [grow,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,and_true,true_and] using good

end
end ExactFourierCircuits.DFTModelResidualAddresses
