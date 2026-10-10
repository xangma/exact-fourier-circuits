import DFTModelCacheDisplacementSum

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDisplacement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDisplacementSum (integer scalar)
noncomputable section

/-- Runtime metadata: radix, (height,width), (row,column), (split,FFT width). -/
abbrev Metadata := p w (p (p w w) (p (p w w) (p w w)))
abbrev Banks := DFTModelCacheDisplacementSum.Banks
abbrev Env := p Metadata Banks
abbrev Cell := p Env w

def metadata (r : ℕ) (p : UniformRankKernelMachine.Parameters) : Metadata.T :=
  (r,((p.a,p.e),((p.i0,p.j0),(p.split,p.N))))
def radix : Prog false Metadata w := .atom .fst
def height : Prog false Metadata w := .comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))
def width : Prog false Metadata w := .comp (.atom .snd) (.comp (.atom .fst) (.atom .snd))
def row : Prog false Metadata w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .fst)))
def column : Prog false Metadata w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
def split : Prog false Metadata w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def size : Prog false Metadata w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def readMeta (f : Prog false Metadata w) : Prog false Cell w :=
  .comp (.comp (.atom .fst) (.atom .fst)) f
def hBank : Prog false Cell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def gBank : Prog false Cell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def index : Prog false Cell w := .atom .snd
def zeroIndex : Prog false Cell w := .atom (.lit 0)
def vAt (i : Prog false Cell w) : Prog false Cell sc := scalar (.sub .scalar)
  (.atom (.cz .scalar)) (.comp (.fork hBank
    (integer .sub (integer .add (readMeta row) i) (readMeta split))) (.atom .look))
def wAt (j : Prog false Cell w) : Prog false Cell sc :=
  .comp (.fork gBank (integer .sub (readMeta split)
    (integer .add (readMeta column) j))) (.atom .look)
def matrixArgument (i j : Prog false Cell w) :
    Prog false Cell DFTModelCacheDisplacementSum.Input :=
  .fork (.fork hBank gBank) (.fork (readMeta split)
    (.fork (integer .add (readMeta row) i) (integer .add (readMeta column) j)))
def matrixAt (i j : Prog false Cell w) : Prog false Cell sc :=
  .comp (matrixArgument i j) DFTModelCacheDisplacementSum.program
def rowCell : Prog false Cell sc := scalar (.sub .scalar)
  (matrixAt zeroIndex index) (scalar (.scale .scalar) (vAt zeroIndex) (wAt index))
def colCell : Prog false Cell sc := .ifz index (.atom (.cz .scalar))
  (scalar (.sub .scalar) (matrixAt index zeroIndex)
    (scalar (.scale .scalar) (vAt index) (wAt zeroIndex)))
def padded (bound : Prog false Metadata w) (f : Prog false Cell sc) : Prog false Cell sc :=
  .ifz (integer .lt index (readMeta bound)) (.atom (.cz .scalar)) f
def delta : Prog false Cell sc := .ifz index (.atom .cone) (.atom (.cz .scalar))
def cell0 : Prog false Cell sc := padded width (wAt index)
def cell1 : Prog false Cell sc := padded height (vAt index)
def cell2 : Prog false Cell sc := padded width rowCell
def cell5 : Prog false Cell sc := padded height colCell

attribute [local irreducible] DFTModelCacheDisplacementSum.program

theorem vAt_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (vAt index) ((metadata r p,(h,g)),j)=
      ⟨-h.look (p.i0+j-p.split) 0,41,p.i0+j,True⟩ := by
  simp [vAt,scalar,hBank,integer,readMeta,row,split,index,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem vAt_zero_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (vAt zeroIndex) ((metadata r p,(h,g)),j)=⟨-h.look (p.i0-p.split) 0,41,p.i0,True⟩ := by
  simp [vAt,scalar,hBank,integer,readMeta,row,split,zeroIndex,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem wAt_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (wAt index) ((metadata r p,(h,g)),j)=
      ⟨g.look (p.split-(p.j0+j)) 0,37,max (p.j0+j) (p.split-(p.j0+j)),True⟩ := by
  simp [wAt,gBank,integer,readMeta,column,split,index,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem wAt_zero_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (wAt zeroIndex) ((metadata r p,(h,g)),j)=
      ⟨g.look (p.split-p.j0) 0,37,max p.j0 (p.split-p.j0),True⟩ := by
  simp [wAt,gBank,integer,readMeta,column,split,zeroIndex,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem matrixArgument_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run (matrixArgument zeroIndex index) ((metadata r p,(h,g)),j)=
      ⟨((h,g),(p.split,(p.i0,p.j0+j))),55,max p.i0 (p.j0+j),True⟩ := by
  simp [matrixArgument,hBank,gBank,integer,readMeta,row,column,split,zeroIndex,index,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem matrixArgument_col_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run (matrixArgument index zeroIndex) ((metadata r p,(h,g)),j)=
      ⟨((h,g),(p.split,(p.i0+j,p.j0))),55,max (p.i0+j) p.j0,True⟩ := by
  simp [matrixArgument,hBank,gBank,integer,readMeta,row,column,split,zeroIndex,index,metadata,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

attribute [local irreducible] matrixArgument vAt wAt

theorem matrixAt_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run (matrixAt zeroIndex index) ((metadata r p,(h,g)),j)=
      (run DFTModelCacheDisplacementSum.program ((h,g),(p.split,(p.i0,p.j0+j)))).pay
        56 (max p.i0 (p.j0+j)) := by
  change ((run (matrixArgument zeroIndex index) _).pass
    (run DFTModelCacheDisplacementSum.program)).pay 1 0=_
  rw [matrixArgument_run]
  simp only [Bill.pass,Bill.pay]
  congr 1 <;> first | omega | simp

theorem matrixAt_col_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run (matrixAt index zeroIndex) ((metadata r p,(h,g)),j)=
      (run DFTModelCacheDisplacementSum.program ((h,g),(p.split,(p.i0+j,p.j0)))).pay
        56 (max (p.i0+j) p.j0) := by
  change ((run (matrixArgument index zeroIndex) _).pass
    (run DFTModelCacheDisplacementSum.program)).pay 1 0=_
  rw [matrixArgument_col_run]
  simp only [Bill.pass,Bill.pay]
  congr 1 <;> first | omega | simp

theorem index_run (x : Cell.T) : run index x=⟨x.2,1,0,True⟩ := rfl

attribute [local irreducible] matrixAt index

def vValue (p : UniformRankKernelMachine.Parameters) (h : Tape ℂ) (i : ℕ) : ℂ :=
  -h.look (p.i0+i-p.split) 0
def wValue (p : UniformRankKernelMachine.Parameters) (g : Tape ℂ) (j : ℕ) : ℂ :=
  g.look (p.split-(p.j0+j)) 0
def matrixValue (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (i j : ℕ) : ℂ :=
  DFTModelCacheDisplacementSum.value h g (p.i0+i) (p.j0+j) (p.split-(p.j0+j))
def rowValue (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) : ℂ :=
  matrixValue p h g 0 j-vValue p h 0*wValue p g j
def colValue (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (i : ℕ) : ℂ :=
  if i=0 then 0 else matrixValue p h g i 0-vValue p h i*wValue p g 0

theorem rowCell_value (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    (run rowCell ((metadata r p,(h,g)),j)).val=rowValue p h g j := by
  change (run (matrixAt zeroIndex index) _).val-
    (run (vAt zeroIndex) _).val*(run (wAt index) _).val=_
  rw [matrixAt_run,DFTModelCacheDisplacementSum.program_run,vAt_zero_run,wAt_run]
  simp [rowValue,matrixValue,vValue,wValue,Bill.pay]

theorem colCell_value (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    (run colCell ((metadata r p,(h,g)),j)).val=colValue p h g j := by
  by_cases hj:j=0
  · simp [colCell,index_run,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,colValue,hj]
  · simp only [colCell,index_run,scalar,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,hj,↓reduceIte]
    change (run (matrixAt index zeroIndex) ((metadata r p,(h,g)),j)).val-
      (run (vAt index) ((metadata r p,(h,g)),j)).val*
      (run (wAt zeroIndex) ((metadata r p,(h,g)),j)).val=_
    rw [matrixAt_col_run r p h g j,DFTModelCacheDisplacementSum.program_run,vAt_run r p h g j,wAt_zero_run r p h g j]
    simp [colValue,matrixValue,vValue,wValue,Bill.pay,hj]

theorem padded_width_run (f : Prog false Cell sc) (r : ℕ)
    (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (padded width f) ((metadata r p,(h,g)),j)=
      (if j<p.e then run f ((metadata r p,(h,g)),j) else Bill.one (0:ℂ)).pay
        14 (if j<p.e then 1 else 0) := by
  by_cases hj:j<p.e <;>
    simp [padded,integer,index_run,readMeta,width,metadata,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay,hj]
  omega

theorem padded_height_run (f : Prog false Cell sc) (r : ℕ)
    (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run (padded height f) ((metadata r p,(h,g)),j)=
      (if j<p.a then run f ((metadata r p,(h,g)),j) else Bill.one (0:ℂ)).pay
        14 (if j<p.a then 1 else 0) := by
  by_cases hj:j<p.a <;>
    simp [padded,integer,index_run,readMeta,height,metadata,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay,hj]
  omega

theorem delta_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (j : ℕ) :
    run delta ((metadata r p,(h,g)),j)=⟨if j=0 then 1 else 0,3,0,True⟩ := by
  by_cases hj:j=0 <;> simp [delta,index_run,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,hj]

end
end ExactFourierCircuits.DFTModelCacheDisplacement
