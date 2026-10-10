import DFTModelCacheDisplacementCell

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDisplacement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDisplacementSum (scalar)
noncomputable section

attribute [local irreducible] vAt wAt matrixAt DFTModelCacheDisplacementSum.program

structure Shape (p : UniformRankKernelMachine.Parameters) (r : ℕ) : Prop where
  positiveA : 0<p.a
  positiveE : 0<p.e
  hRows : p.i0+p.a≤r
  gSplit : p.split<r
  interior : p.split≤p.i0
  columns : p.j0+p.e≤p.split
  widthA : p.a≤p.N
  widthE : p.e≤p.N

theorem scalar_sub_run {s : Ty} (f g : Prog false s sc) (x : s.T) :
    run (scalar (.sub .scalar) f g) x=
      ⟨(run f x).val-(run g x).val,(run f x).work+(run g x).work+3,
        max (run f x).peak (run g x).peak,(run f x).valid ∧ (run g x).valid⟩ := by
  simp [scalar,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem scalar_mul_run {s : Ty} (f g : Prog false s sc) (x : s.T) :
    run (scalar (.scale .scalar) f g) x=
      ⟨(run f x).val*(run g x).val,(run f x).work+(run g x).work+3,
        max (run f x).peak (run g x).peak,(run f x).valid ∧ (run g x).valid⟩ := by
  simp [scalar,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem ifz_index_run (f g : Prog false Cell sc) (x : Cell.T) :
    run (.ifz index f g) x=(if x.2=0 then run f x else run g x).pay 2 0 := by
  by_cases hx:x.2=0 <;> simp [index,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,hx]
  all_goals omega

attribute [local irreducible] index

theorem rowCell_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run rowCell ((metadata r p,(h,g)),j)=
      ⟨rowValue p h g j,52*(p.split-(p.j0+j))+154,
        max p.i0 (max (p.j0+j) (p.split-(p.j0+j))),True⟩ := by
  rw [rowCell,scalar_sub_run,scalar_mul_run,matrixAt_run,
    DFTModelCacheDisplacementSum.program_run,vAt_zero_run,wAt_run]
  simp only [Bill.pay,rowValue,matrixValue,vValue,wValue,Nat.add_zero]
  congr 1 <;> first | omega | simp
  split_ifs <;> omega

theorem colCell_run (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (j : ℕ) :
    run colCell ((metadata r p,(h,g)),j)=
      ⟨colValue p h g j,if j=0 then 3 else 52*(p.split-p.j0)+156,
        if j=0 then 0 else max (p.i0+j) (max p.j0 (p.split-p.j0)),True⟩ := by
  rw [colCell,ifz_index_run]
  by_cases hj:j=0
  · simp [hj,colValue,run,Code.run,Atom.run,Bill.one,Bill.pay]
  · rw [ite_eq_right hj,scalar_sub_run,scalar_mul_run,matrixAt_col_run,
      DFTModelCacheDisplacementSum.program_run,vAt_run,wAt_zero_run]
    simp only [Bill.pay,colValue,matrixValue,vValue,wValue,hj,↓reduceIte,Nat.add_zero]
    congr 1 <;> first | omega | simp
    split_ifs <;> omega

def cell (b : Fin 6) : Prog false Cell sc :=
  if b.val=0 then cell0 else if b.val=1 then cell1 else if b.val=2 then cell2 else
  if b.val=3 then delta else if b.val=4 then delta else cell5
def cellValue (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) (b : Fin 6) (j : ℕ) : ℂ :=
  if b.val=0 then if j<p.e then wValue p g j else 0 else
  if b.val=1 then if j<p.a then vValue p h j else 0 else
  if b.val=2 then if j<p.e then rowValue p h g j else 0 else
  if b.val=3 then if j=0 then 1 else 0 else
  if b.val=4 then if j=0 then 1 else 0 else
  if j<p.a then colValue p h g j else 0


theorem cell_value (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (b : Fin 6) (j : ℕ) :
    (run (cell b) ((metadata r p,(h,g)),j)).val=cellValue p h g b j := by
  fin_cases b
  · change (run cell0 ((metadata r p,(h,g)),j)).val=cellValue p h g 0 j
    rw [cell0,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (wAt index) ((metadata r p,(h,g)),j)).val=_
      rw [wAt_run r p h g j]
      simp [cellValue,wValue,hj]
    · simp only [ite_eq_right hj]
      simp [cellValue,Bill.pay,Bill.one,hj]
  · change (run cell1 ((metadata r p,(h,g)),j)).val=cellValue p h g 1 j
    rw [cell1,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (vAt index) ((metadata r p,(h,g)),j)).val=_
      rw [vAt_run r p h g j]
      simp [cellValue,vValue,hj]
    · simp only [ite_eq_right hj]
      simp [cellValue,Bill.pay,Bill.one,hj]
  · change (run cell2 ((metadata r p,(h,g)),j)).val=cellValue p h g 2 j
    rw [cell2,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (rowCell) ((metadata r p,(h,g)),j)).val=_
      rw [rowCell_run r p h g j]
      simp [cellValue,hj]
    · simp only [ite_eq_right hj]
      simp [cellValue,Bill.pay,Bill.one,hj]
  · change (run delta ((metadata r p,(h,g)),j)).val=cellValue p h g 3 j
    rw [delta_run]
    simp [cellValue]
  · change (run delta ((metadata r p,(h,g)),j)).val=cellValue p h g 4 j
    rw [delta_run]
    simp [cellValue]
  · change (run cell5 ((metadata r p,(h,g)),j)).val=cellValue p h g 5 j
    rw [cell5,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (colCell) ((metadata r p,(h,g)),j)).val=_
      rw [colCell_run r p h g j]
      simp [cellValue,hj]
    · simp only [ite_eq_right hj]
      simp [cellValue,Bill.pay,Bill.one,hj]

theorem cell_valid (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (b : Fin 6) (j : ℕ) :
    (run (cell b) ((metadata r p,(h,g)),j)).valid := by
  fin_cases b
  · change (run cell0 ((metadata r p,(h,g)),j)).valid
    rw [cell0,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (wAt index) ((metadata r p,(h,g)),j)).valid
      rw [wAt_run r p h g j]
      trivial
    · simp only [ite_eq_right hj]
      trivial
  · change (run cell1 ((metadata r p,(h,g)),j)).valid
    rw [cell1,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (vAt index) ((metadata r p,(h,g)),j)).valid
      rw [vAt_run r p h g j]
      trivial
    · simp only [ite_eq_right hj]
      trivial
  · change (run cell2 ((metadata r p,(h,g)),j)).valid
    rw [cell2,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (rowCell) ((metadata r p,(h,g)),j)).valid
      rw [rowCell_run r p h g j]
      trivial
    · simp only [ite_eq_right hj]
      trivial
  · change (run delta ((metadata r p,(h,g)),j)).valid
    rw [delta_run]
    trivial
  · change (run delta ((metadata r p,(h,g)),j)).valid
    rw [delta_run]
    trivial
  · change (run cell5 ((metadata r p,(h,g)),j)).valid
    rw [cell5,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (colCell) ((metadata r p,(h,g)),j)).valid
      rw [colCell_run r p h g j]
      trivial
    · simp only [ite_eq_right hj]
      trivial

theorem cell_work (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (b : Fin 6) (j : ℕ) :
    (run (cell b) ((metadata r p,(h,g)),j)).work≤52*p.split+200 := by
  fin_cases b
  · change (run cell0 ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [cell0,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (wAt index) ((metadata r p,(h,g)),j)).work+14≤_
      rw [wAt_run r p h g j]
      dsimp only [Bill.work]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 15≤52*p.split+200
      omega
  · change (run cell1 ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [cell1,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (vAt index) ((metadata r p,(h,g)),j)).work+14≤_
      rw [vAt_run r p h g j]
      dsimp only [Bill.work]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 15≤52*p.split+200
      omega
  · change (run cell2 ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [cell2,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change (run (rowCell) ((metadata r p,(h,g)),j)).work+14≤_
      rw [rowCell_run r p h g j]
      dsimp only [Bill.work]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 15≤52*p.split+200
      omega
  · change (run delta ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [delta_run]
    change 3≤52*p.split+200
    omega
  · change (run delta ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [delta_run]
    change 3≤52*p.split+200
    omega
  · change (run cell5 ((metadata r p,(h,g)),j)).work≤52*p.split+200
    rw [cell5,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change (run (colCell) ((metadata r p,(h,g)),j)).work+14≤_
      rw [colCell_run r p h g j]
      dsimp only [Bill.work]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 15≤52*p.split+200
      omega

theorem cell_peak (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (b : Fin 6) (j : ℕ) (shape:Shape p r) :
    (run (cell b) ((metadata r p,(h,g)),j)).peak≤r := by
  have hrow:=shape.hRows;have ha:=shape.positiveA
  have hcol:=shape.columns;have hs:=shape.gSplit
  fin_cases b
  · change (run cell0 ((metadata r p,(h,g)),j)).peak≤r
    rw [cell0,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change max (run (wAt index) ((metadata r p,(h,g)),j)).peak 1≤_
      rw [wAt_run r p h g j]
      dsimp only [Bill.peak]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 0≤r
      omega
  · change (run cell1 ((metadata r p,(h,g)),j)).peak≤r
    rw [cell1,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change max (run (vAt index) ((metadata r p,(h,g)),j)).peak 1≤_
      rw [vAt_run r p h g j]
      dsimp only [Bill.peak]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 0≤r
      omega
  · change (run cell2 ((metadata r p,(h,g)),j)).peak≤r
    rw [cell2,padded_width_run]
    by_cases hj:j<p.e
    · simp only [ite_eq_left hj]
      change max (run (rowCell) ((metadata r p,(h,g)),j)).peak 1≤_
      rw [rowCell_run r p h g j]
      dsimp only [Bill.peak]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 0≤r
      omega
  · change (run delta ((metadata r p,(h,g)),j)).peak≤r
    rw [delta_run]
    change 0≤r
    omega
  · change (run delta ((metadata r p,(h,g)),j)).peak≤r
    rw [delta_run]
    change 0≤r
    omega
  · change (run cell5 ((metadata r p,(h,g)),j)).peak≤r
    rw [cell5,padded_height_run]
    by_cases hj:j<p.a
    · simp only [ite_eq_left hj]
      change max (run (colCell) ((metadata r p,(h,g)),j)).peak 1≤_
      rw [colCell_run r p h g j]
      dsimp only [Bill.peak]
      try split_ifs
      all_goals omega
    · simp only [ite_eq_right hj]
      change 0≤r
      omega

end
end ExactFourierCircuits.DFTModelCacheDisplacement
