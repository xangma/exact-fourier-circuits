import DFTModelCacheDisplacementClosed

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDisplacement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier
noncomputable section

variable {r : ℕ} {p : UniformRankKernelMachine.Parameters} {h g : Tape ℂ} {hf gf : ℕ→ℂ}

theorem vValue_source (shape:Shape p r) (hh:∀i,i<r→ h.look i 0=hf i)
    (i : ℕ) (hi:i<p.a) : vValue p h i=UniformRankKernelMachine.vValue p hf i := by
  unfold vValue UniformRankKernelMachine.vValue
  rw [hh]
  have hrows:=shape.hRows
  omega

theorem wValue_source (shape:Shape p r) (hg:∀i,i<r→ g.look i 0=gf i)
    (j : ℕ) (_hj:j<p.e) : wValue p g j=UniformRankKernelMachine.wValue p gf j := by
  unfold wValue UniformRankKernelMachine.wValue
  rw [hg]
  have hs:=shape.gSplit
  omega

theorem matrixValue_source (shape:Shape p r)
    (hh:∀i,i<r→ h.look i 0=hf i) (hg:∀i,i<r→ g.look i 0=gf i)
    (i j : ℕ) (hi:i<p.a) (_hj:j<p.e) :
    matrixValue p h g i j=UniformRankKernelMachine.matrixValue p hf gf i j := by
  unfold matrixValue DFTModelCacheDisplacementSum.value UniformRankKernelMachine.matrixValue
    ToeplitzLayers.cross
  apply Finset.sum_congr rfl
  intro u hu
  have hu:=Finset.mem_range.mp hu
  have hrows:=shape.hRows;have hs:=shape.gSplit
  rw [hh (p.i0+i-(p.j0+j)-u) (by omega),hg u (by omega)]

theorem rowValue_source (shape:Shape p r)
    (hh:∀i,i<r→ h.look i 0=hf i) (hg:∀i,i<r→ g.look i 0=gf i)
    (j : ℕ) (hj:j<p.e) : rowValue p h g j=UniformRankKernelMachine.rowValue p hf gf j := by
  unfold rowValue UniformRankKernelMachine.rowValue
  rw [matrixValue_source shape hh hg 0 j shape.positiveA hj,
    vValue_source shape hh 0 shape.positiveA,wValue_source shape hg j hj]

theorem colValue_source (shape:Shape p r)
    (hh:∀i,i<r→ h.look i 0=hf i) (hg:∀i,i<r→ g.look i 0=gf i)
    (i : ℕ) (hi:i<p.a) : colValue p h g i=UniformRankKernelMachine.colValue p hf gf i := by
  unfold colValue UniformRankKernelMachine.colValue
  by_cases hz:i=0
  · simp [hz]
  · simp only [hz,↓reduceIte]
    rw [matrixValue_source shape hh hg i 0 hi shape.positiveE,
      vValue_source shape hh i hi,wValue_source shape hg 0 shape.positiveE]

theorem cellValue_source (shape:Shape p r)
    (hh:∀i,i<r→ h.look i 0=hf i) (hg:∀i,i<r→ g.look i 0=gf i)
    (b : Fin 6) (j : Fin p.N) :
    cellValue p h g b j.val=UniformRankKernelMachine.finalCells p hf gf b j := by
  fin_cases b <;> simp [cellValue,UniformRankKernelMachine.finalCells]
  · by_cases hj:j.val<p.e
    · simp only [hj,↓reduceIte];exact wValue_source shape hg _ hj
    · simp [hj]
  · by_cases hj:j.val<p.a
    · simp only [hj,↓reduceIte];exact vValue_source shape hh _ hj
    · simp [hj]
  · by_cases hj:j.val<p.e
    · simp only [hj,↓reduceIte];exact rowValue_source shape hh hg _ hj
    · simp [hj]
  · by_cases hj:j.val<p.a
    · simp only [hj,↓reduceIte];exact colValue_source shape hh hg _ hj
    · simp [hj]

/-- Only semantic rectangle geometry is needed; no native heap address or
ready-table premise enters this identification. -/
theorem finalCells_rankKernels (p : UniformRankKernelMachine.Parameters) (K : ℕ)
    (hf gf : ℕ→ℂ) (ha:0<p.a) (he:0<p.e) (width:p.N=UniformRadixTwoDAG.width K)
    (b : Fin 6) (j : Fin (UniformRadixTwoDAG.width K)) :
    UniformRankKernelMachine.finalCells p hf gf b ⟨j.val,by rw [width];exact j.isLt⟩=
      UniformToeplitzCrossDAG.rankKernels K p.a p.e
        (UniformRankKernelMachine.matrixValue p hf gf)
        (UniformRankKernelMachine.vValue p hf) (UniformRankKernelMachine.wValue p gf) b j := by
  fin_cases b
  all_goals simp only [UniformToeplitzCrossDAG.rankKernels]
  all_goals simp (disch:=omega) [UniformToeplitzCrossDAG.leftFactor,UniformToeplitzCrossDAG.rightFactor,
    UniformRankKernelMachine.finalCells,UniformRankKernelMachine.rowValue,
    UniformRankKernelMachine.colValue,OAI.ExactFourier.Displacement.delta,
    UniformRankKernelMachine.inputVector_padding]
  all_goals intro hi hz
  all_goals have hv:=congrArg Fin.val hz
  all_goals simp only [Fin.val_zero] at hv
  all_goals omega

theorem rawValues_lookup (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ)
    (b : Fin 6) (j : Fin p.N) :
    ((rawValues p h g).look b.val (Ty.a sc).blank).look j.val 0=cellValue p h g b j.val := by
  rw [Tape.look_of_lt _ _ (show b.val<(rawValues p h g).len from b.isLt)]
  change (Tape.tab p.N (cellValue p h g ⟨b.val%6,Nat.mod_lt _ (by decide)⟩)).look j.val 0=_
  rw [Tape.look_of_lt _ _ (show j.val<(Tape.tab p.N (cellValue p h g ⟨b.val%6,Nat.mod_lt _ (by decide)⟩)).len from j.isLt)]
  change cellValue p h g ⟨b.val%6,Nat.mod_lt _ (by decide)⟩ j.val=_
  have hb:(⟨b.val%6,Nat.mod_lt _ (by decide)⟩:Fin 6)=b:=Fin.ext (Nat.mod_eq_of_lt b.isLt)
  rw [hb]

theorem program_length (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run program (metadata r p,omega)).val.len=6 := by rw [program_value r p omega hr];rfl

theorem program_kernel_length (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (omega : ℂ) (hr:0<r) (b : Fin 6) :
    ((run program (metadata r p,omega)).val.look b.val (Ty.a sc).blank).len=p.N := by
  rw [program_value r p omega hr]
  simp [rawValues,Tape.look,Tape.tab,b.isLt]

/-- Actual closed program output is the original six rank kernels, in the
original order, from a radix root and runtime rectangle metadata alone. -/
theorem program_rankKernels (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (omega : ℂ) (shape:Shape p r) (K : ℕ) (width:p.N=UniformRadixTwoDAG.width K)
    (b : Fin 6) (j : Fin (UniformRadixTwoDAG.width K)) :
    ((run program (metadata r p,omega)).val.look b.val (Ty.a sc).blank).look j.val 0=
      UniformToeplitzCrossDAG.rankKernels K p.a p.e
        (UniformRankKernelMachine.matrixValue p (fun i=>PowerSeries.coeff i (NewtonFourier.invH omega))
          (DFTModelCacheKernelNewton.gValue omega))
        (UniformRankKernelMachine.vValue p (fun i=>PowerSeries.coeff i (NewtonFourier.invH omega)))
        (UniformRankKernelMachine.wValue p (DFTModelCacheKernelNewton.gValue omega)) b j := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  rw [program_value r p omega hr]
  have hj:j.val<p.N:=by rw [width];exact j.isLt
  rw [rawValues_lookup p _ _ b ⟨j.val,hj⟩]
  rw [cellValue_source (hf:=fun i=>PowerSeries.coeff i (NewtonFourier.invH omega))
    (gf:=DFTModelCacheKernelNewton.gValue omega) shape
    (DFTModelCacheKernelNewton.h_coefficients r omega) (by
    intro i hi
    simp [DFTModelCacheKernelNewton.gValues,Tape.look,Tape.tab,hi]) b ⟨j.val,hj⟩]
  exact finalCells_rankKernels p K _ _ shape.positiveA shape.positiveE width b j

/-- Native rectangle geometry supplies the typed producer's complete entry
conditions once the two original coefficient banks have the radix length. -/
theorem shape_of_geometry (p : UniformRankKernelMachine.Parameters) (B r : ℕ)
    (geo:UniformRankKernelMachine.Geometry p B) (hh:p.hSize=r) (hg:p.gSize=r) : Shape p r := by
  refine ⟨geo.positiveA,geo.positiveE,?_,?_,geo.interior,geo.columns,geo.widthA,geo.widthE⟩
  · simpa only [hh] using geo.hRows
  · simpa only [hg] using geo.gSplit

theorem program_axis_work (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ)
    (shape:Shape p r) (widthBound:p.N≤8*r) :
    (run program (metadata r p,omega)).work≤20000*(r+1)^2 := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  have charge:=program_work r p omega hr
  have splitBound:=shape.gSplit.le
  have prod:=Nat.mul_le_mul widthBound (Nat.add_le_add_right (Nat.mul_le_mul_left 52 splitBound) 300)
  nlinarith

end
end ExactFourierCircuits.DFTModelCacheDisplacement
