import UniformMatchingPhaseFusion
import UniformSectorTensor
import UniformMatchingPackingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingAxisFusion
open OAI.ExactFourier UniformSectorPacking UniformGlobalMatchingScaleMachine
open UniformTensorPhaseFusion UniformMatchingPhaseFusion
noncomputable section

theorem block_chronological {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ι→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]
    (phases : List (∀i,Matrix (E i) (E i) ℂ)) :
    chronological (phases.map Matrix.blockDiagonal')=
      Matrix.blockDiagonal' (fun i=>chronological (phases.map (fun A=>A i))) := by
  induction phases with
  | nil=>
    change (1 : Matrix (Sigma E) (Sigma E) ℂ)=Matrix.blockDiagonal' (1 : ∀i,Matrix (E i) (E i) ℂ)
    exact Matrix.blockDiagonal'_one.symm
  | cons A phases ih=>
    simp only [List.map_cons,chronological,List.reverse_cons,List.prod_append,List.prod_singleton] at *
    rw [ih,←Matrix.blockDiagonal'_mul]

theorem reindex_chronological {E F : Type} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] (e : E≃F) (phases : List (Matrix E E ℂ)) :
    chronological (phases.map (Matrix.reindex e e))=Matrix.reindex e e (chronological phases) := by
  let f:Matrix E E ℂ→*Matrix F F ℂ:=(Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom
  change (phases.map f).reverse.prod=f phases.reverse.prod
  rw [←List.map_reverse,←map_list_prod]

/-- Singleton coordinates are identity through every one of the28 phases. -/
def smallMatrix (q : ℕ) (mu : ℂ) (phase : Phase) : Matrix (Fin q) (Fin q) ℂ :=
  if h:q=2 then Matrix.reindex (finCongr h.symm) (finCongr h.symm) (localMatrix mu phase) else 1
def smallResult (q : ℕ) (mu : ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  if h:q=2 then Matrix.reindex (finCongr h.symm) (finCongr h.symm) (upperShear mu) else 1

theorem smallMatrix_two (mu : ℂ) : smallMatrix 2 mu=localMatrix mu := by
  funext phase
  simp [smallMatrix]
theorem smallMatrix_other (q : ℕ) (mu : ℂ) (hq:q≠2) : smallMatrix q mu=(fun _=>1) := by
  funext phase
  simp [smallMatrix,hq]

theorem small_chronological (q : ℕ) (mu : ℂ) :
    chronological (phases.map (smallMatrix q mu))=smallResult q mu := by
  by_cases h:q=2
  · subst q
    rw [smallMatrix_two]
    simpa [smallResult] using phases_upperShear mu
  · rw [smallMatrix_other q mu h]
    simp [smallResult,h,chronological]

def blockPhase (axis : Axis) (mu : Fin axis.widths.length→ℂ) (phase : Phase) :
    Matrix (BlockPosition axis.widths) (BlockPosition axis.widths) ℂ :=
  Matrix.blockDiagonal' (fun b=>smallMatrix (axis.widths.get b) (mu b) phase)
def blockResult (axis : Axis) (mu : Fin axis.widths.length→ℂ) :
    Matrix (BlockPosition axis.widths) (BlockPosition axis.widths) ℂ :=
  Matrix.blockDiagonal' (fun b=>smallResult (axis.widths.get b) (mu b))

theorem blockPhases_result (axis : Axis) (mu : Fin axis.widths.length→ℂ) :
    chronological (phases.map (blockPhase axis mu))=blockResult axis mu := by
  have h:=block_chronological (phases.map (fun phase b=>smallMatrix (axis.widths.get b) (mu b) phase))
  simp only [List.map_map,Function.comp_def] at h
  unfold blockPhase blockResult
  rw [h]
  exact congrArg Matrix.blockDiagonal' (funext (fun b=>small_chronological (axis.widths.get b) (mu b)))

def axisCoordinates (axis : Axis) : BlockPosition axis.widths≃Fin axis.widths.sum :=
  (blockEquiv axis.widths).trans axis.originalPermutation
def nativePhase (axis : Axis) (mu : Fin axis.widths.length→ℂ) (phase : Phase) :
    Matrix (Fin axis.widths.sum) (Fin axis.widths.sum) ℂ :=
  Matrix.reindex (axisCoordinates axis) (axisCoordinates axis) (blockPhase axis mu phase)
def nativeResult (axis : Axis) (mu : Fin axis.widths.length→ℂ) :
    Matrix (Fin axis.widths.sum) (Fin axis.widths.sum) ℂ :=
  Matrix.reindex (axisCoordinates axis) (axisCoordinates axis) (blockResult axis mu)

def blockCoefficient (axis : Axis) (mu : Fin axis.widths.length→ℂ) (lane : Fin 9)
    (x : BlockPosition axis.widths) : ℂ :=
  if h:axis.widths.get x.1=2 then
    factor (mu x.1) lane (Fin.cast h x.2) else 1
def nativeCoefficient (axis : Axis) (mu : Fin axis.widths.length→ℂ) (lane : Fin 9)
    (j : Fin axis.widths.sum) : ℂ :=
  blockCoefficient axis mu lane ((axisCoordinates axis).symm j)

theorem small_diagonal (q : ℕ) (mu : ℂ) (lane : Fin 9) :
    smallMatrix q mu (.diagonal lane)=Matrix.diagonal (fun j=>
      if h:q=2 then factor mu lane (Fin.cast h j) else 1) := by
  by_cases h:q=2
  · subst q
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smallMatrix,localMatrix,ExactFourierCircuits.diagonal]
  · ext i j
    simp [smallMatrix,h,Matrix.diagonal_apply,Matrix.one_apply]
theorem block_diagonal (axis : Axis) (mu : Fin axis.widths.length→ℂ) (lane : Fin 9) :
    blockPhase axis mu (.diagonal lane)=Matrix.diagonal (blockCoefficient axis mu lane) := by
  ext x y
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  by_cases h:b=c
  · subst c
    simp only [blockPhase,Matrix.blockDiagonal'_apply',small_diagonal]
    simp [Matrix.diagonal_apply,blockCoefficient]
  · simp [blockPhase,Matrix.blockDiagonal'_apply',h,
      show (⟨b,x⟩:BlockPosition axis.widths)≠⟨c,y⟩ from by intro eq;exact h (congrArg Sigma.fst eq)]
theorem nativePhase_diagonal (axis : Axis) (mu : Fin axis.widths.length→ℂ) (lane : Fin 9) :
    nativePhase axis mu (.diagonal lane)=Matrix.diagonal (nativeCoefficient axis mu lane) := by
  rw [nativePhase,block_diagonal]
  ext i j
  simp [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply,nativeCoefficient]

open UniformMatchingAxisTableMachine UniformMatchingPackingPreparation UniformColoring

def matchingCoefficients {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (hpos:2≤r) (mu : Fin M→ℂ) (b : Fin (geometry r E hm hr hpos).widths.length) : ℂ :=
  if h:b.val<M then mu ⟨b.val,h⟩ else 0

theorem nativeCoefficient_pair {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (hpos:2≤r) (mu : Fin M→ℂ) (lane : Fin 9) (i : Fin M) (t : Fin 2) :
    nativeCoefficient (geometry r E hm hr hpos) (matchingCoefficients r E hm hr hpos mu) lane
      (axisCoordinates (geometry r E hm hr hpos) (matchingPosition r E hm hr hpos i t))=
      factor (mu i) lane t := by
  unfold nativeCoefficient
  rw [Equiv.symm_apply_apply]
  unfold blockCoefficient
  have hp:(geometry r E hm hr hpos).widths.get (matchingPosition r E hm hr hpos i t).1=2:=
    pair_width r (matching_capacity r E hm hr) i
  rw [dite_eq_left hp]
  simp [matchingPosition,matchingCoefficients,pairBlock,i.isLt]
  apply congrArg (factor (mu i) lane)
  apply Fin.ext
  rfl

theorem pair_native_value {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (hpos:2≤r) (i : Fin M) (t : Fin 2) :
    (axisCoordinates (geometry r E hm hr hpos) (matchingPosition r E hm hr hpos i t)).val=
      if t.val=0 then (E i).left else (E i).right :=
  matching_position_original r E hm hr hpos i t

theorem pairBlock_all_two {M r : ℕ} (_cap:2*M≤r) (b : Fin (widths r M).length)
    (h:(widths r M).get b=2) : b.val<M := by
  by_contra hb
  have other:(widths r M).get b=1:=by
    change (widths r M)[b.val]=1
    change (List.replicate M 2 ++ List.replicate (r-2*M) 1)[b.val]=1
    rw [List.getElem_append_right (by simp;omega)]
    simp
  omega

theorem nativeCoefficient_unused {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm:Matching E) (hr:InRange r E)
    (hpos:2≤r) (mu : Fin M→ℂ) (lane : Fin 9) (z : Fin (geometry r E hm hr hpos).widths.sum)
    (unused:z.val∉paired E) :
    nativeCoefficient (geometry r E hm hr hpos) (matchingCoefficients r E hm hr hpos mu) lane z=1 := by
  let axis:=geometry r E hm hr hpos
  let p:BlockPosition axis.widths:=(axisCoordinates axis).symm z
  change blockCoefficient axis _ lane p=1
  by_cases h:axis.widths.get p.1=2
  · have hi:p.1.val<M:=pairBlock_all_two (matching_capacity r E hm hr) p.1 h
    let i:Fin M:=⟨p.1.val,hi⟩
    let t:Fin 2:=Fin.cast h p.2
    have hp:p=matchingPosition r E hm hr hpos i t:=by
      have hb:p.1=pairBlock r (matching_capacity r E hm hr) i:=Fin.ext rfl
      apply Sigma.ext hb
      cases hb
      apply heq_of_eq
      apply Fin.ext
      rfl
    have eq:axisCoordinates axis (matchingPosition r E hm hr hpos i t)=z:=by
      rw [←hp]
      exact (axisCoordinates axis).apply_symm_apply z
    have zv:=pair_native_value r E hm hr hpos i t
    rw [eq] at zv
    apply False.elim
    apply unused
    apply (paired_mem E z.val).mpr
    refine ⟨i,?_⟩
    split_ifs at zv with ht
    · exact Or.inl zv
    · exact Or.inr zv
  · rw [blockCoefficient,dite_eq_right h]


theorem nativePhases_result (axis : Axis) (mu : Fin axis.widths.length→ℂ) :
    chronological (phases.map (nativePhase axis mu))=nativeResult axis mu := by
  have h:=reindex_chronological (axisCoordinates axis) (phases.map (blockPhase axis mu))
  unfold nativePhase nativeResult
  simpa only [List.map_map,Function.comp_def,blockPhases_result] using h

theorem small_kernel_entry (q : ℕ) (hq:q=1 ∨ q=2) (mu : ℂ) (i j : Fin q) :
    smallMatrix q mu .kernel i j=UniformSectorTensor.blockEntry q i.val j.val := by
  rcases hq with h|h
  · subst q
    fin_cases i;fin_cases j
    simp [smallMatrix,UniformSectorTensor.blockEntry]
  · subst q
    fin_cases i <;> fin_cases j <;>
      simp [smallMatrix,localMatrix,UniformSectorTensor.blockEntry,C]

/-- The kernel slot is exactly the original width-one/two local operator,
using the actual ordered matching table. -/
theorem block_kernel_entry (axis : Axis) (mu : Fin axis.widths.length→ℂ)
    (x y : BlockPosition axis.widths) :
    blockPhase axis mu .kernel x y=UniformSectorTensor.localEntry axis x y := by
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  by_cases h:b=c
  · subst c
    simp only [blockPhase,Matrix.blockDiagonal'_apply',UniformSectorTensor.localEntry]
    exact small_kernel_entry (axis.widths.get b)
      (axis.widths_one_two _ (List.get_mem _ _)) (mu b) x y
  · simp [blockPhase,Matrix.blockDiagonal'_apply',UniformSectorTensor.localEntry,h]

/-- All axes, their real native permutations, all matched pairs and all unused
singleton coordinates participate in the same28 synchronized phases. -/
theorem native_simultaneous {ι : Type} [Fintype ι] [DecidableEq ι]
    (axes : ι→Axis) (mu : ∀i,Fin (axes i).widths.length→ℂ) :
    chronological (phases.map (fun phase=>PiTensor.matrix (fun i=>nativePhase (axes i) (mu i) phase)))=
      PiTensor.matrix (fun i=>nativeResult (axes i) (mu i)) := by
  have h:=tensor_chronological_congr (D:=fun i=>Fin (axes i).widths.sum)
    (phases.map (fun phase i=>nativePhase (axes i) (mu i) phase)) (fun i=>nativeResult (axes i) (mu i))
    (by intro i;simpa only [List.map_map,Function.comp_def] using nativePhases_result (axes i) (mu i))
  simpa only [List.map_map,Function.comp_def] using h

end
end ExactFourierCircuits.UniformMatchingAxisFusion
