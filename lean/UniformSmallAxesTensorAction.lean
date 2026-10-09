import UniformNativeTensorCoordinates
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSmallAxesTensorAction
open OAI.ExactFourier
noncomputable section
open scoped BigOperators
variable {ι:Type} [Fintype ι] [DecidableEq ι]
 {D:ι→Type} [∀i,Fintype (D i)] [∀i,DecidableEq (D i)]

omit [Fintype ι] [∀i,Fintype (D i)] [∀i,DecidableEq (D i)] in
theorem axisCoordinates_update (i:ι) (d:∀i,D i) (t:D i) :
 PiTensor.axisCoordinates i ⟨fun j=>d j,t⟩=Function.update d i t := by
 funext j
 by_cases h:j=i
 · subst j;simp [PiTensor.axisCoordinates,Equiv.piSplitAt]
 · simp [PiTensor.axisCoordinates,Equiv.piSplitAt,h,Function.update_of_ne]

theorem tensor_axis_action (i:ι) (A:Matrix (D i) (D i) ℂ) (X:(∀i,D i)→ℂ) (d:∀i,D i) :
 (PiTensor.matrix (Function.update (1:∀j,Matrix (D j) (D j) ℂ) i A)).mulVec X d=
 ∑t:D i,A (d i) t*X (Function.update d i t) := by
 rw [PiTensor.axis_matrix]
 simp only [Matrix.mulVec,dotProduct,Matrix.reindex_apply,Matrix.submatrix_apply]
 rw [←(PiTensor.axisCoordinates i).sum_comp]
 simp only [Equiv.symm_apply_apply,PiTensor.axisCoordinates_symm,Fintype.sum_sigma]
 simp [Matrix.blockDiagonal'_apply,axisCoordinates_update]

open UniformInitialPreparation (ell len)
open UniformSelectedAxisFiberPreparation (radices)
open UniformCRTTraversalCycle (ordinalEquiv)
open UniformSmallAxesMachine (axisAt oneValue axisPrefix)

def lifted {n:ℕ} (X:Fin (len n)→ℂ) : (∀i:Fin (ell n+1),Fin (radices n i))→ℂ :=
 fun d=>X ((ordinalEquiv n).symm d)

def stage (n T:ℕ) (i:Fin (ell n+1)) : Matrix (Fin (radices n i)) (Fin (radices n i)) ℂ :=
 if radices n i<T then fourierMatrix (radices n i) else 1

def partialLocal (n T k:ℕ) (i:Fin (ell n+1)) : Matrix (Fin (radices n i)) (Fin (radices n i)) ℂ :=
 if i.val<k then stage n T i else 1

theorem axisTransform_action (n:ℕ) (i:Fin (ell n+1)) (X:Fin (len n)→ℂ) :
 lifted (UniformSmallAxesMachine.axisTransform i X)=
 (PiTensor.matrix (Function.update (1:∀j:Fin (ell n+1),Matrix (Fin (radices n j)) (Fin (radices n j)) ℂ)
  i (fourierMatrix (radices n i)))).mulVec (lifted X) := by
 funext d
 rw [tensor_axis_action]
 rw [lifted,UniformNativeTensorCoordinates.axisTransform_digits]
 simp only [Equiv.apply_symm_apply,fourierMatrix,lifted]

theorem oneValue_action {n i:ℕ} (hi:i<ell n+1) (T:ℕ) (X:Fin (len n)→ℂ) :
 lifted (oneValue T i X)=
 (PiTensor.matrix (Function.update (1:∀j:Fin (ell n+1),Matrix (Fin (radices n j)) (Fin (radices n j)) ℂ)
  ⟨i,hi⟩ (stage n T ⟨i,hi⟩))).mulVec (lifted X) := by
 by_cases small:radices n ⟨i,hi⟩<T
 · simp only [oneValue,UniformSmallAxesMachine.axisAt_eq hi,small,ite_true,stage]
   exact axisTransform_action n ⟨i,hi⟩ X
 · simp only [oneValue,UniformSmallAxesMachine.axisAt_eq hi,small,ite_false,stage]
   have same:Function.update (1:∀j:Fin (ell n+1),Matrix (Fin (radices n j)) (Fin (radices n j)) ℂ)
    ⟨i,hi⟩ 1=1:=Function.update_eq_self (⟨i,hi⟩:Fin (ell n+1))
     (1:∀j:Fin (ell n+1),Matrix (Fin (radices n j)) (Fin (radices n j)) ℂ)
   rw [same,PiTensor.one,Matrix.one_mulVec]

theorem partial_step {n k:ℕ} (hi:k<ell n+1) (T:ℕ) :
 partialLocal n T (k+1)=Function.update
 (1:∀j:Fin (ell n+1),Matrix (Fin (radices n j)) (Fin (radices n j)) ℂ)
 ⟨k,hi⟩ (stage n T ⟨k,hi⟩)*partialLocal n T k := by
 funext j
 by_cases eq:j=(⟨k,hi⟩:Fin (ell n+1))
 · subst j;simp [partialLocal,Function.update_self]
 · have ne:j.val≠k:=by intro h;exact eq (Fin.ext h)
   rw [Pi.mul_apply,Function.update_of_ne eq]
   change (if j.val<k+1 then stage n T j else 1)=1*(if j.val<k then stage n T j else 1)
   by_cases low:j.val<k
   · have next:j.val<k+1:=by omega
     simp only [low,next,ite_true,one_mul]
   · have next:¬j.val<k+1:=by omega
     simp only [low,next,ite_false,one_mul]

theorem prefix_action {n:ℕ} (T:ℕ) (X:Fin (len n)→ℂ) (k:ℕ) (hk:k≤ell n+1) :
 lifted (axisPrefix T X k)=(PiTensor.matrix (partialLocal n T k)).mulVec (lifted X) := by
 induction k with
 |zero=>
  have eq:partialLocal n T 0=1:=by funext i;simp [partialLocal]
  rw [eq,PiTensor.one,Matrix.one_mulVec];rfl
 |succ k ih=>
  have hi:k<ell n+1:=by omega
  rw [axisPrefix,oneValue_action hi,ih (by omega),Matrix.mulVec_mulVec,
   ←PiTensor.mul,←partial_step hi]

theorem full_action (n T:ℕ) (X:Fin (len n)→ℂ) (z:Fin (len n)) :
 axisPrefix T X (ell n+1) z=(PiTensor.matrix (stage n T)).mulVec (lifted X) (ordinalEquiv n z) := by
 have eq:partialLocal n T (ell n+1)=stage n T:=by funext i;simp [partialLocal,i.isLt]
 have action:=congrFun (prefix_action T X (ell n+1) (by omega)) (ordinalEquiv n z)
 rw [eq] at action
 simpa only [lifted,Equiv.symm_apply_apply] using action

def largeStage (n T:ℕ) (i:Fin (ell n+1)) : Matrix (Fin (radices n i)) (Fin (radices n i)) ℂ :=
 if radices n i<T then 1 else fourierMatrix (radices n i)

/-- The separately executed small axes and synchronized large axes compose to
all CRT axis Fourier matrices in the same actual ordinal coordinates. -/
theorem split_complete (n T:ℕ) :
 PiTensor.matrix (largeStage n T)*PiTensor.matrix (stage n T)=
 PiTensor.matrix (fun i:Fin (ell n+1)=>fourierMatrix (radices n i)) := by
 rw [←PiTensor.mul]
 apply congrArg PiTensor.matrix
 funext i
 by_cases h:radices n i<T <;> simp [largeStage,stage,h]

open UniformMachine
open UniformPermutationInversePreparation (Metadata)
open UniformSmallAxesMachine (RootBank Header Values runtime)

theorem runtime_linear {n:ℕ} (hn:0<n) (T:ℕ) :
 runtime n T≤(17+(T+1)*(8*T+165))*len n := by
 have count:ell n+1≤2*n:=by
  have bound:=UniformWorkingLength.firstExceed_bound n
  have pos:=UniformWorkingLength.firstExceed_pos hn
  change UniformWorkingLength.firstExceed n-1+1≤2*n
  omega
 have lower:=UniformWorkingLength.workingLength_lower n
 have lenPos:0<len n:=UniformWorkingLength.workingLength_pos hn
 have countLen:ell n+1≤len n:=by change 2*n≤len n at lower;omega
 have front:10+7*(ell n+1)≤17*len n:=by nlinarith
 have body:(8*T+96)*len n+14*ell n+55≤(8*T+165)*len n:=by nlinarith
 calc
  _≤10+7*(ell n+1)+(T+1)*((8*T+96)*len n+14*ell n+55):=
   UniformSmallAxesMachine.runtime_bound n T
  _≤17*len n+(T+1)*((8*T+165)*len n):=
   Nat.add_le_add front (Nat.mul_le_mul_left _ body)
  _=(17+(T+1)*(8*T+165))*len n:=by ring

/-- Actual182 execution with its tensor matrix conclusion; no supplied action. -/
theorem execution_tensor {n B T A G E:ℕ} (hn:0<n) (x:Fin n→ℂ) (s:State)
 (md:Metadata n s) (roots:RootBank n s) (X:Fin (len n)→ℂ) (values:Values A X s)
 (rootBefore:6+ell n<A) (sepAG:A+len n≤G) (sepGE:G+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B) (code:182≤B) (tb:T≤B)
 (pc:s.pc=0) (a:s.natReg 5102=A) (g:s.natReg 5103=G) (e:s.natReg 5104=E)
 (bound:WordBound B s) : ∃u,
 BoundedExecution (UniformSmallAxesMachine.program T) n x B s (runtime n T) u ∧
 u.pc=181 ∧Metadata n u ∧Header n T A G E (ell n+1) u ∧RootBank n u ∧
 (∀z:Fin (len n),∃v,u.scalarHeap (A+z.val)=some v ∧
  v.value=(PiTensor.matrix (stage n T)).mulVec (lifted X) (ordinalEquiv n z)) ∧
 u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 obtain ⟨u,run,up,um,uh,ur,uv,un,uo,ut⟩:=UniformSmallAxesMachine.execution hn x s md roots X values
  rootBefore sepAG sepGE aBound eBound code tb pc a g e bound
 refine ⟨u,run,up,um,uh,ur,?_,un,uo,ut⟩
 intro z
 obtain ⟨v,hv,answer⟩:=uv z
 exact ⟨v,hv,answer.trans (full_action n T X z)⟩

end
end ExactFourierCircuits.UniformSmallAxesTensorAction
