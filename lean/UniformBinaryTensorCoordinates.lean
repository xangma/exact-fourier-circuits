import UniformBinaryCStageMachine
import UniformCRTTraversalCycle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBinaryTensorCoordinates
open OAI.ExactFourier UniformCRTTraversalCycle
open scoped BigOperators

/- Explicit physical bit coordinates. The upstream tensorCoordinates uses a
   chosen finite enumeration. This bridge does not pretend that enumeration
   is a runtime integer permutation; the algorithm uses the radix formulas. -/
def coordinates (k : ℕ) : Fin (2^k)≃(Fin k→Fin 2) :=
 (finCongr (by simp)).trans (decodeEquiv (fun _ : Fin k=>2) (by intro i;norm_num))

theorem binary_place (k j : ℕ) (hj : j≤k) :
 place (fun _ : Fin k=>2) j=2^j := by
 simp [place,List.ofFn_const,List.take_replicate,List.prod_replicate,Nat.min_eq_left hj]

theorem coordinates_value (k : ℕ) (z : Fin (2^k)) (i : Fin k) :
 (coordinates k z i).val=(z.val/2^i.val)%2 := by
 simp [coordinates,decodeEquiv,decodeDigits,decoded,binary_place k i.val i.isLt.le]

theorem coordinates_inverse (k : ℕ) (ds : Fin k→Fin 2) :
 ((coordinates k).symm ds).val=∑i:Fin k,2^i.val*(ds i).val := by
 simp [coordinates,decodeEquiv,encoded,binary_place k _ (Nat.le_of_lt (Fin.isLt _))]

/-- Updating one binary digit changes only its printed integer weight. -/
theorem update_balance (k : ℕ) (ds : Fin k→Fin 2) (i : Fin k) (t : Fin 2) :
 ((coordinates k).symm (Function.update ds i t)).val+2^i.val*(ds i).val=
 ((coordinates k).symm ds).val+2^i.val*t.val := by
 classical
 rw [coordinates_inverse,coordinates_inverse]
 rw [Fintype.sum_eq_add_sum_compl i,Fintype.sum_eq_add_sum_compl i]
 simp only [Finset.compl_eq_univ_sdiff]
 have same : (∑j ∈ Finset.univ \ {i},2^j.val*(Function.update ds i t j).val)=
   ∑j ∈ Finset.univ \ {i},2^j.val*(ds j).val := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.update_of_ne (by simpa using (Finset.mem_sdiff.mp hj).2)]
 rw [same,Function.update_self]
 omega

theorem update_address (k : ℕ) (z : Fin (2^k)) (i : Fin k) (t : Fin 2) :
 ((coordinates k).symm (Function.update (coordinates k z) i t)).val=
 z.val%2^i.val+2^i.val*(t.val+2*(z.val/(2^i.val*2))) := by
 have h:=update_balance k (coordinates k z) i t
 rw [Equiv.symm_apply_apply,coordinates_value] at h
 have first:=Nat.mod_add_div z.val (2^i.val)
 have second:=Nat.mod_add_div (z.val/2^i.val) 2
 rw [Nat.div_div_eq_div_mul] at second
 have split : z.val=z.val%2^i.val+2^i.val*((z.val/2^i.val)%2)+
   2^i.val*2*(z.val/(2^i.val*2)) := by
  calc
   _=z.val%2^i.val+2^i.val*(z.val/2^i.val):=first.symm
   _=z.val%2^i.val+2^i.val*((z.val/2^i.val)%2+2*(z.val/(2^i.val*2))):=by rw [second]
   _=_:=by ring
 -- Treat the quotient, remainder and old digit as integers and cancel them.
 nlinarith

theorem axis_volume (k : ℕ) (i : Fin k) :
 2^i.val*2*2^(k-(i.val+1))=2^k := by
 rw [←Nat.pow_succ,←Nat.pow_add]
 congr 1
 omega

def fiber (k : ℕ) (i : Fin k) :
 (Fin (2^i.val*2^(k-(i.val+1)))×Fin 2)≃Fin (2^k) :=
 (UniformTensorAddressMachine.fiberEquiv (2^i.val) 2 (2^(k-(i.val+1)))).trans
  (finCongr (axis_volume k i))

theorem fiber_address (k : ℕ) (i : Fin k)
 (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2) :
 (fiber k i (j,t)).val=UniformTensorAddressMachine.address (2^i.val) 2 j.val t.val := rfl

theorem address_parts (P j t : ℕ) (hp : 0<P) (ht : t<2) :
 UniformTensorAddressMachine.address P 2 j t%P=j%P ∧
 UniformTensorAddressMachine.address P 2 j t/P=t+2*(j/P) ∧
 UniformTensorAddressMachine.address P 2 j t/(P*2)=j/P := by
 unfold UniformTensorAddressMachine.address
 have hm:=Nat.mod_lt j hp
 have first:(j%P+P*(t+2*(j/P)))/P=t+2*(j/P):=by
  rw [Nat.add_mul_div_left _ _ hp]
  rw [Nat.div_eq_of_lt hm,Nat.zero_add]
 refine ⟨by simp [Nat.add_mod],first,?_⟩
 rw [←Nat.div_div_eq_div_mul,first,Nat.add_mul_div_left _ _ (by omega)]
 rw [Nat.div_eq_of_lt ht,Nat.zero_add]

theorem fiber_digit (k : ℕ) (i : Fin k)
 (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2) :
 coordinates k (fiber k i (j,t)) i=t := by
 apply Fin.ext
 rw [coordinates_value,fiber_address,(address_parts _ _ _ (by positivity) t.isLt).2.1]
 simp [Nat.add_mod,Nat.mod_eq_of_lt t.isLt]

theorem fiber_update (k : ℕ) (i : Fin k)
 (j : Fin (2^i.val*2^(k-(i.val+1)))) (t u : Fin 2) :
 (coordinates k).symm (Function.update (coordinates k (fiber k i (j,t))) i u)=
 fiber k i (j,u) := by
 apply Fin.ext
 rw [update_address,fiber_address,fiber_address]
 rw [(address_parts _ _ _ (by positivity) t.isLt).1,
  (address_parts _ _ _ (by positivity) t.isLt).2.2]
 rfl

noncomputable section

def physicalMatrix (k : ℕ) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 Matrix.reindex (coordinates k).symm (coordinates k).symm
  (PiTensor.matrix (fun _ : Fin k=>C))

theorem physicalMatrix_apply (k : ℕ) (x y : Fin (2^k)) :
 physicalMatrix k x y=∏i:Fin k,C (coordinates k x i) (coordinates k y i) := rfl

def toAbstract (k : ℕ) : Fin (2^k)≃Fin (2^k) :=
 (coordinates k).trans (tensorCoordinates 2 k).symm

/-- Reindexing cancels the paper's abstract enumeration without computing it. -/
theorem abstract_bridge (k : ℕ) :
 Matrix.reindex (toAbstract k).symm (toAbstract k).symm (tensorPower C k)=physicalMatrix k := by
 ext x y
 simp [Matrix.reindex_apply,toAbstract,tensorPower,physicalMatrix,PiTensor.matrix]

def axisMatrix (k : ℕ) (i : Fin k) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 Matrix.reindex (coordinates k).symm (coordinates k).symm
  (PiTensor.matrix (Function.update (1:Fin k→Matrix (Fin 2) (Fin 2) ℂ) i C))

theorem axisCoordinates_update (k : ℕ) (ds : Fin k→Fin 2) (i : Fin k) (t : Fin 2) :
 PiTensor.axisCoordinates i ⟨fun j=>ds j,t⟩=Function.update ds i t := by
 classical
 apply (PiTensor.axisCoordinates i).symm.injective
 rw [Equiv.symm_apply_apply,PiTensor.axisCoordinates_symm]
 congr 1
 · funext j
   simp [Function.update_of_ne j.property]
 · simp

theorem abstract_axis_mulVec (k : ℕ) (ds : Fin k→Fin 2) (i : Fin k)
 (v : (Fin k→Fin 2)→ℂ) :
 (PiTensor.matrix (Function.update (1:Fin k→Matrix (Fin 2) (Fin 2) ℂ) i C)).mulVec v ds=
 ∑t:Fin 2,C (ds i) t*v (Function.update ds i t) := by
 classical
 rw [PiTensor.axis_matrix]
 unfold Matrix.mulVec dotProduct
 change (∑d,Matrix.blockDiagonal' (fun _ : {j:Fin k // j≠i}→Fin 2=>C)
   ((PiTensor.axisCoordinates i).symm ds) ((PiTensor.axisCoordinates i).symm d)*v d)=_
 rw [Fintype.sum_equiv (PiTensor.axisCoordinates i).symm _
  (fun z=>Matrix.blockDiagonal' (fun _ : {j:Fin k // j≠i}→Fin 2=>C)
   ((PiTensor.axisCoordinates i).symm ds) z*v (PiTensor.axisCoordinates i z))
  (by intro d;simp only [Equiv.apply_symm_apply])]
 simp only [Fintype.sum_sigma,PiTensor.axisCoordinates_symm]
 rw [Fintype.sum_eq_single (fun j : {j:Fin k // j≠i}=>ds j)]
 · simp only [Matrix.blockDiagonal'_apply_eq,axisCoordinates_update]
 · intro f hf
   apply Finset.sum_eq_zero
   intro t _
   rw [Matrix.blockDiagonal'_apply_ne _ _ _ hf.symm,zero_mul]

theorem axisMatrix_mulVec (k : ℕ) (i : Fin k) (v : Fin (2^k)→ℂ) (z : Fin (2^k)) :
 (axisMatrix k i).mulVec v z=
 ∑t:Fin 2,C (coordinates k z i) t*
  v ((coordinates k).symm (Function.update (coordinates k z) i t)) := by
 classical
 rw [←abstract_axis_mulVec k (coordinates k z) i (fun ds=>v ((coordinates k).symm ds))]
 unfold Matrix.mulVec dotProduct
 unfold axisMatrix
 change (∑y,PiTensor.matrix _ (coordinates k z) (coordinates k y)*v y)=_
 exact Fintype.sum_equiv (coordinates k) _ _ (by intro y;simp)

theorem axisMatrix_fiber (k : ℕ) (i : Fin k) (v : Fin (2^k)→ℂ)
 (j : Fin (2^i.val*2^(k-(i.val+1)))) (t : Fin 2) :
 (axisMatrix k i).mulVec v (fiber k i (j,t))=
 C.mulVec (fun d=>v (fiber k i (j,d))) t := by
 rw [axisMatrix_mulVec,fiber_digit]
 simp only [fiber_update,Matrix.mulVec,dotProduct]

def axisAction (k : ℕ) (i : Fin k) (v : Fin (2^k)→UniformMachine.Scalar)
 (z : Fin (2^k)) : UniformMachine.Scalar :=
 ⟨(axisMatrix k i).mulVec (fun y=>(v y).value) z,
  (v ((coordinates k).symm (Function.update (coordinates k z) i 0))).dependent ||
  (v ((coordinates k).symm (Function.update (coordinates k z) i 1))).dependent⟩

/-- The actual integer-addressed stage realizes the abstract tensor axis,
including physical dependency flags; no permutation oracle is an input. -/
theorem axis_execution (n B k A : ℕ) (x : Fin n→ℂ) (i : Fin k)
 (v : Fin (2^k)→UniformMachine.Scalar) (s : UniformMachine.State)
 (pc : s.pc=0) (p : s.natReg 2800=2^i.val) (base : s.natReg 2801=A)
 (q : s.natReg 2802=2^(k-(i.val+1))) (a : 3≤A)
 (constants : UniformBinaryCStageMachine.Constants s)
 (data : ∀z,s.scalarHeap (A+z.val)=some (v z))
 (bound : UniformMachine.WordBound B s) (code : 30≤B) (extent : A+2^k≤B) :
 ∃u,UniformMachine.BoundedExecution UniformBinaryCStageMachine.program n x B s
  (25*(2^i.val*2^(k-(i.val+1)))+6) u ∧
  (∀z,u.scalarHeap (A+z.val)=some (axisAction k i v z)) ∧
  UniformBinaryCStageMachine.Frame A (2^k) s u ∧
  UniformBinaryCStageMachine.Constants u := by
 let fv:=fun j t=>v (fiber k i (j,t))
 have initial : ∀j t,s.scalarHeap
   (UniformBinaryCStageMachine.coordinate (2^i.val) A (2^(k-(i.val+1))) j t)=some (fv j t) := by
  intro j t
  exact data (fiber k i (j,t))
 obtain ⟨u,run,result,frame⟩:=UniformBinaryCStageMachine.execution n B x
  (2^i.val) A (2^(k-(i.val+1))) fv s pc p base q (by positivity) a constants initial bound code
  (by simpa only [axis_volume] using extent)
 refine ⟨u,run,?_,by simpa only [axis_volume] using frame,frame.constants a constants⟩
 intro z
 obtain ⟨⟨j,t⟩,rfl⟩:=(fiber k i).surjective z
 have r:=result j t
 rw [UniformBinaryCStageMachine.transformed_C] at r
 simpa only [UniformBinaryCStageMachine.coordinate,←fiber_address,axisAction,
  axisMatrix_fiber,fiber_update,fv] using r

theorem all_axes (k : ℕ) :
 ((List.finRange k).map (axisMatrix k)).prod=physicalMatrix k := by
 let upd:=fun i:Fin k=>Function.update (1:Fin k→Matrix (Fin 2) (Fin 2) ℂ) i C
 have inner:((List.finRange k).map (fun i=>PiTensor.matrix (upd i))).prod=
  PiTensor.matrix (fun _ : Fin k=>C):=by
   rw [show (List.finRange k).map (fun i=>PiTensor.matrix (upd i))=
    ((List.finRange k).map upd).map PiTensor.hom from by rw [List.map_map];rfl]
   rw [←map_list_prod]
   change PiTensor.matrix (((List.finRange k).map upd).prod)=_
   congr 1
   funext i
   rw [Embedded.list_update_prod _ _ (List.nodup_finRange k)]
   simp
 unfold axisMatrix physicalMatrix
 have hom:=congrArg (Matrix.reindex (coordinates k).symm (coordinates k).symm) inner
 simpa [axisMatrix,physicalMatrix,upd,List.map_map,Function.comp_def] using
  ((Matrix.reindexAlgEquiv ℂ ℂ (coordinates k).symm).toMonoidHom.map_list_prod
   ((List.finRange k).map (fun i=>PiTensor.matrix (upd i)))).symm.trans hom

theorem all_axes_reverse (k : ℕ) :
 (((List.finRange k).reverse).map (axisMatrix k)).prod=physicalMatrix k := by
 let upd:=fun i:Fin k=>Function.update (1:Fin k→Matrix (Fin 2) (Fin 2) ℂ) i C
 have inner:(((List.finRange k).reverse).map (fun i=>PiTensor.matrix (upd i))).prod=
  PiTensor.matrix (fun _ : Fin k=>C):=by
   rw [show ((List.finRange k).reverse).map (fun i=>PiTensor.matrix (upd i))=
    (((List.finRange k).reverse).map upd).map PiTensor.hom from by rw [List.map_map];rfl]
   rw [←map_list_prod]
   change PiTensor.matrix ((((List.finRange k).reverse).map upd).prod)=_
   congr 1
   funext i
   rw [Embedded.list_update_prod _ _ (List.nodup_reverse.mpr (List.nodup_finRange k))]
   simp
 unfold axisMatrix physicalMatrix
 have hom:=congrArg (Matrix.reindex (coordinates k).symm (coordinates k).symm) inner
 simpa [upd,List.map_map,Function.comp_def] using
  ((Matrix.reindexAlgEquiv ℂ ℂ (coordinates k).symm).toMonoidHom.map_list_prod
   (((List.finRange k).reverse).map (fun i=>PiTensor.matrix (upd i)))).symm.trans hom

def applyAxes (k : ℕ) (l : List (Fin k)) (v : Fin (2^k)→UniformMachine.Scalar) :
 Fin (2^k)→UniformMachine.Scalar := l.foldl (fun w i=>axisAction k i w) v

theorem applyAxes_values (k : ℕ) (l : List (Fin k)) (v : Fin (2^k)→UniformMachine.Scalar) :
 (fun z=>(applyAxes k l v z).value)=
 (((l.reverse).map (axisMatrix k)).prod).mulVec (fun z=>(v z).value) := by
 induction l generalizing v with
 | nil => simp [applyAxes]
 | cons i l ih =>
  change (fun z=>(applyAxes k l (axisAction k i v) z).value)=_
  rw [ih]
  simp only [axisAction,List.reverse_cons,List.map_append,List.map_singleton,List.prod_append,List.prod_singleton]
  rw [Matrix.mulVec_mulVec]

theorem applyAxes_tensor (k : ℕ) (v : Fin (2^k)→UniformMachine.Scalar) :
 (fun z=>(applyAxes k (List.finRange k) v z).value)=
 (physicalMatrix k).mulVec (fun z=>(v z).value) := by
 rw [applyAxes_values,all_axes_reverse]

end
end ExactFourierCircuits.UniformBinaryTensorCoordinates
