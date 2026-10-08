import UniformMatchingCoefficientValueBridge
import UniformSixCDirtyReplayMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingActionBridge
open UniformMachine OAI.ExactFourier
open UniformPackedMatchingShearMachine (pairUpdate matchingAction)
noncomputable section

/-- Numeric coordinates after inverse scatter. Tags remain governed by the
actual matching result and are deliberately not discarded in execution. -/
def unpackValues {L : ℕ} (phi : Fin L ≃ Fin L) (v : ℕ → Scalar) : Fin L → ℂ :=
 fun j => (v (phi.symm j).val).value

def pairShear {L : ℕ} (phi : Fin L ≃ Fin L) (i : ℕ)
 (hi : 2*i+1 < L) (mu : ℂ) : Shear (Fin L) :=
 ⟨phi ⟨2*i,by omega⟩,phi ⟨2*i+1,hi⟩,fun eq => by
   have same := congrArg Fin.val (phi.injective eq)
   change 2*i=2*i+1 at same
   omega,mu⟩

theorem pairUpdate_unpacked {L : ℕ} (phi : Fin L ≃ Fin L) (i : ℕ)
 (hi : 2*i+1 < L) (mu : ℂ) (v : ℕ → Scalar) :
 unpackValues phi (pairUpdate i mu v) = (pairShear phi i hi mu).act (unpackValues phi v) := by
 funext j
 by_cases left : (phi.symm j).val=2*i
 · have coord : phi.symm j = ⟨2*i,Nat.lt_trans (Nat.lt_succ_self _) hi⟩ := Fin.ext left
   have dest : j=phi ⟨2*i,Nat.lt_trans (Nat.lt_succ_self _) hi⟩ := by
    rw [←coord,phi.apply_symm_apply]
   subst j
   simp [unpackValues,pairUpdate,pairShear,Shear.act]
 · have dest : j≠phi ⟨2*i,by omega⟩ := by
    intro eq
    have same := congrArg (fun z => (phi.symm z).val) eq
    simp only [phi.symm_apply_apply] at same
    exact left same
   by_cases right : (phi.symm j).val=2*i+1
   · simp [unpackValues,pairUpdate,pairShear,Shear.act,right,dest]
   · simp [unpackValues,pairUpdate,pairShear,Shear.act,left,right,dest]

/-- Ordered physical shears derived from the actual packed pair coordinates.
No supplied action theorem or reverse scheduling is part of this definition. -/
def physicalShears {L : ℕ} (phi : Fin L ≃ Fin L) (coeff : ℕ → ℂ)
 (start : ℕ) : (fuel : ℕ) → (2*(start+fuel) ≤ L) → List (Shear (Fin L))
 | 0,_ => []
 | fuel+1,cap => pairShear phi start (by omega) (coeff start) ::
   physicalShears phi coeff (start+1) fuel (by omega)

theorem physicalShears_length {L : ℕ} (phi : Fin L ≃ Fin L) (coeff : ℕ → ℂ)
 (start fuel : ℕ) (cap : 2*(start+fuel) ≤ L) :
 (physicalShears phi coeff start fuel cap).length=fuel := by
 induction fuel generalizing start with
 | zero => rfl
 | succ fuel ih => simp [physicalShears,ih]

/-- Complete numeric matching action in the original coordinates, including
all untouched tail coordinates. The permutation is the actual packing result
when this theorem is specialized to a producer. -/
theorem matchingAction_runShears {R L : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (labels : ℕ → UniformMatchingConjugateLoadMachine.Coefficient R)
 (phi : Fin L ≃ Fin L) (start fuel : ℕ) (cap : 2*(start+fuel) ≤ L)
 (v : ℕ → Scalar) :
 unpackValues phi (matchingAction K bank labels start fuel v) =
 runShears (physicalShears phi (fun i => UniformMatchingConjugateLoadMachine.value K bank (labels i))
  start fuel cap) (unpackValues phi v) := by
 induction fuel generalizing start v with
 | zero => rfl
 | succ fuel ih =>
   rw [matchingAction,physicalShears,runShears_cons]
   rw [ih (start+1) (by omega),pairUpdate_unpacked]

/-- Forgetting finite-coordinate bounds changes neither a shear nor a whole
word on the bounded physical array. -/
def natShear {L : ℕ} (s : Shear (Fin L)) : Shear ℕ :=
 ⟨s.i.val,s.j.val,fun eq => s.hij (Fin.ext eq),s.c⟩

theorem natShear_act {L : ℕ} (s : Shear (Fin L)) (v : ℕ → ℂ) :
 (fun j : Fin L => (natShear s).act v j.val) = s.act (fun j => v j.val) := by
 funext j
 have eq : (j.val=s.i.val) ↔ j=s.i := ⟨Fin.ext,congrArg Fin.val⟩
 simp only [Shear.act,natShear,eq]

theorem natShears_run {L : ℕ} (W : List (Shear (Fin L))) (v : ℕ → ℂ) :
 (fun j : Fin L => runShears (W.map natShear) v j.val) =
 runShears W (fun j => v j.val) := by
 induction W generalizing v with
 | nil => rfl
 | cons s W ih =>
   simp only [List.map_cons,runShears_cons]
   rw [ih,natShear_act]

theorem physicalShears_ofFn {L : ℕ} (phi : Fin L ≃ Fin L) (coeff : ℕ → ℂ)
 (start fuel : ℕ) (cap : 2*(start+fuel) ≤ L) :
 physicalShears phi coeff start fuel cap = List.ofFn (fun i : Fin fuel =>
  pairShear phi (start+i.val) (by have:=i.isLt;omega) (coeff (start+i.val))) := by
 induction fuel generalizing start with
 | zero => simp [physicalShears]
 | succ fuel ih =>
   rw [physicalShears,List.ofFn_succ,ih]
   congr 1
   apply congrArg List.ofFn
   funext i
   simp only [Fin.val_succ]
   simp only [Nat.add_assoc, Nat.add_comm 1 i.val]

def actualPhi {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformMatchingPackingPreparation.Layout p B) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W)
 (degree : UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 Fin l.packing.total ≃ Fin l.packing.total :=
 UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
  l.packing (UniformMatchingPackingPreparation.axis_volume l W dom degree)

theorem actual_capacity {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformMatchingPackingPreparation.Layout p B) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W)
 (degree : UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 2*(UniformChunkMatchingPreparation.indices p W).length ≤ l.packing.total := by
 rw [l.volume]
 exact UniformMatchingAxisTableMachine.matching_capacity p.radix _
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom)

theorem actualPhi_pair {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformMatchingPackingPreparation.Layout p B) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W)
 (degree : UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i : Fin (UniformChunkMatchingPreparation.indices p W).length) (t : Fin 2) :
 (actualPhi l W dom degree ⟨2*i.val+t.val,by
   have:=actual_capacity l W dom degree;have:=i.isLt;have:=t.isLt;omega⟩).val =
 if t.val=0 then (UniformChunkMatchingPreparation.physicalEdges l.matching W dom i).left
 else (UniformChunkMatchingPreparation.physicalEdges l.matching W dom i).right := by
 let axes := [UniformChunkMatchingPreparation.axis l.matching W dom degree]
 let volume := UniformMatchingPackingPreparation.axis_volume l W dom degree
 let pos := UniformMatchingPackingPreparation.pairPosition l W dom degree i t
 have h := UniformMatchingPackingPreparation.physicalUnpacking_coordinate axes l.packing volume pos
 have packed : finCongr volume (UniformSectorPacking.packedEquiv _ pos) =
  (⟨2*i.val+t.val,by have:=actual_capacity l W dom degree;have:=i.isLt;have:=t.isLt;omega⟩ : Fin l.packing.total) := by
  apply Fin.ext
  exact UniformMatchingPackingPreparation.pair_packed_value l W dom degree i t
 rw [packed] at h
 have values := congrArg Fin.val h
 exact values.trans (UniformMatchingPackingPreparation.pair_source_value l W dom degree i t)

theorem shear_ext {ι : Type} (s t : Shear ι) (left : s.i=t.i)
 (right : s.j=t.j) (coefficient : s.c=t.c) : s=t := by
 cases s
 cases t
 cases left
 cases right
 cases coefficient
 rfl

/-- The generated packing permutation and actual selected coefficient decoder
give exactly the existing mapped physical word, in its original chronology. -/
theorem actualWord_eq {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformMatchingPackingPreparation.Layout p B) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W)
 (degree : UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (bank : Fin R → ℂ)
 (good : ∀ s ∈ W, UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K s.coefficient) :
 (physicalShears (actualPhi l W dom degree)
  (fun i => UniformMatchingConjugateLoadMachine.value p.height.K bank
    (UniformPackedMatchingShearMachine.selectedLabels p W i)) 0
  (UniformChunkMatchingPreparation.indices p W).length (by simpa only [Nat.zero_add] using actual_capacity l W dom degree)).map natShear =
 (UniformSixCDirtyReplayMachine.physicalWord l.matching W dom).map (UniformReplayPrint.ShearCode.eval bank) := by
 rw [physicalShears_ofFn,List.map_ofFn]
 simp only [UniformSixCDirtyReplayMachine.physicalWord,List.map_ofFn]
 apply congrArg List.ofFn
 funext i
 apply shear_ext
 · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
     UniformReplayPrint.ShearCode.eval,Fin.val_zero,Nat.add_zero,ite_true] using
    actualPhi_pair l W dom degree i 0
 · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
     UniformReplayPrint.ShearCode.eval,Fin.val_one,Nat.one_ne_zero,ite_false] using
    actualPhi_pair l W dom degree i 1
 · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
     UniformReplayPrint.ShearCode.eval,UniformMatchingCoefficientValueBridge.selectedReference] using
    UniformMatchingCoefficientValueBridge.selected_labels_value p.height.K bank p W good i

def originalValues {L : ℕ} (phi : Fin L ≃ Fin L) (v : ℕ → Scalar) : ℕ → ℂ :=
 fun a => if ha : a<L then unpackValues phi v ⟨a,ha⟩ else 0

theorem originalValues_restrict {L : ℕ} (phi : Fin L ≃ Fin L) (v : ℕ → Scalar) :
 (fun j : Fin L => originalValues phi v j.val)=unpackValues phi v := by
 funext j
 simp [originalValues,j.isLt]

/-- The entire packed matching loop, scattered by the producer's actual
permutation, acts as the selected physical word on every bounded coordinate. -/
theorem actual_matching_action {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformMatchingPackingPreparation.Layout p B) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W)
 (degree : UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (bank : Fin R → ℂ)
 (good : ∀ s ∈ W, UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K s.coefficient)
 (v : ℕ → Scalar) :
 unpackValues (actualPhi l W dom degree)
  (matchingAction p.height.K bank (UniformPackedMatchingShearMachine.selectedLabels p W) 0
    (UniformChunkMatchingPreparation.indices p W).length v) =
 (fun j : Fin l.packing.total => runShears
   ((UniformSixCDirtyReplayMachine.physicalWord l.matching W dom).map
     (UniformReplayPrint.ShearCode.eval bank))
   (originalValues (actualPhi l W dom degree) v) j.val) := by
 have cap : 2*(0+(UniformChunkMatchingPreparation.indices p W).length)≤l.packing.total := by
  simpa only [Nat.zero_add] using actual_capacity l W dom degree
 rw [matchingAction_runShears p.height.K bank _ _ 0 _ cap]
 rw [←actualWord_eq l W dom degree bank good,natShears_run,originalValues_restrict]

theorem inverseWord_eq {R K : ℕ}
 (c : UniformSixCInverseMatchingPreparation.Config) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.reverseEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (UniformSixCInverseMatchingPreparation.reverseEdges W))
 (hp : 2≤c.packing.total) (bank : Fin R → ℂ)
 (good : ∀ row ∈ W,UniformMatchingCoefficientValueBridge.ForwardLeaf K row.coefficient) :
 (physicalShears (UniformSixCInverseMatchingPreparation.unpacking c W hm hr hp)
  (fun i => UniformMatchingConjugateLoadMachine.value K bank
    (UniformSixCInverseMatchingPreparation.inverseLabels W i)) 0 W.length
  (by simpa only [Nat.zero_add] using (UniformMatchingAxisTableMachine.matching_capacity
    c.packing.total (UniformSixCInverseMatchingPreparation.reverseEdges W) hm hr))).map natShear =
 (UniformReplayPrint.reverseCode W).map (UniformReplayPrint.ShearCode.eval bank) := by
 rw [physicalShears_ofFn,List.map_ofFn]
 apply List.ext_getElem
 · simp [UniformReplayPrint.reverseCode]
 · intro i hi hj
   have bound : i<W.length := by simpa only [List.length_ofFn] using hi
   let z : Fin W.length := ⟨i,bound⟩
   have rev : W.length-i-1=W.length-1-i := by omega
   simp only [List.getElem_ofFn,List.getElem_map,UniformReplayPrint.reverseCode,
     List.getElem_reverse]
   apply shear_ext
   · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
       UniformReplayPrint.ShearCode.eval,UniformReplayPrint.ShearCode.inverse,
       UniformSixCInverseMatchingPreparation.reverseEdges,Fin.val_zero,Nat.add_zero,ite_true,z,rev] using
      UniformSixCInverseMatchingPreparation.unpacking_pair c W hm hr hp z 0
   · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
       UniformReplayPrint.ShearCode.eval,UniformReplayPrint.ShearCode.inverse,
       UniformSixCInverseMatchingPreparation.reverseEdges,Fin.val_one,Nat.one_ne_zero,ite_false,z,rev] using
      UniformSixCInverseMatchingPreparation.unpacking_pair c W hm hr hp z 1
   · simpa only [Function.comp_apply,natShear,pairShear,Nat.zero_add,
       UniformReplayPrint.ShearCode.eval,UniformReplayPrint.ShearCode.inverse,
       UniformReplayPrint.Coefficient.eval_negate,
       UniformSixCInverseMatchingPreparation.reverseReference,z,rev] using
      UniformSixCInverseMatchingPreparation.inverseLabels_value K bank W good z

theorem inverse_matching_action {R K : ℕ}
 (c : UniformSixCInverseMatchingPreparation.Config) (W : List (UniformReplayPrint.ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.reverseEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (UniformSixCInverseMatchingPreparation.reverseEdges W))
 (hp : 2≤c.packing.total) (bank : Fin R → ℂ)
 (good : ∀ row ∈ W,UniformMatchingCoefficientValueBridge.ForwardLeaf K row.coefficient)
 (v : Fin c.packing.total → Scalar) :
 unpackValues (UniformSixCInverseMatchingPreparation.unpacking c W hm hr hp)
  (matchingAction K bank (UniformSixCInverseMatchingPreparation.inverseLabels W) 0 W.length
    (UniformSixCInverseMatchingPreparation.packedInput c W hm hr hp v)) =
 (fun j : Fin c.packing.total => runShears
  ((UniformReplayPrint.reverseCode W).map (UniformReplayPrint.ShearCode.eval bank))
  (fun z => if hz:z<c.packing.total then (v ⟨z,hz⟩).value else 0) j.val) := by
 have cap : 2*(0+W.length)≤c.packing.total := by
  simpa only [Nat.zero_add] using UniformMatchingAxisTableMachine.matching_capacity
   c.packing.total (UniformSixCInverseMatchingPreparation.reverseEdges W) hm hr
 rw [matchingAction_runShears K bank _ _ 0 _ cap]
 rw [←inverseWord_eq c W hm hr hp bank good,natShears_run]
 congr 1
 funext j
 simp [unpackValues,UniformSixCInverseMatchingPreparation.packedInput,
  (UniformSixCInverseMatchingPreparation.unpacking c W hm hr hp).symm j |>.isLt,j.isLt]

end
end ExactFourierCircuits.UniformMatchingActionBridge
