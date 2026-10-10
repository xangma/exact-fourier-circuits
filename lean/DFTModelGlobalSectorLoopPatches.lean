import DFTModelGlobalSectorLoopExecution
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorLoop
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.program

lemma roles_positive : 1≤W := by
 change 1≤UniformBatching.width
 rw[UniformBatching.width_eq_pow]
 exact Nat.two_pow_pos _

/-- Actual tagged patches, including presence and dependency flags, at every
sector address after the original whole child loop. -/
theorem Result.patch_cells {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace)
 (i : ℕ) (hi : i<xs.length) (r : Fin W) (j : Fin (2^(xs[i]'hi).pairs)) :
 ∃a a0,u.scalarHeap (A+W*(xs[i]'hi).start+r.val*2^(xs[i]'hi).pairs+j.val)=some a ∧
 u0.scalarHeap (A+W*(xs[i]'hi).start+r.val*2^(xs[i]'hi).pairs+j.val)=some a0 ∧
 (patch v v0 (xs[i]'hi)).look (r.val*2^(xs[i]'hi).pairs+j.val) Tagged.blank=encodePaired a a0 := by
 obtain ⟨out,out0,data,data0,value⟩:=h.completed i hi hi
 refine ⟨out r j,out0 r j,data r j,data0 r j,?_⟩
 rw[value,paired_lookup]

lemma patch_valid (v v0 : ℕ→ℕ→Scalar) (st : UniformSectorPacking.BlockState) :
 (run DFTModelSavingProgram.program ((st.pairs,Complex.I),paired (input v st) (input v0 st))).valid :=
 DFTModelSavingValidity.program_valid _ _ _

lemma patch_peak (v v0 : ℕ→ℕ→Scalar) (st : UniformSectorPacking.BlockState) :
 (run DFTModelSavingProgram.program ((st.pairs,Complex.I),paired (input v st) (input v0 st))).peak≤
 DFTModelSavingPeak.wholeCoeff*(2^st.pairs*2^st.pairs) :=
 DFTModelSavingPeak.program_peak_bound _ _ _ rfl (DFTModelGlobalSectorSaving.paired_boolean _ _)

def Encoded (V : ℕ) (bank : Tape Tagged.T) (v v0 : ℕ→ℕ→Scalar) : Prop :=
 ∀r,r<W→∀j,j<V→bank.look (r*V+j) Tagged.blank=encodePaired (v r j) (v0 r j)
def gatherTicks (st : UniformSectorPacking.BlockState) : ℕ := W*(7*2^st.pairs+12)+17
def savingBill (V : ℕ) (bank : Tape Tagged.T) (st : UniformSectorPacking.BlockState) : ℕ :=
 (run DFTModelSectorTranspose.saving ((st.pairs,Complex.I),((W,(V,st.start)),bank))).work

lemma gathered_eq {V : ℕ} (bank : Tape Tagged.T) (v v0 : ℕ→ℕ→Scalar)
 (st : UniformSectorPacking.BlockState) (encoded : Encoded V bank v v0) (fit : st.start+2^st.pairs≤V) :
 DFTModelSectorTranspose.gathered W V st.start (2^st.pairs) bank Tagged.blank=
 paired (input v st) (input v0 st) := by
 apply DFTModelGlobalSectorSaving.gathered_paired
 intro r j
 simpa only[Nat.add_assoc,input] using encoded r.val r.isLt (st.start+j.val) (by have:=j.isLt;omega)

/-- The actual typed sector caller's compact returned patch is the exact
patch retained by the paired source-loop invariant. -/
theorem saving_patch {V : ℕ} (bank : Tape Tagged.T) (v v0 : ℕ→ℕ→Scalar)
 (st : UniformSectorPacking.BlockState) (encoded : Encoded V bank v v0) (fit : st.start+2^st.pairs≤V) :
 (run DFTModelSectorTranspose.saving ((st.pairs,Complex.I),((W,(V,st.start)),bank))).val.2=
 patch v v0 st := by
 rw[DFTModelSectorTranspose.saving_value,gathered_eq bank v v0 st encoded fit]
 rfl

lemma saving_bill_eq {V : ℕ} (bank : Tape Tagged.T) (v v0 : ℕ→ℕ→Scalar)
 (st : UniformSectorPacking.BlockState) (encoded : Encoded V bank v v0) (fit : st.start+2^st.pairs≤V) :
 savingBill V bank st=61*(W*2^st.pairs)+8*st.pairs+74+bill v v0 st := by
 unfold savingBill
 rw[DFTModelSectorTranspose.saving_work,gathered_eq bank v v0 st encoded fit]
 rfl

lemma overhead_bound (st : UniformSectorPacking.BlockState) :
 61*(W*2^st.pairs)+8*st.pairs+74≤11*gatherTicks st := by
 have q : st.pairs≤2^st.pairs:=Nat.le_of_lt st.pairs.lt_two_pow_self
 have width : 2^st.pairs≤W*2^st.pairs:=Nat.le_mul_of_pos_left _ roles_positive
 unfold gatherTicks
 nlinarith

lemma saving_sum {V : ℕ} (bank : Tape Tagged.T) (v v0 : ℕ→ℕ→Scalar)
 (xs : List UniformSectorPacking.BlockState) (encoded : Encoded V bank v v0)
 (fits : ∀st∈xs,st.start+2^st.pairs≤V) :
 (xs.map (savingBill V bank)).sum≤11*(xs.map gatherTicks).sum+(xs.map (bill v v0)).sum := by
 induction xs with
 | nil=>simp
 | cons st xs ih=>
   have first:=saving_bill_eq bank v v0 st encoded (fits st (by simp))
   have later:=ih (fun q hq=>fits q (by simp[hq]))
   have overhead:=overhead_bound st
   simp only[List.map_cons,List.sum_cons]
   omega

/-- SAME actual native loop ticks; the typed caller additionally charges its
sector gather/argument construction once. All original gathers precede the
loop, so these gather ticks are summed separately, without per-child scatter. -/
theorem Result.saving_work {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace)
 (bank : Tape Tagged.T) (encoded : Encoded volume bank v v0)
 (fits : ∀st∈xs,st.start+2^st.pairs≤volume) :
 (xs.map (savingBill volume bank)).sum≤(K+11)*((xs.map gatherTicks).sum+ticks) := by
 have source:=h.work_native
 have total:=saving_sum bank v v0 xs encoded fits
 calc
  _ ≤ 11*(xs.map gatherTicks).sum+K*ticks:=total.trans (Nat.add_le_add_left source _)
  _ ≤ _ := by rw[Nat.add_mul,Nat.mul_add,Nat.mul_add];omega

/-- Pointwise ABI for a typed sector tab: its returned compact patch is linked
by the same sector index to exact cells of the completed actual paired run. -/
theorem Result.saving_cells {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace)
 (bank : Tape Tagged.T) (encoded : Encoded volume bank v v0)
 (fits : ∀st∈xs,st.start+2^st.pairs≤volume)
 (i : ℕ) (hi : i<xs.length) (r : Fin W) (j : Fin (2^(xs[i]'hi).pairs)) :
 ∃a a0,u.scalarHeap (A+W*(xs[i]'hi).start+r.val*2^(xs[i]'hi).pairs+j.val)=some a ∧
 u0.scalarHeap (A+W*(xs[i]'hi).start+r.val*2^(xs[i]'hi).pairs+j.val)=some a0 ∧
 (run DFTModelSectorTranspose.saving
  (((xs[i]'hi).pairs,Complex.I),((W,(volume,(xs[i]'hi).start)),bank))).val.2.look
  (r.val*2^(xs[i]'hi).pairs+j.val) Tagged.blank=encodePaired a a0 := by
 rw[saving_patch bank v v0 (xs[i]'hi) encoded (fits _ (List.getElem_mem hi))]
 exact h.patch_cells i hi r j

end
end ExactFourierCircuits.DFTModelGlobalSectorLoop
