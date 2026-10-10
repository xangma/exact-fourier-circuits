import DFTModelCacheMatchingFactorsScatter
import DFTModelCacheMatchingFactorsBounds
import UniformMatchingPackingPreparation

set_option autoImplicit false

/-! Exact physical-coordinate correspondence. Raw input tapes must be outputs
of the actual matching/coefficient producers, represented by explicit source
predicates. This module does not supply an uncharged selector or permutation. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
open UniformGlobalMatchingScaleBankBridge
noncomputable section
attribute [local irreducible] program scalar

def PermutationSource {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm : Matching E)
    (hr : InRange r E) (p : Tape ℕ) : Prop :=
  p.len=r ∧ ∀j:Fin r,p.look j.val 0=(originalPermutation r E hm hr j).val

def CoefficientSource {M : ℕ} (z : Tape (ℂ × ℂ)) (mu : Fin M→ℂ) : Prop :=
  z.len=M ∧ ∀i:Fin M,z.look i.val (0,0)=(mu i,starRingEnd ℂ (mu i))

theorem coefficients_paired {M : ℕ} (z : Tape (ℂ × ℂ)) (mu : Fin M→ℂ)
    (source : CoefficientSource z mu) : Paired z := by
  intro j hj
  let i:Fin M:=⟨j,by rw [←source.1];exact hj⟩
  rw [show j=i.val from rfl,source.2 i]

/-- Pair ordinal2i+t is exactly the original matching endpoint. -/
theorem pair_original {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm : Matching E)
    (hr : InRange r E) (i : Fin M) (t : Fin 2) :
    (originalPermutation r E hm hr
      ⟨2*i.val+t.val,by have :=matching_capacity r E hm hr;omega⟩).val=
      if t.val=0 then (E i).left else (E i).right := by
  apply Option.some.inj
  change some ((ordered r E)[2*i.val+t.val]'_)=_
  rw [←List.getElem?_eq_getElem]
  fin_cases t
  · exact UniformMatchingPackingPreparation.ordered_left r E i
  · exact UniformMatchingPackingPreparation.ordered_right r E i

theorem packed_index (r : ℕ) (positive : 0<r) (l : Fin 9) (j : Fin r) :
    (l.val*r+j.val)/r=l.val ∧ (l.val*r+j.val)%r=j.val := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt j.isLt,
    Nat.zero_add,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  exact ⟨rfl,rfl⟩

theorem packed_native {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm : Matching E)
    (hr : InRange r E) (positive : 0<r) (z : Tape (ℂ × ℂ)) (mu : Fin M→ℂ)
    (source : CoefficientSource z mu) (l : Fin 9) (j : Fin r) :
    packedValue r z Complex.I ExactFourierCircuits.a⁻¹ (l.val*r+j.val)=
      nativeFactor E mu l (originalPermutation r E hm hr j).val := by
  have indices:=packed_index r positive l j
  unfold packedValue
  rw [indices.2,source.1]
  by_cases hit:j.val/2<M
  · rw [ite_eq_left hit]
    let i:Fin M:=⟨j.val/2,hit⟩
    let t:Fin 2:=⟨j.val%2,Nat.mod_lt _ (by decide)⟩
    have ordinal:2*i.val+t.val=j.val:=by
      simpa only [i,t,Nat.mul_comm] using Nat.div_add_mod j.val 2
    have endpoint:(originalPermutation r E hm hr j).val=
        if t.val=0 then (E i).left else (E i).right := by
      have pp:=pair_original r E hm hr i t
      have eq:(⟨2*i.val+t.val,by have :=matching_capacity r E hm hr;omega⟩:Fin r)=j:=Fin.ext ordinal
      simpa only [eq] using pp
    have argument:pairArgs r z Complex.I ExactFourierCircuits.a⁻¹ (l.val*r+j.val)=input l t (mu i) := by
      simp only [pairArgs,input,indices.1,indices.2]
      exact congrArg (fun c=>((l.val,t.val),(c,(Complex.I,ExactFourierCircuits.a⁻¹)))) (source.2 i)
    rw [argument,(scalar_correct l t (mu i)).1,endpoint]
    by_cases zero:t.val=0
    · have equal:t=0:=Fin.ext zero
      rw [equal]
      exact (nativeFactor_left E mu hm l i).symm
    · have equal:t=1:=Fin.ext (by have :=t.isLt;omega)
      rw [equal]
      exact (nativeFactor_right E mu hm l i).symm
  · rw [ite_eq_right hit]
    apply (nativeFactor_unused E mu l _ ?_).symm
    intro i incident
    rcases incident with left|right
    · let a:Fin r:=⟨2*i.val,by have :=matching_capacity r E hm hr;omega⟩
      have eq:(originalPermutation r E hm hr j)=(originalPermutation r E hm hr a):=by
        apply Fin.ext
        exact left.symm.trans (by simpa only [Fin.val_zero,ite_true,Nat.add_zero] using (pair_original r E hm hr i 0).symm)
      have equal:j=a:=(originalPermutation r E hm hr).injective eq
      have small:j.val/2<M:=by
        rw [equal]
        change 2*i.val/2<M
        simp
      exact hit small
    · let a:Fin r:=⟨2*i.val+1,by have :=matching_capacity r E hm hr;omega⟩
      have eq:(originalPermutation r E hm hr j)=(originalPermutation r E hm hr a):=by
        apply Fin.ext
        exact right.symm.trans (by simpa using (pair_original r E hm hr i 1).symm)
      have equal:j=a:=(originalPermutation r E hm hr).injective eq
      have small:j.val/2<M:=by
        rw [equal]
        change (2*i.val+1)/2<M
        omega
      exact hit small

/-- Every physical cell, including every unused singleton, agrees with the
actual native nine-lane formula. Metadata is explicit produced input. -/
theorem produces_native {M : ℕ} (r : ℕ) (E : Fin M→Edge) (hm : Matching E)
    (hr : InRange r E) (radix : 2≤r) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (mu : Fin M→ℂ)
    (permutation : PermutationSource r E hm hr p) (coefficients : CoefficientSource z mu) :
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).valid ∧
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).work≤2781*r+13 ∧
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).peak≤9*r ∧
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).val.len=9*r ∧
    ∀l:Fin 9,∀d:Fin r,
      (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).val.look (l.val*r+d.val) 0=
        nativeFactor E mu l d.val := by
  have count:z.len≤r:=by rw [coefficients.1];have :=matching_capacity r E hm hr;omega
  have bound:=program_bounds r p z radix count (coefficients_paired z mu coefficients)
    (fun a ha=>by
      have eq:=permutation.2 (⟨a,ha⟩:Fin r)
      exact eq ▸ (originalPermutation r E hm hr ⟨a,ha⟩).isLt)
  refine ⟨bound.1,bound.2.1,bound.2.2,program_length _ _ _ _ _,?_⟩
  intro l d
  let phi:=originalPermutation r E hm hr
  have observed:=at_packed phi p permutation.2 z Complex.I ExactFourierCircuits.a⁻¹ l (phi.symm d)
  rw [phi.apply_symm_apply] at observed
  exact observed.trans (by simpa only [phi,Equiv.apply_symm_apply] using
    (packed_native r E hm hr (by omega) z mu coefficients l (phi.symm d)))

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors
