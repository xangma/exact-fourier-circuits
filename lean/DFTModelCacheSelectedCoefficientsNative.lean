import DFTModelCacheSelectedCoefficientsCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] program constants decode cell setup finish

/-- An actual produced bank, paired in native shared-bank order. -/
def PairSource {R : ℕ} (b : Tape (ℂ × ℂ)) (bank : Fin R→ℂ) : Prop :=
  DFTModelCacheMatchingFactors.CoefficientSource b bank

/-- The only address assumptions are ordinary disjoint placement. A finite
native label supplies the in-range index before truncated subtraction. -/
theorem decode_native {R : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (bank : Fin R→ℂ)
    (source:PairSource b bank) (positive:C+R≤T) (negative:T+R≤P) (c:UniformMatchingConjugateLoadMachine.Coefficient R) :
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P c) b (constantValues K))).val=
      (UniformMatchingConjugateLoadMachine.value K bank c,starRingEnd ℂ (UniformMatchingConjugateLoadMachine.value K bank c)) ∧
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P c) b (constantValues K))).valid ∧
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P c) b (constantValues K))).work≤59 ∧
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P c) b (constantValues K))).peak≤ max R 6 := by
  cases c with
  | positive i =>
    simp only [UniformMatchingConjugateLoadMachine.address]
    rw [decode_positive _ _ _ _ _ _ (by have :=i.isLt;omega)]
    simp only [Nat.add_sub_cancel_left,source.2 i,UniformMatchingConjugateLoadMachine.value]
    refine ⟨trivial,trivial,by omega,?_⟩
    have :=i.isLt
    omega
  | negative i =>
    simp only [UniformMatchingConjugateLoadMachine.address]
    rw [decode_negative _ _ _ _ _ _ (by omega) (by have :=i.isLt;omega)]
    simp only [Nat.add_sub_cancel_left,source.2 i,UniformMatchingConjugateLoadMachine.value,map_neg]
    refine ⟨trivial,trivial,by omega,?_⟩
    have :=i.isLt
    omega
  | constant i =>
    simp only [UniformMatchingConjugateLoadMachine.address]
    rw [decode_constant _ _ _ _ _ _ (by omega) (by omega)]
    have same:starRingEnd ℂ (UniformReplayCoefficientMachine.constant K i.val)=
      UniformReplayCoefficientMachine.constant K i.val:=UniformMatchingConjugateLoadMachine.constant_conjugate K i
    simp only [Nat.add_sub_cancel_left,UniformMatchingConjugateLoadMachine.value,same]
    have look:(constantValues K).look i.val 0=UniformReplayCoefficientMachine.constant K i.val := by
      rw [Tape.look_of_lt _ _ (show i.val<(constantValues K).len from i.isLt)]
      rfl
    rw [look]
    refine ⟨rfl,trivial,by omega,?_⟩
    have :=i.isLt
    omega

theorem decode_forward {R : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (bank : Fin R→ℂ)
    (source:PairSource b bank) (positive:C+R≤T) (negative:T+R≤P)
    (c:UniformReplayPrint.Coefficient R) (leaf:UniformMatchingCoefficientValueBridge.ForwardLeaf K c) :
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P (UniformMatchingConjugateLoadMachine.fromReference c)) b (constantValues K))).val=
      (c.eval bank,starRingEnd ℂ (c.eval bank)) := by
  rw [(decode_native K C T P b bank source positive negative (UniformMatchingConjugateLoadMachine.fromReference c)).1,
    UniformMatchingCoefficientValueBridge.forward_value K bank c leaf]

theorem decode_inverse {R : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (bank : Fin R→ℂ)
    (source:PairSource b bank) (positive:C+R≤T) (negative:T+R≤P)
    (c:UniformReplayPrint.Coefficient R) (leaf:UniformMatchingCoefficientValueBridge.ForwardLeaf K c) :
    (run decode (argument C T P (UniformMatchingConjugateLoadMachine.address C T P (UniformMatchingCoefficientValueBridge.inverseReference c)) b (constantValues K))).val=
      (c.negate.eval bank,starRingEnd ℂ (c.negate.eval bank)) := by
  rw [(decode_native K C T P b bank source positive negative (UniformMatchingCoefficientValueBridge.inverseReference c)).1,
    UniformMatchingCoefficientValueBridge.inverse_value K bank c leaf]

/-- The signed normalization route is P+3 at nontrivial width and P+1 at K=0. -/
theorem inverse_normalization_address {R : ℕ} (K C T P : ℕ) :
    UniformMatchingConjugateLoadMachine.address C T P (UniformMatchingCoefficientValueBridge.inverseReference (R:=R)
      (.rational ((UniformRadixTwoDAG.width K:ℚ)⁻¹)))=
      if UniformRadixTwoDAG.width K=1 then P+1 else P+3 :=
  UniformMatchingCoefficientValueBridge.inverse_reciprocal_address K C T P

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
