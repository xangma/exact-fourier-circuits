import DFTModelSavingPeakStream
import DFTModelSavingPeakBinary
import DFTModelSavingClosedBoolean

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.large DFTModelCacheRecords.seed
  DFTModelSavingRecords.stream DFTModelSavingBinarySuffix.program UniformBatching.width
  UniformFixedNetworkScheduleMachine.baseSchedule streamCoeff

def seedPeak : ℕ := DFTModelCacheRecords.recordsPeak UniformFixedNetworkScheduleMachine.baseSchedule

def coefficientOf (s p M W : ℕ) : ℕ := s+p+M+4*W+100

def largeCoeff : ℕ := coefficientOf streamCoeff seedPeak m UniformBatching.width
attribute [local irreducible] seedPeak largeCoeff

lemma large_peak_exact (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    let z:=(run DFTModelSavingProgram.setup ((k,I),v)).val
    let a:=(run DFTModelSavingProgram.seedArgs z).val
    let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h a).val
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).peak=
      max (run DFTModelSavingProgram.setup ((k,I),v)).peak
        (max (run DFTModelSavingProgram.seedArgs z).peak
          (max (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h a).peak
            (max (run DFTModelSavingProgram.suffixArgs (z,u)).peak
              (run DFTModelSavingBinarySuffix.program
                (run DFTModelSavingProgram.suffixArgs (z,u)).val).peak))) := by
  simp only [DFTModelSavingProgram.large,Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero,max_assoc]

lemma large_peak_normalized (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    let q:=k/m
    let r:=k%m
    let rs:=(run DFTModelCacheRecords.seed q).val
    let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h (r,(rs,((k,I),v)))).val
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).peak=
      max (max m q) (max (run DFTModelCacheRecords.seed q).peak
        (max (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h (r,(rs,((k,I),v)))).peak
          (max (max m (q*m))
            (run DFTModelSavingBinarySuffix.program (q*m,u)).peak))) := by
  let q:=k/m
  let r:=k%m
  let rs:=(run DFTModelCacheRecords.seed q).val
  let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h (r,(rs,((k,I),v)))).val
  have exactPeak:=large_peak_exact h k I v
  rw [DFTModelSavingProgram.setup_run] at exactPeak
  dsimp only [Bill.val,Bill.peak] at exactPeak
  rw [DFTModelSavingCost.seedArgs_run] at exactPeak
  dsimp only [Bill.val,Bill.peak] at exactPeak
  change (Code.run DFTModelSavingProgram.large h ((k,I),v)).peak=
    max (max m q) (max (run DFTModelCacheRecords.seed q).peak
      (max (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h (r,(rs,((k,I),v)))).peak
        (max (run DFTModelSavingProgram.suffixArgs ((q,(r,((k,I),v))),u)).peak
          (run DFTModelSavingBinarySuffix.program
            (run DFTModelSavingProgram.suffixArgs ((q,(r,((k,I),v))),u)).val).peak))) at exactPeak
  rw [DFTModelSavingCost.suffixArgs_run] at exactPeak
  exact exactPeak

lemma suffix_peak_node (b k : ℕ) (I : ℂ) (node : Node.T)
    (key : node.1=(k,I)) (before : Boolean node.2) (cap : b ≤ k) :
    (run DFTModelSavingBinarySuffix.program (b,node)).peak ≤ 4*node.2.len+2*2^k+4 := by
  rcases node with ⟨⟨j,J⟩,bank⟩
  cases key
  exact suffix_peak b k I bank before cap

lemma coefficient_bounds (s p M W : ℕ) :
    s ≤ coefficientOf s p M W ∧ M+1 ≤ coefficientOf s p M W ∧
    p+1 ≤ coefficientOf s p M W ∧ 4*W+6 ≤ coefficientOf s p M W := by
  unfold coefficientOf
  omega

lemma local_numeric_bounds (A M P W k q : ℕ)
    (coefM : M+1 ≤ A) (coefSeed : P+1 ≤ A) (coefBinary : 4*W+6 ≤ A)
    (qk : q ≤ k) (qm : q*M ≤ k) :
    M ≤ A*(2^k*2^k) ∧ q ≤ A*(2^k*2^k) ∧ q*M ≤ A*(2^k*2^k) ∧
    q+P ≤ A*(2^k*2^k) ∧ 4*(W*2^k)+2*2^k+4 ≤ A*(2^k*2^k) := by
  have one : 1 ≤ 2^k*2^k:=Nat.mul_pos (Nat.two_pow_pos k) (Nat.two_pow_pos k)
  have V : 2^k ≤ 2^k*2^k:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have kB : k ≤ 2^k*2^k:=Nat.lt_two_pow_self.le.trans V
  have mB : M ≤ A*(2^k*2^k):=by
    have scaled:=Nat.mul_le_mul_left A one
    omega
  have cp:1 ≤ A:=by omega
  have qB : q ≤ A*(2^k*2^k):=
    (qk.trans kB).trans (Nat.le_mul_of_pos_left _ cp)
  have qmB : q*M ≤ A*(2^k*2^k):=
    qm.trans (kB.trans (Nat.le_mul_of_pos_left _ cp))
  have seedB : q+P ≤ A*(2^k*2^k) := by
    have boundSeed:=Nat.mul_le_mul_left P one
    have scaled:=Nat.mul_le_mul_right (2^k*2^k) coefSeed
    nlinarith
  have suffixB : 4*(W*2^k)+2*2^k+4 ≤ A*(2^k*2^k):=by
    have wV:=Nat.mul_le_mul_left (4*W+2) V
    have scaled:=Nat.mul_le_mul_right (2^k*2^k) coefBinary
    nlinarith
  exact ⟨mB,qB,qmB,seedB,suffixB⟩

lemma large_coefficients : streamCoeff ≤ largeCoeff ∧ m+1 ≤ largeCoeff ∧
    seedPeak+1 ≤ largeCoeff ∧ 4*UniformBatching.width+6 ≤ largeCoeff := by
  unfold largeCoeff
  exact coefficient_bounds streamCoeff seedPeak m UniformBatching.width

lemma large_local_bounds (k q : ℕ) (qk : q ≤ k) (qm : q*m ≤ k) :
    m ≤ largeCoeff*(2^k*2^k) ∧ q ≤ largeCoeff*(2^k*2^k) ∧
    q*m ≤ largeCoeff*(2^k*2^k) ∧ q+seedPeak ≤ largeCoeff*(2^k*2^k) ∧
    4*(UniformBatching.width*2^k)+2*2^k+4 ≤ largeCoeff*(2^k*2^k) :=
  local_numeric_bounds largeCoeff m seedPeak UniformBatching.width k q
    large_coefficients.2.1 large_coefficients.2.2.1 large_coefficients.2.2.2 qk qm

lemma seed_peak_budget (q : ℕ) : (run DFTModelCacheRecords.seed q).peak ≤ q+seedPeak := by
  unfold seedPeak
  exact DFTModelCacheRecords.seed_peak q

/-- The real large branch has a quadratic local peak and the maximum of
its complete smaller-child peaks. It internally produces its actual seed. -/
theorem large_peak (h : Handler ChildPort) (k C : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (qp : 1 ≤ k/m) (len : v.len=UniformBatching.width*2^k) (before : Boolean v)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (bank : Tape Tagged.T),bank.len=UniformBatching.width*2^(k/m)→Boolean bank→
      (h ((k/m,J),bank)).peak ≤ C) :
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).peak ≤ max C (largeCoeff*(2^k*2^k)) := by
  let q:=k/m
  let r:=k%m
  let rs:=(run DFTModelCacheRecords.seed q).val
  let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h (r,(rs,((k,I),v)))).val
  have mp : 0 < m:=by norm_num [m,ExplicitSeedBudget.m]
  have shape : k=q*m+r:=by
    dsimp only [q,r]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod k m).symm
  have rp : r < m:=Nat.mod_lt k mp
  have qm : q*m ≤ k := (Nat.le_add_right (q*m) r).trans_eq shape.symm
  have pk:=stream_peak q r k C I v h qp rp shape len before preserve children
  rw [←DFTModelCacheRecords.seed_value] at pk
  have sh:=DFTModelSavingShape.stream_preserves UniformBatching.width r rs ((k,I),v) h
  have bankLen : u.2.len=v.len:=sh.2
  have flags:Boolean u.2:=DFTModelSavingShapeBoolean.stream_boolean UniformBatching.width r rs
    ((k,I),v) h before preserve
  have suffix:=suffix_peak_node (q*m) k I u sh.1 flags qm
  have suffixLen : 4*u.2.len+2*2^k+4=4*(UniformBatching.width*2^k)+2*2^k+4 :=
    congrArg (fun L=>4*L+2*2^k+4) (bankLen.trans len)
  have suffixSized:=suffix.trans_eq suffixLen
  have exactPeak:=large_peak_normalized h k I v
  have bounds:=large_local_bounds k q (Nat.div_le_self k m) qm
  have mB:=bounds.1
  have qB:=bounds.2.1
  have qmB:=bounds.2.2.1
  have seed : (run DFTModelCacheRecords.seed q).peak ≤ largeCoeff*(2^k*2^k) :=
    (seed_peak_budget q).trans bounds.2.2.2.1
  have suffixB:=bounds.2.2.2.2
  have coefStream:=large_coefficients.1
  have streamB :
      (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
        (r,(rs,((k,I),v)))).peak ≤ max C (largeCoeff*(2^k*2^k)) :=
    pk.trans (max_le_max (le_refl C) (Nat.mul_le_mul_right (2^k*2^k) coefStream))
  have suffixFinal :
      (run DFTModelSavingBinarySuffix.program (q*m,u)).peak ≤
        max C (largeCoeff*(2^k*2^k)) :=
    suffixSized.trans (suffixB.trans (le_max_right C (largeCoeff*(2^k*2^k))))
  have total :
      max (max m q) (max (run DFTModelCacheRecords.seed q).peak
        (max (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
          (r,(rs,((k,I),v)))).peak
          (max (max m (q*m))
            (run DFTModelSavingBinarySuffix.program (q*m,u)).peak))) ≤
        max C (largeCoeff*(2^k*2^k)) :=
    max_le
      ((max_le mB qB).trans (le_max_right C (largeCoeff*(2^k*2^k))))
      (max_le (seed.trans (le_max_right C (largeCoeff*(2^k*2^k))))
        (max_le streamB
          (max_le ((max_le mB qmB).trans (le_max_right C (largeCoeff*(2^k*2^k))))
            suffixFinal)))
  exact exactPeak.le.trans total
end
end ExactFourierCircuits.DFTModelSavingPeak
