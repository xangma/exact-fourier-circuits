import UniformLocalFourierWord
import UniformNetworkCost
import UniformSelectedCRT

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCommonSlots
open OAI.ExactFourier
noncomputable section

/- This enlarges the reserved count envelope to the actual proved local-word
depth constant. It does not assert that an operational network realizes it. -/
def scale : ℕ := UniformLocalFourierWord.depthUnit
def slotCount (n : ℕ) : ℕ := scale*UniformNetworkCost.slotCount n
def workingCount (d n : ℕ) : ℕ := scale*UniformNetworkCost.workingCount d n

theorem scale_pos : 0<scale := by decide

theorem radix_lt_twice_nextPrime {n : ℕ} (hn:0<n)
    (i : Fin (UniformWorkingLength.axisCount n+1)) :
    UniformSelectedCRT.radices n i<2*UniformWorkingLength.nextPrime n := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa [UniformSelectedCRT.radices] using UniformWorkingLength.binaryFactor_upper hn
  · simp only [UniformSelectedCRT.radices,Fin.snoc_castSucc]
    have h:=UniformWorkingLength.oddPrime_strictMono j.isLt
    have hq:=UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
    change UniformWorkingLength.oddPrime j.val<UniformWorkingLength.nextPrime n at h
    change UniformWorkingLength.axisCount n+3≤UniformWorkingLength.nextPrime n at hq
    omega

theorem clog_radix_bound {n : ℕ} (hn:0<n)
    (i : Fin (UniformWorkingLength.axisCount n+1)) :
    Nat.clog 2 (UniformSelectedCRT.radices n i)≤
      Nat.clog 2 (UniformWorkingLength.nextPrime n)+1 := by
  have hr:=radix_lt_twice_nextPrime hn i
  have hq:=Nat.le_pow_clog (by decide : 1<2) (UniformWorkingLength.nextPrime n)
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  rw [pow_succ]
  omega

theorem localSlots_bound {n : ℕ} (hn:0<n)
    (i : Fin (UniformWorkingLength.axisCount n+1)) :
    UniformLocalFourierWord.sufficientSlots (UniformSelectedCRT.radices n i)≤ slotCount n := by
  have hl:=clog_radix_bound hn i
  have hbase:Nat.clog 2 (UniformSelectedCRT.radices n i)+1≤
      2*(Nat.clog 2 (UniformWorkingLength.nextPrime n)+1):=by omega
  have hp:=Nat.pow_le_pow_left hbase 4
  rw [mul_pow] at hp
  norm_num only [Nat.reducePow] at hp
  have hm:=Nat.mul_le_mul_left UniformLocalFourierWord.depthUnit hp
  have ht:=UniformLocalFourierWord.sufficientSlots_bound (UniformSelectedCRT.radices n i)
  have hunit:16≤64:=by decide
  have hmajor:=Nat.mul_le_mul_right
    (UniformLocalFourierWord.depthUnit*(Nat.clog 2 (UniformWorkingLength.nextPrime n)+1)^4) hunit
  unfold slotCount scale UniformNetworkCost.slotCount
  nlinarith

theorem local_word_depth {n : ℕ} (hn:0<n)
    (i : Fin (UniformWorkingLength.axisCount n+1)) {omega : ℂ}
    (hroot:IsPrimitiveRoot omega (UniformSelectedCRT.radices n i)) :
    Layered (wordMatrix (UniformLocalFourierWord.word (UniformSelectedCRT.radix_pos n i) hroot))
      (slotCount n) :=
  (UniformLocalFourierWord.word_depth (UniformSelectedCRT.radix_pos n i) hroot).weaken
    (localSlots_bound hn i)

theorem prepared_local_word_depth {n a : ℕ} (hn:0<n)
    (i : Fin (UniformWorkingLength.axisCount n+1)) {omega : ℂ}
    (hroot:IsPrimitiveRoot omega (UniformSelectedCRT.radices n i)) (s : UniformMachine.State)
    (hp:UniformNewtonTableMachine.PreparedOutputs (UniformSelectedCRT.radices n i) omega a s) :
    Layered (wordMatrix (UniformLocalFourierWord.preparedWord
      (UniformSelectedCRT.radix_pos n i) hroot s hp)) (slotCount n) :=
  (UniformLocalFourierWord.preparedWord_depth (UniformSelectedCRT.radix_pos n i) hroot s hp).weaken
    (localSlots_bound hn i)

theorem slotCount_bound (n : ℕ) :
    (slotCount n:ℝ)≤(scale:ℝ)*(64*8^4:ℕ)*UniformNetworkCost.logFactor n^4 := by
  have h:=mul_le_mul_of_nonneg_left (UniformNetworkCost.slotCount_bound n) (Nat.cast_nonneg scale)
  simpa only [slotCount,Nat.cast_mul,mul_assoc] using h

theorem workingCount_isBigO_paper (d : ℕ) :
    (fun n : ℕ => (workingCount d n:ℝ)) =O[Filter.atTop]
      UniformMachine.asymptoticCost UniformExponent.theta := by
  simpa only [workingCount,Nat.cast_mul] using
    (UniformNetworkCost.workingCount_isBigO_paper d).const_mul_left (scale:ℝ)

theorem workingCount_isLittleO_decimal (d : ℕ) :
    (fun n : ℕ => (workingCount d n:ℝ)) =o[Filter.atTop] UniformAsymptotics.decimalCost := by
  simpa only [workingCount,Nat.cast_mul] using
    (UniformNetworkCost.workingCount_isLittleO_decimal d).const_mul_left (scale:ℝ)

end
end ExactFourierCircuits.UniformCommonSlots
