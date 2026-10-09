import UniformRecursiveLocalAllowance
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualOrientationAllowance
noncomputable section

def directionTicks (q m rest header width : ℕ) : ℕ :=
 UniformRecursiveLocalAllowance.directionTicks q m rest header+13+7*width+1

lemma direction_bound (q m rest header width : ℕ) (hq:1 ≤ q) (hm:3 ≤ m)
 (hr:rest < m) (hh:header ≤ 38) (hw:width ≤ m) :
 directionTicks q m rest header width ≤ (99*m+444)*2^(q*m+rest) := by
 have h:=UniformRecursiveLocalAllowance.direction_bound q m rest header hq hm hr hh
 have hp:1 ≤ 2^(q*m+rest):=Nat.two_pow_pos _
 have scanner:13+7*width ≤ (7*m+13)*2^(q*m+rest) := by
  have up:13+7*width ≤ 7*m+13 := by omega
  exact up.trans (Nat.le_mul_of_pos_right _ hp)
 unfold directionTicks
 nlinarith

lemma residual_record_bound (m k d data localTicks : ℕ)
 (work:localTicks ≤ (99*m+444)*2^k) :
 53+d*localTicks ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have b:=UniformRecursiveLocalAllowance.affine_reserve m d data (2^k) (99*m+444) 53 hp
  (by omega) (by omega)
 have runs:=Nat.mul_le_mul_left d work
 nlinarith

lemma padding_record_bound (m k roles data localTicks : ℕ) (hm:1 ≤ m)
 (work:localTicks ≤ (99*m+444)*2^k) :
 73+roles*(64+m*localTicks) ≤ 1000*(m+1)*(roles*m+data+1)*2^k := by
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have roles_le:roles ≤ roles*m:=Nat.le_mul_of_pos_right _ hm
 have runs:=Nat.mul_le_mul_left (roles*m) work
 have control:64*roles ≤ 64*(roles*m)*2^k:=by nlinarith
 have cap:=UniformRecursiveLocalAllowance.affine_reserve m (roles*m) data (2^k) (99*m+508) 73 hp
  (by omega) (by omega)
 nlinarith
end
end ExactFourierCircuits.UniformResidualOrientationAllowance
