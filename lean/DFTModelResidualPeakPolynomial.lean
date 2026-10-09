import DFTModelResidualClosedExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualPeakPolynomial
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- In the real block/spectator geometry, every generated Nat is bounded by
a fixed polynomial in the native bank volume. No exponent is evaluated here. -/
theorem budget_bound (q m r:ℕ) (qp:1 ≤ q) (mp:1 ≤ m) (rp:r < m) :
    DFTModelResidualClosedPeak.budget q m r ≤ 40*(2^(q*m+r)*2^(q*m+r)) := by
  let k:=q*m+r
  let V:=2^k
  have km:m ≤ k:=by dsimp [k];nlinarith
  have kq:q ≤ k:=by dsimp [k];nlinarith
  have kr:r ≤ k:=by dsimp [k];omega
  have kv:k ≤ V:=Nat.le_of_lt k.lt_two_pow_self
  have vp:1 ≤ V:=Nat.two_pow_pos k
  have pm:2^m ≤ V:=Nat.pow_le_pow_right (by decide) km
  have pq:2^q ≤ V:=Nat.pow_le_pow_right (by decide) kq
  have qmr:q*(m+r) ≤ k+k := by
    have mul:=Nat.mul_le_mul_left q rp.le
    dsimp [k]
    nlinarith
  have pqr:2^(q*(m+r)) ≤ V*V := by
    calc
      _ ≤ 2^(k+k):=Nat.pow_le_pow_right (by decide) qmr
      _=V*V:=by rw [pow_add]
  have square:2^q*2^q ≤ V*V:=Nat.mul_le_mul pq pq
  have product:k*(m+2) ≤ V*(V+2):=Nat.mul_le_mul kv (by omega)
  unfold DFTModelResidualClosedPeak.budget
  change (2^m+m+2)+(V+k*(m+2)+2*m+2)+(2^q*2^q+2^q+2)+
    (k+m+r+2^q+2)+(2^(q*(m+r))+2^q*2^q+(m+r)+V+2) ≤ 40*(V*V)
  nlinarith

theorem source_peak (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1))) (raw:Tape ℕ)
    (qp:1 ≤ q) (rp:r < w+1)
    (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).peak ≤
      40*(2^(q*(w+1)+r)*2^(q*(w+1)+r)) :=
  (DFTModelResidualClosedExecution.source_bounds q w r v raw qp source nonzero).2.1.trans
    (budget_bound q (w+1) r qp (by omega) rp)

end
end ExactFourierCircuits.DFTModelResidualPeakPolynomial
