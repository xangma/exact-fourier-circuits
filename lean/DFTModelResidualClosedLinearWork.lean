import DFTModelResidualClosedRoleBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedLinearWork
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem square_le_twice_pow (k:ℕ) : k*k ≤ 2*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases small:k<3
    · interval_cases k <;> decide
    · have large:3 ≤ k:=by omega
      rw [pow_succ]
      nlinarith


/-- After the once-per-node q-XOR materialization, charged address production
and movement are linear in native volume with fixed block/spectator widths. -/
theorem budget_linear (q m r:ℕ) (qp:1 ≤ q) (mp:1 ≤ m) :
    DFTModelResidualClosedBounds.budget q m r ≤
      (300*m+240*r+651)*2^(q*m+r)+(86*q+36)*(2^q*2^q) := by
  let k:=q*m+r
  let V:=2^k
  have qk:q ≤ k:=by dsimp [k];nlinarith
  have kv:k ≤ V:=Nat.le_of_lt k.lt_two_pow_self
  have vp:1 ≤ V:=Nat.two_pow_pos k
  have square:=square_le_twice_pow k
  change k*k ≤ 2*V at square
  have qV:q ≤ V:=qk.trans kv
  have metadata:(8*k+204)*k ≤ 220*V:=by nlinarith
  have mV:m ≤ m*V:=by nlinarith
  unfold DFTModelResidualClosedBounds.budget
  change 60*m+(8*k+204)*k+(86*q+36)*(2^q*2^q)+16*q+
    (240*(m+r)+215)*V+200 ≤ (300*m+240*r+651)*V+(86*q+36)*(2^q*2^q)
  nlinarith

theorem source_work (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1))) (raw:Tape ℕ)
    (qp:1 ≤ q) (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).work ≤
      (300*(w+1)+240*r+651)*2^(q*(w+1)+r)+(86*q+36)*(2^q*2^q) :=
  (DFTModelResidualClosedExecution.source_bounds q w r v raw qp source nonzero).1.trans
    (budget_linear q (w+1) r qp (by omega))

end
end ExactFourierCircuits.DFTModelResidualClosedLinearWork
