import DFTModelSavingResidualBounds
import DFTModelSavingResidualAction

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualSourcePeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry DFTModelSavingResidualBounds
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidualSetup.program
  batchArgs DFTModelSavingResidualBatch.program DFTModelSavingResidualFinish.program
  DFTModelResidualClosedRole.gather DFTModelResidualClosedAddresses.program

 theorem combined_peak (h : Handler Port) (x : Input.T) (B : ℕ)
  (setup : (run DFTModelSavingResidualSetup.program x).peak ≤ B)
  (args : (run batchArgs (DFTModelSavingResidual.prepared x)).peak ≤ B)
  (batch : (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).peak ≤ B)
  (finish : (run DFTModelSavingResidualFinish.program (DFTModelSavingResidual.prepared x,returned h x)).peak ≤ B) :
  (Code.run DFTModelSavingResidual.program h x).peak ≤ B := by
  simpa only [DFTModelSavingResidual.program,DFTModelSavingResidual.prepared,arguments,returned,
    Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero,max_le_iff]
    using And.intro setup (And.intro (And.intro args batch) finish)

 theorem source_peak (h : Handler Port) (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
  (bits : Tape ℕ) (a k : ℕ) (I : ℂ) (inverse : Bool) (old : Tape Tagged.T) (B : ℕ)
  (qp : 1 ≤ q) (rp : r < w+1)
  (source : ∀ i : Fin (w+1), bits.look i.val 0=(v i).val) (nonzero : v≠0)
  (fits : UniformBatching.roleBits ≤ q*w+r)
  (room : a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ≤ old.len)
  (bound : 40*(2^(q*(w+1)+r)*2^(q*(w+1)+r))+2*old.len+3*2^(q*(w+1)+r)+(w+1)+10 ≤ B)
  (children : ∀ g, g < 2^(q*w+r-UniformBatching.roleBits) →
    (h ((q,I),DFTModelClockBatch.sliced (UniformBatching.width*2^q) g
      (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2 Tagged.blank)).peak ≤ B) :
  (Code.run DFTModelSavingResidual.program h
    ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).peak ≤ B := by
  let ctx : DFTModelResidualClosedBasis.Meta.T := (q,(w+1,(r,bits)))
  let raw := UniformResidualOrientationArithmetic.boolCode inverse
  let x : Input.T := (ctx,(a,(raw,((k,I),old))))
  let V := 2^(q*(w+1)+r)
  let N := 2^q
  let G := 2^(q*w+r-UniformBatching.roleBits)
  let T := UniformBatching.width*N
  have np : 0 < N := Nat.two_pow_pos _
  have gp : 0 < G := Nat.two_pow_pos _
  have tp : 0 < T := Nat.mul_pos
    (by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _) np
  have partitioned : G*T=V := (partition q w r fits).2
  have tle : T ≤ V := by nlinarith
  have gle : G ≤ V := by nlinarith
  have nle : N ≤ V := by
    have wp : 0 < UniformBatching.width := by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _
    exact (Nat.le_mul_of_pos_left _ wp).trans tle
  obtain ⟨_,_,al,_⟩:=DFTModelResidualClosedAddresses.source q w r v bits qp source nonzero
  obtain ⟨_,_,_,_,gl,_⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v bits a old qp source nonzero
  have address:=DFTModelResidualPeakPolynomial.source_peak q w r v bits qp rp source nonzero
  have binary : ∀ j : ℕ, j < w+1 → bits.look j 0 < 2 := by
    intro j hj
    rw [source ⟨j,hj⟩]
    exact ZMod.val_lt _
  have small : raw < 2 := by cases inverse <;> decide
  have sw:=DFTModelSavingResidualSetup.peak ctx a raw k I old binary small
  rw [al] at sw
  have setup : (run DFTModelSavingResidualSetup.program x).peak ≤ B := by
    change (run DFTModelSavingResidualSetup.program x).peak ≤
      (run DFTModelResidualClosedAddresses.program ctx).peak+a*V+V+(w+1)+T+5 at sw
    change (run DFTModelResidualClosedAddresses.program ctx).peak ≤ 40*(V*V) at address
    change a*V+V ≤ old.len at room
    change 40*(V*V)+2*old.len+3*V+(w+1)+10 ≤ B at bound
    omega
  have args : (run batchArgs (DFTModelSavingResidual.prepared x)).peak ≤ B := by
    rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
      DFTModelSavingResidualSetup.initial_value,DFTModelSavingResidualSetup.batchArgs_run,gl]
    change max V (V/T) ≤ B
    rw [(partition q w r fits).1]
    change max V G ≤ B
    omega
  have batch : (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).peak ≤ B := by
    rw [show x=(ctx,(a,(raw,((k,I),old)))) from rfl,args_value,gl,(partition q w r fits).1]
    exact DFTModelSavingResidualBatch.peak Params Tagged h (q,I) G T B _
      (by omega) (by omega) (by rw [partitioned];omega) children
  have rl : (returned h x).len=V := returned_length h q w r v bits a raw k I old qp source nonzero fits
  have multiple : N ∣ (returned h x).len := by rw [rl];exact DFTModelSavingResidualAction.size_divides q w r
  have fw:=DFTModelSavingResidualFinish.peak (DFTModelSavingResidual.prepared x).1 N T (returned h x) np multiple
  have finish : (run DFTModelSavingResidualFinish.program (DFTModelSavingResidual.prepared x,returned h x)).peak ≤ B := by
    rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
      DFTModelSavingResidualSetup.initial_value,DFTModelResidualClosedRole.gather_value,al,rl] at fw
    have same : (DFTModelSavingResidual.prepared x).2=(N,T) := by
      rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value]
    have pe : DFTModelSavingResidual.prepared x=((DFTModelSavingResidual.prepared x).1,(N,T)) := by
      apply Prod.ext
      · rfl
      · exact same
    rw [pe]
    have final : (run DFTModelSavingResidualFinish.program
      (((DFTModelSavingResidual.prepared x).1,(N,T)),returned h x)).peak ≤ a*V+V+old.len+V+N+1 := by
      rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
        DFTModelSavingResidualSetup.initial_value,DFTModelResidualClosedRole.gather_value]
      exact fw
    apply final.trans
    dsimp only [V,N]
    omega
  exact combined_peak h x B setup args batch finish

end
end ExactFourierCircuits.DFTModelSavingResidualSourcePeak
