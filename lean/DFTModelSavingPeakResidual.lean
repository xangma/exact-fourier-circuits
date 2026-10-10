import DFTModelSavingResidualBounds
import DFTModelSavingResidualBoolean

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program
  DFTModelSavingResidualSetup.program DFTModelSavingResidualFinish.program
  DFTModelSavingResidualBatch.program DFTModelResidualClosedRole.gather
  DFTModelResidualClosedAddresses.program UniformBatching.width

lemma residual_peak_exact (h : Handler Port) (x : Input.T) :
    (Code.run DFTModelSavingResidual.program h x).peak=
      max (run DFTModelSavingResidualSetup.program x).peak
        (max (run batchArgs (DFTModelSavingResidual.prepared x)).peak
          (max (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).peak
            (run DFTModelSavingResidualFinish.program (DFTModelSavingResidual.prepared x,returned h x)).peak)) := by
  simp only [DFTModelSavingResidual.program,DFTModelSavingResidual.prepared,arguments,returned,run,Code.run,
    Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero,max_assoc]

/-- One complete paired residual direction takes the maximum of its genuine
child peaks and a polynomial local address allowance. -/
theorem residual_source_peak (h : Handler Port) (q w r : ℕ)
    (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a flag k C : ℕ)
    (I : ℂ) (old : Tape Tagged.T) (qp : 1 ≤ q) (rp : r < w+1)
    (source : ∀i:Fin (w+1),bits.look i.val 0=(v i).val) (nonzero : v≠0)
    (small : flag < 2) (before : DFTModelSavingResidualBoolean.Boolean old)
    (children : ∀J (bank : Tape Tagged.T),bank.len=UniformBatching.width*2^q→DFTModelSavingResidualBoolean.Boolean bank→
      (h ((q,J),bank)).peak ≤ C) :
    (Code.run DFTModelSavingResidual.program h
      ((q,(w+1,(r,bits))),(a,(flag,((k,I),old))))).peak ≤ max C (40*(2^(q*(w+1)+r)*2^(q*(w+1)+r))+
        (a+3)*2^(q*(w+1)+r)+old.len+(w+1)+UniformBatching.width*2^q+10) := by
  let ctx : DFTModelResidualClosedBasis.Meta.T:=(q,(w+1,(r,bits)))
  let x : Input.T:=(ctx,(a,(flag,((k,I),old))))
  let V:=2^(q*(w+1)+r)
  let T:=UniformBatching.width*2^q
  let L:=40*(V*V)+(a+3)*V+old.len+(w+1)+T+10
  let B:=max C L
  obtain ⟨p,hp,len,table⟩:=DFTModelResidualClosedAddresses.source q w r v bits qp source nonzero
  change (run DFTModelResidualClosedAddresses.program ctx).val.len=V at len
  have binary : ∀j,j<w+1→bits.look j 0<2 := by
    intro j hj
    rw [source ⟨j,hj⟩]
    exact (v ⟨j,hj⟩).isLt
  have setup:=DFTModelSavingResidualSetup.peak ctx a flag k I old binary small
  rw [len] at setup
  have address:=DFTModelResidualPeakPolynomial.source_peak q w r v bits qp rp source nonzero
  change (run DFTModelResidualClosedAddresses.program ctx).peak ≤ 40*(V*V) at address
  have gatherLen : (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2.len=V := by
    rw [DFTModelResidualClosedRole.gather_value,DFTModelResidualMovement.gather_value]
    exact len
  have args : arguments x=((q,I),(V/T,(T,
      (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2))) := by
    rw [args_value,gatherLen]
  have argPeak : (run batchArgs (DFTModelSavingResidual.prepared x)).peak ≤ V := by
    rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,DFTModelSavingResidualSetup.initial_value,
      batchArgs_run,gatherLen]
    exact max_le le_rfl (Nat.div_le_self _ _)
  have returnedLen : (returned h x).len=(V/T)*T := by
    rw [returned,args,DFTModelSavingResidualBatch.length]
  have mul : (V/T)*T ≤ V:=Nat.div_mul_le_self V T
  have finish:=DFTModelSavingResidualFinish.peak
    (run DFTModelSavingResidualSetup.initial x).val (2^q) T (returned h x)
    (Nat.two_pow_pos q) (by
      rw [returnedLen]
      change 2^q∣V/T*(UniformBatching.width*2^q)
      refine ⟨V/T*UniformBatching.width,?_⟩
      ring)
  have prepEq : DFTModelSavingResidual.prepared x=
      ((run DFTModelSavingResidualSetup.initial x).val,(2^q,T)) := by
    rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value]
  rw [←prepEq] at finish
  dsimp only [x] at finish
  conv at finish =>
    rhs
    rw [DFTModelSavingResidualSetup.initial_value,DFTModelResidualClosedRole.gather_value]
  rw [len,returnedLen] at finish
  have wp : 0<UniformBatching.width := by rw [UniformBatching.width_eq_pow];positivity
  have smallN : 2^q ≤ T:=Nat.le_mul_of_pos_left _ wp
  have VL : V ≤ L := by dsimp only [L];nlinarith
  have VB : V ≤ B:=VL.trans (le_max_right _ _)
  have TB : T ≤ B := by dsimp [B,L];omega
  have batch : (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (arguments x)).peak ≤ B := by
    rw [args]
    apply DFTModelSavingResidualBatch.peak Params Tagged h (q,I) (V/T) T B _
      ((Nat.div_le_self _ _).trans VB) TB (mul.trans VB)
    intro g _
    exact (children I _ rfl (DFTModelSavingResidualBoolean.sliced_boolean _ _ _
      (DFTModelSavingResidualBoolean.gather_boolean ctx a old before))).trans (le_max_left _ _)
  change (Code.run DFTModelSavingResidual.program h x).peak ≤ B
  rw [residual_peak_exact]
  refine max_le ?_ (max_le (argPeak.trans VB) (max_le batch ?_))
  · calc
      _ ≤ (run DFTModelResidualClosedAddresses.program ctx).peak+a*V+V+(w+1)+T+5 := setup
      _ ≤ 40*(V*V)+a*V+V+(w+1)+T+5 := by omega
      _ ≤ L := by dsimp [L];nlinarith
      _ ≤ B := le_max_right _ _
  · calc
      _ ≤ a*V+V+old.len+(V/T)*T+2^q+1 := finish
      _ ≤ L := by dsimp [L];nlinarith
      _ ≤ B := le_max_right _ _

end
end ExactFourierCircuits.DFTModelSavingPeak
