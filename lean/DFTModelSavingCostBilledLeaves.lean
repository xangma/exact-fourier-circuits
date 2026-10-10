import DFTModelSavingCostFixed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingY.program
  DFTModelSavingScalar.program DFTModelRecursiveExchange.program

lemma pay_time_ratio (work A ticks extra : ℕ) (actual : work≤A*ticks) (positive : 1≤ticks) :
    work+extra≤(A+extra)*ticks := by
  have pay:=Nat.mul_le_mul_left extra positive
  nlinarith only [actual,pay]

lemma scalar_native_ratio (R V k c : ℕ) :
    127+179*(R*V)+22≤(20*R+200)*(10*V+4*k+c+102) := by nlinarith

lemma exchange_native_ratio (R V k rows : ℕ) :
    90+(74+131*(R*V))*rows+22≤(20*R+200)*((10*V+21)*rows+4*k+99) := by
  have row : 74+131*(R*V)≤(20*R+200)*(10*V+21) := by nlinarith
  have rowsBound:=Nat.mul_le_mul_right rows row
  have control : 112≤(20*R+200)*(4*k+99) := by nlinarith
  nlinarith only [rowsBound,control]

/-- The real scalar branch, including the stream's 22 instructions per record,
compared with the exact native scalar-loop duration. -/
theorem scalar_native_billed (R rest k c : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : raw.look 0 0=1) (len : bank.len=R*2^k) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,((k,I),bank)))).work+22≤
      (20*R+200)*(10*2^k+4*k+c+102) := by
  have cost:=scalar_dispatch_work R rest k I raw bank h opcode
  rw [len] at cost
  exact (Nat.add_le_add_right cost 22).trans (scalar_native_ratio R (2^k) k c)

/-- Chronological signed exchanges retain the actual runtime pair count.
Overlapping pairs remain sequential in the selected typed computation. -/
theorem exchange_native_billed (R rest k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : raw.look 0 0=4) (len : bank.len=R*2^k) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,((k,I),bank)))).work+22≤
      (20*R+200)*((10*2^k+21)*raw.look 6 0+4*k+99) := by
  have cost:=exchange_dispatch_work R rest k I raw bank h opcode
  rw [len] at cost
  exact (Nat.add_le_add_right cost 22).trans (exchange_native_ratio R (2^k) k (raw.look 6 0))

/-- Both actual marker branches include only charged control. -/
theorem marker_native_billed (R rest head dispatch : ℕ) (raw : Tape ℕ)
    (node : Node.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : raw.look 0 0=2 ∨ raw.look 0 0=6) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22≤
      1000*(6+2*head+dispatch) := by
  rw [dispatch_work]
  rcases opcode with opcode|opcode
  all_goals rw [opcode]
  all_goals norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  all_goals omega

/-- The genuine runtime Y records and exact native loop formula. Both paired
channels are handled by the single existing typed translation computation. -/
theorem translation_native_billed {R m : ℕ} (q rest k : ℕ) (I : ℂ)
    (raw : Tape ℕ) (ds : List (UniformNativeYRecordMachine.Direction R m))
    (source : DFTModelSavingY.RecordSource q ds raw)
    (f f0 : Fin R→Fin (2^k)→Scalar) (roles : 0<R) (shape : k=q*m+rest)
    (qp : 1≤q) (opcode : raw.look 0 0=3) (h : Handler DFTModelSavingRecords.Port) :
    (Code.run (DFTModelSavingRecords.dispatch R) h
      (rest,(raw,((k,I),paired f f0)))).work+22≤
      (32*(R+1)+71)*(UniformNativeYRecordMachine.runtime q m rest k ds.length+51) := by
  rw [dispatch_work,opcode]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  change (run (DFTModelSavingY.program R) (DFTModelSavingY.input rest k I raw (paired f f0))).work+49+22≤_
  have cost:=DFTModelSavingY.program_work q rest k I raw ds source f f0 roles shape qp
  have longer:=Nat.mul_le_mul_left (32*(R+1))
    (show UniformNativeYRecordMachine.runtime q m rest k ds.length≤
      UniformNativeYRecordMachine.runtime q m rest k ds.length+51 by omega)
  have actual : (run (DFTModelSavingY.program R)
      (DFTModelSavingY.input rest k I raw (paired f f0))).work≤
      (32*(R+1))*(UniformNativeYRecordMachine.runtime q m rest k ds.length+51) := cost.trans longer
  calc
    _=(run (DFTModelSavingY.program R)
      (DFTModelSavingY.input rest k I raw (paired f f0))).work+71 := by omega
    _≤_ := pay_time_ratio _ (32*(R+1))
      (UniformNativeYRecordMachine.runtime q m rest k ds.length+51) 71 actual (by omega)

end
end ExactFourierCircuits.DFTModelSavingCost
