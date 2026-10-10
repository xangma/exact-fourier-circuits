import DFTModelSavingYLoop

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
open UniformNativeYRecordMachine (Direction actions)
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] DFTModelRecursiveYDirection.program

theorem arguments_valid (x : Body.T) : (run arguments x).valid := by
  simp [arguments,rowBase,original,index,old,rest,raw,field,DFTModelResidualCore.binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem body_valid (R : ℕ) (x : Body.T) : (run (body R) x).valid :=
  ⟨arguments_valid x,DFTModelRecursiveYDirection.program_valid R _⟩

theorem steps_valid (R : ℕ) (x : Input.T) (count : ℕ) : (steps R x count).valid := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨ih,body_valid R _⟩

theorem program_valid (R : ℕ) (x : Input.T) : (run (program R) x).valid := by
  rw [program_run]
  exact steps_valid R x _

theorem body_work {R m : ℕ} (q r k i : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v0 : Tape Tagged.T) (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar) :
    (run (body R) (rowInput r k i I raw v0 (paired f f0))).work≤
      16*(R+1)*UniformNativePreparedYTranslationMachine.runtime q m r k+58 := by
  have bound:=DFTModelRecursiveYDirection.work_source_bound R q m r (8+(m+1)*i) k I raw
    (paired f f0) rfl
  change (((run arguments (rowInput r k i I raw v0 (paired f f0))).pass
    (fun z => run (DFTModelRecursiveYDirection.program R) z)).pay 1 0).work≤_
  rw [arguments_run]
  dsimp only [Bill.pass,Bill.pay,Bill.work,Bill.val]
  rw [source.headers.1,source.headers.2.1]
  omega

theorem steps_work {R m : ℕ} (q r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q)
    (i : ℕ) (hi : i≤ds.length) :
    (steps R (input r k I raw (paired f f0)) i).work≤
      (16*(R+1)*UniformNativePreparedYTranslationMachine.runtime q m r k+59)*i+1 := by
  induction i with
  | zero => simp [steps,Bill.steps,Bill.one]
  | succ i ih =>
    change (steps R (input r k I raw (paired f f0)) i).work+
      (run (body R) (input r k I raw (paired f f0),
        (i,(steps R (input r k I raw (paired f f0)) i).val))).work+1≤_
    rw [steps_value q r k I raw ds source f f0 positive shape qp i (by omega)]
    have wb:=body_work q r k i I raw (paired f f0) ds source
      (actions q m k (ds.take i) f) (actions q m k (ds.take i) f0)
    have ih:=ih (by omega)
    change _≤_ at wb
    dsimp only [rowInput] at wb
    rw [Nat.mul_add,Nat.mul_one]
    omega

theorem program_work {R m : ℕ} (q r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q) :
    (run (program R) (input r k I raw (paired f f0))).work≤
      32*(R+1)*UniformNativeYRecordMachine.runtime q m r k ds.length := by
  rw [program_run]
  change (steps R (input r k I raw (paired f f0)) (raw.look 6 0)).work+11≤_
  rw [source.headers.2.2]
  have wb:=steps_work q r k I raw ds source f f0 positive shape qp ds.length le_rfl
  have small : 31≤UniformNativePreparedYTranslationMachine.runtime q m r k := by
    unfold UniformNativePreparedYTranslationMachine.runtime
    omega
  unfold UniformNativeYRecordMachine.runtime
  nlinarith

theorem body_peak {R m : ℕ} (q r k i B : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v0 : Tape Tagged.T) (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q) (hi : i<ds.length)
    (extent : R*2^k≤B) (recordEnd : 8+(m+1)*ds.length≤B)
    (padded : 2^(q*(m+r))≤B) (square : 2^q*2^q≤B) :
    (run (body R) (rowInput r k i I raw v0 (paired f f0))).peak≤4*B+2 := by
  have row:=source.direction i hi
  have room : 8+(m+1)*i+m+1≤B := by
    have h:=Nat.mul_le_mul_left (m+1) (Nat.succ_le_iff.mpr hi)
    simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one] at h
    omega
  have pk:=DFTModelRecursiveYDirection.program_peak q r (8+(m+1)*i) k B I raw
    (paired f f0) (ds[i]'hi) positive rfl shape qp row.1 row.2 extent room padded square
  change (((run arguments (rowInput r k i I raw v0 (paired f f0))).pass
    (fun z => run (DFTModelRecursiveYDirection.program R) z)).pay 1 0).peak≤_
  rw [arguments_run]
  dsimp only [Bill.pass,Bill.pay,Bill.peak,Bill.val]
  rw [source.headers.1,source.headers.2.1]
  have mul : (m+1)*i≤B := by omega
  omega

theorem steps_peak {R m : ℕ} (q r k B : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q)
    (extent : R*2^k≤B) (recordEnd : 8+(m+1)*ds.length≤B)
    (padded : 2^(q*(m+r))≤B) (square : 2^q*2^q≤B)
    (i : ℕ) (hi : i≤ds.length) :
    (steps R (input r k I raw (paired f f0)) i).peak≤4*B+2 := by
  induction i with
  | zero => simp [steps,Bill.steps,Bill.one]
  | succ i ih =>
    change max (max (steps R (input r k I raw (paired f f0)) i).peak
      (run (body R) (input r k I raw (paired f f0),
        (i,(steps R (input r k I raw (paired f f0)) i).val))).peak) (i+1)≤_
    rw [steps_value q r k I raw ds source f f0 positive shape qp i (by omega)]
    have pb:=body_peak q r k i B I raw (paired f f0) ds source
      (actions q m k (ds.take i) f) (actions q m k (ds.take i) f0)
      positive shape qp (by omega) extent recordEnd padded square
    dsimp only [rowInput] at pb
    have count : ds.length≤B := by nlinarith only [recordEnd]
    have ih:=ih (by omega)
    omega

theorem program_peak {R m : ℕ} (q r k B : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q)
    (extent : R*2^k≤B) (recordEnd : 8+(m+1)*ds.length≤B)
    (padded : 2^(q*(m+r))≤B) (square : 2^q*2^q≤B) :
    (run (program R) (input r k I raw (paired f f0))).peak≤4*B+2 := by
  rw [program_run]
  change max (steps R (input r k I raw (paired f f0)) (raw.look 6 0)).peak 6≤_
  rw [source.headers.2.2]
  have pk:=steps_peak q r k B I raw ds source f f0 positive shape qp extent recordEnd
    padded square ds.length le_rfl
  omega

end
end ExactFourierCircuits.DFTModelSavingY
