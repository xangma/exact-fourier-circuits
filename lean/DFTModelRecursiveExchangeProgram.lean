import DFTModelRecursiveExchangeDecode

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section

attribute [local irreducible] pairProgram body pairsProgram decode program

theorem program_run (R : ℕ) (raw : Tape ℕ) (initial : DFTModelClockControl.Node.T) :
    run (program R) (raw,initial)=
      ((run decode raw).pass (fun ps => run (pairsProgram R) (ps,initial))).pay 5 0 := by
  simp only [program,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [max_zero,true_and,and_true]
  congr 1
  omega

theorem program_value {R V : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) (k : ℕ) (I : ℂ) :
    (run (program R) (recordTape q w ps,((k,I),paired f f0))).val=
      ((k,I),paired (UniformNativeExchangeRecordMachine.actions ps f)
        (UniformNativeExchangeRecordMachine.actions ps f0)) := by
  rw [program_run]
  change (run (pairsProgram R) ((run decode (recordTape q w ps)).val,((k,I),paired f f0))).val=_
  rw [decode_record]
  exact pairs_value ps positive f f0 k I

theorem program_valid (R : ℕ) (raw : Tape ℕ) (initial : DFTModelClockControl.Node.T) :
    (run (program R) (raw,initial)).valid := by
  rw [program_run]
  exact ⟨decode_valid raw,pairs_valid R _ initial⟩

theorem program_work_bound {R V : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) (k : ℕ) (I : ℂ) :
    (run (program R) (recordTape q w ps,((k,I),paired f f0))).work≤
      19+(74+131*(R*V))*ps.length := by
  rw [program_run]
  change (run decode (recordTape q w ps)).work+
    (run (pairsProgram R) ((run decode (recordTape q w ps)).val,((k,I),paired f f0))).work+5≤_
  rw [decode_work,recordTape_count,decode_record]
  have h := pairs_work_bound ps positive f f0 k I
  nlinarith

theorem program_peak_bound {R V : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (roles : 0<R) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k B : ℕ) (I : ℂ) (endFit : 8+4*ps.length≤B) (fit : R*V≤B) :
    (run (program R) (recordTape q w ps,((k,I),paired f f0))).peak≤B := by
  rw [program_run]
  change max (max (run decode (recordTape q w ps)).peak
    (run (pairsProgram R) ((run decode (recordTape q w ps)).val,((k,I),paired f f0))).peak) 0≤B
  rw [decode_record,max_zero]
  refine max_le (decode_peak _ B ?_) (pairs_peak_bound ps positive roles f f0 k B I (by omega) fit)
  rwa [recordTape_count]

theorem program_lookup {R V : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k : ℕ) (I : ℂ) (i : Fin R) (j : Fin V) :
    (run (program R) (recordTape q w ps,((k,I),paired f f0))).val.2.look
      (i.val*V+j.val) Tagged.blank=
      encodePaired (UniformNativeExchangeRecordMachine.actions ps f i j)
        (UniformNativeExchangeRecordMachine.actions ps f0 i j) := by
  rw [program_value q w ps positive f f0 k I]
  exact paired_lookup _ _ i j

/-- Uniformly linear work in the actual 98-cell native exchange runtime.
The coefficient depends only on the fixed number of roles. -/
theorem program_native_work {R : ℕ} (q w k : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (f f0 : Fin R → Fin (2^k) → UniformMachine.Scalar) (I : ℂ) :
    (run (program R) (recordTape q w ps,((k,I),paired f f0))).work≤
      (20*R+10)*((10*2^k+21)*ps.length+4*k+50) := by
  have h := program_work_bound q w ps (by positivity) f f0 k I
  have hc : 74+131*(R*2^k)≤(20*R+10)*(10*2^k+21) := by
    rw [show (20*R+10)*(10*2^k+21)=200*(R*2^k)+100*2^k+420*R+210 by ring]
    omega
  have hm := Nat.mul_le_mul_right ps.length hc
  nlinarith

end
end ExactFourierCircuits.DFTModelRecursiveExchange
