import DFTModelCRTInverse
import DFTModelCRTPeak
import DFTModelCRTGeometry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem prefix_axes_le (k : ℕ) (x : Args.T) (rows : RowsTwo k x) :
    k+1≤(prefixTable k x).len := by
  induction k generalizing x with
  | zero => exact le_rfl
  | succ k ih =>
      have row : 2≤(readRow x).1 := by simpa [readRow] using rows 0 (by omega)
      have childRows : RowsTwo k (successor x) := by
        intro i hi
        simpa [successor,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using rows (i+1) (by omega)
      have h := ih (successor x) childRows
      change k+1+1≤(readRow x).1*(prefixTable k (successor x)).len
      nlinarith

theorem program_work_linear (k : ℕ) (x : Args.T) (rows : RowsTwo k x) :
    (run program (k,x)).work ≤ 300*((prefixTable k x).len+1) := by
  have size := prefix_volumeSum_le k x rows
  have axes := prefix_axes_le k x rows
  rw [program_work]
  omega

theorem program_peak_le (k : ℕ) (x : Args.T) (V : ℕ)
    (positive : 0<V) (volumeEq : x.2.1=V) (indexBound : x.1+k≤V)
    (rows : RowsTwo k x) (weights : WeightsBound k x V)
    (lengthBound : (prefixTable k x).len≤V) :
    (run program (k,x)).peak ≤ (V+1)^2 := by
  have tp := tables_peak_le k x V positive volumeEq indexBound rows weights lengthBound
  have vv : V≤(V+1)^2 := by nlinarith
  change max (max (run tables (k,x)).peak
    (max (run alpha (run tables (k,x)).val).peak
      (max (run inverseBeta (run tables (k,x)).val).peak 0))) 0≤_
  rw [tables_value,alpha_peak,inverse_peak]
  exact max_le (max_le tp
    (max_le (lengthBound.trans vv) (max_le (lengthBound.trans vv) (by omega)))) (by omega)

theorem program_alpha_value (k : ℕ) (x : Args.T) :
    (run program (k,x)).val.1 =
      Tape.tab (prefixTable k x).len (fun j => ((prefixTable k x).look j (0,0)).1) := by
  change (run alpha (run tables (k,x)).val).val = _
  rw [tables_value,alpha_value]

theorem program_inverse_value {V : ℕ} (k : ℕ) (x : Args.T)
    (length : (prefixTable k x).len=V) (beta : Fin V ≃ Fin V)
    (values : ∀j : Fin V,((prefixTable k x).look j.val (0,0)).2=(beta j).val)
    (j : Fin V) :
    (run program (k,x)).val.2.look j.val 0=(beta.symm j).val := by
  change (run inverseBeta (run tables (k,x)).val).val.look j.val 0 = _
  rw [tables_value]
  exact inverse_permutation _ length beta values j

end
end ExactFourierCircuits.DFTModelCRT
