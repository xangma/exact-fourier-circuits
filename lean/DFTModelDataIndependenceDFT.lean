import DFTModelDataIndependenceCode
import OAI.Computability.FourierTransform.Goal

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelDataIndependence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- A fixed length and supplied root are independent of homogeneous input cells. -/
theorem dft_inputs (n : ℕ) (rho : ℂ) (x y : Fin n → ℂ) :
    Related dftInKind (n,rho,(⟨n,x⟩ : Tape ℂ)) (n,rho,(⟨n,y⟩ : Tape ℂ)) :=
  ⟨rfl,rfl,rfl,fun _ => trivial⟩

/-- Applies to every concrete false-mode transform program, independently of its value theorem. -/
theorem dft_bills (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (x y : Fin n → ℂ) :
    Bills dftOutKind (run solve (n,rho,(⟨n,x⟩ : Tape ℂ)))
      (run solve (n,rho,(⟨n,y⟩ : Tape ℂ))) :=
  prog_run solve (dft_inputs n rho x y)

/-- Exact equality discharges the usual input-versus-zero work bound. -/
theorem dft_work_zero (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (x : Fin n → ℂ) :
    (run solve (n,rho,(⟨n,x⟩ : Tape ℂ))).work =
      (run solve (n,rho,(⟨n,fun _ => 0⟩ : Tape ℂ))).work :=
  (dft_bills solve n rho x (fun _ => 0)).work

theorem dft_valid_zero (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (x : Fin n → ℂ) :
    (run solve (n,rho,(⟨n,x⟩ : Tape ℂ))).valid =
      (run solve (n,rho,(⟨n,fun _ => 0⟩ : Tape ℂ))).valid :=
  (dft_bills solve n rho x (fun _ => 0)).valid

theorem dft_peak_zero (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (x : Fin n → ℂ) :
    (run solve (n,rho,(⟨n,x⟩ : Tape ℂ))).peak =
      (run solve (n,rho,(⟨n,fun _ => 0⟩ : Tape ℂ))).peak :=
  (dft_bills solve n rho x (fun _ => 0)).peak

theorem dft_uniform_work (solve : Prog false dftInKind dftOutKind)
    (n : ℕ) (rho : ℂ) (x : Fin n → ℂ) :
    (run solve (n,rho,(⟨n,x⟩ : Tape ℂ))).work ≤
      (run solve (n,rho,(⟨n,fun _ => 0⟩ : Tape ℂ))).work :=
  (dft_work_zero solve n rho x).le

end
end ExactFourierCircuits.DFTModelDataIndependence
