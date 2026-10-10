import DFTModelOuterAssemblyRoleSource

set_option autoImplicit false

/-! Paper §5.3: save the prepared kernel transform before reloading the data
roles. This joins the charged typed operations corresponding to outer stages
10 and 12. The intervening source header block is proved in SavedSource. -/
namespace ExactFourierCircuits.DFTModelOuterAssemblySaved
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p (DFTModelMemoryCopy.Input sc) DFTModelOuterAssemblyRole.Input
abbrev Output := p (Ty.a sc) (Ty.a DFTModelAffine.Tagged)
def save : Prog false Input (Ty.a sc) := .comp (.atom .fst) (DFTModelMemoryCopy.program sc)
def load : Prog false Input (Ty.a DFTModelAffine.Tagged) :=
  .comp (.atom .snd) DFTModelOuterAssemblyRole.program
def program : Prog false Input Output := .fork save load

attribute [local irreducible] DFTModelMemoryCopy.program DFTModelOuterAssemblyRole.program

theorem program_run (V : ℕ) (y : Tape ℂ) (v : DFTModelOuterAssemblyRole.Input.T) :
    run program ((V,y),v) =
      ((run (DFTModelMemoryCopy.program sc) (V,y)).pass
        (fun saved => (run DFTModelOuterAssemblyRole.program v).pass
          (fun loaded => Bill.one (saved,loaded)))).pay 4 0 := by
  simp only [program,save,load,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem program_value (W V : ℕ) (y : Tape ℂ) (a : Tape ℕ)
    (z : Tape DFTModelAffine.Tagged.T) (k : Tape ℂ) :
    (run program ((V,y),DFTModelOuterAssemblyRole.input W V a z k)).val =
      ((run (DFTModelMemoryCopy.program sc) (V,y)).val,
        (run DFTModelOuterAssemblyRole.program (DFTModelOuterAssemblyRole.input W V a z k)).val) := by
  rw [program_run]
  rfl

theorem program_valid (W V : ℕ) (y : Tape ℂ) (a : Tape ℕ)
    (z : Tape DFTModelAffine.Tagged.T) (k : Tape ℂ) :
    (run program ((V,y),DFTModelOuterAssemblyRole.input W V a z k)).valid := by
  rw [program_run]
  exact ⟨DFTModelMemoryCopy.program_valid _ _ _,
    DFTModelOuterAssemblyRole.program_valid _ _ _ _ _,trivial⟩

theorem program_work (W V : ℕ) (y : Tape ℂ) (a : Tape ℕ)
    (z : Tape DFTModelAffine.Tagged.T) (k : Tape ℂ) :
    (run program ((V,y),DFTModelOuterAssemblyRole.input W V a z k)).work ≤
      61*(W*V)+11*V+21 := by
  rw [program_run]
  change (run (DFTModelMemoryCopy.program sc) (V,y)).work+
    ((run DFTModelOuterAssemblyRole.program (DFTModelOuterAssemblyRole.input W V a z k)).work+1)+4 ≤ _
  rw [DFTModelMemoryCopy.program_work]
  have h := DFTModelOuterAssemblyRole.program_work W V a z k
  omega

theorem work_preserved (W V : ℕ) (y : Tape ℂ) (a : Tape ℕ)
    (z : Tape DFTModelAffine.Tagged.T) (k : Tape ℂ) :
    (run program ((V,y),DFTModelOuterAssemblyRole.input W V a z k)).work ≤
      13*((7*V+9)+19+(5*(W*V)+16*V+24)) := by
  have h := program_work W V y a z k
  omega

theorem program_peak (W V : ℕ) (y : Tape ℂ) (a : Tape ℕ)
    (z : Tape DFTModelAffine.Tagged.T) (k : Tape ℂ) (roles : 2≤W) :
    (run program ((V,y),DFTModelOuterAssemblyRole.input W V a z k)).peak ≤ W*V := by
  rw [program_run]
  change max (max (run (DFTModelMemoryCopy.program sc) (V,y)).peak
    (max (run DFTModelOuterAssemblyRole.program (DFTModelOuterAssemblyRole.input W V a z k)).peak 0)) 0 ≤ _
  rw [DFTModelMemoryCopy.program_peak]
  have h := DFTModelOuterAssemblyRole.program_peak W V a z k roles
  have v : V≤W*V := by nlinarith
  omega

end
end ExactFourierCircuits.DFTModelOuterAssemblySaved
