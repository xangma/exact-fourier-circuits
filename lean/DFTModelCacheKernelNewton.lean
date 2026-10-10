import DFTModelCacheKernelReciprocalCorrect
import DFTModelCacheForestInverseH
import UniformSeedRankCrossPreparation

set_option autoImplicit false

/-! The public entry contains only radix and its prepared root. The actual
Newton producer is invoked once, and the reciprocal recurrence consumes its
inverse-H coefficients. No coefficient or kernel table is an entry premise. -/
namespace ExactFourierCircuits.DFTModelCacheKernelNewton
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier
noncomputable section

attribute [local irreducible] DFTModelCacheKernelReciprocal.program
  DFTModelCacheForest.prepareInverseH

abbrev Input := p w sc
abbrev Output := Ty.a sc

def argument : Prog false Input DFTModelCacheKernelReciprocal.Input :=
  .fork (.atom .fst) DFTModelCacheForest.prepareInverseH
def program : Prog false Input Output :=
  .comp argument DFTModelCacheKernelReciprocal.program

def hValues (r : ℕ) (omega : ℂ) : Tape ℂ :=
  Tape.tab r (fun j=>(NewtonFourier.H omega j)⁻¹)
def gValue (omega : ℂ) (j : ℕ) : ℂ :=
  PowerSeries.coeff j (NewtonFourier.invH omega)⁻¹
def gValues (r : ℕ) (omega : ℂ) : Tape ℂ := Tape.tab r (gValue omega)

theorem argument_value (r : ℕ) (omega : ℂ) :
    (run argument (r,omega)).val=(r,hValues r omega) := by
  change (r,(run DFTModelCacheForest.prepareInverseH (r,omega)).val)=_
  rw [DFTModelCacheForest.prepareInverseH_value]
  rfl

theorem h_coefficients (r : ℕ) (omega : ℂ) :
    ∀i,i<r → (hValues r omega).look i 0=PowerSeries.coeff i (NewtonFourier.invH omega) := by
  intro i hi
  simp [hValues,Tape.look,Tape.tab,hi,NewtonFourier.invH]

theorem program_value (r : ℕ) (omega : ℂ) (hr:0<r) :
    (run program (r,omega)).val=gValues r omega := by
  change (run DFTModelCacheKernelReciprocal.program (run argument (r,omega)).val).val=_
  rw [argument_value]
  exact DFTModelCacheKernelReciprocal.program_value r (hValues r omega)
    (NewtonFourier.invH omega) hr (h_coefficients r omega)

theorem program_valid {r : ℕ} (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) : (run program (r,omega)).valid := by
  change (run argument (r,omega)).valid ∧
    (run DFTModelCacheKernelReciprocal.program (run argument (r,omega)).val).valid
  refine ⟨?_,?_⟩
  · change True ∧ ((run DFTModelCacheForest.prepareInverseH (r,omega)).valid ∧ True)
    exact ⟨trivial,DFTModelCacheForest.prepareInverseH_valid hr primitive,trivial⟩
  rw [argument_value]
  apply DFTModelCacheKernelReciprocal.program_valid
  simp [hValues,Tape.look,Tape.tab,hr]

private theorem sum_bound (r a b : ℕ) (ha:a≤80*(r+1)^2) (hb:b≤110*(r+1)^2) :
    1+a+1+b+1≤200*(r+1)^2 := by
  have hs:0<(r+1)^2:=by positivity
  omega

theorem program_work (r : ℕ) (omega : ℂ) :
    (run program (r,omega)).work≤200*(r+1)^2 := by
  change (run argument (r,omega)).work+
    (run DFTModelCacheKernelReciprocal.program (run argument (r,omega)).val).work+1≤_
  rw [argument_value]
  have hg:=DFTModelCacheKernelReciprocal.program_work r (hValues r omega)
  have hh:=DFTModelCacheForest.prepareInverseH_work r omega
  change 1+(run DFTModelCacheForest.prepareInverseH (r,omega)).work+1+
    (run DFTModelCacheKernelReciprocal.program (r,hValues r omega)).work+1≤_
  exact sum_bound r _ _ hh hg

theorem program_peak (r : ℕ) (omega : ℂ) : (run program (r,omega)).peak≤r := by
  change max (max (run argument (r,omega)).peak
    (run DFTModelCacheKernelReciprocal.program (run argument (r,omega)).val).peak) 0≤r
  rw [argument_value]
  have hg:=DFTModelCacheKernelReciprocal.program_peak r (hValues r omega)
  have hh:=DFTModelCacheForest.prepareInverseH_peak r omega
  change max (max (max 0 (max (run DFTModelCacheForest.prepareInverseH (r,omega)).peak 0))
    (run DFTModelCacheKernelReciprocal.program (r,hValues r omega)).peak) 0≤r
  omega

/-- Exact closed producer contract, with honest quadratic work and linear
integer peak. The source's G bank is a power-series reciprocal. -/
theorem specification {r : ℕ} (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) :
    (run program (r,omega)).val=gValues r omega ∧ (run program (r,omega)).valid ∧
    (run program (r,omega)).work≤200*(r+1)^2 ∧ (run program (r,omega)).peak≤r :=
  ⟨program_value r omega hr,program_valid hr primitive,program_work r omega,program_peak r omega⟩

/-- Correspondence to the actual retained source G coefficients used by
`UniformSeedRankCrossPreparation`, not a new arbitrary table specification. -/
theorem source_gValue (n : ℕ) (axis : Fin (UniformAllAxisSeedPreparation.axisCount n)) (i : ℕ) :
    gValue (UniformSeedRankCrossPreparation.omega n axis) i=
      UniformSeedRankCrossPreparation.gValue n axis i := rfl

end
end ExactFourierCircuits.DFTModelCacheKernelNewton
