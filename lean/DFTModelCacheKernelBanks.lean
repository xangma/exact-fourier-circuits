import DFTModelCacheKernelNewton

set_option autoImplicit false

/-! Shared Newton and reciprocal banks: one closed Newton production, one
charged inverse-H extraction, and one charged reciprocal recurrence. -/
namespace ExactFourierCircuits.DFTModelCacheKernelBanks
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier
noncomputable section

attribute [local irreducible] DFTModelCacheForest.program
  DFTModelCacheForest.inverseHBank DFTModelCacheKernelReciprocal.program

abbrev Input := DFTModelCacheForest.Input
abbrev Output := p DFTModelCacheForest.Output (Ty.a sc)

def argument : Prog false DFTModelCacheForest.Output DFTModelCacheKernelReciprocal.Input :=
  .fork (.atom .len) DFTModelCacheForest.inverseHBank
def reciprocal : Prog false DFTModelCacheForest.Output (Ty.a sc) :=
  .comp argument DFTModelCacheKernelReciprocal.program
def program : Prog false Input Output :=
  .comp DFTModelCacheForest.program (.fork (.atom .id) reciprocal)

theorem inverseH_value (r : ℕ) (omega : ℂ) :
    (run DFTModelCacheForest.inverseHBank (DFTModelCacheForest.values r omega)).val=
      DFTModelCacheKernelNewton.hValues r omega := by
  have h:=DFTModelCacheForest.prepareInverseH_value r omega
  change (run DFTModelCacheForest.inverseHBank
    (run DFTModelCacheForest.program (r,omega)).val).val=_ at h
  rw [DFTModelCacheForest.program_value] at h
  exact h

theorem argument_value (r : ℕ) (omega : ℂ) :
    (run argument (DFTModelCacheForest.values r omega)).val=
      (r,DFTModelCacheKernelNewton.hValues r omega) := by
  change (r,(run DFTModelCacheForest.inverseHBank (DFTModelCacheForest.values r omega)).val)=_
  rw [inverseH_value]

theorem reciprocal_value (r : ℕ) (omega : ℂ) (hr:0<r) :
    (run reciprocal (DFTModelCacheForest.values r omega)).val=
      DFTModelCacheKernelNewton.gValues r omega := by
  change (run DFTModelCacheKernelReciprocal.program
    (run argument (DFTModelCacheForest.values r omega)).val).val=_
  rw [argument_value]
  exact DFTModelCacheKernelReciprocal.program_value r _ _ hr
    (DFTModelCacheKernelNewton.h_coefficients r omega)

theorem reciprocal_valid (r : ℕ) (omega : ℂ) (hr:0<r) :
    (run reciprocal (DFTModelCacheForest.values r omega)).valid := by
  change (run argument (DFTModelCacheForest.values r omega)).valid ∧
    (run DFTModelCacheKernelReciprocal.program
      (run argument (DFTModelCacheForest.values r omega)).val).valid
  refine ⟨?_,?_⟩
  · change True ∧ ((run DFTModelCacheForest.inverseHBank _).valid ∧ True)
    exact ⟨trivial,DFTModelCacheForest.inverseHBank_valid _,trivial⟩
  · rw [argument_value]
    apply DFTModelCacheKernelReciprocal.program_valid
    simp [DFTModelCacheKernelNewton.hValues,Tape.look,Tape.tab,hr]

theorem reciprocal_work (t : Tape DFTModelCacheForest.Row.T) :
    (run reciprocal t).work≤110*(t.len+1)^2+15*t.len+7 := by
  change (run argument t).work+
    (run DFTModelCacheKernelReciprocal.program (run argument t).val).work+1≤_
  have ha:(run argument t).val=(t.len,(run DFTModelCacheForest.inverseHBank t).val):=rfl
  rw [ha]
  have h:=DFTModelCacheKernelReciprocal.program_work t.len
    (run DFTModelCacheForest.inverseHBank t).val
  change 1+(run DFTModelCacheForest.inverseHBank t).work+1+
    (run DFTModelCacheKernelReciprocal.program
      (t.len,(run DFTModelCacheForest.inverseHBank t).val)).work+1≤_
  rw [DFTModelCacheForest.inverseHBank_work]
  omega

theorem reciprocal_peak (t : Tape DFTModelCacheForest.Row.T) :
    (run reciprocal t).peak≤t.len := by
  change max (max (run argument t).peak
    (run DFTModelCacheKernelReciprocal.program (run argument t).val).peak) 0≤_
  have ha:(run argument t).val=(t.len,(run DFTModelCacheForest.inverseHBank t).val):=rfl
  rw [ha]
  have h:=DFTModelCacheKernelReciprocal.program_peak t.len
    (run DFTModelCacheForest.inverseHBank t).val
  have p:=DFTModelCacheForest.inverseHBank_peak t
  change max (max (max t.len (max (run DFTModelCacheForest.inverseHBank t).peak 0))
    (run DFTModelCacheKernelReciprocal.program
      (t.len,(run DFTModelCacheForest.inverseHBank t).val)).peak) 0≤_
  omega

theorem program_value (r : ℕ) (omega : ℂ) (hr:0<r) :
    (run program (r,omega)).val=
      (DFTModelCacheForest.values r omega,DFTModelCacheKernelNewton.gValues r omega) := by
  change ((run DFTModelCacheForest.program (r,omega)).val,
    (run reciprocal (run DFTModelCacheForest.program (r,omega)).val).val)=_
  rw [DFTModelCacheForest.program_value,reciprocal_value r omega hr]

theorem program_valid {r : ℕ} (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) : (run program (r,omega)).valid := by
  change (run DFTModelCacheForest.program (r,omega)).valid ∧
    (True ∧ ((run reciprocal (run DFTModelCacheForest.program (r,omega)).val).valid ∧ True))
  rw [DFTModelCacheForest.program_value]
  exact ⟨DFTModelCacheForest.program_valid hr primitive,trivial,reciprocal_valid r omega hr,trivial⟩

private theorem sum_bound (r a b : ℕ) (ha:a≤60*(r+1)^2)
    (hb:b≤110*(r+1)^2+15*r+7) : a+(1+b+1)+1≤200*(r+1)^2 := by nlinarith

theorem program_work (r : ℕ) (omega : ℂ) :
    (run program (r,omega)).work≤200*(r+1)^2 := by
  change (run DFTModelCacheForest.program (r,omega)).work+
    (1+(run reciprocal (run DFTModelCacheForest.program (r,omega)).val).work+1)+1≤_
  have h:=reciprocal_work (run DFTModelCacheForest.program (r,omega)).val
  rw [DFTModelCacheForest.program_length] at h
  exact sum_bound r _ _ (DFTModelCacheForest.program_work r omega) h

theorem program_peak (r : ℕ) (omega : ℂ) : (run program (r,omega)).peak≤r := by
  change max (max (run DFTModelCacheForest.program (r,omega)).peak
    (max 0 (max (run reciprocal (run DFTModelCacheForest.program (r,omega)).val).peak 0))) 0≤_
  have h:=reciprocal_peak (run DFTModelCacheForest.program (r,omega)).val
  rw [DFTModelCacheForest.program_length] at h
  have p:=DFTModelCacheForest.program_peak r omega
  omega

theorem specification {r : ℕ} (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) :
    (run program (r,omega)).val=
      (DFTModelCacheForest.values r omega,DFTModelCacheKernelNewton.gValues r omega) ∧
    (run program (r,omega)).valid ∧ (run program (r,omega)).work≤200*(r+1)^2 ∧
    (run program (r,omega)).peak≤r :=
  ⟨program_value r omega hr,program_valid hr primitive,program_work r omega,program_peak r omega⟩

end
end ExactFourierCircuits.DFTModelCacheKernelBanks
