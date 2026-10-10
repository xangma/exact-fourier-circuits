import DFTModelCacheCompactBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheCompact
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

attribute [local irreducible] program DFTModelCacheKernelBanks.program

def pairValues (r : ℕ) (eta : ℂ) : Input.T :=
  (DFTModelCacheForest.values r eta,DFTModelCacheKernelNewton.gValues r eta)

def localProgram : Prog false (p w sc) (Ty.a sc) :=
  .comp DFTModelCacheKernelBanks.program program

theorem local_value (r : ℕ) (eta : ℂ) (hr : 0<r) :
    (run localProgram (r,eta)).val=Tape.tab (5*r) (expected (pairValues r eta)) := by
  change (run program (run DFTModelCacheKernelBanks.program (r,eta)).val).val=_
  rw [DFTModelCacheKernelBanks.program_value r eta hr,program_value]
  rfl

theorem lane_value (r : ℕ) (eta : ℂ) (q : Fin 5) (j : Fin r) :
    (run localProgram (r,eta)).val.look (q.val*r+j.val) 0=
      UniformLocalSeedTableMachine.seedValue eta q j.val := by
  have hr : 0<r := Nat.zero_lt_of_lt j.isLt
  rw [local_value r eta hr,Tape.look_of_lt _ _ (show q.val*r+j.val<5*r by nlinarith [q.isLt,j.isLt])]
  change expected (pairValues r eta) (q.val*r+j.val)=_
  have hd : (q.val*r+j.val)/r=q.val := by
    rw [Nat.mul_comm q.val r,Nat.mul_add_div hr,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (q.val*r+j.val)%r=j.val := by
    rw [Nat.mul_comm q.val r,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  unfold expected
  change (if (q.val*r+j.val)/r=0 then _ else if (q.val*r+j.val)/r=1 then _ else
    if (q.val*r+j.val)/r=2 then _ else if (q.val*r+j.val)/r=3 then _ else _)=_
  rw [hd]
  have hl : (DFTModelCacheForest.values r eta).look ((q.val*r+j.val)%r)
      DFTModelCacheForest.Row.blank=DFTModelCacheForest.row eta j.val := by
    rw [hm,Tape.look_of_lt _ _ j.isLt];rfl
  have hg : (DFTModelCacheKernelNewton.gValues r eta).look ((q.val*r+j.val)%r) 0=
      DFTModelCacheKernelNewton.gValue eta j.val := by
    rw [hm,Tape.look_of_lt _ _ j.isLt];rfl
  change (if q.val=0 then _ else if q.val=1 then _ else if q.val=2 then _ else
    if q.val=3 then _ else _)=_
  dsimp only [pairValues,Prod.fst,Prod.snd]
  have hlen : (DFTModelCacheForest.values r eta).len=r := rfl
  rw [hlen,hl,hg]
  fin_cases q <;> rfl

theorem local_valid (r : ℕ) (hr : 0<r) (eta : ℂ) (primitive : IsPrimitiveRoot eta r) :
    (run localProgram (r,eta)).valid := by
  change (run DFTModelCacheKernelBanks.program (r,eta)).valid ∧ (run program _).valid
  exact ⟨DFTModelCacheKernelBanks.program_valid hr primitive,program_valid _⟩

theorem local_work (r : ℕ) (eta : ℂ) :
    (run localProgram (r,eta)).work≤200*(r+1)^2+1000*(r+1)+1 := by
  change (run DFTModelCacheKernelBanks.program (r,eta)).work+
    (run program (run DFTModelCacheKernelBanks.program (r,eta)).val).work+1≤_
  have hf:=DFTModelCacheKernelBanks.program_work r eta
  have hc:=program_work (run DFTModelCacheKernelBanks.program (r,eta)).val
  have len : (run DFTModelCacheKernelBanks.program (r,eta)).val.1.len=r := by
    rw [DFTModelCacheKernelBanks.program]
    change (run DFTModelCacheForest.program (r,eta)).val.len=r
    exact DFTModelCacheForest.program_length r eta
  rw [len] at hc
  omega

theorem local_peak (r : ℕ) (eta : ℂ) :
    (run localProgram (r,eta)).peak≤5*(r+1) := by
  change max (max (run DFTModelCacheKernelBanks.program (r,eta)).peak
    (run program (run DFTModelCacheKernelBanks.program (r,eta)).val).peak) 0≤_
  have hf:=DFTModelCacheKernelBanks.program_peak r eta
  have hc:=program_peak (run DFTModelCacheKernelBanks.program (r,eta)).val
  have len : (run DFTModelCacheKernelBanks.program (r,eta)).val.1.len=r := by
    rw [DFTModelCacheKernelBanks.program]
    change (run DFTModelCacheForest.program (r,eta)).val.len=r
    exact DFTModelCacheForest.program_length r eta
  rw [len] at hc
  omega

end
end ExactFourierCircuits.DFTModelCacheCompact
