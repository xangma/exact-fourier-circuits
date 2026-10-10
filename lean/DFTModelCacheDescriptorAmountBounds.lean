import DFTModelCacheDescriptorAmount

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] logarithm amountSeed amountCore amount

theorem amount_seed_value (a e : ℕ) :
    (run amountSeed (a,e)).val=((a,e),(Nat.clog 2 (2*(a+e)),2^Nat.clog 2 (2*(a+e)))) := by
  obtain ⟨hv,_,_,_⟩:=logarithm_spec (2*(a+e))
  rw [amountSeed]
  change ((a,e),(run logarithm (2*(a+e))).val)=_
  rw [hv]

theorem amount_seed_peak (a e : ℕ) : (run amountSeed (a,e)).peak ≤ 4*(a+e)+2 := by
  obtain ⟨_,_,_,hp⟩:=logarithm_spec (2*(a+e))
  dsimp only [run] at hp
  simp only [amountSeed,pairSize,nat,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay] at ⊢
  omega

theorem amount_peak (a e : ℕ) : (run amount (a,e)).peak ≤ 1000*(a+e+1)^2 := by
  let t:=2*(a+e)
  have hk : Nat.clog 2 t≤t := UniformWorkspaceSearchMachine.clog_bound t
  have hw : 2^Nat.clog 2 t≤2*t+1 := UniformWorkspaceSearchMachine.clog_width_bound t
  have km : Nat.clog 2 t*2^Nat.clog 2 t≤t*(2*t+1) := Nat.mul_le_mul hk hw
  have seed:=amount_seed_peak a e
  rw [amount]
  change max (max (run amountSeed (a,e)).peak
    (run amountCore (run amountSeed (a,e)).val).peak) 0≤_
  rw [amount_seed_value,amountCore_run]
  dsimp only [Bill.peak]
  have b1 : 3*Nat.clog 2 t≤1000*(a+e+1)^2 := by dsimp [t] at hk;nlinarith
  have b2 : 3*Nat.clog 2 t*2^Nat.clog 2 t+2*2^Nat.clog 2 t≤1000*(a+e+1)^2 := by
    dsimp [t] at km hw ⊢
    nlinarith
  have b3 : 6*(3*Nat.clog 2 t*2^Nat.clog 2 t+2*2^Nat.clog 2 t)+(3*a+e)≤1000*(a+e+1)^2 := by
    dsimp [t] at km hw ⊢
    nlinarith
  change max (max (run amountSeed (a,e)).peak
    (max (3*Nat.clog 2 t) (max (3*Nat.clog 2 t*2^Nat.clog 2 t+2*2^Nat.clog 2 t)
      (max 6 (6*(3*Nat.clog 2 t*2^Nat.clog 2 t+2*2^Nat.clog 2 t)+(3*a+e)))))) 0≤_
  have bs : (run amountSeed (a,e)).peak≤1000*(a+e+1)^2 := by nlinarith
  exact max_le (max_le bs (max_le b1 (max_le b2 (max_le (by nlinarith) b3)))) (Nat.zero_le _)

theorem amount_work_bound (a e : ℕ) : (run amount (a,e)).work≤100*(a+e+1) := by
  rw [amount_work]
  have hk:=UniformWorkspaceSearchMachine.clog_bound (2*(a+e))
  omega

end
end ExactFourierCircuits.DFTModelCacheDescriptor
