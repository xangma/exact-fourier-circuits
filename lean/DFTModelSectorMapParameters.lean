import DFTModelSectorMapBitsPack
import DFTModelCacheDescriptorLog

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapParameters
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

def blockBits (V : ℕ) : ℕ := Nat.clog 2 (V+1) / 2 + 1

def increment : Prog false w w := binary .add (.atom .id) (.atom (.lit 1))
def finish : Prog false (p w w) w :=
  binary .add (binary .div (.atom .fst) (.atom (.lit 2))) (.atom (.lit 1))
def program : Prog false w w :=
  .comp increment (.comp DFTModelCacheDescriptor.logarithm finish)

theorem blockBits_pos (V : ℕ) : 1 ≤ blockBits V := by unfold blockBits; omega

theorem blockBits_le (V : ℕ) : blockBits V ≤ V+1 := by
  have h := UniformWorkspaceSearchMachine.clog_bound (V+1)
  by_cases hv : V = 0
  · simp [hv, blockBits]
  · unfold blockBits
    omega

theorem clog_le_twice_blockBits (M V : ℕ) (hMV : M ≤ V) :
    Nat.clog 2 (M+1) ≤ 2*blockBits V := by
  have h := Nat.clog_mono_right 2 (show M+1 ≤ V+1 by omega)
  unfold blockBits
  omega

theorem blockBits_mul_pow (V : ℕ) : blockBits V * 2^blockBits V ≤ 6*(V+1) := by
  let L := Nat.clog 2 (V+1)
  have hl : 2^L ≤ 2*(V+1)+1 := UniformWorkspaceSearchMachine.clog_width_bound (V+1)
  have hb : blockBits V ≤ 2^(L/2) := by
    change L/2+1 ≤ 2^(L/2)
    exact Nat.succ_le_of_lt (L/2).lt_two_pow_self
  calc
    blockBits V * 2^blockBits V ≤ 2^(L/2) * 2^(L/2+1) := by
      exact Nat.mul_le_mul_right _ hb
    _ = 2^(L/2+(L/2+1)) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ 6*(V+1) := by rw [Nat.pow_succ]; omega

theorem blockBits_square (V : ℕ) : blockBits V ^ 2 ≤ 6*(V+1) := by
  have h := blockBits_mul_pow V
  have hb : blockBits V ≤ 2^blockBits V := Nat.le_of_lt (blockBits V).lt_two_pow_self
  calc
    blockBits V ^ 2 = blockBits V * blockBits V := by rw [pow_two]
    _ ≤ blockBits V * 2^blockBits V := Nat.mul_le_mul_left _ hb
    _ ≤ _ := h

theorem blockBits_pow (V : ℕ) : 2^blockBits V ≤ 6*(V+1) := by
  have hp := blockBits_pos V
  have h := blockBits_mul_pow V
  have he : 2^blockBits V ≤ blockBits V * 2^blockBits V := Nat.le_mul_of_pos_left _ hp
  omega

theorem packed_span (V : ℕ) : (V/blockBits V+1)*blockBits V ≤ 2*V+1 := by
  have hdiv : V / blockBits V * blockBits V ≤ V := Nat.div_mul_le_self _ _
  have hb := blockBits_le V
  rw [Nat.add_mul]
  omega

theorem increment_run (V : ℕ) : run increment V = ⟨V+1,5,V+1,True⟩ := by
  simp [increment,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.word,Bill.one]

theorem finish_run (L W : ℕ) : run finish (L,W) = ⟨L/2+1,9,max 2 (L/2+1),True⟩ := by
  simp [finish,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.word,Bill.one]

theorem program_value (V : ℕ) : (run program V).val = blockBits V := by
  have hv := (DFTModelCacheDescriptor.logarithm_spec (V+1)).1
  change (run finish (run DFTModelCacheDescriptor.logarithm (run increment V).val).val).val = _
  rw [increment_run, hv, finish_run]
  rfl

theorem program_work (V : ℕ) : (run program V).work = 28*Nat.clog 2 (V+1)+39 := by
  obtain ⟨hv,_,hw,_⟩ := DFTModelCacheDescriptor.logarithm_spec (V+1)
  change (run increment V).work +
    ((run DFTModelCacheDescriptor.logarithm (run increment V).val).work +
      (run finish (run DFTModelCacheDescriptor.logarithm (run increment V).val).val).work + 1) + 1 = _
  rw [increment_run, hv, hw, finish_run]
  dsimp only [Bill.work]
  omega

theorem program_valid (V : ℕ) : (run program V).valid := by
  obtain ⟨hv,hd,_,_⟩ := DFTModelCacheDescriptor.logarithm_spec (V+1)
  change (run increment V).valid ∧
    ((run DFTModelCacheDescriptor.logarithm (run increment V).val).valid ∧
      (run finish (run DFTModelCacheDescriptor.logarithm (run increment V).val).val).valid)
  rw [increment_run, hv, finish_run]
  exact ⟨trivial,hd,trivial⟩

theorem program_peak (V : ℕ) : (run program V).peak ≤ 4*(V+1) := by
  obtain ⟨hv,_,_,hp⟩ := DFTModelCacheDescriptor.logarithm_spec (V+1)
  change max (max (run increment V).peak
    (max (max (run DFTModelCacheDescriptor.logarithm (run increment V).val).peak
      (run finish (run DFTModelCacheDescriptor.logarithm (run increment V).val).val).peak) 0)) 0 ≤ _
  rw [increment_run, hv, finish_run]
  have hb := blockBits_le V
  change Nat.clog 2 (V+1)/2+1 ≤ V+1 at hb
  dsimp only [Bill.peak, Bill.val] at hp ⊢
  omega

theorem program_work_linear (V : ℕ) : (run program V).work ≤ 67*(V+1) := by
  rw [program_work]
  have h := UniformWorkspaceSearchMachine.clog_bound (V+1)
  omega

theorem highTable_work_linear (V : ℕ) :
    (run DFTModelSectorMapBits.highTable (blockBits V)).work ≤ 255*(V+1) := by
  rw [DFTModelSectorMapBits.highTable_work]
  have hb := blockBits_le V
  have hp := blockBits_pow V
  have hm := blockBits_mul_pow V
  nlinarith

theorem pack_work_linear (V : ℕ) (m : Tape ℕ) :
    (run DFTModelSectorMapBits.pack (blockBits V,(V,m))).work ≤ 144*(V+1) := by
  rw [DFTModelSectorMapBits.pack_work]
  have hp := blockBits_pos V
  have hs := packed_span V
  have hc : V/blockBits V+1 ≤ (V/blockBits V+1)*blockBits V := Nat.le_mul_of_pos_right _ hp
  nlinarith

theorem highTable_peak_linear (V : ℕ) :
    (run DFTModelSectorMapBits.highTable (blockBits V)).peak ≤ 6*(V+1) := by
  have h := DFTModelSectorMapBits.highTable_peak (blockBits V)
  have hp := blockBits_pow V
  omega

theorem pack_peak_linear (V : ℕ) (m : Tape ℕ) :
    (run DFTModelSectorMapBits.pack (blockBits V,(V,m))).peak ≤ 6*(V+1) := by
  have h := DFTModelSectorMapBits.pack_peak (blockBits V) V m (blockBits_pos V)
  have hp := blockBits_pow V
  have hs := packed_span V
  omega

theorem preparation_work_linear (V : ℕ) (m : Tape ℕ) :
    (run program V).work + (run DFTModelSectorMapBits.highTable (blockBits V)).work +
      (run DFTModelSectorMapBits.pack (blockBits V,(V,m))).work ≤ 466*(V+1) := by
  have ha := program_work_linear V
  have hb := highTable_work_linear V
  have hc := pack_work_linear V m
  omega

end
end ExactFourierCircuits.DFTModelSectorMapParameters
