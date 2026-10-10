import DFTModelSavingShapeBinary
import DFTModelSavingBinaryPeak
import DFTModelSavingCostSuffix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelBinaryPhysical.program DFTModelBinaryStage.program
  DFTModelRecursiveBinary.body DFTModelRecursiveBinary.program

lemma packing_address_peak (P M j t : ℕ) (live : j<M) (lane : t<2) :
    DFTModelBinaryPacking.addressPeak P j t ≤ 4*M+P+2 := by
  have div:=Nat.div_le_self j P
  have rem:=Nat.mod_le j P
  have mul:=Nat.div_mul_le_self j P
  unfold DFTModelBinaryPacking.addressPeak UniformTensorAddressMachine.address
  simp only [max_le_iff]
  have scaled : P*(t+2*(j/P)) ≤ P+2*j := by nlinarith
  omega

lemma packing_peak (M P : ℕ) (v : Tape Tagged.T) :
    (run DFTModelBinaryPacking.program (M,(P,v))).peak ≤ 4*M+P+2 := by
  change max (max 0 (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j=>run DFTModelBinaryPacking.cell ((M,(P,v)),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero]
  refine max_le (by omega) (Finset.sup_le ?_)
  intro j hj
  rw [DFTModelBinaryPacking.cell_run]
  exact max_le (packing_address_peak P M j 0 (Finset.mem_range.mp hj) (by decide))
    (packing_address_peak P M j 1 (Finset.mem_range.mp hj) (by decide))

lemma affine_peak (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T)
    (flags : ∀j,j<M→(v.look j DFTModelBinaryAffinePair.Pair.blank).1.1<2 ∧
      (v.look j DFTModelBinaryAffinePair.Pair.blank).2.1<2) :
    (run DFTModelBinaryAffine.program (M,((c,d),v))).peak ≤ max M 2 := by
  change max (max 0 (Bill.tab M DFTModelBinaryAffinePair.Pair.blank
    (fun j=>run DFTModelBinaryAffine.cell ((M,((c,d),v)),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero]
  refine max_le (le_max_left _ _) (Finset.sup_le ?_)
  intro j hj
  rw [DFTModelBinaryAffine.cell_run]
  have fs:=flags j (Finset.mem_range.mp hj)
  exact (Nat.add_le_add (Nat.le_of_lt_succ fs.1) (Nat.le_of_lt_succ fs.2)).trans (le_max_right _ _)

lemma stage_peak (M P : ℕ) (c d : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    (run DFTModelBinaryStage.program (M,(P,((c,d),v)))).peak ≤ 4*M+P+2 := by
  have packed : ∀j,j<M→
      ((run DFTModelBinaryPacking.program (M,(P,v))).val.look j DFTModelBinaryAffinePair.Pair.blank).1.1<2 ∧
      ((run DFTModelBinaryPacking.program (M,(P,v))).val.look j DFTModelBinaryAffinePair.Pair.blank).2.1<2 := by
    intro j hj
    rw [DFTModelBinaryPacking.program_value,Tape.look_of_lt _ _ hj]
    exact ⟨look_boolean before _,look_boolean before _⟩
  have physical : (run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).peak ≤ 4*M+P+2 := by
    rw [DFTModelBinaryPhysical.program,comp_run,DFTModelBinaryPhysical.ready_run]
    simp only [Bill.pass,Bill.pay,max_zero]
    exact max_le (packing_peak M P v) ((affine_peak M c d _ packed).trans (max_le (by omega) (by omega)))
  rw [DFTModelBinaryStage.program,comp_run,DFTModelBinaryStage.ready_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  exact max_le physical (DFTModelBinaryUnpacking.program_peak M P (4*M+P+2) _ (by omega) (by omega))

lemma binary_body_peak (k i P : ℕ) (I : ℂ) (old v : Tape Tagged.T) (before : Boolean v) :
    (run DFTModelRecursiveBinary.body (((k,I),old),(i,(P,v)))).peak ≤ 4*v.len+2*P+4 := by
  rw [DFTModelRecursiveBinary.body,fork_run,DFTModelRecursiveBinary.doubled_run,
    comp_run,DFTModelRecursiveBinary.argument_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero]
  refine max_le (max_le (by omega) (by omega)) (max_le (max_le (by omega) (by omega)) ?_)
  exact (stage_peak _ _ _ _ v before).trans (by have h:=Nat.div_le_self v.len 2;omega)

lemma states_len_le (I : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    (DFTModelRecursiveBinary.states I v j).2.len ≤ v.len := by
  induction j with
  | zero=>exact le_rfl
  | succ j ih=>
    change (DFTModelRecursiveBinary.next I _ _).len ≤ _
    rw [DFTModelRecursiveBinary.next_len]
    have h:=Nat.div_mul_le_self (DFTModelRecursiveBinary.states I v j).2.len 2
    omega

lemma binary_stages_peak (k j : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (cap : j ≤ k) :
    (DFTModelRecursiveBinary.stages k I v j).peak ≤ 4*v.len+2*2^k+4 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have prior:=ih (by omega)
    change max (max (DFTModelRecursiveBinary.stages k I v j).peak
      (run DFTModelRecursiveBinary.body (((k,I),v),(j,
        (DFTModelRecursiveBinary.stages k I v j).val))).peak) (j+1) ≤ _
    rw [DFTModelRecursiveBinary.stages_value]
    have step:=binary_body_peak k j (DFTModelRecursiveBinary.states I v j).1 I v
      (DFTModelRecursiveBinary.states I v j).2
      (DFTModelSavingShapeBinary.states_boolean I v before j)
    rw [DFTModelRecursiveBinary.states_stride] at step
    have vol:=states_len_le I v j
    have power:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show j ≤ k by omega)
    have bits:=DFTModelSavingBinary.bits_le_volume k
    have stepB : (run DFTModelRecursiveBinary.body (((k,I),v),(j,
        DFTModelRecursiveBinary.states I v j))).peak ≤ 4*v.len+2*2^k+4 := by
      calc
        _ ≤ 4*(DFTModelRecursiveBinary.states I v j).2.len+
          2*(DFTModelRecursiveBinary.states I v j).1+4 := binary_body_peak _ _ _ _ _ _
            (DFTModelSavingShapeBinary.states_boolean I v before j)
        _ ≤ _ := by rw [DFTModelRecursiveBinary.states_stride];omega
    exact max_le (max_le prior stepB) (by omega)

/-- Arbitrary Boolean tag patterns and arbitrary prepared root parameters. -/
theorem ordinary_peak (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    (run DFTModelRecursiveBinary.program ((k,I),v)).peak ≤ 4*v.len+2*2^k+4 := by
  rw [DFTModelRecursiveBinary.program,comp_run,DFTModelRecursiveBinary.loop_run]
  simp only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero]
  exact max_le (by omega) (binary_stages_peak k k I v before le_rfl)

attribute [local irreducible] DFTModelSavingBinarySuffix.program DFTModelSavingBinarySuffix.body

lemma suffix_stages_shape (b k j : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (DFTModelSavingBinarySuffix.stages b k I v j).val.1=2^(b+j) ∧
      (DFTModelSavingBinarySuffix.stages b k I v j).val.2.len ≤ v.len := by
  induction j with
  | zero=>exact ⟨by simp [DFTModelSavingBinarySuffix.stages,Bill.steps,Bill.one],le_rfl⟩
  | succ j ih=>
    change (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
      (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).val.1=_ ∧
      (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
      (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).val.2.len ≤ _
    rcases h:(DFTModelSavingBinarySuffix.stages b k I v j).val with ⟨P,bank⟩
    rw [h] at ih
    change P=2^(b+j) ∧ bank.len ≤ v.len at ih
    rw [DFTModelSavingBinarySuffix.body_run]
    simp only [Bill.pay]
    rw [DFTModelRecursiveBinary.body_value]
    refine ⟨?_,?_⟩
    · rw [ih.1,Nat.add_succ,Nat.pow_succ,Nat.mul_comm]
    · rw [DFTModelRecursiveBinary.next_len]
      have div:=Nat.div_mul_le_self bank.len 2
      omega

lemma suffix_stages_peak (b k j : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (cap : b+j ≤ k) :
    (DFTModelSavingBinarySuffix.stages b k I v j).peak ≤ 4*v.len+2*2^k+4 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have prior:=ih (by omega)
    have shape:=suffix_stages_shape b k j I v
    have flags:=DFTModelSavingShapeBinary.suffix_stages_boolean b k I v before j
    change max (max (DFTModelSavingBinarySuffix.stages b k I v j).peak
      (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
        (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).peak) (j+1) ≤ _
    rcases h:(DFTModelSavingBinarySuffix.stages b k I v j).val with ⟨P,bank⟩
    rw [h] at shape flags
    change P=2^(b+j) ∧ bank.len ≤ v.len at shape
    change Boolean bank at flags
    rw [DFTModelSavingBinarySuffix.body_run]
    simp only [Bill.pay,max_zero]
    have step:=binary_body_peak k j P I v bank flags
    have power:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show b+j ≤ k by omega)
    have bits:=DFTModelSavingBinary.bits_le_volume k
    have stepB : (run DFTModelRecursiveBinary.body (((k,I),v),(j,(P,bank)))).peak ≤ 4*v.len+2*2^k+4 := by
      apply step.trans
      rw [shape.1]
      omega
    exact max_le (max_le prior stepB) (by omega)

theorem suffix_peak (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (cap : b ≤ k) :
    (run DFTModelSavingBinarySuffix.program (b,((k,I),v))).peak ≤ 4*v.len+2*2^k+4 := by
  rw [DFTModelSavingBinarySuffix.program_run,DFTModelSavingBinarySuffix.tapeProgram,
    comp_run,DFTModelSavingBinarySuffix.loop_run]
  simp only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero]
  have power:=(DFTModelSavingBinarySuffix.power_peak b ((k,I),v)).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) cap)
  have bits:=DFTModelSavingBinary.bits_le_volume k
  exact max_le (max_le (by omega) (power.trans (by omega)))
    (suffix_stages_peak b k (k-b) I v before (by omega))

end
end ExactFourierCircuits.DFTModelSavingPeak
