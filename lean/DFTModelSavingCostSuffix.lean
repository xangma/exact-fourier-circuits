import DFTModelSavingBinarySuffixBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelSavingBinarySuffix.program DFTModelSavingBinarySuffix.body
  DFTModelRecursiveBinary.body

/-- Billing uses the actual bank length, irrespective of its output tags. -/
theorem suffix_stages_length (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) (j : ℕ) :
    (DFTModelSavingBinarySuffix.stages b k I v j).val.2.len=v.len := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
      (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).val.2.len=_
    rcases he : (DFTModelSavingBinarySuffix.stages b k I v j).val with ⟨P,bank⟩
    rw [he] at ih
    rw [DFTModelSavingBinarySuffix.body_run]
    simp only [Bill.pay]
    rw [DFTModelRecursiveBinary.body_value,DFTModelRecursiveBinary.next_len,ih,even]

theorem suffix_stages_work (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) (j : ℕ) :
    (DFTModelSavingBinarySuffix.stages b k I v j).work=1+j*(420*(v.len/2)+123) := by
  induction j with
  | zero => simp only [DFTModelSavingBinarySuffix.stages,Bill.steps,Bill.one,Nat.zero_mul,Nat.add_zero]
  | succ j ih =>
    have len:=suffix_stages_length b k I v even j
    change (DFTModelSavingBinarySuffix.stages b k I v j).work+
      (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
        (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).work+1=_
    rcases he : (DFTModelSavingBinarySuffix.stages b k I v j).val with ⟨P,bank⟩
    rw [he] at len
    rw [ih,DFTModelSavingBinarySuffix.body_run]
    simp only [Bill.pay]
    rw [DFTModelRecursiveBinary.body_work,len]
    ring

theorem suffix_work (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (run DFTModelSavingBinarySuffix.program (b,((k,I),v))).work=
      25+8*b+(k-b)*(420*(v.len/2)+123) := by
  rw [DFTModelSavingBinarySuffix.program_run,DFTModelSavingBinarySuffix.tapeProgram,
    comp_run,DFTModelSavingBinarySuffix.loop_run]
  simp only [Bill.pass,Bill.pay,atom_run,Atom.run,Bill.one]
  rw [suffix_stages_work b k I v even]
  ring

/-- The small branch retains its genuine ordinary implementation and fixed
threshold allowance; only the actual tape parity is needed for billing. -/
theorem ordinary_work (k threshold : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) (small : k<threshold) :
    (run DFTModelRecursiveBinary.program ((k,I),v)).work≤
      (537*threshold+10)*(v.len+1) :=
  DFTModelRecursiveBinary.base_work_bound k threshold I v even small

end
end ExactFourierCircuits.DFTModelSavingCost
