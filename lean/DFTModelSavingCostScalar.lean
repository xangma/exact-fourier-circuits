import DFTModelSavingScalar

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section

/-- Runtime coefficient decoding has fixed work, including malformed codes. -/
theorem scalar_decode_work (c : ℕ) :
    (run DFTModelSavingScalar.decode c).work≤40 := by
  simp only [DFTModelSavingScalar.decode,DFTModelSavingScalar.decodeTail,
    DFTModelRecursiveMetadata.predecessor,negative,half,two,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  by_cases h0:c=0 <;> by_cases h1:c-1=0 <;>
    by_cases h2:c-1-1=0 <;> by_cases h3:c-1-1-1=0 <;> simp_all

attribute [local irreducible] DFTModelSavingScalar.decode

theorem scalar_cell_work (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    (run DFTModelSavingScalar.cell ((c,((d,s),(V,v))),j)).work≤175 := by
  rw [DFTModelSavingScalar.cell,ifz_run,DFTModelSavingScalar.test_run]
  change 43+(if j/V-d+(d-j/V)=0 then
    run DFTModelSavingScalar.update ((c,((d,s),(V,v))),j)
    else run DFTModelSavingScalar.old ((c,((d,s),(V,v))),j)).work+1≤175
  split_ifs
  · rw [DFTModelSavingScalar.update_run]
    split_ifs <;> norm_num
  · rw [DFTModelSavingScalar.old_run]
    norm_num

attribute [local irreducible] DFTModelSavingScalar.cell

theorem scalar_rows_work (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    (run DFTModelSavingScalar.rows (c,((d,s),(V,v)))).work≤10+179*v.len := by
  rw [DFTModelSavingScalar.rows,DFTModelRecursiveScalar.tab_run,comp_run,
    DFTModelSavingScalar.source_run]
  change 7+(Bill.tab v.len Tagged.blank
    (fun j=>run DFTModelSavingScalar.cell ((c,((d,s),(V,v))),j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum : (∑j∈Finset.range v.len,
      (run DFTModelSavingScalar.cell ((c,((d,s),(V,v))),j)).work)≤175*v.len := by
    calc
      _≤∑j∈Finset.range v.len,175 := Finset.sum_le_sum (fun j _=>scalar_cell_work c d s V j v)
      _=_ := by simp [Nat.mul_comm]
  omega

attribute [local irreducible] DFTModelSavingScalar.rows

theorem scalar_setup_work (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (DFTModelSavingScalar.setup R) (raw,((k,I),v))).work≤80 := by
  have decode:=scalar_decode_work (raw.look 7 0)
  simp only [DFTModelSavingScalar.setup,comp_run,fork_run,DFTModelSavingScalar.field,
    DFTModelSavingScalar.bank,DFTModelSavingScalar.E.nat,atom_run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  omega

/-- One genuinely executed scalar record has linear whole-bank work, for
arbitrary tags and affine values; no supplied output contract is required. -/
theorem scalar_work (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (DFTModelSavingScalar.program R) (raw,((k,I),v))).work≤95+179*v.len := by
  rw [DFTModelSavingScalar.program,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  have setup:=scalar_setup_work R k I raw v
  have rows:=scalar_rows_work (run DFTModelSavingScalar.decode (raw.look 7 0)).val
    (raw.look 3 0) (raw.look 4 0) (v.len/R) v
  rw [DFTModelSavingScalar.setup_value]
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
