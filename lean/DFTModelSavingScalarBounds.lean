import DFTModelSavingScalar

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section

/-- The decoder is total; every reciprocal it executes is the prepared 2. -/
theorem decode_bounds (n : ℕ) :
    (run decode n).valid ∧ (run decode n).work≤40 ∧ (run decode n).peak≤ max 1 n := by
  rcases n with _|n
  · norm_num [decode,negative,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rcases n with _|n
  · norm_num [decode,decodeTail,DFTModelRecursiveMetadata.predecessor,half,two,negative,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rcases n with _|n
  · norm_num [decode,decodeTail,DFTModelRecursiveMetadata.predecessor,half,two,negative,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rcases n with _|n
  · norm_num [decode,decodeTail,DFTModelRecursiveMetadata.predecessor,half,two,negative,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  · simp [decode,decodeTail,DFTModelRecursiveMetadata.predecessor,half,two,negative,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
      Nat.add_assoc]

theorem cell_valid (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell ((c,((d,s),(V,v))),j)).valid := by
  rw [cell,ifz_run,test_run]
  simp only [Bill.pass,Bill.pay,true_and]
  split_ifs
  · rw [update_run];trivial
  · rw [old_run];trivial

theorem cell_work (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell ((c,((d,s),(V,v))),j)).work≤175 := by
  rw [cell,ifz_run,test_run]
  simp only [Bill.pass,Bill.pay]
  split_ifs
  · rw [update_run];split_ifs <;> norm_num
  · rw [old_run];norm_num

attribute [local irreducible] cell

theorem length_run (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    run (.comp source (.atom .len)) (c,((d,s),(V,v)))=⟨v.len,7,v.len,True⟩ := by
  rw [comp_run,source_run]
  simp [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.word]

theorem rows_valid (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows (c,((d,s),(V,v)))).valid := by
  rw [rows,DFTModelRecursiveScalar.tab_run,length_run]
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _;exact cell_valid c d s V j v

theorem rows_work (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows (c,((d,s),(V,v)))).work≤10+179*v.len := by
  rw [rows,DFTModelRecursiveScalar.tab_run,length_run]
  change 7+(Bill.tab v.len Tagged.blank (fun j=>run cell ((c,((d,s),(V,v))),j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (∑j∈Finset.range v.len,(run cell ((c,((d,s),(V,v))),j)).work)≤175*v.len := by
    calc
      _≤∑j∈Finset.range v.len,175:=Finset.sum_le_sum (fun j _=>cell_work c d s V j v)
      _=_:=by simp [Nat.mul_comm]
  omega

attribute [local irreducible] rows decode

theorem setup_run (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    run (setup R) (raw,((k,I),v))=
      ⟨((run decode (raw.look 7 0)).val,((raw.look 3 0,raw.look 4 0),(v.len/R,v))),
        (run decode (raw.look 7 0)).work+32,
        max 7 (max (run decode (raw.look 7 0)).peak (max R (max v.len (v.len/R)))),
        (run decode (raw.look 7 0)).valid⟩ := by
  simp only [setup,fork_run,comp_run,field,bank,E.nat,atom_run,Atom.run,
    NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,true_and,and_true,
    max_zero,zero_max]
  congr 1
  · omega
  · omega

theorem program_valid (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (program R) (raw,((k,I),v))).valid := by
  rw [program,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,true_and,and_true]
  rw [setup_run]
  exact ⟨(decode_bounds _).1,rows_valid _ _ _ _ _⟩

theorem program_work (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (program R) (raw,((k,I),v))).work≤92+179*v.len := by
  rw [program,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_run]
  have dh:=(decode_bounds (raw.look 7 0)).2.1
  have rh:=rows_work (run decode (raw.look 7 0)).val (raw.look 3 0)
    (raw.look 4 0) (v.len/R) v
  dsimp only [Bill.work,Bill.val] at *
  omega


theorem cell_peak (c : ℂ) (d s V j B : ℕ) (v : Tape Tagged.T)
    (dest : d≤B) (roleFit : j/V≤B) (addressFit : s*V+j%V≤B) (one : 1≤B) :
    (run cell ((c,((d,s),(V,v))),j)).peak≤B := by
  have diff:j/V-d+(d-j/V)≤B := by
    by_cases h:j/V≤d
    · rw [Nat.sub_eq_zero_of_le h,Nat.zero_add]
      exact (Nat.sub_le d _).trans dest
    · rw [Nat.sub_eq_zero_of_le (by omega : d≤j/V),Nat.add_zero]
      exact (Nat.sub_le (j/V) _).trans roleFit
  rw [cell,ifz_run,test_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  split_ifs
  · rw [update_run];split_ifs <;> simp only [max_zero] <;> omega
  · rw [old_run];simp only [max_zero];omega

theorem rows_peak (R V d s B : ℕ) (c : ℂ) (v : Tape Tagged.T)
    (positive : 0<V) (_roles : 0<R) (len : v.len=R*V)
    (dest : d<R) (src : s<R) (fit : R*V≤B) :
    (run rows (c,((d,s),(V,v)))).peak≤B := by
  rw [rows,DFTModelRecursiveScalar.tab_run,length_run]
  change max (max v.len (Bill.tab v.len Tagged.blank
    (fun j=>run cell ((c,((d,s),(V,v))),j))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le (by omega) (max_le (by omega) ?_)
  apply Finset.sup_le
  intro j hj
  have jfit:j<R*V:=by simpa [len] using Finset.mem_range.mp hj
  have rb:R≤R*V:=by simpa using Nat.mul_le_mul_left R positive
  have rfit:j/V<R:=(Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.mul_comm] using jfit)
  have remFit:=Nat.mod_lt j positive
  have mulFit:(s+1)*V≤R*V:=Nat.mul_le_mul_right V (by omega)
  have addrFit:s*V+j%V<R*V:=by nlinarith
  exact cell_peak c d s V j B v (by omega) (by omega) (by omega) (by omega)

theorem program_peak (R V d s k B : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T)
    (positive : 0<V) (roles : 0<R) (len : v.len=R*V)
    (dest : d<R) (src : s<R) (fit : R*V≤B) (seven : 7≤B)
    (hd : raw.look 3 0=d) (hs : raw.look 4 0=s) (code : raw.look 7 0≤4) :
    (run (program R) (raw,((k,I),v))).peak≤B := by
  have div:v.len/R=V:=by rw [len,Nat.mul_div_cancel_left V roles]
  have rb:R≤R*V:=by simpa using Nat.mul_le_mul_left R positive
  have dec:=(decode_bounds (raw.look 7 0)).2.2
  have hp:=rows_peak R V d s B (run decode (raw.look 7 0)).val v positive roles len dest src fit
  rw [program,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
  rw [setup_run]
  dsimp only [Bill.peak,Bill.val]
  simp only [hd,hs,div]
  have lenB:v.len≤B:=by omega
  have divB:v.len/R≤B:=(Nat.div_le_self _ _).trans lenB
  have decB:(run decode (raw.look 7 0)).peak≤B:=by omega
  omega

end
end ExactFourierCircuits.DFTModelSavingScalar
