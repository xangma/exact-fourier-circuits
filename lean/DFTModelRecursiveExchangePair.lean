import DFTModelRecursiveExchangeCore

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section

theorem rowLength_run (d s V : ℕ) (v : Tape Tagged.T) :
    run rowLength ((d,s),(V,v))=⟨v.len,5,v.len,True⟩ := by
  simp [rowLength,rowSource,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem rows_value (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows ((d,s),(V,v))).val=Tape.tab v.len (result d s V v) := by
  rw [rows,DFTModelRecursiveScalar.tab_run,rowLength_run]
  change (Bill.tab v.len Tagged.blank (fun j => run cell (((d,s),(V,v)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab v.len) (funext (fun j => cell_value d s V j v))

theorem rows_valid (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows ((d,s),(V,v))).valid := by
  rw [rows,DFTModelRecursiveScalar.tab_run,rowLength_run]
  change True ∧ (Bill.tab v.len Tagged.blank (fun j => run cell (((d,s),(V,v)),j))).valid
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _ => cell_valid d s V j v)⟩

theorem rows_work_bound (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows ((d,s),(V,v))).work≤8+131*v.len := by
  rw [rows,DFTModelRecursiveScalar.tab_run,rowLength_run]
  change 5+(Bill.tab v.len Tagged.blank (fun j => run cell (((d,s),(V,v)),j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (∑j ∈ Finset.range v.len,(run cell (((d,s),(V,v)),j)).work)≤127*v.len := by
    calc
      _≤∑j ∈ Finset.range v.len,127 := Finset.sum_le_sum (fun j _ => cell_work_bound d s V j v)
      _=_ := by simp [Nat.mul_comm]
  omega

theorem setup_run (R d s k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run (setup R) ((d,s),((k,I),v))=
      ⟨((d,s),(v.len/R,v)),15,max R v.len,True⟩ := by
  simp [setup,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    max_comm,Nat.div_le_self]

theorem pair_value (R d s k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run (pairProgram R) ((d,s),((k,I),v))).val=
      ((k,I),Tape.tab v.len (result d s (v.len/R) v)) := by
  simp only [pairProgram,fork_run,comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_run]
  dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid]
  rw [rows_value]

theorem pair_valid (R d s k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run (pairProgram R) ((d,s),((k,I),v))).valid := by
  simp only [pairProgram,fork_run,comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_run]
  simp only [true_and,and_true]
  exact rows_valid _ _ _ _

theorem pair_work_bound (R d s k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run (pairProgram R) ((d,s),((k,I),v))).work≤28+131*v.len := by
  simp only [pairProgram,fork_run,comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_run]
  dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid]
  have h := rows_work_bound d s (v.len/R) v
  omega

theorem pair_length (R d s k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run (pairProgram R) ((d,s),((k,I),v))).val.2.len=v.len := by
  rw [pair_value]
  rfl

theorem cell_peak_bound (d s V j B : ℕ) (v : Tape Tagged.T)
    (dest : d≤B) (src : s≤B) (role : j/V≤B)
    (firstAddress : d*V+j%V≤B) (secondAddress : s*V+j%V≤B) :
    (run cell (((d,s),(V,v)),j)).peak≤B := by
  have difference (a b : ℕ) (ha : a≤B) (hb : b≤B) : a-b+(b-a)≤B := by omega
  have df := max_le role (difference (j/V) d role dest)
  have sf := max_le role (difference (j/V) s role src)
  rw [cell,ifz_run,test_run first d s V j d v (first_run _ _ _ _ _)]
  simp only [Bill.pass,Bill.pay,max_zero]
  split_ifs
  · rw [readRole_run second d s V j s v (second_run _ _ _ _ _)]
    exact max_le df secondAddress
  · rw [ifz_run,test_run second d s V j s v (second_run _ _ _ _ _)]
    simp only [Bill.pass,Bill.pay,max_zero]
    split_ifs
    · rw [comp_run,readRole_run first d s V j d v (first_run _ _ _ _ _)]
      simp only [Bill.pass,Bill.pay]
      rw [negate_run]
      simp only [max_zero]
      exact max_le df (max_le sf firstAddress)
    · rw [current_run]
      simp only [max_zero]
      exact max_le df sf

theorem rows_peak_bound (R d s V B : ℕ) (v : Tape Tagged.T)
    (positive : 0<V) (len : v.len=R*V) (dest : d<R) (src : s<R) (fit : R*V≤B) :
    (run rows ((d,s),(V,v))).peak≤B := by
  rw [rows,DFTModelRecursiveScalar.tab_run,rowLength_run]
  change max (max v.len (Bill.tab v.len Tagged.blank
    (fun j => run cell (((d,s),(V,v)),j))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le (by omega) (max_le (by omega) ?_)
  apply Finset.sup_le
  intro j hj
  have jfit : j<R*V := by simpa [len] using Finset.mem_range.mp hj
  have rb : R≤R*V := by simpa using Nat.mul_le_mul_left R positive
  have rf : j/V<R := (Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.mul_comm] using jfit)
  have rem := Nat.mod_lt j positive
  have df := Nat.mul_le_mul_right V (show d+1≤R by omega)
  have sf := Nat.mul_le_mul_right V (show s+1≤R by omega)
  apply cell_peak_bound d s V j B v <;> nlinarith

theorem pair_peak_bound (R d s k V B : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (positive : 0<V) (roles : 0<R) (len : v.len=R*V)
    (dest : d<R) (src : s<R) (fit : R*V≤B) :
    (run (pairProgram R) ((d,s),((k,I),v))).peak≤B := by
  have div : v.len/R=V := by rw [len,Nat.mul_div_cancel_left V roles]
  have rb : R≤R*V := by simpa using Nat.mul_le_mul_left R positive
  have hp := rows_peak_bound R d s V B v positive len dest src fit
  simp only [pairProgram,fork_run,comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_run]
  simp only [zero_max,max_zero,div]
  exact max_le (max_le (by omega) (by omega)) hp

theorem result_paired {R V : ℕ} (d s : Fin R) (positive : 0<V)
    (f f0 : Fin R → Fin V → UniformMachine.Scalar) (i : Fin R) (j : Fin V) :
    result d.val s.val V (paired f f0) (i.val*V+j.val)=
      encodePaired (UniformFixedNetworkExchangeChildMachine.values d s f i j)
        (UniformFixedNetworkExchangeChildMachine.values d s f0 i j) := by
  have div : (i.val*V+j.val)/V=i.val := by
    rw [Nat.mul_comm i.val V,Nat.add_comm,Nat.add_mul_div_left _ _ positive,
      Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have rem : (i.val*V+j.val)%V=j.val := by
    rw [Nat.mul_comm i.val V,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  simp only [result,div,rem]
  by_cases hd : i=d
  · subst i
    simp only [ite_true,UniformFixedNetworkExchangeChildMachine.values]
    exact paired_lookup f f0 s j
  · have hd' : i.val≠d.val := fun eq => hd (Fin.ext eq)
    simp only [hd',ite_false,UniformFixedNetworkExchangeChildMachine.values,hd]
    by_cases hs : i=s
    · subst i
      simp only [ite_true]
      rw [paired_lookup]
      exact negated_paired _ _
    · have hs' : i.val≠s.val := fun eq => hs (Fin.ext eq)
      simp only [hs',hs,ite_false]
      exact paired_lookup f f0 i j

/-- Extensional equality includes the exact flags and both affine channels. -/
theorem tape_ext {α : Type} (z : α) {a b : Tape α} (len : a.len=b.len)
    (look : ∀i,a.look i z=b.look i z) : a=b := by
  cases a with
  | mk al ap =>
    cases b with
    | mk bl bp =>
      dsimp only at len
      subst bl
      congr 1
      funext i
      exact (Tape.look_of_lt _ z i.isLt).symm.trans ((look i.val).trans (Tape.look_of_lt _ z i.isLt))

theorem pair_paired {R V : ℕ} (d s : Fin R) (positive : 0<V)
    (f f0 : Fin R → Fin V → UniformMachine.Scalar) (k : ℕ) (I : ℂ) :
    (run (pairProgram R) ((d.val,s.val),((k,I),paired f f0))).val=
      ((k,I),paired (UniformFixedNetworkExchangeChildMachine.values d s f)
        (UniformFixedNetworkExchangeChildMachine.values d s f0)) := by
  rw [pair_value]
  have roles : 0<R := by have := d.isLt;omega
  have div : (paired f f0).len/R=V := Nat.mul_div_cancel_left V roles
  simp only [div]
  refine Prod.ext rfl ?_
  refine tape_ext Tagged.blank rfl ?_
  intro z
  by_cases hz : z<R*V
  · let ij := (finProdFinEquiv : Fin R×Fin V ≃ Fin (R*V)).symm ⟨z,hz⟩
    have ordinal : ij.1.val*V+ij.2.val=z := by
      have h := congrArg Fin.val ((finProdFinEquiv : Fin R×Fin V ≃ Fin (R*V)).apply_symm_apply ⟨z,hz⟩)
      simpa [ij,finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h
    rw [Tape.look_of_lt _ _ hz]
    change result d.val s.val V (paired f f0) z=_
    rw [←ordinal,paired_lookup]
    exact result_paired d s positive f f0 ij.1 ij.2
  · have hle : R*V≤z := by omega
    rw [Tape.look_of_le _ _ hle,Tape.look_of_le _ _ hle]

end
end ExactFourierCircuits.DFTModelRecursiveExchange
