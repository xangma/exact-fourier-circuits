import DFTModelRecursiveScalarCore
import DFTModelClockControl

set_option autoImplicit false

/-! A concrete scalar record emitter for the saving-network bank. The old
bank is read-only during one charged whole-array tab. Runtime volume is
computed from its length and the fixed number of roles, not supplied free. -/
namespace ExactFourierCircuits.DFTModelRecursiveScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section

abbrev Row := p sc (p w (Ty.a Tagged))
abbrev Cell := p Row w

def rowSource : Prog false Row (Ty.a Tagged) := .comp (.atom .snd) (.atom .snd)
def source : Prog false Cell (Ty.a Tagged) := .comp (.atom .fst) rowSource
def volume : Prog false Cell w := .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def coefficient : Prog false Cell sc := .comp (.atom .fst) (.atom .fst)
def role : Prog false Cell w := .comp (.fork (.atom .snd) volume) (.atom (.int .div))
def test (d : ℕ) : Prog false Cell w :=
  .comp (.fork
    (.comp (.fork role (.atom (.lit d))) (.atom (.int .sub)))
    (.comp (.fork (.atom (.lit d)) role) (.atom (.int .sub)))) (.atom (.int .add))
def sourceIndex (s : ℕ) : Prog false Cell w :=
  .comp (.fork
    (.comp (.fork (.atom (.lit s)) volume) (.atom (.int .mul)))
    (.comp (.fork (.atom .snd) volume) (.atom (.int .mod)))) (.atom (.int .add))
def current : Prog false Cell Tagged := .comp (.fork source (.atom .snd)) (.atom .look)
def fromSource (s : ℕ) : Prog false Cell Tagged :=
  .comp (.fork source (sourceIndex s)) (.atom .look)
def update (s : ℕ) : Prog false Cell Tagged :=
  .comp (.fork coefficient (.fork current (fromSource s))) operation

def cell (d s : ℕ) : Prog false Cell Tagged := .ifz (test d) (update s) current

def rowLength : Prog false Row w := .comp rowSource (.atom .len)
def rows (d s : ℕ) : Prog false Row (Ty.a Tagged) := .tab rowLength (cell d s)

def setup (R : ℕ) (c : Fin 5) : Prog false DFTModelClockControl.Node Row :=
  .fork (DFTModelRecursiveScalarCore.coefficient c)
    (.fork
      (.comp (.fork (.comp (.atom .snd) (.atom .len)) (.atom (.lit R))) (.atom (.int .div)))
      (.atom .snd))
def program (R d s : ℕ) (c : Fin 5) :
    Prog false DFTModelClockControl.Node DFTModelClockControl.Node :=
  .fork (.atom .fst) (.comp (setup R c) (rows d s))

def result (d s V : ℕ) (c : ℂ) (v : Tape Tagged.T) (j : ℕ) : Tagged.T :=
  if j/V=d then updated c (v.look j Tagged.blank) (v.look (s*V+j%V) Tagged.blank)
  else v.look j Tagged.blank

theorem rowSource_run (c : ℂ) (V : ℕ) (v : Tape Tagged.T) :
    run rowSource (c,(V,v))=⟨v,3,0,True⟩ := by
  simp [rowSource,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem role_run (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run role ((c,(V,v)),j)=⟨j/V,9,j/V,True⟩ := by
  simp [role,volume,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.pass,Bill.pay,Bill.word]

theorem test_run (d : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run (test d) ((c,(V,v)),j)=
      ⟨j/V-d+(d-j/V),29,max d (j/V),True⟩ := by
  simp only [test,comp_run,fork_run,atom_run,Atom.run]
  simp only [atom_run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [role_run]
  simp only [and_true]
  apply congrArg (fun p => Bill.mk (j/V-d+(d-j/V)) 29 p True)
  simp only [max_zero]
  have h1 : j/V-d ≤ max d (j/V) := (Nat.sub_le _ _).trans (le_max_right _ _)
  have h2 : d-j/V ≤ max d (j/V) := (Nat.sub_le _ _).trans (le_max_left _ _)
  have h3 : j/V-d+(d-j/V) ≤ max d (j/V) := by omega
  rw [max_comm (j/V) d,max_eq_left h1,max_eq_left h2,max_self,max_eq_left h3]

theorem sourceIndex_run (s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run (sourceIndex s) ((c,(V,v)),j)=
      ⟨s*V+j%V,21,max s (s*V+j%V),True⟩ := by
  simp [sourceIndex,volume,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem current_run (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run current ((c,(V,v)),j)=⟨v.look j Tagged.blank,9,0,True⟩ := by
  simp [current,source,rowSource,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem fromSource_run (s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run (fromSource s) ((c,(V,v)),j)=
      ⟨v.look (s*V+j%V) Tagged.blank,29,max s (s*V+j%V),True⟩ := by
  simp only [fromSource,comp_run,fork_run]
  rw [sourceIndex_run]
  simp [source,rowSource,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem update_run (s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    run (update s) ((c,(V,v)),j)=
      ⟨updated c (v.look j Tagged.blank) (v.look (s*V+j%V) Tagged.blank),
       if (v.look j Tagged.blank).1=0 then 115 else 113,
       max (max s (s*V+j%V)) (if (v.look j Tagged.blank).1=0 then 0 else 1),True⟩ := by
  simp only [update,comp_run,fork_run]
  rw [current_run,fromSource_run]
  simp only [coefficient,atom_run,comp_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [operation_run]
  by_cases h:(v.look j Tagged.blank).1=0 <;> simp [h]

theorem cell_value (d s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    (run (cell d s) ((c,(V,v)),j)).val=result d s V c v j := by
  rw [cell,ifz_run,test_run]
  have h:(j/V-d+(d-j/V)=0)↔j/V=d := by omega
  simp only [Bill.pass,Bill.pay,h,result]
  split_ifs
  · rw [update_run]
  · rw [current_run]


theorem cell_valid (d s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    (run (cell d s) ((c,(V,v)),j)).valid := by
  rw [cell,ifz_run,test_run]
  have h : (j/V-d+(d-j/V)=0) ↔ j/V=d := by omega
  simp only [Bill.pass,Bill.pay,h,true_and]
  split_ifs
  · rw [update_run]; trivial
  · rw [current_run]; trivial

theorem cell_work_bound (d s : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T) :
    (run (cell d s) ((c,(V,v)),j)).work ≤ 145 := by
  rw [cell,ifz_run,test_run]
  have h : (j/V-d+(d-j/V)=0) ↔ j/V=d := by omega
  simp only [Bill.pass,Bill.pay,h]
  split_ifs
  · rw [update_run]
    split_ifs <;> norm_num
  · rw [current_run]; norm_num

theorem rowLength_run (c : ℂ) (V : ℕ) (v : Tape Tagged.T) :
    run rowLength (c,(V,v))=⟨v.len,5,v.len,True⟩ := by
  rw [rowLength,comp_run,rowSource_run]
  simp [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.word]

theorem tab_run {s t : Ty} (n : Prog false s w)
    (body : Prog false (p s w) t) (x : s.T) :
    run (.tab n body) x = ((run n x).pass (fun l =>
      Bill.tab l t.blank (fun j => run body (x,j)))).pay 1 0 := rfl

theorem rows_value (d s : ℕ) (c : ℂ) (V : ℕ) (v : Tape Tagged.T) :
    (run (rows d s) (c,(V,v))).val = Tape.tab v.len (result d s V c v) := by
  rw [rows,tab_run,rowLength_run]
  change (Bill.tab v.len Tagged.blank (fun j => run (cell d s) ((c,(V,v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab v.len) (funext (cell_value d s c V · v))

theorem rows_valid (d s : ℕ) (c : ℂ) (V : ℕ) (v : Tape Tagged.T) :
    (run (rows d s) (c,(V,v))).valid := by
  rw [rows,tab_run,rowLength_run]
  change True ∧ (Bill.tab v.len Tagged.blank (fun j => run (cell d s) ((c,(V,v)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _; exact cell_valid d s c V j v

theorem rows_work_bound (d s : ℕ) (c : ℂ) (V : ℕ) (v : Tape Tagged.T) :
    (run (rows d s) (c,(V,v))).work ≤ 8+149*v.len := by
  rw [rows,tab_run,rowLength_run]
  change 5+(Bill.tab v.len Tagged.blank (fun j => run (cell d s) ((c,(V,v)),j))).work+1 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (∑j ∈ Finset.range v.len,(run (cell d s) ((c,(V,v)),j)).work) ≤ 145*v.len := by
    calc
      _ ≤ ∑j ∈ Finset.range v.len,145 := Finset.sum_le_sum (fun j _ => cell_work_bound d s c V j v)
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem setup_run (R k : ℕ) (I : ℂ) (c : Fin 5) (v : Tape Tagged.T) :
    run (setup R c) ((k,I),v) =
      ⟨(UniformFixedCoefficientCodec.decode c,(v.len/R,v)),
        coefficientWork c+10,max R v.len,True⟩ := by
  simp only [setup,fork_run,comp_run,atom_run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [coefficient_run]
  simp [max_comm,Nat.div_le_self]

theorem program_value (R d s k : ℕ) (I : ℂ) (c : Fin 5) (v : Tape Tagged.T) :
    (run (program R d s c) ((k,I),v)).val =
      ((k,I),Tape.tab v.len (result d s (v.len/R) (UniformFixedCoefficientCodec.decode c) v)) := by
  rw [program,fork_run,comp_run,setup_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [rows_value]

theorem program_valid (R d s k : ℕ) (I : ℂ) (c : Fin 5) (v : Tape Tagged.T) :
    (run (program R d s c) ((k,I),v)).valid := by
  rw [program,fork_run,comp_run,setup_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and]
  exact ⟨rows_valid d s _ _ v,trivial⟩

theorem program_work_bound (R d s k : ℕ) (I : ℂ) (c : Fin 5) (v : Tape Tagged.T) :
    (run (program R d s c) ((k,I),v)).work ≤ 32+149*v.len := by
  rw [program,fork_run,comp_run,setup_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  have h := rows_work_bound d s (UniformFixedCoefficientCodec.decode c) (v.len/R) v
  have hc := coefficient_work_bound c
  omega


theorem cell_peak_bound (d s B : ℕ) (c : ℂ) (V j : ℕ) (v : Tape Tagged.T)
    (dest : d≤B) (src : s≤B) (roleFit : j/V≤B)
    (addressFit : s*V+j%V≤B) (one : 1≤B) :
    (run (cell d s) ((c,(V,v)),j)).peak≤B := by
  rw [cell,ifz_run,test_run]
  have h : (j/V-d+(d-j/V)=0) ↔ j/V=d := by omega
  simp only [Bill.pass,Bill.pay,h,max_zero]
  split_ifs
  · rw [update_run]
    split_ifs <;> simp only [max_zero, max_le_iff] <;> omega
  · rw [current_run]
    simp only [max_zero,max_le_iff]; exact ⟨dest,roleFit⟩

theorem rows_peak_bound (R d s V B : ℕ) (c : ℂ) (v : Tape Tagged.T)
    (positive : 0<V) (_roles : 0<R) (len : v.len=R*V)
    (dest : d<R) (src : s<R) (fit : R*V≤B) :
    (run (rows d s) (c,(V,v))).peak≤B := by
  rw [rows,tab_run,rowLength_run]
  change max (max v.len (Bill.tab v.len Tagged.blank
    (fun j => run (cell d s) ((c,(V,v)),j))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le (by omega) (max_le (by omega) ?_)
  apply Finset.sup_le
  intro j hj
  have jfit : j<R*V := by simpa [len] using Finset.mem_range.mp hj
  have rb : R≤R*V := by simpa using Nat.mul_le_mul_left R positive
  have roleFit : j/V<R := (Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.mul_comm] using jfit)
  have remFit := Nat.mod_lt j positive
  have mulFit : (s+1)*V≤R*V := Nat.mul_le_mul_right V (by omega)
  have addrFit : s*V+j%V<R*V := by nlinarith
  exact cell_peak_bound d s B c V j v (by omega) (by omega) (by omega) (by omega) (by omega)

theorem program_peak_bound (R d s k V B : ℕ) (I : ℂ) (c : Fin 5) (v : Tape Tagged.T)
    (positive : 0<V) (roles : 0<R) (len : v.len=R*V)
    (dest : d<R) (src : s<R) (fit : R*V≤B) :
    (run (program R d s c) ((k,I),v)).peak≤B := by
  have div : v.len/R=V := by rw [len,Nat.mul_div_cancel_left V roles]
  have rb : R≤R*V := by simpa using Nat.mul_le_mul_left R positive
  have hp := rows_peak_bound R d s V B (UniformFixedCoefficientCodec.decode c) v positive roles len dest src fit
  rw [program,fork_run,comp_run,setup_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,div]
  exact max_le (max_le (by omega) (by omega)) hp

end
end ExactFourierCircuits.DFTModelRecursiveScalar
