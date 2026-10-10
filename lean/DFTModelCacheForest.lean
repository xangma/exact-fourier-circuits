import DFTModelCacheForestProduct

set_option autoImplicit false

/-! Closed prepared Newton rows. This bank has explicit typed fields
H, scale, inverseH, diagonal, inverseDiagonal; it is not the historical compact
five-lane bank, whose last lane stores a different reciprocal coefficient. -/
namespace ExactFourierCircuits.DFTModelCacheForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier NewtonFourier
noncomputable section

abbrev Row := p sc (p sc (p sc (p sc sc)))
abbrev Output := Ty.a Row
abbrev Cell := p Input w

def rowH : Prog false Product sc := .comp (.atom .snd) (.atom .fst)
def rowScale : Prog false Product sc := .comp (.atom .snd) (.atom .snd)
def inverseH : Prog false Product sc := .comp rowH (.atom .inv)
def diagonal : Prog false Product sc := scalar (.scale .scalar) rowH rowScale
def inverseDiagonal : Prog false Product sc := .comp diagonal (.atom .inv)
def finish : Prog false Product Row :=
  .fork rowH (.fork rowScale (.fork inverseH (.fork diagonal inverseDiagonal)))
def argument : Prog false Cell Input :=
  .fork (.atom .snd) (.comp (.atom .fst) (.atom .snd))
def cell : Prog false Cell Row := .comp argument (.comp product finish)

/-- Every row computes its products by the finite three-register loop and
inverts only H_j and H_j*scale_j. No prepared row is an input. -/
def program : Prog false Input Output := .tab (.atom .fst) cell

def row (omega : ℂ) (j : ℕ) : Row.T :=
  (NewtonFourier.H omega j,(NewtonFourier.scale omega j,
    ((NewtonFourier.H omega j)⁻¹,(UniformNewton.diagonalValue omega j,
      (UniformNewton.diagonalValue omega j)⁻¹))))
def values (r : ℕ) (omega : ℂ) : Tape Row.T := Tape.tab r (row omega)

theorem finish_run (p h s : ℂ) :
    run finish (p,(h,s))=
      ⟨(h,(s,(h⁻¹,(h*s,(h*s)⁻¹)))),35,0,h≠0 ∧ h*s≠0⟩ := by
  simp [finish,rowH,rowScale,inverseH,diagonal,inverseDiagonal,scalar,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem argument_run (r j : ℕ) (omega : ℂ) :
    run argument ((r,omega),j)=⟨(j,omega),5,0,True⟩ := by
  simp [argument,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] product finish argument

theorem cell_run (r j : ℕ) (omega : ℂ) :
    run cell ((r,omega),j)=
      ⟨row omega j,58*j+50,j,
        NewtonFourier.H omega j≠0 ∧ UniformNewton.diagonalValue omega j≠0⟩ := by
  change ((run argument ((r,omega),j)).pass
    (fun a => ((run product a).pass (run finish)).pay 1 0)).pay 1 0=_
  rw [argument_run]
  dsimp only [Bill.pass]
  rw [product_run,finish_run]
  simp [Bill.pay,row,UniformNewton.diagonalValue]
  omega

theorem program_run (r : ℕ) (omega : ℂ) :
    run program (r,omega)=
      (Bill.tab r Row.blank (fun j => run cell ((r,omega),j))).pay 2 0 := by
  change ((Bill.one r).pass (fun n =>
    Bill.tab n Row.blank (fun j => run cell ((r,omega),j)))).pay 1 0=_
  simp [Bill.one,Bill.pass,Bill.pay]
  omega

theorem program_value (r : ℕ) (omega : ℂ) :
    (run program (r,omega)).val=values r omega := by
  rw [program_run]
  change (Bill.tab r Row.blank (fun j => run cell ((r,omega),j))).val=values r omega
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab r)
  funext j
  exact congrArg Bill.val (cell_run r j omega)

theorem program_length (r : ℕ) (omega : ℂ) :
    (run program (r,omega)).val.len=r := by rw [program_value];rfl

theorem program_lookup (r : ℕ) (omega : ℂ) (j : Fin r) :
    (run program (r,omega)).val.look j.val Row.blank=row omega j.val := by
  rw [program_value,Tape.look_of_lt _ _ j.isLt]
  rfl

theorem program_valid {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) : (run program (r,omega)).valid := by
  rw [program_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j hj
  rw [cell_run]
  exact ⟨UniformNewton.Hvalue_ne_zero primitive ⟨j,hj⟩,
    UniformNewton.diagonalValue_ne_zero hr primitive ⟨j,hj⟩⟩

theorem program_work (r : ℕ) (omega : ℂ) :
    (run program (r,omega)).work≤60*(r+1)^2 := by
  rw [program_run]
  change (Bill.tab r Row.blank (fun j => run cell ((r,omega),j))).work+2≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have bound : (∑j∈Finset.range r,(run cell ((r,omega),j)).work)≤r*(58*r+50) := by
    calc
      _≤∑_j∈Finset.range r,(58*r+50) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [cell_run]
        have h := Finset.mem_range.mp hj
        dsimp only [Bill.work]
        omega
      _=_ := by simp [Nat.mul_comm]
  nlinarith

theorem program_peak (r : ℕ) (omega : ℂ) : (run program (r,omega)).peak≤r := by
  rw [program_run]
  change max (Bill.tab r Row.blank (fun j => run cell ((r,omega),j))).peak 0≤r
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le le_rfl ?_) (Nat.zero_le _)
  apply Finset.sup_le
  intro j hj
  rw [cell_run]
  exact (Finset.mem_range.mp hj).le

/-- The root's primitivity is an ordinary entry condition; the product and
reciprocal tables are generated internally by the actual typed program. -/
theorem specification {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) :
    (run program (r,omega)).val=values r omega ∧
    (run program (r,omega)).valid ∧
    (run program (r,omega)).work≤60*(r+1)^2 ∧
    (run program (r,omega)).peak≤r :=
  ⟨program_value r omega,program_valid hr primitive,program_work r omega,program_peak r omega⟩

end
end ExactFourierCircuits.DFTModelCacheForest
