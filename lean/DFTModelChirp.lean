import DFTModelPreparationCorrect
import UniformChirpTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirp
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w sc
abbrev Full := p Input (Ty.a sc)
abbrev Cell := p Full w

def double : Prog false Input w :=
  .comp (.fork (.atom .fst) (.atom (.lit 2))) (.atom (.int .mul))

def modulus : Prog false Cell w :=
  .comp (.comp (.atom .fst) (.atom .fst)) double

def index : Prog false Cell w :=
  .comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .div))

def quadratic : Prog false Cell w :=
  .comp (.fork index index) (.atom (.int .mul))

def residue : Prog false Cell w :=
  .comp (.fork quadratic modulus) (.atom (.int .mod))

def negative : Prog false Cell w :=
  .comp (.fork (.comp (.fork modulus residue) (.atom (.int .sub))) modulus)
    (.atom (.int .mod))

def exponent : Prog false Cell w :=
  .ifz (.comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .mod)))
    residue negative

def cell : Prog false Cell sc :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) exponent) (.atom .look)

def publishLength : Prog false Full w := .comp (.atom .fst) double

def publish : Prog false Full (Ty.a sc) := .tab publishLength cell

/-- Only one power-table construction, of length 2n, followed by constant-cost reads. -/
def program : Prog false Input (Ty.a sc) :=
  .comp (.fork (.atom .id)
    (.comp (.fork double (.atom .snd)) DFTModelPreparation.program)) publish

def address (n i : ℕ) : ℕ :=
  if i%2=0 then ((i/2)^2)%(2*n) else (2*n-((i/2)^2)%(2*n))%(2*n)

theorem double_run (n : ℕ) (z : ℂ) :
    run double (n,z) = ⟨2*n,5,max 2 (2*n),True⟩ := by
  simp [double, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word, Nat.mul_comm]

theorem cell_run (n i : ℕ) (z : ℂ) (v : Tape ℂ) :
    run cell (((n,z),v),i) = ⟨v.look (address n i) 0,
      if i%2=0 then 37 else 61, max 2 (max (2*n) ((i/2)^2)),True⟩ := by
  have hm := Nat.mod_le ((i/2)^2) (2*n)
  have hs := Nat.sub_le (2*n) (((i/2)^2)%(2*n))
  have hr := Nat.mod_le (2*n-((i/2)^2)%(2*n)) (2*n)
  have hj : i/2 ≤ (i/2)^2 := by nlinarith
  simp only [pow_two, Nat.mul_comm] at hm hs hr hj
  by_cases he : i%2=0
  · simp [cell, exponent, residue, quadratic, modulus, double, index,
      Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word,
      address, he, Ty.blank, pow_two, Nat.mul_comm]
    omega
  · simp [cell, exponent, residue, quadratic, modulus, double, index, negative,
      Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word,
      address, he, Ty.blank, pow_two, Nat.mul_comm]
    omega

attribute [local irreducible] double cell publishLength

theorem publishLength_run (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    run publishLength ((n,z),v) = ⟨2*n,7,max 2 (2*n),True⟩ := by
  unfold publishLength
  change ((Bill.one (n,z)).pass (run double)).pay 1 0 = _
  simp only [Bill.pass,Bill.one]
  rw [double_run]
  simp [Bill.pay]

theorem publish_run (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    run publish ((n,z),v) =
      (Bill.tab (2*n) sc.blank (fun i => run cell (((n,z),v),i))).pay 8 (max 2 (2*n)) := by
  change ((run publishLength ((n,z),v)).pass
    (fun l => Bill.tab l sc.blank (fun i => run cell (((n,z),v),i)))).pay 1 0 = _
  rw [publishLength_run]
  simp [Bill.pass, Bill.pay]
  constructor <;> omega

theorem publish_value (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run publish ((n,z),v)).val = Tape.tab (2*n) (fun i => v.look (address n i) 0) := by
  rw [publish_run]
  change (Bill.tab (2*n) sc.blank (fun i => run cell (((n,z),v),i))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 1
  funext i
  exact congrArg Bill.val (cell_run n i z v)

theorem publish_work (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run publish ((n,z),v)).work ≤ 130*n+10 := by
  rw [publish_run]
  change (Bill.tab (2*n) sc.blank (fun i => run cell (((n,z),v),i))).work+8 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑ i ∈ Finset.range (2*n), (run cell (((n,z),v),i)).work) ≤ 61*(2*n) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (2*n), 61 := Finset.sum_le_sum (fun i _ => by
        rw [cell_run]
        dsimp only [Bill.work]
        split <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem publish_valid (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (run publish ((n,z),v)).valid := by
  rw [publish_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro i _
  rw [cell_run]
  trivial

end
end ExactFourierCircuits.DFTModelChirp
