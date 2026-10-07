import SavingBudget

/- The paper's h=100 arithmetic budget, with exponentials retained symbolically.
   This verifies a proposed count formula, not an actual circuit or word. -/
namespace ExactFourierCircuits.ExplicitSeedBudget

def h : ℕ := 100
def v : ℕ := 161700
def degree : ℕ := 147731
def m : ℕ := 1000000
def invocations : ℕ := 3 * v ^ 2
def roles : ℕ := 1873807244643542670000
def roleBits : ℕ := 71
def paddedRoles : ℕ := 2361183241434822606848
def margin : ℕ := 6871402692000000
def residuals : ℕ := 2361183241427951204156000000
def pointwiseCalls : ℕ := 22486194194905980000000
def columns : ℕ := 2 * pointwiseCalls / margin + 1
def bits : ℕ := m * columns + roleBits
-- Keep the address exponent a parameter, preventing eager evaluation of 2^6544862999999.
def factor (n : ℕ) : ℕ := 2 ^ (n - 1)
def calls (n : ℕ) : ℕ := (residuals * columns + roleBits * paddedRoles + 2 * pointwiseCalls) * factor n
def ordinaryCalls (n : ℕ) : ℕ := (n + roleBits) * 2 ^ (n + roleBits - 1)

theorem parameter_formulas :
    v = Nat.choose h 3 ∧ degree = Nat.choose (h - 3) 3 + 3 * (h - 3) ∧
    m = h ^ 3 ∧ roles = 2 * v ^ 3 + invocations * (v * degree + h + 1) ∧
    margin = 2 * v ^ 3 - 2 * invocations * (h + 1) * h ∧
    pointwiseCalls = 3 * invocations * (4 * v * degree + 16 * v) := by
  norm_num [h, v, degree, m, roles, margin, pointwiseCalls, invocations, Nat.choose]

theorem padding : paddedRoles = 2 ^ roleBits ∧
    2 ^ (roleBits - 1) < roles ∧ roles ≤ paddedRoles := by
  norm_num [paddedRoles, roleBits, roles]

theorem residual_balance : residuals + margin = paddedRoles * m := by
  norm_num [residuals, margin, paddedRoles, m]

theorem columns_value : columns = 6544863 := by
  norm_num [columns, pointwiseCalls, margin]

theorem bits_value : bits = 6544863000071 := by
  rw [bits, columns_value]
  norm_num [m, roleBits]

theorem strict_margin : 2 * pointwiseCalls < margin * columns :=
  SavingBudget.floor_choice_saves (by norm_num [margin])

theorem saved_coefficient : margin * columns - 2 * pointwiseCalls = 847159236000000 := by
  rw [columns_value]
  norm_num [margin, pointwiseCalls]

theorem bits_at_least_two : 2 ≤ bits := by rw [bits_value]; norm_num

theorem ordinary_factorization (n : ℕ) (hn : 0 < n) :
    ordinaryCalls n = ((n + roleBits) * paddedRoles) * factor n := by
  have he := SavingBudget.tensor_axis_factorization n roleBits hn
  have hw := congrArg (fun W : ℕ => ((n + roleBits) * W) * factor n) padding.1
  exact he.trans hw.symm

/-- The proposed call formula is strictly below the ordinary tensor-axis budget. -/
theorem proposed_count_saves (n : ℕ) (hn : n = m * columns) : calls n < ordinaryCalls n := by
  have hp : 0 < n := by
    have hm : 0 < m * columns := by rw [columns_value]; norm_num [m]
    omega
  have hc := SavingBudget.factored_saving (r := roleBits) residual_balance
    (show 0 < factor n by unfold factor; positivity) strict_margin
  have hb : m * columns + roleBits = n + roleBits := by omega
  rw [hb] at hc
  change calls n < ((n + roleBits) * paddedRoles) * factor n at hc
  rw [← ordinary_factorization n hp] at hc
  exact hc

/-- Closed h=100 arithmetic instance; no astronomical power is evaluated. -/
theorem closed_proposed_count_saves : calls (m * columns) < ordinaryCalls (m * columns) :=
  proposed_count_saves (m * columns) rfl

end ExactFourierCircuits.ExplicitSeedBudget
