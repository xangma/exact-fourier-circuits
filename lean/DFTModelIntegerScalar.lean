import DFTModelPreparationCorrect
import UniformNormalizationMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelIntegerScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Convert the actual Nat input by charged scalar additions. -/
def increment : Prog false (p w (p w sc)) sc :=
  .comp (.fork (.comp (.atom .snd) (.atom .snd)) (.atom .cone))
    (.atom (.add .scalar))

def natural : Prog false w sc := .loop (.atom .id) (.atom (.cz .scalar)) increment

theorem increment_run (n i : ℕ) (z : ℂ) :
    run increment (n,(i,z)) = ⟨z+1,7,0,True⟩ := by
  simp [increment, run, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay]

attribute [local irreducible] increment

theorem steps_run (n k : ℕ) :
    Bill.steps (0 : ℂ) (fun i z => run increment (n,(i,z))) k =
      ⟨(k:ℂ),1+8*k,k,True⟩ := by
  induction k with
  | zero => simp [Bill.steps, Bill.one]
  | succ k ih =>
    rw [Bill.steps, ih]
    simp only [Bill.pass, Bill.pay]
    rw [increment_run]
    simp [Nat.cast_add, Nat.cast_one]
    omega

theorem natural_run (n : ℕ) : run natural n = ⟨(n:ℂ),8*n+4,n,True⟩ := by
  change ((Bill.one n).pass (fun k => (Bill.one (0:ℂ)).pass (fun z =>
    Bill.steps z (fun i v => run increment (n,(i,v))) k))).pay 1 0 = _
  simp [Bill.pass, Bill.one, Bill.pay, steps_run]
  omega

/-- The prepared reciprocal used by the real normalization source. -/
def reciprocal : Prog false w sc := .comp natural (.atom .inv)

theorem reciprocal_run (n : ℕ) :
    run reciprocal n = ⟨(n:ℂ)⁻¹,8*n+6,n,n≠0⟩ := by
  change ((run natural n).pass Atom.inv.run).pay 1 0 = _
  rw [natural_run]
  simp [Atom.run, Bill.pass, Bill.pay]

theorem reciprocal_contract (n : ℕ) (hn : 0<n) :
    (run reciprocal n).val = (n:ℂ)⁻¹ ∧ (run reciprocal n).valid ∧
    (run reciprocal n).work = 8*n+6 ∧ (run reciprocal n).peak = n := by
  rw [reciprocal_run]
  exact ⟨rfl,hn.ne',rfl,rfl⟩

/-- Equality to the scalar stored by the actual source normalization helper. -/
theorem normalization_source {n : ℕ} (x : Fin n → ℂ) (B L c : ℕ)
    (s : UniformMachine.State) (hp : s.pc=0) (h17 : s.natReg 17=L)
    (h27 : s.natReg 27=c) (hL : 0<L) (hB : 64≤B) (hs : UniformMachine.WordBound B s) :
    ∃u, UniformMachine.BoundedExecution UniformNormalizationMachine.program n x B s
      (UniformNormalizationMachine.runtime L) u ∧
      u.scalarHeap c = some (UniformPairMachine.prepared (run reciprocal L).val) := by
  obtain ⟨u,he,hv,_⟩ := UniformNormalizationMachine.normalization_execution x B L c s
    hp h17 h27 hL hB hs
  refine ⟨u,he,?_⟩
  simpa only [reciprocal_run] using hv

end
end ExactFourierCircuits.DFTModelIntegerScalar
