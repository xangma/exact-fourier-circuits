import DFTModelCostBounds
import UniformFinalDFTExecution

set_option autoImplicit false

/-! Introduction of the upstream DFT contract from an explicit computational
translation certificate for our actual fixed twenty-stage program. This is a
conditional adapter, not a proof that a compiler certificate already exists.
No independent upstream DFT-existence theorem is imported or combined here. -/
namespace ExactFourierCircuits.DFTModelCost
open UniformMachine OAI.PowerSaving.RAM
open Filter Asymptotics
noncomputable section

local notation "c" => UniformActualGlobalConstants.constants
local notation "sourceCost" => UniformFinalLinearTableCost.finalBudget c UniformRecursiveSelfCallMachine.W
local notation "paperCost" => UniformMachine.asymptoticCost UniformExponent.theta

abbrev OrderProgram := Prog false .w .w
abbrev SolveProgram := Prog false OAI.PowerSaving.dftInKind OAI.PowerSaving.dftOutKind

def sourceDegree : ℕ := UniformJointAllocation.degree c
def sourceWordCap (n : ℕ) : ℕ := (n+2)^sourceDegree

def orderBill (order : OrderProgram) (n : ℕ) := run order n

def solveBill (order : OrderProgram) (solve : SolveProgram) (n : ℕ) (x : Fin n → ℂ) :=
  run solve (n,OAI.PowerSaving.root (orderBill order n).val,(⟨n,x⟩ : OAI.PowerSaving.Tape ℂ))

/-- A natural count of charged operations in actual translated-program runs,
including exactly one root provision. It is not a rounded real estimate or a
fuel supplied by an asymptotic oracle. -/
def measuredWork (order : OrderProgram) (solve : SolveProgram) (n : ℕ) : ℕ :=
  (orderBill order n).work+1+(solveBill order solve n (fun _ => 0)).work

def outputTape (n : ℕ) (u : State) : OAI.PowerSaving.Tape ℂ :=
  ⟨n,fun i => (u.outputs i.val).getD 0⟩

/-- These are concrete computational obligations for a same-program
translation. In particular `execution` maps runs of the named source program,
not arbitrary DFT-correct outputs, and charges the source instruction count.
The certificate must be proved by compiler/memory/control-flow lemmas; this
structure itself is not a compiler or an equivalence theorem. -/
structure ComputationalPremises (order : OrderProgram) (solve : SolveProgram)
    (C spaceDegree : ℕ) : Prop where
  order_value : ∀ n, 0<n → (orderBill order n).val = UniformMasterRootMachine.order n
  order_valid : ∀ n, 0<n → (orderBill order n).valid
  order_peak : ∀ n, 0<n → (orderBill order n).peak ≤ (n+2)^spaceDegree
  uniform_work : ∀ n, 0<n → ∀ x : Fin n → ℂ,
    (solveBill order solve n x).work ≤ (solveBill order solve n (fun _ => 0)).work
  execution : ∀ n, 0<n → ∀ x : Fin n → ℂ, ∀ ticks u,
    BoundedExecution UniformFinalOuterProgram.program n x (sourceWordCap n) initial ticks u →
    (solveBill order solve n x).valid ∧
    (solveBill order solve n x).peak ≤ (n+2)^spaceDegree ∧
    (solveBill order solve n x).val = outputTape n u ∧
    (orderBill order n).work+1+(solveBill order solve n x).work ≤ C*ticks+C*(n+1)

/-- The source side is the existing unconditional operational theorem, with
its original polynomial degree; no source-execution callback is assumed. -/
theorem actual_source_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃ ticks u,
      BoundedExecution UniformFinalOuterProgram.program n x (sourceWordCap n) initial ticks u ∧
      ComputesDFT n x u ∧ u.rootOrders=[UniformMasterRootMachine.order n] ∧
      (ticks : ℝ) ≤ sourceCost n := by
  obtain ⟨ticks,u,execution,answer,roots,cheap⟩ := UniformFinalDFTExecution.execution hn x
  refine ⟨ticks,u,?_,answer,roots,cheap⟩
  exact UniformGlobalEnvelope.execution_mono execution (UniformJointAllocation.polynomial c hn)

theorem outputTape_dft {n : ℕ} {x : Fin n → ℂ} {u : State}
    (answer : ComputesDFT n x u) : outputTape n u = ⟨n,OAI.PowerSaving.dft n x⟩ := by
  unfold outputTape
  congr 1
  funext j
  rw [answer j]
  rfl

/-- Transport the actual instruction-count bound to the natural allowance
measured in the translated programs. Only the compiler certificate is open. -/
theorem measured_majorant {order : OrderProgram} {solve : SolveProgram} {C space : ℕ}
    (mapping : ComputationalPremises order solve C space) :
    ∀ n, 0<n → (measuredWork order solve n : ℝ) ≤
      (C : ℝ)*sourceCost n+(C : ℝ)*((n : ℝ)+1) := by
  intro n hn
  obtain ⟨ticks,u,execution,_,_,cheap⟩ := actual_source_execution hn (fun _ => 0)
  have simulated := (mapping.execution n hn (fun _ => 0) ticks u execution).2.2.2
  have counted : (measuredWork order solve n : ℝ) ≤ (C : ℝ)*(ticks : ℝ)+(C : ℝ)*((n : ℝ)+1) := by
    exact_mod_cast simulated
  exact counted.trans (add_le_add (mul_le_mul_of_nonneg_left cheap (Nat.cast_nonneg C)) le_rfl)

theorem measured_isBigO {order : OrderProgram} {solve : SolveProgram} {C space : ℕ}
    (mapping : ComputationalPremises order solve C space) :
    (fun n => (measuredWork order solve n : ℝ)) =O[atTop] paperCost :=
  transfer _ C (measured_majorant mapping)

theorem measured_timeBounds {order : OrderProgram} {solve : SolveProgram} {C space : ℕ}
    (mapping : ComputationalPremises order solve C space) :
    OAI.PowerSaving.TimeBounds (measuredWork order solve) :=
  timeBounds _ (measured_isBigO mapping)

/-- The exact upstream DFTProgram contract, for the supplied translated code
and our same single-root recipe. The larger target degree accounts for both
translated register peaks and charged work/allocation; the source degree and
source execution are unchanged. -/
theorem dftProgram {order : OrderProgram} {solve : SolveProgram} {C space : ℕ}
    (mapping : ComputationalPremises order solve C space) :
    OAI.PowerSaving.DFTProgram order solve (measuredWork order solve) := by
  obtain ⟨workDegree,workBound⟩ := work_polynomial (measuredWork order solve)
    ((measured_isBigO mapping).trans paper_isBigO_square)
  let degree := max workDegree (max space sourceDegree)
  refine ⟨degree,fun n hn => ?_⟩
  have raise (d : ℕ) (hd : d ≤ degree) : (n+2)^d ≤ (n+2)^degree :=
    Nat.pow_le_pow_right (by omega : 1≤n+2) hd
  have workCap := (workBound n hn).trans (raise workDegree (le_max_left _ _))
  have spaceCap := raise space ((le_max_left space sourceDegree).trans (le_max_right _ _))
  have sourceCap := raise sourceDegree ((le_max_right space sourceDegree).trans (le_max_right _ _))
  obtain ⟨ticks,u,source,_,roots,_⟩ := actual_source_execution hn (fun _ => 0)
  have rootCap : UniformMasterRootMachine.order n ≤ sourceWordCap n :=
    source.final_bound.2.2.2.2.2 _ (by rw [roots];simp)
  have orderValue := mapping.order_value n hn
  refine ⟨workCap,(mapping.order_peak n hn).trans spaceCap,mapping.order_valid n hn,
    ?_,?_,?_,?_⟩
  · exact orderValue ▸ (UniformMasterRootMachine.order_bounds hn).1
  · exact orderValue ▸ (UniformMasterRootMachine.order_bounds hn).2
  · exact orderValue ▸ rootCap.trans sourceCap
  · intro x
    obtain ⟨ticks,u,execution,answer,_,_⟩ := actual_source_execution hn x
    obtain ⟨valid,peak,value,_⟩ := mapping.execution n hn x ticks u execution
    refine ⟨valid,peak.trans spaceCap,?_,value.trans (outputTape_dft answer)⟩
    exact Nat.add_le_add_left (mapping.uniform_work n hn x) _

/-- Conditional same-program bridge, with the programs and measured work
fixed by the caller's computational certificate. No independent upstream
algorithm-existence result is used. -/
theorem contract {order : OrderProgram} {solve : SolveProgram} {C space : ℕ}
    (mapping : ComputationalPremises order solve C space) :
    OAI.PowerSaving.DFTProgram order solve (measuredWork order solve) ∧
    OAI.PowerSaving.TimeBounds (measuredWork order solve) :=
  ⟨dftProgram mapping,measured_timeBounds mapping⟩

end
end ExactFourierCircuits.DFTModelCost
