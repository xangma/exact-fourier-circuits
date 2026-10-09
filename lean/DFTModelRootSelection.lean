import DFTModelRootPrime

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM Ty
noncomputable section

abbrev selectionState : Ty := p w (p w w)
abbrev selectionPort : Port := some (selectionState, w)

def getN {r : Port} : Code false r selectionState w := .atom .fst
def getP {r : Port} : Code false r selectionState w := .comp (.atom .snd) (.atom .fst)
def getR {r : Port} : Code false r selectionState w := .comp (.atom .snd) (.atom .snd)
def nextP {r : Port} : Code false r selectionState w :=
  .comp (.fork getP (.atom (.lit 1))) (.atom (.int .add))
def newR {r : Port} : Code false r selectionState w :=
  .comp (.fork getR getP) (.atom (.int .mul))
def twiceN {r : Port} : Code false r selectionState w :=
  .comp (.fork (.atom (.lit 2)) getN) (.atom (.int .mul))
def tooBig {r : Port} : Code false r selectionState w :=
  .comp (.fork twiceN newR) (.atom (.int .lt))
def skipState {r : Port} : Code false r selectionState selectionState :=
  .fork getN (.fork nextP getR)
def acceptState {r : Port} : Code false r selectionState selectionState :=
  .fork getN (.fork nextP newR)
def checkPrime : Code false selectionPort selectionState w :=
  .comp getP (.importClosed prime)
def skipCall : Code false selectionPort selectionState w := .comp skipState .call
def acceptCall : Code false selectionPort selectionState w := .comp acceptState .call
def acceptOrStop : Code false selectionPort selectionState w := .ifz tooBig acceptCall getR
def selectionBody : Code false selectionPort selectionState w := .ifz checkPrime skipCall acceptOrStop
def selectionBase : Prog false selectionState w := .atom (.lit 0)

theorem checkPrime_run (h : Handler selectionPort) (n p R : ℕ) :
    checkPrime.run h (n, (p, R)) = (run prime p).pay 5 0 := by
  change (((Bill.one (p, R)).pass (fun x => Bill.one x.1)).pay 1 0 |>.pass
    (fun p => (run prime p).pay 1 0)).pay 1 0 = _
  simp [Bill.one, Bill.pass, Bill.pay, Nat.add_comm, Nat.add_left_comm]
  omega

theorem skipCall_run (h : Handler selectionPort) (n p R : ℕ) :
    skipCall.run h (n, (p, R)) = (h (n, (p + 1, R))).pay 15 (p + 1) := by
  simp [skipCall, skipState, getN, nextP, getP, getR, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, Nat.add_comm, Nat.add_left_comm,
    max_comm]
  omega

theorem acceptCall_run (h : Handler selectionPort) (n p R : ℕ) :
    acceptCall.run h (n, (p, R)) =
      (h (n, (p + 1, R * p))).pay 21 (max (p + 1) (R * p)) := by
  simp [acceptCall, acceptState, getN, nextP, newR, getP, getR, Code.run, Atom.run,
    NOp.run, Bill.word, Bill.one, Bill.pass, Bill.pay, Nat.add_comm, Nat.add_left_comm,
    max_assoc, max_comm]
  omega

theorem tooBig_run (h : Handler selectionPort) (n p R : ℕ) :
    tooBig.run h (n, (p, R)) =
      ⟨if 2 * n < R * p then 1 else 0, 17,
       max (max 2 (2 * n)) (max (R * p) (if 2 * n < R * p then 1 else 0)), True⟩ := by
  simp [tooBig, twiceN, newR, getN, getP, getR, Code.run, Atom.run, NOp.run,
    Bill.word, Bill.one, Bill.pass, Bill.pay, max_assoc]

theorem acceptOrStop_run (h : Handler selectionPort) (n p R : ℕ) :
    acceptOrStop.run h (n, (p, R)) =
      if 2 * n < R * p then ⟨R, 21, max 2 (max (2 * n) (R * p)), True⟩
      else (h (n, (p + 1, R * p))).pay 39
        (max 2 (max (2 * n) (max (R * p) (p + 1)))) := by
  change ((tooBig.run h (n, (p, R))).pass (fun x =>
    if x = 0 then acceptCall.run h (n, (p, R)) else getR.run h (n, (p, R)))).pay 1 0 = _
  rw [tooBig_run, acceptCall_run]
  by_cases hb : 2 * n < R * p <;>
    simp [getR, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay, hb,
      Nat.add_comm, max_assoc, max_comm, max_left_comm]
  all_goals omega

theorem selectionBody_run (h : Handler selectionPort) (n p R : ℕ) :
    selectionBody.run h (n, (p, R)) =
      (((run prime p).pay 5 0).pass (fun check =>
        if check = 0 then (h (n, (p + 1, R))).pay 15 (p + 1)
        else if 2 * n < R * p then ⟨R, 21, max 2 (max (2 * n) (R * p)), True⟩
        else (h (n, (p + 1, R * p))).pay 39
          (max 2 (max (2 * n) (max (R * p) (p + 1)))))).pay 1 0 := by
  change ((checkPrime.run h (n, (p, R))).pass (fun check =>
    if check = 0 then skipCall.run h (n, (p, R)) else acceptOrStop.run h (n, (p, R)))).pay 1 0 = _
  rw [checkPrime_run, skipCall_run, acceptOrStop_run]

def selectionAux (fuel n p R : ℕ) : Bill ℕ :=
  depthRun (selectionBase.run ()) (selectionBody.run) fuel (n, (p, R))

theorem selectionAux_zero (n p R : ℕ) : selectionAux 0 n p R = ⟨0, 2, 0, True⟩ := rfl

theorem selectionAux_step (fuel n p R : ℕ) :
    selectionAux (fuel + 1) n p R =
      ((((run prime p).pay 5 0).pass (fun check =>
        if check = 0 then (selectionAux fuel n (p + 1) R).pay 15 (p + 1)
        else if 2 * n < R * p then ⟨R, 21, max 2 (max (2 * n) (R * p)), True⟩
        else (selectionAux fuel n (p + 1) (R * p)).pay 39
          (max 2 (max (2 * n) (max (R * p) (p + 1)))))).pay 1 0).pay 1 (fuel + 1) := by
  change ((selectionBody.run (depthRun (selectionBase.run ()) selectionBody.run fuel)
    (n, (p, R))).pay 1 (fuel + 1)) = _
  rw [selectionBody_run]
  rfl


def selectedProduct (v : Option UniformWorkingPreparation.Prefix) : ℕ :=
  match v with
  | none => 0
  | some x => x.product

theorem loopCost_le_counted (p d f : ℕ) :
    UniformPrimeMachine.loopCost p d f ≤ (UniformWorkingPreparation.trialLoop p d f).cost + 1 := by
  induction f generalizing d with
  | zero => simp [UniformPrimeMachine.loopCost, UniformWorkingPreparation.trialLoop]
  | succ f ih =>
    by_cases hz : p % d = 0 <;>
      simp only [UniformPrimeMachine.loopCost, UniformWorkingPreparation.trialLoop, hz, ite_true, ite_false]
    · omega
    · have := ih (d + 1)
      omega

theorem totalCost_le_counted (p : ℕ) :
    UniformPrimeMachine.totalCost p ≤ (UniformWorkingPreparation.trialPrime p).cost + 5 := by
  have h := loopCost_le_counted p 2 (p - 2)
  by_cases hp : p < 2 <;>
    simp only [UniformPrimeMachine.totalCost, UniformWorkingPreparation.trialPrime, hp, ite_true, ite_false] <;> omega

theorem selectionAux_spec (n : ℕ) (hn : 0 < n) (p j R fuel P : ℕ)
    (hR : R ≤ 2 * n) (h2 : 2 ≤ P) (hf : fuel ≤ P) (hprod : 2 * n * (p + fuel) ≤ P) :
    (selectionAux fuel n p R).val = selectedProduct (UniformWorkingPreparation.selectLoop n p j R fuel).value ∧
    (selectionAux fuel n p R).work ≤ 6 * (UniformWorkingPreparation.selectLoop n p j R fuel).cost ∧
    (selectionAux fuel n p R).peak ≤ P ∧ (selectionAux fuel n p R).valid := by
  induction fuel generalizing p j R with
  | zero =>
    rw [selectionAux_zero]
    simp [selectedProduct, UniformWorkingPreparation.selectLoop]
  | succ f ih =>
    obtain ⟨pv, pw, pp, pd⟩ := prime_spec p
    have pc := totalCost_le_counted p
    have pwork : (run prime p).work ≤ 4 * (UniformWorkingPreparation.trialPrime p).cost + 20 := by omega
    have hsum : p + (f + 1) ≤ P := by
      have hm := Nat.mul_le_mul_right (p + (f + 1)) (show 1 ≤ 2 * n by omega)
      simp only [Nat.one_mul] at hm
      exact hm.trans hprod
    have hp : p ≤ P := by omega
    have ppeak : (run prime p).peak ≤ P := pp.trans (max_le h2 hp)
    have hnew : R * p ≤ P :=
      (Nat.mul_le_mul hR (show p ≤ p + (f + 1) by omega)).trans hprod
    have hn2 : 2 * n ≤ P := by
      have hm := Nat.mul_le_mul_left (2 * n) (show 1 ≤ p + (f + 1) by omega)
      simp only [Nat.mul_one] at hm
      exact hm.trans hprod
    have childProd : 2 * n * (p + 1 + f) ≤ P := by
      have he : p + 1 + f = p + (f + 1) := by omega
      rw [he]
      exact hprod
    rw [selectionAux_step]
    dsimp only [Bill.pass, Bill.pay]
    rw [pv]
    cases hc : (UniformWorkingPreparation.trialPrime p).value with
    | false =>
      obtain ⟨iv, iw, ip, id⟩ := ih (p + 1) j R hR (by omega) childProd
      simp only [UniformPrimeMachine.boolCode, hc, Bool.false_eq_true, ite_false,
        ite_true, Nat.max_zero,
        UniformWorkingPreparation.selectLoop]
      refine ⟨iv, by omega, ?_, ⟨pd, id⟩⟩
      exact max_le (max_le ppeak (max_le ip (by omega))) (by omega)
    | true =>
      by_cases hb : 2 * n < R * p
      · simp only [UniformPrimeMachine.boolCode, hc, ite_true, Nat.one_ne_zero, ite_false,
          hb, Nat.max_zero, UniformWorkingPreparation.selectLoop,
          selectedProduct]
        refine ⟨by trivial, by omega, ?_, ⟨pd, True.intro⟩⟩
        exact max_le (max_le ppeak (max_le h2 (max_le hn2 hnew))) (by omega)
      · obtain ⟨iv, iw, ip, id⟩ := ih (p + 1) (j + 1) (R * p) (by omega) (by omega) childProd
        simp only [UniformPrimeMachine.boolCode, hc, ite_true, Nat.one_ne_zero, ite_false,
          hb, Nat.max_zero, UniformWorkingPreparation.selectLoop]
        refine ⟨iv, by omega, ?_, ⟨pd, id⟩⟩
        exact max_le (max_le ppeak (max_le ip (max_le h2 (max_le hn2 (max_le hnew (by omega)))))) (by omega)

end
end ExactFourierCircuits.DFTModelRoot
