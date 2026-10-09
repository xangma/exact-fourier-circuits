import UniformGlobalCalendarGeometry
import UniformCacheTimingControl

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarSelector
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

/-- Inputs6700..6705: strided ABI7 directory, stride, entry count, global tick,
fresh selection output, existing output count. All entries are scanned. -/
def boot : List Op := [.literal 6710 0,.literal 6711 1,.literal 6712 2,
  .literal 6713 6,.literal 6714 28,.literal 6715 0]
def readEntry : List Op := [.mul 6723 6715 6701,.add 6723 6700 6723,
  .getNat 6717 6723,.add 6716 6723 6713,.getNat 6718 6716]
def stop : List Op := [.add 6720 6717 6719]
def phase : List Op := [.sub 6721 6703 6717]
def emit : List Op := [.mul 6722 6705 6712,.add 6722 6704 6722,
  .putNat 6722 6723,.add 6722 6722 6711,.putNat 6722 6721,.add 6705 6705 6711]
def advance : List Op := [.add 6715 6715 6711]

/-- Thirty literal instructions. Output records are [actual ABI address,local phase]. -/
def program : Program := boot.map Op.code ++ [.branchLT 6715 6702 7 29] ++
  readEntry.map Op.code ++ [.branchLT 6710 6718 15 13,
  .natLiteral 6719 28,.jump 17,.natLiteral 6719 1,.jump 17] ++ stop.map Op.code ++
  [.branchLT 6703 6717 27 19,.branchLT 6703 6720 20 27] ++ phase.map Op.code ++
  emit.map Op.code ++ advance.map Op.code ++ [.jump 6,.halt]

lemma program_length : program.length = 30 := rfl
lemma boot_code : BlockAt boot program 0 := by
  intro i hi; change i < 6 at hi; interval_cases i <;> rfl
lemma readEntry_code : BlockAt readEntry program 7 := by
  intro i hi; change i < 5 at hi; interval_cases i <;> rfl
lemma stop_code : BlockAt stop program 17 := by
  intro i hi
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  rfl
lemma phase_code : BlockAt phase program 20 := by
  intro i hi
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  rfl
lemma emit_code : BlockAt emit program 21 := by
  intro i hi; change i < 6 at hi; interval_cases i <;> rfl
lemma advance_code : BlockAt advance program 27 := by
  intro i hi
  change i < 1 at hi
  have h : i = 0 := by omega
  subst i
  rfl
lemma code_6 : program[6]? = some (.branchLT 6715 6702 7 29) := rfl
lemma code_12 : program[12]? = some (.branchLT 6710 6718 15 13) := rfl
lemma code_13 : program[13]? = some (.natLiteral 6719 28) := rfl
lemma code_14 : program[14]? = some (.jump 17) := rfl
lemma code_15 : program[15]? = some (.natLiteral 6719 1) := rfl
lemma code_16 : program[16]? = some (.jump 17) := rfl
lemma code_18 : program[18]? = some (.branchLT 6703 6717 27 19) := rfl
lemma code_19 : program[19]? = some (.branchLT 6703 6720 20 27) := rfl
lemma code_28 : program[28]? = some (.jump 6) := rfl
lemma code_29 : program[29]? = some .halt := rfl

def duration (kind : ℕ) : ℕ := if kind = 0 then 28 else 1
def active (tick start kind : ℕ) : Prop := start ≤ tick ∧ tick < start + duration kind
instance (tick start kind : ℕ) : Decidable (active tick start kind) := inferInstanceAs (Decidable (_ ∧ _))

structure Header (D stride N tick O used j : ℕ) (s : State) : Prop where
  directory : s.natReg 6700 = D
  spacing : s.natReg 6701 = stride
  count : s.natReg 6702 = N
  tick : s.natReg 6703 = tick
  output : s.natReg 6704 = O
  used : s.natReg 6705 = used
  zero : s.natReg 6710 = 0
  one : s.natReg 6711 = 1
  two : s.natReg 6712 = 2
  six : s.natReg 6713 = 6
  twentyEight : s.natReg 6714 = 28
  index : s.natReg 6715 = j

lemma Header.pc {D stride N tick O used j : ℕ} {s : State}
    (h : Header D stride N tick O used j s) (pc : ℕ) :
    Header D stride N tick O used j (setPC s pc) :=
  ⟨h.directory,h.spacing,h.count,h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index⟩

structure Loaded (D stride N tick O used j start kind : ℕ) (s : State) : Prop
    extends Header D stride N tick O used j s where
  address : s.natReg 6723 = D + stride * j
  startReg : s.natReg 6717 = start
  kindReg : s.natReg 6718 = kind

lemma Loaded.pc {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Loaded D stride N tick O used j start kind s) (pc : ℕ) :
    Loaded D stride N tick O used j start kind (setPC s pc) :=
  ⟨h.toHeader.pc pc,h.address,h.startReg,h.kindReg⟩

lemma readEntry_loaded {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Header D stride N tick O used j s)
    (a : s.natHeap (D + stride * j) = some start)
    (b : s.natHeap (D + stride * j + 6) = some kind) :
    Loaded D stride N tick O used j start kind (applyBlock readEntry s) := by
  constructor
  · constructor <;> simp [readEntry,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,
      h.count,h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]
  all_goals simp [readEntry,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.index,h.six,
    a,b,Nat.mul_comm]

theorem readEntry_execution {n D stride N tick O used j start kind B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Header D stride N tick O used j s) (pc : s.pc = 7)
    (wb : WordBound B s) (code : 30 ≤ B) (fit : D + stride * j + 7 ≤ B)
    (startFit : start ≤ B) (kindFit : kind ≤ B)
    (a : s.natHeap (D + stride * j) = some start)
    (b : s.natHeap (D + stride * j + 6) = some kind) :
    BoundedRuns program n x B s 5 (applyBlock readEntry s) := by
  apply block_runs readEntry program 7 n B x s readEntry_code pc wb (by change 12 ≤ B; omega)
  · simp [readEntry,readable,Op.readable,Op.apply,writeNat,next,h.directory,h.spacing,h.index,h.six,
      a,b,Nat.mul_comm]
  · simp [readEntry,peak,Op.peak,Op.apply,writeNat,next,h.directory,h.spacing,h.index,h.six,
      a,b,Nat.mul_comm]
    omega

lemma duration_bound (kind : ℕ) : duration kind ≤ 28 := by unfold duration; split_ifs <;> omega

/-- Kind selection is three actual instructions, with ordinary28 and direct1. -/
theorem duration_execution {n D stride N tick O used j start kind B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Loaded D stride N tick O used j start kind s) (pc : s.pc = 12)
    (wb : WordBound B s) (code : 30 ≤ B) :
    BoundedRuns program n x B s 3 (setPC (writeNat s 6719 (duration kind)) 17) := by
  by_cases zero : kind = 0
  · have enterStep : step program n x s = .running (setPC s 13) := by
      simp [step,pc,code_12,h.zero,h.kindReg,zero,setPC]
    have enter := control_run program n B 13 x s wb (by omega) enterStep
    have literalStep : step program n x (setPC s 13) =
        .running (writeNat (setPC s 13) 6719 28) := by simp [step,code_13,setPC]
    have literal := (BoundedRuns.next enter.final_bound literalStep
      (BoundedRuns.refl (writeNat_bound B (setPC s 13) 6719 28 enter.final_bound (by change 14 ≤ B; omega) (by omega))))
    have jumpStep : step program n x (writeNat (setPC s 13) 6719 28) =
        .running (setPC (writeNat (setPC s 13) 6719 28) 17) := by simp [step,code_14,setPC,writeNat,next]
    have jump := control_run program n B 17 x _ literal.final_bound (by omega) jumpStep
    simpa [duration,zero,setPC,writeNat,next] using enter.trans (literal.trans jump)
  · have enterStep : step program n x s = .running (setPC s 15) := by
      simp [step,pc,code_12,h.zero,h.kindReg,show 0 < kind by omega,setPC]
    have enter := control_run program n B 15 x s wb (by omega) enterStep
    have literalStep : step program n x (setPC s 15) =
        .running (writeNat (setPC s 15) 6719 1) := by simp [step,code_15,setPC]
    have literal := (BoundedRuns.next enter.final_bound literalStep
      (BoundedRuns.refl (writeNat_bound B (setPC s 15) 6719 1 enter.final_bound (by change 16 ≤ B; omega) (by omega))))
    have jumpStep : step program n x (writeNat (setPC s 15) 6719 1) =
        .running (setPC (writeNat (setPC s 15) 6719 1) 17) := by simp [step,code_16,setPC,writeNat,next]
    have jump := control_run program n B 17 x _ literal.final_bound (by omega) jumpStep
    simpa [duration,zero,setPC,writeNat,next] using enter.trans (literal.trans jump)

lemma ordinary_phase (tick start : ℕ) (h : active tick start 0) :
    (tick - start) % 28 = tick - start := by
  simp only [active,duration,ite_true] at h
  exact Nat.mod_eq_of_lt (by omega)

lemma direct_phase (tick start kind : ℕ) (kindNe : kind ≠ 0) (h : active tick start kind) :
    tick - start = 0 := by
  simp only [active,duration,ite_eq_right kindNe] at h
  omega

end
end ExactFourierCircuits.UniformGlobalCalendarSelector
