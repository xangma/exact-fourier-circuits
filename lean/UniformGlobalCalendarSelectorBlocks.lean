import UniformGlobalCalendarSelector

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarSelector
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

lemma Loaded.duration {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Loaded D stride N tick O used j start kind s) :
    Loaded D stride N tick O used j start kind (setPC (writeNat s 6719 (duration kind)) 17) := by
  constructor
  · constructor <;> simp [setPC,writeNat,next,h.directory,h.spacing,h.count,h.tick,h.output,
      h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]
  all_goals simp [setPC,writeNat,next,h.address,h.startReg,h.kindReg]

structure Stopped (D stride N tick O used j start kind : ℕ) (s : State) : Prop
    extends Loaded D stride N tick O used j start kind s where
  durationValue : s.natReg 6719 = duration kind
  stopValue : s.natReg 6720 = start + duration kind

lemma Stopped.pc {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Stopped D stride N tick O used j start kind s) (pc : ℕ) :
    Stopped D stride N tick O used j start kind (setPC s pc) :=
  ⟨h.toLoaded.pc pc,h.durationValue,h.stopValue⟩

lemma stop_stopped {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Loaded D stride N tick O used j start kind s) (dur : s.natReg 6719 = duration kind) :
    Stopped D stride N tick O used j start kind (applyBlock stop s) := by
  constructor
  · constructor
    · constructor <;> simp [stop,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.count,
        h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]
    all_goals simp [stop,applyBlock,Op.apply,writeNat,next,h.address,h.startReg,h.kindReg]
  all_goals simp [stop,applyBlock,Op.apply,writeNat,next,h.startReg,dur]

theorem stop_execution {n D stride N tick O used j start kind B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Loaded D stride N tick O used j start kind s)
    (dur : s.natReg 6719 = duration kind) (pc : s.pc = 17) (wb : WordBound B s)
    (code : 30 ≤ B) (fit : start + 28 ≤ B) :
    BoundedRuns program n x B s 1 (applyBlock stop s) := by
  apply block_runs stop program 17 n B x s stop_code pc wb (by change 18 ≤ B; omega)
  · simp [stop,readable,Op.readable]
  · have hb := duration_bound kind
    simp [stop,peak,Op.peak,h.startReg,dur]
    omega

lemma phase_stopped {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Stopped D stride N tick O used j start kind s) :
    Stopped D stride N tick O used j start kind (applyBlock phase s) := by
  constructor
  · constructor
    · constructor <;> simp [phase,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.count,
        h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]
    all_goals simp [phase,applyBlock,Op.apply,writeNat,next,h.address,h.startReg,h.kindReg]
  all_goals simp [phase,applyBlock,Op.apply,writeNat,next,h.durationValue,h.stopValue]

lemma phase_value {D stride N tick O used j start kind : ℕ} {s : State}
    (h : Stopped D stride N tick O used j start kind s) :
    (applyBlock phase s).natReg 6721 = tick - start := by
  simp [phase,applyBlock,Op.apply,writeNat,next,h.tick,h.startReg]

theorem phase_execution {n D stride N tick O used j start kind B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Stopped D stride N tick O used j start kind s)
    (pc : s.pc = 20) (wb : WordBound B s) (code : 30 ≤ B) :
    BoundedRuns program n x B s 1 (applyBlock phase s) := by
  apply block_runs phase program 20 n B x s phase_code pc wb (by change 21 ≤ B; omega)
  · simp [phase,readable,Op.readable]
  · have ht := wb.2.1 6703
    rw [h.tick] at ht
    simp [phase,peak,Op.peak,h.tick,h.startReg]
    omega

def storeSelection (O used address phase : ℕ) (heap : ℕ → Option ℕ) : ℕ → Option ℕ :=
  Function.update (Function.update heap (O + 2 * used) (some address))
    (O + 2 * used + 1) (some phase)

lemma emit_header {D stride N tick O used j : ℕ} {s : State}
    (h : Header D stride N tick O used j s) :
    Header D stride N tick O (used + 1) j (applyBlock emit s) := by
  constructor <;> simp [emit,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.count,
    h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]

lemma emit_heap {D stride N tick O used j start kind phaseValue : ℕ} {s : State}
    (h : Loaded D stride N tick O used j start kind s) (phase : s.natReg 6721 = phaseValue) :
    (applyBlock emit s).natHeap = storeSelection O used (D + stride * j) phaseValue s.natHeap := by
  simp [emit,applyBlock,Op.apply,writeNat,next,h.used,h.two,h.output,h.one,h.address,phase,
    storeSelection,Nat.mul_comm]

theorem emit_execution {n D stride N tick O used j B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Header D stride N tick O used j s)
    (pc : s.pc = 21) (wb : WordBound B s) (code : 30 ≤ B) (fit : O + 2 * (used + 1) ≤ B) :
    BoundedRuns program n x B s 6 (applyBlock emit s) := by
  apply block_runs emit program 21 n B x s emit_code pc wb (by change 27 ≤ B; omega)
  · simp [emit,readable,Op.readable]
  · have addr := wb.2.1 6723
    have phase := wb.2.1 6721
    simp [emit,peak,Op.peak,Op.apply,writeNat,next,h.used,h.two,h.output,h.one]
    omega

lemma advance_header {D stride N tick O used j : ℕ} {s : State}
    (h : Header D stride N tick O used j s) :
    Header D stride N tick O used (j + 1) (applyBlock advance s) := by
  constructor <;> simp [advance,applyBlock,Op.apply,writeNat,next,h.directory,h.spacing,h.count,
    h.tick,h.output,h.used,h.zero,h.one,h.two,h.six,h.twentyEight,h.index]

theorem advance_execution {n D stride N tick O used j B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Header D stride N tick O used j s)
    (pc : s.pc = 27) (wb : WordBound B s) (code : 30 ≤ B) (fit : j + 1 ≤ B) :
    BoundedRuns program n x B s 2 (setPC (applyBlock advance s) 6) := by
  have run := block_runs advance program 27 n B x s advance_code pc wb (by change 28 ≤ B; omega)
    (by simp [advance,readable,Op.readable]) (by simp [advance,peak,Op.peak,h.index,h.one];exact fit)
  have at28 : (applyBlock advance s).pc = 28 := by rw [applyBlock_pc,pc]; rfl
  have backStep : step program n x (applyBlock advance s) = .running (setPC (applyBlock advance s) 6) := by
    simp [step,at28,code_28,setPC]
  exact run.trans (control_run program n B 6 x _ run.final_bound (by omega) backStep)

end
end ExactFourierCircuits.UniformGlobalCalendarSelector
