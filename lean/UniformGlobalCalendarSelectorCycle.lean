import UniformGlobalCalendarSelectorBlocks

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarSelector
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

/-- One genuine ABI entry is always inspected. Active entries append their
actual address and phase; inactive entries preserve the output heap. -/
theorem cycle {n D stride N tick O used j start kind B : ℕ} (x : Fin n → ℂ)
    (s : State) (h : Header D stride N tick O used j s) (pc : s.pc = 6)
    (wb : WordBound B s) (code : 30 ≤ B) (index : j < N)
    (sourceFit : D + stride * j + 7 ≤ B) (timeFit : start + 28 ≤ B)
    (kindFit : kind ≤ B) (outputFit : O + 2 * (used + 1) ≤ B)
    (a : s.natHeap (D + stride * j) = some start)
    (b : s.natHeap (D + stride * j + 6) = some kind) :
    ∃ (ticks : ℕ) (u : State),
      BoundedRuns program n x B s ticks u ∧ ticks ≤ 21 ∧ u.pc = 6 ∧
      Header D stride N tick O (if active tick start kind then used + 1 else used) (j + 1) u ∧
      u.natHeap = if active tick start kind then
        storeSelection O used (D + stride * j) (tick - start) s.natHeap else s.natHeap := by
  have nextFit : j + 1 ≤ B := by
    have bound := wb.2.1 6702
    rw [h.count] at bound
    omega
  have enterStep : step program n x s = .running (setPC s 7) := by
    simp [step,pc,code_6,h.index,h.count,index,setPC]
  have enter := control_run program n B 7 x s wb (by omega) enterStep
  let aState := setPC s 7
  have read := readEntry_execution x aState (h.pc 7) rfl enter.final_bound code sourceFit
    (by omega) kindFit a b
  let bState := applyBlock readEntry aState
  have bh : Loaded D stride N tick O used j start kind bState := readEntry_loaded (h.pc 7) a b
  have bp : bState.pc = 12 := by rw [applyBlock_pc]; rfl
  have dur := duration_execution x bState bh bp read.final_bound code
  let cState := setPC (writeNat bState 6719 (duration kind)) 17
  have ch : Loaded D stride N tick O used j start kind cState := bh.duration
  have cd : cState.natReg 6719 = duration kind := by simp [cState,setPC,writeNat,next]
  have stopRun := stop_execution x cState ch cd rfl dur.final_bound code timeFit
  let dState := applyBlock stop cState
  have dh : Stopped D stride N tick O used j start kind dState := stop_stopped ch cd
  have dp : dState.pc = 18 := by rw [applyBlock_pc]; rfl
  have prefixRun : BoundedRuns program n x B s 10 dState := enter.trans (read.trans (dur.trans stopRun))
  by_cases before : tick < start
  · have inactive : ¬ active tick start kind := by intro ha; exact (not_le_of_gt before) ha.1
    have branchStep : step program n x dState = .running (setPC dState 27) := by
      simp [step,dp,code_18,dh.tick,dh.startReg,before,setPC]
    have branch := control_run program n B 27 x dState prefixRun.final_bound (by omega) branchStep
    have finish := advance_execution x (setPC dState 27) (dh.pc 27).toHeader rfl branch.final_bound code nextFit
    refine ⟨13,_,prefixRun.trans (branch.trans finish),by omega,rfl,?_,?_⟩
    · simpa only [ite_eq_right inactive] using (advance_header (dh.pc 27).toHeader).pc 6
    · simp only [ite_eq_right inactive]
      rfl
  · have branchStep : step program n x dState = .running (setPC dState 19) := by
      simp [step,dp,code_18,dh.tick,dh.startReg,before,setPC]
    have branch := control_run program n B 19 x dState prefixRun.final_bound (by omega) branchStep
    let eState := setPC dState 19
    have eh : Stopped D stride N tick O used j start kind eState := dh.pc 19
    by_cases inside : tick < start + duration kind
    · have enabled : active tick start kind := ⟨by omega,inside⟩
      have activeStep : step program n x eState = .running (setPC eState 20) := by
        simp [step,show eState.pc = 19 from rfl,code_19,eh.tick,eh.stopValue,inside,setPC]
      have activeRun := control_run program n B 20 x eState branch.final_bound (by omega) activeStep
      let fState := setPC eState 20
      have fh : Stopped D stride N tick O used j start kind fState := eh.pc 20
      have phaseRun := phase_execution x fState fh rfl activeRun.final_bound code
      let gState := applyBlock phase fState
      have gh : Stopped D stride N tick O used j start kind gState := phase_stopped fh
      have gp : gState.pc = 21 := by rw [applyBlock_pc]; rfl
      have emitRun := emit_execution x gState gh.toHeader gp phaseRun.final_bound code outputFit
      let iState := applyBlock emit gState
      have ih : Header D stride N tick O (used + 1) j iState := emit_header gh.toHeader
      have ip : iState.pc = 27 := by rw [applyBlock_pc,gp]; rfl
      have finish := advance_execution x iState ih ip emitRun.final_bound code nextFit
      refine ⟨21,_,prefixRun.trans (branch.trans (activeRun.trans (phaseRun.trans (emitRun.trans finish)))),
        le_rfl,rfl,?_,?_⟩
      · simpa only [ite_eq_left enabled] using (advance_header ih).pc 6
      · simp only [ite_eq_left enabled]
        change (applyBlock emit gState).natHeap = _
        exact emit_heap gh.toLoaded (phase_value fh)
    · have inactive : ¬ active tick start kind := by intro ha; exact inside ha.2
      have inactiveStep : step program n x eState = .running (setPC eState 27) := by
        simp [step,show eState.pc = 19 from rfl,code_19,eh.tick,eh.stopValue,inside,setPC]
      have inactiveRun := control_run program n B 27 x eState branch.final_bound (by omega) inactiveStep
      have finish := advance_execution x (setPC eState 27) (eh.pc 27).toHeader rfl
        inactiveRun.final_bound code nextFit
      refine ⟨14,_,prefixRun.trans (branch.trans (inactiveRun.trans finish)),by omega,rfl,?_,?_⟩
      · simpa only [ite_eq_right inactive] using (advance_header (eh.pc 27).toHeader).pc 6
      · simp only [ite_eq_right inactive]
        rfl

end
end ExactFourierCircuits.UniformGlobalCalendarSelector
