import DFTModelCacheReplaySlots

set_option autoImplicit false

/-! Six fixed phase printers, joined by charged fresh-tape copying.
The only runtime input is the height. No slot list or replay plan is supplied.
Timestamps, scalar factors and the physical cache caller are separate. -/
namespace ExactFourierCircuits.DFTModelCacheReplayAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheChronology
open DFTModelCacheReplaySlots (Slot5 encode phase)
open DFTModelCacheTraversal (ofList append append_lists append_value append_valid
  append_work append_peak comp_work fork_work comp_peak fork_peak)
noncomputable section

def join (f g : Prog false w (Ty.a Slot5)) : Prog false w (Ty.a Slot5) :=
  .comp (.fork f g) (append Slot5)

structure Printed (H count : ℕ) (xs : List Slot5.T) (p : Prog false w (Ty.a Slot5)) : Prop where
  value : (run p H).val=ofList xs
  valid : (run p H).valid
  length : xs.length ≤ 11*count*(H+1)
  work : (run p H).work ≤ 1000*count^2*(H+1)
  peak : (run p H).peak ≤ 11*count*(H+1)

theorem phase_printed (H : ℕ) (b e i : Bool) :
    Printed H 1 ((UniformLocalReplaySlotMachine.slots H b e i).map encode) (phase b e i) := by
  have levels : UniformLocalReplaySlotMachine.levelCount H b ≤ H+1 := by
    cases b <;> simp [UniformLocalReplaySlotMachine.levelCount]
  refine ⟨DFTModelCacheReplaySlots.phase_value H b e i,
    DFTModelCacheReplaySlots.phase_valid H b e i,?_,?_,?_⟩
  · rw [List.length_map,UniformLocalReplaySlotMachine.slots_length]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 11 levels
  · have h:=DFTModelCacheReplaySlots.phase_work H b e i
    norm_num only [one_pow,Nat.mul_one] at *
    omega
  · simpa only [Nat.mul_one] using DFTModelCacheReplaySlots.phase_peak H b e i

theorem join_printed (H c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (xs ys : List Slot5.T) (f g : Prog false w (Ty.a Slot5))
    (pf : Printed H c xs f) (pg : Printed H d ys g) :
    Printed H (c+d) (xs++ys) (join f g) := by
  have len : (xs++ys).length ≤ 11*(c+d)*(H+1) := by
    rw [List.length_append]
    have x:=pf.length
    have y:=pg.length
    nlinarith
  refine ⟨?_,?_,len,?_,?_⟩
  · change (run (append Slot5) ((run f H).val,(run g H).val)).val=_
    rw [pf.value,pg.value,append_value,append_lists]
  · change ((run f H).valid ∧ (run g H).valid ∧ True) ∧
      (run (append Slot5) ((run f H).val,(run g H).val)).valid
    exact ⟨⟨pf.valid,pg.valid,trivial⟩,append_valid _ _ _⟩
  · rw [join,comp_work,fork_work]
    change (run f H).work+(run g H).work+1+
      (run (append Slot5) ((run f H).val,(run g H).val)).work+1 ≤ _
    have copy:=append_work Slot5 (ofList xs) (ofList ys)
    rw [←pf.value,←pg.value] at copy
    have xl : (run f H).val.len=xs.length := by rw [pf.value];rfl
    have yl : (run g H).val.len=ys.length := by rw [pg.value];rfl
    rw [xl,yl] at copy
    have x:=pf.work
    have y:=pg.work
    have cx:=pf.length
    have cy:=pg.length
    have cross : c+d ≤ 2*c*d := by
      have cp : c ≤ c*d := Nat.le_mul_of_pos_right c hd
      have dp : d ≤ c*d := Nat.le_mul_of_pos_left d hc
      nlinarith only [cp,dp]
    have scaled:=Nat.mul_le_mul_right (H+1) cross
    have hpos : 1 ≤ H+1 := by omega
    nlinarith
  · rw [join,comp_peak,fork_peak]
    change max (max (run f H).peak (run g H).peak)
      (run (append Slot5) ((run f H).val,(run g H).val)).peak ≤ _
    have copy:=append_peak Slot5 (ofList xs) (ofList ys)
    rw [←pf.value,←pg.value] at copy
    have xl : (run f H).val.len=xs.length := by rw [pf.value];rfl
    have yl : (run g H).val.len=ys.length := by rw [pg.value];rfl
    rw [xl,yl] at copy
    refine max_le (max_le (pf.peak.trans ?_) (pg.peak.trans ?_)) (copy.trans ?_)
    · nlinarith
    · nlinarith
    · rw [List.length_append] at len
      exact len

/-- Exactly the native six-phase order, including disabled and empty slots. -/
def program : Prog false w (Ty.a Slot5) :=
  join (join (join (phase false true false) (phase true true false))
    (join (phase false true true) (phase false false false)))
    (join (phase true false true) (phase false false true))

theorem program_printed (H : ℕ) :
    Printed H 6 ((replaySlots H).map encode) program := by
  have p0:=phase_printed H false true false
  have p1:=phase_printed H true true false
  have p2:=phase_printed H false true true
  have p3:=phase_printed H false false false
  have p4:=phase_printed H true false true
  have p5:=phase_printed H false false true
  have p01:=join_printed H 1 1 (by decide) (by decide) _ _ _ _ p0 p1
  have p23:=join_printed H 1 1 (by decide) (by decide) _ _ _ _ p2 p3
  have p45:=join_printed H 1 1 (by decide) (by decide) _ _ _ _ p4 p5
  have p03:=join_printed H 2 2 (by decide) (by decide) _ _ _ _ p01 p23
  have all:=join_printed H 4 2 (by decide) (by decide) _ _ _ _ p03 p45
  have order:=congrArg (List.map encode) (UniformLocalReplaySlotMachine.slots_all_phases H)
  simp only [List.map_append] at order
  simpa only [program,List.append_assoc,←order] using all

theorem program_value (H : ℕ) :
    (run program H).val=ofList ((replaySlots H).map encode) := (program_printed H).value

theorem program_valid (H : ℕ) : (run program H).valid := (program_printed H).valid

theorem program_work (H : ℕ) : (run program H).work ≤ 36000*(H+1) := by
  simpa only [show 1000*6^2=36000 by decide] using (program_printed H).work

theorem program_peak (H : ℕ) : (run program H).peak ≤ 66*(H+1) := by
  simpa only [show 11*6=66 by decide] using (program_printed H).peak

end
end ExactFourierCircuits.DFTModelCacheReplayAssembly
