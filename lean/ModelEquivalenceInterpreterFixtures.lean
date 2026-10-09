import ModelEquivalenceInterpreter

set_option autoImplicit false

/-! Small independent kernel reductions of the actual typed program. -/
namespace ExactFourierCircuits.ModelEquivalenceInterpreterFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open ModelEquivalenceInterpreter
noncomputable section

def numbers : Tape ℕ := Tape.tab 3 (fun j => 7*j+2)

theorem middle_left :
    (run (update w) ((numbers,1),99)).val.look 0 0 = 2 := by rfl

theorem middle_written :
    (run (update w) ((numbers,1),99)).val.look 1 0 = 99 := by rfl

theorem middle_right :
    (run (update w) ((numbers,1),99)).val.look 2 0 = 16 := by rfl

theorem middle_length : (run (update w) ((numbers,1),99)).val.len = 3 := by rfl

theorem middle_work : (run (update w) ((numbers,1),99)).work = 107 := by rfl

theorem middle_peak : (run (update w) ((numbers,1),99)).peak = 3 := by rfl

theorem last_written :
    (run (update w) ((numbers,2),99)).val.look 2 0 = 99 := by rfl

theorem last_work : (run (update w) ((numbers,2),99)).work = 107 := by rfl

theorem outside_unchanged :
    (run (update w) ((numbers,3),99)).val.look 2 0 = 16 := by rfl

theorem outside_absent :
    (run (update w) ((numbers,3),99)).val.look 3 0 = 0 := by rfl

theorem outside_work : (run (update w) ((numbers,3),99)).work = 113 := by rfl

theorem distant_peak : (run (update w) ((numbers,50),99)).peak = 50 := by rfl

theorem empty_length :
    (run (update w) ((Tape.empty ℕ,100),99)).val.len = 0 := by rfl

theorem empty_work : (run (update w) ((Tape.empty ℕ,100),99)).work = 8 := by rfl

theorem empty_peak : (run (update w) ((Tape.empty ℕ,100),99)).peak = 0 := by rfl

theorem singleton_work :
    (run (update w) ((Tape.tab 1 (fun _ => 2),0),99)).work = 37 := by rfl

theorem eight_work :
    (run (update w) ((Tape.tab 8 (fun j => j),4),99)).work = 282 := by rfl

def dirtyHeap : Tape (ℕ × ℕ) :=
  Tape.tab 3 (fun j => if j = 0 then (1,7) else if j = 1 then (0,55) else (2,9))

theorem dirty_absent : decodeNatHeap dirtyHeap 1 = none := by rfl

theorem dirty_left :
    decodeNatHeap (run (update (p w w)) ((dirtyHeap,1),(1,11))).val 0 = some 7 := by rfl

theorem dirty_written :
    decodeNatHeap (run (update (p w w)) ((dirtyHeap,1),(1,11))).val 1 = some 11 := by rfl

theorem dirty_right :
    decodeNatHeap (run (update (p w w)) ((dirtyHeap,1),(1,11))).val 2 = some 9 := by rfl

theorem dirty_outside :
    decodeNatHeap (run (update (p w w)) ((dirtyHeap,1),(1,11))).val 3 = none := by rfl

end
end ExactFourierCircuits.ModelEquivalenceInterpreterFixtures
