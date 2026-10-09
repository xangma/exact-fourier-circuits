import DFTModelClock
import DFTModelClockControl

set_option autoImplicit false

/-! Small exact kernel and syntax-template fixtures. These do not instantiate
the saving-network record emitter or its recursive body. Scalar coefficients
are inputs to the tested programs, never arbitrary complex Code literals. -/
namespace ExactFourierCircuits.DFTModelClockFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
namespace C

def input : Tape ℂ := Tape.tab 4
  (fun j => if j=0 then Complex.I else if j=1 then -Complex.I else if j=2 then 0 else 3)

theorem empty_length :
    (run DFTModelClock.program ((2,-1),(0,input))).val.len=0 := by rfl
theorem empty_work :
    (run DFTModelClock.program ((2,-1),(0,input))).work=10 := by rfl
theorem two_pairs_work :
    (run DFTModelClock.program ((2,-1),(2,input))).work=214 := by rfl
theorem two_pairs_peak :
    (run DFTModelClock.program ((2,-1),(2,input))).peak=4 := by rfl
theorem complex_even :
    (run DFTModelClock.program ((2,-1),(2,input))).val.look 0 0=3*Complex.I := by
  change (2:ℂ)*Complex.I+(-1)*(-Complex.I)=3*Complex.I
  ring
theorem complex_odd :
    (run DFTModelClock.program ((2,-1),(2,input))).val.look 1 0= -3*Complex.I := by
  change (2:ℂ)*(-Complex.I)+(-1)*Complex.I= -3*Complex.I
  ring
theorem zero_source_even :
    (run DFTModelClock.program ((2,-1),(2,input))).val.look 2 0= -3 := by
  change (2:ℂ)*0+(-1)*3= -3
  ring
theorem zero_source_odd :
    (run DFTModelClock.program ((2,-1),(2,input))).val.look 3 0=6 := by
  change (2:ℂ)*3+(-1)*0=6
  ring
theorem zero_coefficient :
    (run DFTModelClock.program ((0,1),(2,input))).val.look 0 0= -Complex.I := by
  change (0:ℂ)*Complex.I+1*(-Complex.I)= -Complex.I
  ring
theorem actual_C_constant_pair :
    (run DFTModelClock.program ((ExactFourierCircuits.a,ExactFourierCircuits.b),
      (1,Tape.tab 2 (fun _ => 1)))).val.look 0 0=1 := by
  change ExactFourierCircuits.a*1+ExactFourierCircuits.b*1=1
  simp [ExactFourierCircuits.a,ExactFourierCircuits.b]
  ring
end C

namespace Batch
abbrev Tagged := DFTModelAffine.Tagged
def identityChild : Prog false (DFTModelClockBatch.Child w Tagged) (Ty.a Tagged) := .atom .snd
def dirty : Tape Tagged.T := Tape.tab 6
  (fun j => if j=0 then (1,(2,Complex.I)) else
    if j=1 then (0,(-3,0)) else (1,(0,-Complex.I)))

theorem length :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(2,(3,dirty)))).val.len=6 := by rfl
theorem work :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(2,(3,dirty)))).work=483 := by
  rw [DFTModelClockBatch.program_work]
  simp [identityChild,run,Code.run,Atom.run,Bill.one]
theorem peak :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(2,(3,dirty)))).peak≤6 := by
  apply DFTModelClockBatch.program_peak w Tagged identityChild 9 2 3 6 dirty
    (by omega) (by omega) (by omega)
  intro g hg
  change 0≤6
  omega
theorem valid :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(2,(3,dirty)))).valid := by
  trivial
theorem first_tag :
    ((run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 0 (0,(0,0))).1=1 := by rfl
theorem first_offset :
    ((run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 0 (0,(0,0))).2.1=2 := by rfl
theorem first_homogeneous :
    ((run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 0 (0,(0,0))).2.2=Complex.I := by rfl
theorem prepared_tag :
    ((run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 1 (0,(0,0))).1=0 := by rfl
theorem second_group_homogeneous :
    ((run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 4 (0,(0,0))).2.2= -Complex.I := by rfl
theorem empty_count_work :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(0,(3,dirty)))).work=35 := by rfl
theorem empty_size_work :
    (run (DFTModelClockBatch.program w Tagged identityChild) (9,(2,(0,dirty)))).work=75 := by rfl
theorem outside_default :
    (run (DFTModelClockBatch.program w Tagged identityChild)
      (9,(2,(3,dirty)))).val.look 6 (7,(8,9))=(7,(8,9)) := by rfl
end Batch

namespace Control
def addThree : Prog false w w :=
  .comp (.fork (.atom .id) (.atom (.lit 3))) (.atom (.int .add))
def divideTwo : Prog false w w :=
  .comp (.fork (.atom .id) (.atom (.lit 2))) (.atom (.int .div))
theorem chronological :
    (run (DFTModelClockControl.sequence [addThree,divideTwo]) 4).val=3 := by rfl
theorem reverse_differs :
    (run (DFTModelClockControl.sequence [divideTwo,addThree]) 4).val=5 := by rfl
theorem sequence_work :
    (run (DFTModelClockControl.sequence [addThree,divideTwo]) 4).work=13 := by rfl

/-- A bounded-descent fixture only: a recursive identity, not the saving body. -/
def base : Prog false DFTModelClockControl.Node DFTModelClockControl.Result := .atom .snd
def body : Code false DFTModelClockControl.ChildPort
    DFTModelClockControl.Node DFTModelClockControl.Result := .call
theorem descend_value :
    (run (DFTModelClockControl.descendTemplate base body) ((3,Complex.I),Batch.dirty)).val=
      Batch.dirty := by rfl
theorem descend_work :
    (run (DFTModelClockControl.descendTemplate base body) ((3,Complex.I),Batch.dirty)).work=15 := by rfl
theorem descend_peak :
    (run (DFTModelClockControl.descendTemplate base body) ((3,Complex.I),Batch.dirty)).peak=3 := by rfl
end Control
end
end ExactFourierCircuits.DFTModelClockFixtures
