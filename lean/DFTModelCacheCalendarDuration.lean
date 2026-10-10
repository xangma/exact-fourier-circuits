import DFTModelCacheTraversalWordBound
import DFTModelCacheDescriptorSearchBounds
import UniformLocalCacheTiming

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformWorkspacePlanner UniformLocalCacheTiming
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section

abbrev Row7 : Ty := DFTModelCacheTraversal.Record7
abbrev Event9 : Ty := p w (p w Row7)
def eventEncode (e : TimedEvent) : Event9.T :=
  match e.event with
  | .direct v o => (e.start,(0,(v,(o,(0,(0,(0,(0,0))))))))
  | .rectangle q => (e.start,(1,rectangleEncode q))

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def rowA : Prog false Row7 w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def rowE : Prog false Row7 w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def rowTarget : Prog false Row7 w := nat .mul (.atom (.lit 2)) (nat .add rowA rowE)
def rowExponent : Prog false Row7 w :=
  .comp rowTarget (.comp DFTModelCacheDescriptor.logarithm (.atom .fst))
def durationFromExponent : Prog false w w :=
  nat .mul (nat .mul (.atom (.lit 28))
    (nat .add (nat .mul (.atom (.lit 4))
      (nat .add (nat .mul (.atom (.lit 8)) (.atom .id)) (.atom (.lit 7))))
      (.atom (.lit 2)))) (.atom (.lit 11))
def rowDuration : Prog false Row7 w := .comp rowExponent durationFromExponent

theorem rowTarget_run (q : Row) : run rowTarget (rectangleEncode q)=
    ⟨2*(q.a+q.e),19, max 2 (2*(q.a+q.e)),True⟩ := by
  simp [rowTarget,nat,rowA,rowE,rectangleEncode,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

theorem durationFromExponent_run (k : ℕ) : run durationFromExponent k=
    ⟨28*(4*(8*k+7)+2)*11,25,28*(4*(8*k+7)+2)*11,True⟩ := by
  simp [durationFromExponent,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] DFTModelCacheDescriptor.logarithm durationFromExponent

theorem rowExponent_run (q : Row) :
    run rowExponent (rectangleEncode q)=
      ⟨(run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).val.1,
       (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).work+22,
       max (max 2 (2*(q.a+q.e))) (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).peak,
       (run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).valid⟩ := by
  change ((run rowTarget (rectangleEncode q)).pass (fun t =>
    ((run DFTModelCacheDescriptor.logarithm t).pass (fun z=>Bill.one z.1)).pay 1 0)).pay 1 0 = _
  rw [rowTarget_run]
  simp only [Bill.one,Bill.pass,Bill.pay,max_zero,true_and,and_true]
  congr 1; omega

attribute [local irreducible] rowExponent rowDuration

theorem rowExponent_spec (q : Row) :
    (run rowExponent (rectangleEncode q)).val=exponent q.a q.e ∧
    (run rowExponent (rectangleEncode q)).valid ∧
    (run rowExponent (rectangleEncode q)).work=28*exponent q.a q.e+45 ∧
    (run rowExponent (rectangleEncode q)).peak ≤ 4*(q.a+q.e)+2 := by
  have h:=DFTModelCacheDescriptor.logarithm_spec (2*(q.a+q.e))
  rw [rowExponent_run]
  dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid,exponent]
  refine ⟨congrArg Prod.fst h.1,h.2.1,?_,?_⟩
  · have hw:=h.2.2.1
    omega
  · have hp:=h.2.2.2
    omega

theorem rowDuration_value (q : Row) :
    (run rowDuration (rectangleEncode q)).val=rectangleDuration q := by
  rw [rowDuration]
  change (run durationFromExponent (run rowExponent (rectangleEncode q)).val).val=_
  rw [(rowExponent_spec q).1,durationFromExponent_run]
  rfl

theorem rowDuration_valid (q : Row) :
    (run rowDuration (rectangleEncode q)).valid := by
  rw [rowDuration]
  change (run rowExponent (rectangleEncode q)).valid ∧
    (run durationFromExponent (run rowExponent (rectangleEncode q)).val).valid
  rw [durationFromExponent_run]
  exact ⟨(rowExponent_spec q).2.1,trivial⟩

theorem rectangleDuration_bound (q : Row) : rectangleDuration q ≤ 100000*(q.a+q.e+1) := by
  have h:=UniformWorkspaceSearchMachine.clog_bound (2*(q.a+q.e))
  unfold rectangleDuration exponent
  omega

theorem rowDuration_work (q : Row) :
    (run rowDuration (rectangleEncode q)).work ≤ 1000*(q.a+q.e+1) := by
  rw [rowDuration]
  change (run rowExponent (rectangleEncode q)).work+
    (run durationFromExponent (run rowExponent (rectangleEncode q)).val).work+1 ≤ _
  rw [durationFromExponent_run,(rowExponent_spec q).2.2.1]
  have h:=UniformWorkspaceSearchMachine.clog_bound (2*(q.a+q.e))
  dsimp only [exponent]
  omega

theorem rowDuration_peak (q : Row) :
    (run rowDuration (rectangleEncode q)).peak ≤ 100000*(q.a+q.e+1) := by
  rw [rowDuration,DFTModelCacheTraversal.comp_peak]
  rw [(rowExponent_spec q).1,durationFromExponent_run]
  have hp:=(rowExponent_spec q).2.2.2
  have h:=UniformWorkspaceSearchMachine.clog_bound (2*(q.a+q.e))
  dsimp only [exponent]
  apply max_le <;> omega

end
end ExactFourierCircuits.DFTModelCacheCalendar
