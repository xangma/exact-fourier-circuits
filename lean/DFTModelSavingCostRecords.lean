import DFTModelSavingCostSetup
import DFTModelSavingDirection

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
open scoped BigOperators
noncomputable section
attribute [local irreducible] dispatch recordBody stream

/-- Importing and composing the real record decoder costs twenty-one steps. -/
theorem recordBody_run (R rest i : ℕ) (rs : Tape (Tape ℕ))
    (old node : Node.T) (h : Handler Port) :
    Code.run (recordBody R) h ((rest,(rs,old)),(i,node))=
      (Code.run (dispatch R) h (rest,(rs.look i (Tape.empty ℕ),node))).pay 21 0 := by
  rw [recordBody,DFTModelSavingDirection.imported_comp_run recordArgs (dispatch R) h _
    (by rw [recordArgs_run];trivial),recordArgs_run]

/-- Exact loop accounting; each iteration executes one original record. -/
theorem steps_pay {α : Type} (x : α) (f : ℕ→α→Bill α) (c n : ℕ) :
    Bill.steps x (fun i z=>(f i z).pay c 0) n=
      (Bill.steps x f n).pay (n*c) 0 := by
  induction n with
  | zero => simp [Bill.steps,Bill.one,Bill.pay]
  | succ n ih =>
    change ((Bill.steps x (fun i z=>(f i z).pay c 0) n).pass
      (fun z=>(f n z).pay c 0)).pay 1 (n+1)=_
    rw [ih]
    simp only [Bill.steps,Bill.pay,Bill.pass,max_zero]
    congr 1
    rw [Nat.add_mul]
    omega

def recordSteps (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler Port) (n : ℕ) : Bill Node.T :=
  Bill.steps node (fun i z=>Code.run (dispatch R) h
    (rest,(rs.look i (Tape.empty ℕ),z))) n

theorem imported_loop_run {s t : Ty} (n : Prog false s w) (initial : Prog false s t)
    (f : Code false Port (p s (p w t)) t) (h : Handler Port) (x : s.T) :
    Code.run (.loop (.importClosed n) (.importClosed initial) f) h x=
      ((run n x).pass (fun count=>(run initial x).pass
        (fun z=>Bill.steps z (fun i u=>Code.run f h (x,(i,u))) count))).pay 3 0 := by
  change (((run n x).pay 1 0).pass (fun count=>((run initial x).pay 1 0).pass
    (fun z=>Bill.steps z (fun i u=>Code.run f h (x,(i,u))) count))).pay 1 0=_
  simp only [Bill.pay,Bill.pass,max_zero]
  congr 1
  omega

theorem streamCount_run (rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T) :
    run (.comp records (.atom .len)) (rest,(rs,node))=⟨rs.len,5,rs.len,True⟩ := by
  simp [records,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem streamInitial_run (rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T) :
    run streamInitial (rest,(rs,node))=⟨node,3,0,True⟩ := by
  simp [streamInitial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem stream_run (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler Port) :
    Code.run (stream R) h (rest,(rs,node))=
      (recordSteps R rest rs node h rs.len).pay (11+21*rs.len) rs.len := by
  have body : (fun i z=>Code.run (recordBody R) h ((rest,(rs,node)),(i,z)))=
      (fun i z=>(Code.run (dispatch R) h (rest,(rs.look i (Tape.empty ℕ),z))).pay 21 0) := by
    funext i z
    exact recordBody_run R rest i rs node z h
  rw [stream,imported_loop_run,streamCount_run,streamInitial_run,body]
  simp only [Bill.pass,steps_pay]
  simp only [recordSteps,Bill.pay,true_and,max_zero,zero_max]
  congr 1
  · omega
  · exact max_comm _ _

theorem steps_work_exact {α : Type} (x : α) (f : ℕ→α→Bill α) (n : ℕ) :
    (Bill.steps x f n).work=1+n+
      ∑i∈Finset.range n,(f i (Bill.steps x f i).val).work := by
  induction n with
  | zero => simp [Bill.steps,Bill.one]
  | succ n ih =>
    change (Bill.steps x f n).work+(f n (Bill.steps x f n).val).work+1=_
    rw [ih,Finset.sum_range_succ]
    omega

/-- The sum charges the actual intermediate bank at every chronological record. -/
theorem stream_work (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler Port) :
    (Code.run (stream R) h (rest,(rs,node))).work=12+22*rs.len+
      ∑i∈Finset.range rs.len,(Code.run (dispatch R) h
        (rest,(rs.look i (Tape.empty ℕ),(recordSteps R rest rs node h i).val))).work := by
  rw [stream_run]
  dsimp only [Bill.pay,recordSteps]
  rw [steps_work_exact]
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
