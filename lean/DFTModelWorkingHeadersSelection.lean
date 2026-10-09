import DFTModelWorkingHeadersTape

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev State := DFTModelRoot.selectionState
abbrev SelectionPort : Port := some (State,PrimeResult)

def empty {s : Ty} {r : Port} : Code false r s (a w) :=
  .tab (.atom (.lit 0)) (.atom (.lit 0))
def stop : Prog false State PrimeResult := .fork DFTModelRoot.getR empty
def base : Prog false State PrimeResult := .fork (.atom (.lit 0)) empty
def skip : Code false SelectionPort State PrimeResult := .comp DFTModelRoot.skipState .call
def acceptTail : Code false SelectionPort State PrimeResult := .comp DFTModelRoot.acceptState .call
def finishTape : Prog false (p w PrimeResult) (a w) :=
  .comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .snd))) prepend
def finish : Prog false (p w PrimeResult) PrimeResult :=
  .fork (.comp (.atom .snd) (.atom .fst)) finishTape
def accept : Code false SelectionPort State PrimeResult :=
  .comp (.fork DFTModelRoot.getP acceptTail) (.importClosed finish)
def body : Code false SelectionPort State PrimeResult :=
  .ifz (.comp DFTModelRoot.getP (.importClosed DFTModelRoot.prime)) skip
    (.ifz DFTModelRoot.tooBig accept (.importClosed stop))

def aux (fuel n p R : ℕ) : Bill PrimeResult.T :=
  depthRun (base.run ()) body.run fuel (n,(p,R))

theorem finish_run (p R : ℕ) (v : Tape ℕ) :
    run finish (p,(R,v)) =
      ⟨(R,(run prepend (p,v)).val),(run prepend (p,v)).work+10,
        (run prepend (p,v)).peak,(run prepend (p,v)).valid⟩ := by
  have ht : run finishTape (p,(R,v))=(run prepend (p,v)).pay 6 0 := by
    rw [finishTape,DFTModelRoot.code_comp,DFTModelRoot.code_fork]
    change (((Bill.one p).pass (fun j =>
      ((Bill.one (R,v)).pass (fun t => Bill.one t.2)).pay 1 0 |>.pass
        (fun t => Bill.one (j,t)))).pass (run prepend)).pay 1 0 = _
    simp [Bill.pass,Bill.pay,Bill.one,Nat.add_comm]
    omega
  rw [finish,DFTModelRoot.code_fork,ht]
  change (((Bill.one (R,v)).pass (fun t => Bill.one t.1)).pay 1 0 |>.pass
    (fun j => ((run prepend (p,v)).pay 6 0).pass (fun t => Bill.one (j,t)))) = _
  simp [Bill.pass,Bill.pay,Bill.one,Nat.add_comm,Nat.add_left_comm]
  omega

theorem stop_run (n p R : ℕ) : run stop (n,(p,R))=⟨(R,Tape.empty ℕ),8,0,True⟩ := by
  simp [stop,empty,DFTModelRoot.getR,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    Bill.word,Bill.tab,Bill.sow,Bill.steps,Tape.empty,Tape.tab]
  funext i
  exact Fin.elim0 i

theorem skip_run (h : Handler SelectionPort) (n p R : ℕ) :
    skip.run h (n,(p,R))=(h (n,(p+1,R))).pay 15 (p+1) := by
  simp [skip,DFTModelRoot.skipState,DFTModelRoot.getN,DFTModelRoot.nextP,
    DFTModelRoot.getP,DFTModelRoot.getR,Code.run,Atom.run,NOp.run,Bill.pass,
    Bill.pay,Bill.one,Bill.word,Nat.add_comm,Nat.add_left_comm,max_comm]
  omega

theorem acceptTail_run (h : Handler SelectionPort) (n p R : ℕ) :
    acceptTail.run h (n,(p,R))=(h (n,(p+1,R*p))).pay 21 (max (p+1) (R*p)) := by
  simp [acceptTail,DFTModelRoot.acceptState,DFTModelRoot.getN,DFTModelRoot.nextP,
    DFTModelRoot.newR,DFTModelRoot.getP,DFTModelRoot.getR,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Nat.add_comm,Nat.add_left_comm,max_assoc,max_comm]
  omega

theorem accept_run (h : Handler SelectionPort) (n p R : ℕ) :
    accept.run h (n,(p,R))=
      (((h (n,(p+1,R*p))).pay 21 (max (p+1) (R*p))).pass
        (fun t => (run finish (p,t)).pay 1 0)).pay 5 0 := by
  change (((DFTModelRoot.getP.run h (n,(p,R))).pass (fun j =>
    (acceptTail.run h (n,(p,R))).pass (fun t => Bill.one (j,t)))).pass
      (fun t => (run finish t).pay 1 0)).pay 1 0 = _
  rw [acceptTail_run]
  have hp : DFTModelRoot.getP.run h (n,(p,R))=⟨p,3,0,True⟩ := by
    simp [DFTModelRoot.getP,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [hp]
  simp [Bill.pass,Bill.pay,Bill.one,Nat.add_comm,Nat.add_left_comm]
  omega

theorem aux_zero (n p R : ℕ) : aux 0 n p R=⟨(0,Tape.empty ℕ),7,0,True⟩ := by
  simp [aux,depthRun,base,empty,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    Bill.word,Bill.tab,Bill.sow,Bill.steps,Tape.empty,Tape.tab]
  funext i
  exact Fin.elim0 i

theorem check_run (h : Handler SelectionPort) (n p R : ℕ) :
    (Code.comp DFTModelRoot.getP (.importClosed DFTModelRoot.prime)).run h (n,(p,R)) =
      (run DFTModelRoot.prime p).pay 5 0 := by
  change (((Bill.one (p,R)).pass (fun x => Bill.one x.1)).pay 1 0 |>.pass
    (fun p => (run DFTModelRoot.prime p).pay 1 0)).pay 1 0 = _
  simp [Bill.one,Bill.pass,Bill.pay,Nat.add_comm,Nat.add_left_comm]
  omega

theorem tooBig_run (h : Handler SelectionPort) (n p R : ℕ) :
    DFTModelRoot.tooBig.run h (n,(p,R)) =
      ⟨if 2*n<R*p then 1 else 0,17,
        max (max 2 (2*n)) (max (R*p) (if 2*n<R*p then 1 else 0)),True⟩ := by
  simp [DFTModelRoot.tooBig,DFTModelRoot.twiceN,DFTModelRoot.newR,
    DFTModelRoot.getN,DFTModelRoot.getP,DFTModelRoot.getR,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,max_assoc]

theorem choice_run (h : Handler SelectionPort) (n p R : ℕ) :
    (Code.ifz DFTModelRoot.tooBig accept (.importClosed stop)).run h (n,(p,R)) =
      if 2*n<R*p then ⟨(R,Tape.empty ℕ),27,max 2 (max (2*n) (R*p)),True⟩
      else ((h (n,(p+1,R*p))).pass (fun t => run finish (p,t))).pay 45
        (max 2 (max (2*n) (max (R*p) (p+1)))) := by
  change ((DFTModelRoot.tooBig.run h (n,(p,R))).pass (fun x =>
    if x=0 then accept.run h (n,(p,R)) else (run stop (n,(p,R))).pay 1 0)).pay 1 0 = _
  rw [tooBig_run,accept_run,stop_run]
  by_cases hb : 2*n<R*p <;>
    simp [Bill.pass,Bill.pay,hb,Nat.add_comm,Nat.add_left_comm,
      max_assoc,max_comm,max_left_comm]
  all_goals omega

theorem body_run (h : Handler SelectionPort) (n p R : ℕ) :
    body.run h (n,(p,R)) =
      (((run DFTModelRoot.prime p).pay 5 0).pass (fun check =>
        if check=0 then (h (n,(p+1,R))).pay 15 (p+1)
        else if 2*n<R*p then ⟨(R,Tape.empty ℕ),27,max 2 (max (2*n) (R*p)),True⟩
        else ((h (n,(p+1,R*p))).pass (fun t => run finish (p,t))).pay 45
          (max 2 (max (2*n) (max (R*p) (p+1)))))).pay 1 0 := by
  change (((Code.comp DFTModelRoot.getP (.importClosed DFTModelRoot.prime)).run h (n,(p,R))).pass
    (fun check => if check=0 then skip.run h (n,(p,R)) else
      (Code.ifz DFTModelRoot.tooBig accept (.importClosed stop)).run h (n,(p,R)))).pay 1 0 = _
  rw [check_run,skip_run,choice_run]

theorem aux_step (fuel n p R : ℕ) :
    aux (fuel+1) n p R =
      ((((run DFTModelRoot.prime p).pay 5 0).pass (fun check =>
        if check=0 then (aux fuel n (p+1) R).pay 15 (p+1)
        else if 2*n<R*p then ⟨(R,Tape.empty ℕ),27,max 2 (max (2*n) (R*p)),True⟩
        else ((aux fuel n (p+1) (R*p)).pass (fun t => run finish (p,t))).pay 45
          (max 2 (max (2*n) (max (R*p) (p+1)))))).pay 1 0).pay 1 (fuel+1) := by
  change ((body.run (depthRun (base.run ()) body.run fuel) (n,(p,R))).pay 1 (fuel+1)) = _
  rw [body_run]
  rfl

end
end ExactFourierCircuits.DFTModelWorkingHeaders
