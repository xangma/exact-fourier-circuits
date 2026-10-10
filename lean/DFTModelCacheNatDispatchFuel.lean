import DFTModelCacheNatDispatchBounds
import DFTModelCacheNatControl

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

abbrev FuelInput := p w Local

def body (code : List Instruction) : Prog false (p FuelInput (p w Local)) Local :=
  .comp (.comp (.atom .snd) (.atom .snd)) (program code)

/-- Fuel is runtime natural data. Every iteration dispatches; a selected halt
stutters and is still charged, including after native termination. -/
def fuelProgram (code : List Instruction) : Prog false FuelInput Local :=
  .loop (.atom .fst) (.atom .snd) (body code)

def trajectory (code : List Instruction) (v : LocalValue) : ℕ→LocalValue
  | 0=>v
  | j+1=>next code (trajectory code v j)

def chargedStep (code : List Instruction) (u : LocalValue) : Bill LocalValue :=
  (run (program code) u).pay 4 0

def ticks (code : List Instruction) (v : LocalValue) (fuel : ℕ) : Bill LocalValue :=
  Bill.steps v (fun _=>chargedStep code) fuel

theorem body_run (code : List Instruction) (fuel j : ℕ) (v u : LocalValue) :
    run (body code) ((fuel,v),(j,u))=(run (program code) u).pay 4 0 := by
  simp only [body,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
  congr 1; omega

theorem ticks_zero (code : List Instruction) (v : LocalValue) : ticks code v 0=Bill.one v := rfl

theorem ticks_succ (code : List Instruction) (v : LocalValue) (fuel : ℕ) :
    ticks code v (fuel+1)=((ticks code v fuel).pass
      (fun u=>(run (program code) u).pay 4 0)).pay 1 (fuel+1) := by
  rfl

theorem fuel_run (code : List Instruction) (fuel : ℕ) (v : LocalValue) :
    run (fuelProgram code) (fuel,v)=(ticks code v fuel).pay 3 0 := by
  have hb:(fun i z=>run (body code) ((fuel,v),(i,z)))=
      (fun (_ : ℕ)=>chargedStep code) := by
    funext i z;exact body_run code fuel i v z
  change ((Bill.one fuel).pass (fun l=>(Bill.one v).pass (fun y=>
    Bill.steps y (fun i z=>run (body code) ((fuel,v),(i,z))) l))).pay 1 0=_
  rw [hb]
  change ((Bill.one fuel).pass (fun _=>(Bill.one v).pass (fun _=>ticks code v fuel))).pay 1 0=_
  generalize ticks code v fuel=b
  cases b
  simp only [Bill.one,Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  congr 1; omega


theorem ticks_value (code : List Instruction) (v : LocalValue) (fuel : ℕ) :
    (ticks code v fuel).val=trajectory code v fuel := by
  induction fuel with
  | zero=>rfl
  | succ j ih=>
    rw [ticks_succ]
    simp only [Bill.pay,Bill.pass,program_value,ih,trajectory]

theorem fuel_value (code : List Instruction) (fuel : ℕ) (v : LocalValue) :
    (run (fuelProgram code) (fuel,v)).val=trajectory code v fuel := by
  rw [fuel_run];exact ticks_value code v fuel

theorem ticks_valid (code : List Instruction) (v : LocalValue) (fuel : ℕ) :
    (ticks code v fuel).valid↔∀j,j<fuel→Accepted code (trajectory code v j) := by
  induction fuel with
  | zero=>simp [ticks_zero,Bill.one]
  | succ k ih=>
    rw [ticks_succ]
    simp only [Bill.pay,Bill.pass,ticks_value,program_valid,ih]
    constructor
    · rintro ⟨before,last⟩ j hj
      by_cases h:j=k
      · subst j;exact last
      · exact before j (by omega)
    · intro all;exact ⟨fun j hj=>all j (by omega),all k (by omega)⟩

theorem fuel_valid (code : List Instruction) (fuel : ℕ) (v : LocalValue) :
    (run (fuelProgram code) (fuel,v)).valid↔∀j,j<fuel→Accepted code (trajectory code v j) := by
  rw [fuel_run];exact ticks_valid code v fuel

theorem next_lengths (code : List Instruction) (v : LocalValue) :
    (next code v).2.1.len=v.2.1.len ∧ (next code v).2.2.len=v.2.2.len := by
  cases h:code[v.1]? with
  | none=>simp only [next,h];trivial
  | some i=>
    have lengths:=instruction_lengths i v
    rw [instruction_value] at lengths
    simpa only [next,h] using lengths

theorem trajectory_lengths (code : List Instruction) (v : LocalValue) (j : ℕ) :
    (trajectory code v j).2.1.len=v.2.1.len ∧ (trajectory code v j).2.2.len=v.2.2.len := by
  induction j with
  | zero=>exact ⟨rfl,rfl⟩
  | succ j ih=>
    have now:=next_lengths code (trajectory code v j)
    exact ⟨now.1.trans ih.1,now.2.trans ih.2⟩

theorem ticks_work (code : List Instruction) (v : LocalValue) (fuel : ℕ) :
    (ticks code v fuel).work≤1+fuel*(35*(v.2.1.len+v.2.2.len)+105+6*code.length) := by
  induction fuel with
  | zero=>simp [ticks_zero,Bill.one]
  | succ k ih=>
    rw [ticks_succ]
    simp only [Bill.pay,Bill.pass,ticks_value]
    have bound:=program_work code (trajectory code v k)
    obtain ⟨regs,heap⟩:=trajectory_lengths code v k
    rw [regs,heap] at bound
    nlinarith

theorem fuel_work (code : List Instruction) (fuel : ℕ) (v : LocalValue) :
    (run (fuelProgram code) (fuel,v)).work≤
      4+fuel*(35*(v.2.1.len+v.2.2.len)+105+6*code.length) := by
  rw [fuel_run]
  have bound:=ticks_work code v fuel
  change (ticks code v fuel).work+3≤_
  omega

theorem ticks_peak (code : List Instruction) (v : LocalValue) (fuel B : ℕ)
    (fuelBound : fuel≤B)
    (pcBounds : ∀j,j<fuel→(trajectory code v j).1≤B)
    (selected : ∀j,j<fuel→∀i,code[(trajectory code v j).1]?=some i→
      PeakBound i (trajectory code v j) B) :
    (ticks code v fuel).peak≤B := by
  induction fuel with
  | zero=>exact Nat.zero_le _
  | succ k ih=>
    rw [ticks_succ]
    simp only [Bill.pay,Bill.pass,ticks_value,max_zero]
    have before:=ih (by omega) (fun j hj=>pcBounds j (by omega))
      (fun j hj=>selected j (by omega))
    have last:=program_peak code (trajectory code v k) B (pcBounds k (by omega))
      (selected k (by omega))
    omega

theorem fuel_peak (code : List Instruction) (fuel : ℕ) (v : LocalValue) (B : ℕ)
    (fuelBound : fuel≤B)
    (pcBounds : ∀j,j<fuel→(trajectory code v j).1≤B)
    (selected : ∀j,j<fuel→∀i,code[(trajectory code v j).1]?=some i→
      PeakBound i (trajectory code v j) B) :
    (run (fuelProgram code) (fuel,v)).peak≤B := by
  rw [fuel_run]
  simpa only [Bill.pay,max_zero] using ticks_peak code v fuel B fuelBound pcBounds selected

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
