import DFTModelCacheNatControlBounds

set_option autoImplicit false
/-! A fixed compile-time natural instruction list is selected by its real PC.
The exceptional guard is the inherited inverse-of-zero validity rejection;
all successful instruction paths compute only natural data. -/
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

def selectFrom (base : ℕ) : List Instruction → Prog false Local Local
  | [] => invalid
  | i::is => .ifz (nat .sub pc (literal base)) (instruction i) (selectFrom (base+1) is)

def program (code : List Instruction) : Prog false Local Local := selectFrom 0 code

def next (code : List Instruction) (v : LocalValue) : LocalValue :=
  match code[v.1]? with
  | none => v
  | some i => result i v

def Accepted (code : List Instruction) (v : LocalValue) : Prop :=
  ∃ i, code[v.1]?=some i ∧ Domain i v

theorem test_run (base : ℕ) (v : LocalValue) :
    run (nat .sub pc (literal base)) v=⟨v.1-base,5,max base (v.1-base),True⟩ := by
  simp [nat,pc,literal,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem invalid_run (v : LocalValue) : run invalid v=⟨v,7,0,False⟩ := by
  simp [invalid,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem selectFrom_nil (base : ℕ) (v : LocalValue) :
    run (selectFrom base []) v=⟨v,7,0,False⟩ := invalid_run v

theorem selectFrom_cons (base : ℕ) (i : Instruction) (is : List Instruction) (v : LocalValue) :
    run (selectFrom base (i::is)) v=
      (if v.1-base=0 then run (instruction i) v else run (selectFrom (base+1) is) v).pay
        6 (max base (v.1-base)) := by
  rw [selectFrom]
  simp only [run,Code.run,test_run,Bill.pass,Bill.pay,true_and]
  split <;> congr 1 <;> omega

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
