import DFTModelCacheDescriptorLog

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Pair := p w w
abbrev AmountInput := p Pair LogResult

def pairSize : Prog false Pair w :=
  nat .mul (.atom (.lit 2)) (nat .add (.atom .fst) (.atom .snd))
def amountSeed : Prog false Pair AmountInput :=
  .fork (.atom .id) (.comp pairSize logarithm)
def amountA : Prog false AmountInput w := .comp (.atom .fst) (.atom .fst)
def amountE : Prog false AmountInput w := .comp (.atom .fst) (.atom .snd)
def amountK : Prog false AmountInput w := .comp (.atom .snd) (.atom .fst)
def amountW : Prog false AmountInput w := .comp (.atom .snd) (.atom .snd)
def amountCore : Prog false AmountInput w :=
  nat .add (nat .mul (.atom (.lit 6))
    (nat .add (nat .mul (nat .mul (.atom (.lit 3)) amountK) amountW)
      (nat .mul (.atom (.lit 2)) amountW)))
    (nat .add (nat .mul (.atom (.lit 3)) amountA) amountE)
def amount : Prog false Pair w := .comp amountSeed amountCore

theorem amountCore_run (a e k W : ℕ) :
    run amountCore ((a,e),(k,W))=⟨6*(3*k*W+2*W)+(3*a+e),43,
      max (3*k) (max (3*k*W+2*W)
        (max 6 (6*(3*k*W+2*W)+(3*a+e)))),True⟩ := by
  simp [amountCore,nat,amountA,amountE,amountK,amountW,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,max_assoc,max_comm,max_left_comm]

attribute [local irreducible] logarithm amountCore amountSeed amount

theorem amount_value (a e : ℕ) :
    (run amount (a,e)).val=UniformWorkspacePlanner.gateCount a e+a+e := by
  obtain ⟨hv,_,_,_⟩:=logarithm_spec (2*(a+e))
  rw [amount]
  change (run amountCore (run amountSeed (a,e)).val).val=_
  have hs : (run amountSeed (a,e)).val=((a,e),(run logarithm (2*(a+e))).val) := by
    simp [amountSeed,pairSize,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [hs,hv,amountCore_run,UniformWorkspacePlanner.gateCount_eq]
  dsimp only [Bill.val,UniformWorkspacePlanner.exponent]
  ring

theorem amount_valid (a e : ℕ) : (run amount (a,e)).valid := by
  obtain ⟨hv,hd,_,_⟩:=logarithm_spec (2*(a+e))
  rw [amount]
  change (run amountSeed (a,e)).valid ∧ (run amountCore (run amountSeed (a,e)).val).valid
  constructor
  · simpa [amountSeed,pairSize,nat,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay] using hd
  · rcases (run amountSeed (a,e)).val with ⟨⟨a,e⟩,⟨k,W⟩⟩
    rw [amountCore_run]
    trivial

theorem amount_work (a e : ℕ) :
    (run amount (a,e)).work=28*Nat.clog 2 (2*(a+e))+79 := by
  obtain ⟨hv,_,hw,_⟩:=logarithm_spec (2*(a+e))
  rw [amount]
  change (run amountSeed (a,e)).work+(run amountCore (run amountSeed (a,e)).val).work+1=_
  have hs : run amountSeed (a,e)=
      ⟨((a,e),(run logarithm (2*(a+e))).val),
        (run logarithm (2*(a+e))).work+12,
        max (max 2 (a+e)) (max (2*(a+e)) (run logarithm (2*(a+e))).peak),
        (run logarithm (2*(a+e))).valid⟩ := by
    simp [amountSeed,pairSize,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
      Nat.add_assoc,max_assoc]
    omega
  rw [hs]
  dsimp only [Bill.val,Bill.work]
  rw [hv,amountCore_run,hw]
  simp only [Nat.add_assoc]

end
end ExactFourierCircuits.DFTModelCacheDescriptor
