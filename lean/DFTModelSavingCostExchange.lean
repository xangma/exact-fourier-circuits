import DFTModelSavingShape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelRecursiveExchange.body
  DFTModelRecursiveExchange.pairProgram DFTModelRecursiveExchange.pairsProgram
  DFTModelRecursiveExchange.decode DFTModelRecursiveExchange.program

theorem exchange_steps_length (R : ℕ) (ps : Tape DFTModelRecursiveExchange.PairNat.T)
    (node : Node.T) (n : ℕ) :
    (DFTModelRecursiveExchange.steps R ps node n).val.2.len=node.2.len :=
  (DFTModelSavingShape.steps_preserves node
    (fun i old=>run (DFTModelRecursiveExchange.body R) ((ps,node),(i,old)))
    (fun _ _=>DFTModelSavingShape.exchange_body_preserves R _) n).2

theorem exchange_steps_work (R : ℕ) (ps : Tape DFTModelRecursiveExchange.PairNat.T)
    (node : Node.T) (n : ℕ) :
    (DFTModelRecursiveExchange.steps R ps node n).work≤1+(43+131*node.2.len)*n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have len:=exchange_steps_length R ps node n
    change (DFTModelRecursiveExchange.steps R ps node n).work+
      (run (DFTModelRecursiveExchange.body R)
        ((ps,node),(n,(DFTModelRecursiveExchange.steps R ps node n).val))).work+1≤_
    rcases he : (DFTModelRecursiveExchange.steps R ps node n).val with ⟨⟨k,I⟩,v⟩
    rw [he] at len
    rw [DFTModelRecursiveExchange.body_run]
    obtain ⟨d,s⟩:=ps.look n DFTModelRecursiveExchange.PairNat.blank
    have cost:=DFTModelRecursiveExchange.pair_work_bound R d s k I v
    dsimp only [Bill.pay]
    rw [len] at cost
    rw [Nat.mul_add,Nat.mul_one]
    omega

/-- Actual chronological signed exchanges, including overlapping pairs,
are billed without assuming canonical tags or a precomputed action. -/
theorem exchange_work (R : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (run (DFTModelRecursiveExchange.program R) (raw,node)).work≤
      19+(74+131*node.2.len)*(raw.look 6 0) := by
  rw [DFTModelRecursiveExchange.program_run]
  change (run DFTModelRecursiveExchange.decode raw).work+
    (run (DFTModelRecursiveExchange.pairsProgram R)
      ((run DFTModelRecursiveExchange.decode raw).val,node)).work+5≤_
  rw [DFTModelRecursiveExchange.pairs_run,DFTModelRecursiveExchange.decode_work]
  have cost:=exchange_steps_work R (run DFTModelRecursiveExchange.decode raw).val node
    (run DFTModelRecursiveExchange.decode raw).val.len
  have count : (run DFTModelRecursiveExchange.decode raw).val.len=raw.look 6 0 := by
    rw [DFTModelRecursiveExchange.decode_value]
    rfl
  rw [count] at cost ⊢
  dsimp only [Bill.pay]
  nlinarith

end
end ExactFourierCircuits.DFTModelSavingCost
