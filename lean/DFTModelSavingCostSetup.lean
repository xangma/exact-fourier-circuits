import DFTModelSavingProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.seed DFTModelSavingRecords.stream
  DFTModelSavingBinarySuffix.program DFTModelSavingProgram.large DFTModelSavingProgram.body
  DFTModelSavingProgram.ordinary UniformRecursiveSavingProgram.threshold

/-- A fixed preparation allowance for the actual finite seed literal syntax. -/
def seedAllowance : ℕ :=
  DFTModelCacheRecords.recordsCost UniformFixedNetworkScheduleMachine.baseSchedule

theorem seedArgs_run (q r : ℕ) (node : Node.T) :
    run DFTModelSavingProgram.seedArgs (q,(r,node))=
      {run DFTModelCacheRecords.seed q with
        val:=(r,((run DFTModelCacheRecords.seed q).val,node)),
        work:=(run DFTModelCacheRecords.seed q).work+10} := by
  simp only [DFTModelSavingProgram.seedArgs,DFTModelSavingProgram.rest,
    DFTModelSavingProgram.q,DFTModelSavingProgram.node,fork_run,comp_run,atom_run,
    Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem seedArgs_work (q r : ℕ) (node : Node.T) :
    (run DFTModelSavingProgram.seedArgs (q,(r,node))).work≤ seedAllowance+10 := by
  rw [seedArgs_run]
  exact Nat.add_le_add_right (DFTModelCacheRecords.seed_work q) 10

theorem seedArgs_peak (q r : ℕ) (node : Node.T) :
    (run DFTModelSavingProgram.seedArgs (q,(r,node))).peak≤
      q+DFTModelCacheRecords.recordsPeak UniformFixedNetworkScheduleMachine.baseSchedule := by
  rw [seedArgs_run]
  exact DFTModelCacheRecords.seed_peak q

theorem suffixArgs_run (q r : ℕ) (old node : Node.T) :
    run DFTModelSavingProgram.suffixArgs ((q,(r,old)),node)=
      ⟨(q*UniformFixedNetwork.m,node),9,
        max UniformFixedNetwork.m (q*UniformFixedNetwork.m),True⟩ := by
  simp [DFTModelSavingProgram.suffixArgs,DFTModelSavingProgram.q,DFTModelResidualCore.binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem recordArgs_run (r i : ℕ) (rs : Tape (Tape ℕ)) (old node : Node.T) :
    run DFTModelSavingRecords.recordArgs ((r,(rs,old)),(i,node))=
      ⟨(r,(rs.look i (Tape.empty ℕ),node)),19,0,True⟩ := by
  simp [DFTModelSavingRecords.recordArgs,DFTModelSavingRecords.records,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

/-- The body really selects one branch. This is an exact billing identity for
its actual test, not a supplied branch execution or output contract. -/
theorem body_run (h : Handler DFTModelClockControl.ChildPort) (k : ℕ)
    (I : ℂ) (v : Tape Tagged.T) :
    Code.run DFTModelSavingProgram.body h ((k,I),v)=
      (if k<UniformRecursiveSavingProgram.threshold then
        (run DFTModelSavingProgram.ordinary ((k,I),v)).pay 1 0
      else Code.run DFTModelSavingProgram.large h ((k,I),v)).pay
        9 UniformRecursiveSavingProgram.threshold := by
  rw [DFTModelSavingProgram.body]
  change (((run DFTModelSavingProgram.small ((k,I),v)).pay 1 0).pass
    (fun b=>if b=0 then Code.run DFTModelSavingProgram.large h ((k,I),v)
      else (run DFTModelSavingProgram.ordinary ((k,I),v)).pay 1 0)).pay 1 0=_
  rw [DFTModelSavingProgram.small_run]
  split_ifs <;> simp only [Bill.pay,Bill.pass,true_and,↓reduceIte,max_zero,Nat.one_ne_zero] <;>
    congr 1 <;> omega

/-- Exact work of the large branch: setup, produced seed, chronological stream,
charged spectator suffix, and fixed syntax overhead. The stream and suffix
are the real computations at their actual intermediate states. -/
theorem large_work (h : Handler DFTModelClockControl.ChildPort) (k : ℕ)
    (I : ℂ) (v : Tape Tagged.T) :
    let z:=(run DFTModelSavingProgram.setup ((k,I),v)).val
    let a:=(run DFTModelSavingProgram.seedArgs z).val
    let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h a).val
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).work=
      (run DFTModelSavingProgram.setup ((k,I),v)).work+
      (run DFTModelSavingProgram.seedArgs z).work+
      (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h a).work+
      (run DFTModelSavingProgram.suffixArgs (z,u)).work+
      (run DFTModelSavingBinarySuffix.program
        (run DFTModelSavingProgram.suffixArgs (z,u)).val).work+12 := by
  simp only [DFTModelSavingProgram.large,Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
