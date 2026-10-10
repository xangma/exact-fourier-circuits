import DFTModelSavingCostInstruction
import DFTModelSavingCostList

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics UniformFixedNetwork
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.stream
  DFTModelCacheRecords.seed ExplicitSeedBudget.m recordUnit recordWeight
  UniformRecursiveRuntimeInventory.recursiveDirections

def tapeWeight (rs : List Record) : ℕ := (rs.map recordWeight).sum

lemma sum_recordCharge (q r C : ℕ) (rs : List Record) :
    (rs.map (recordCharge q r C)).sum=
      recordUnit m UniformBatching.width*tapeWeight rs*2^(q*m+r)+
        UniformRecursiveRuntimeInventory.directions rs*2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  induction rs with
  | nil=>simp [tapeWeight,UniformRecursiveRuntimeInventory.directions]
  | cons x rs ih=>
    simp only [List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [recordCharge,tapeWeight,List.map_cons,List.sum_cons,
      UniformRecursiveRuntimeInventory.directions]
    ring

lemma tapeWeight_columns (q : ℕ) (rs : List Record) :
    tapeWeight (rs.map (Record.withColumns q))=tapeWeight rs := by
  simp only [tapeWeight,List.map_map,Function.comp_def,recordWeight_columns]

/-- The sum bounds the real chronological intermediate banks. They need only
retain length; dependency flags and both affine channels are unrestricted. -/
theorem typed_stream_work (q r k C : ℕ) (I : ℂ) (is : List Instruction)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1≤q) (hr : r < m) (fits : UniformBatching.roleBits≤q*(m-1)+r)
    (len : bank.len=UniformBatching.width*2^(q*m+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
      (r,(DFTModelCacheRecords.recordTape (is.map (Instruction.record q)),((k,I),bank)))).work≤
      12+22*is.length+recordUnit m UniformBatching.width*
        tapeWeight (is.map (Instruction.record q))*2^(q*m+r)+
        UniformRecursiveRuntimeInventory.directions (is.map (Instruction.record q))*
          2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  let rs:=is.map (Instruction.record q)
  let tape:=DFTModelCacheRecords.recordTape rs
  have length : tape.len=is.length := by simp [tape,rs,DFTModelCacheRecords.recordTape,Tape.tab]
  have cap : ∀i,i < is.length→
      (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
        (r,(tape.look i (Tape.empty ℕ),
          (recordSteps UniformBatching.width r tape ((k,I),bank) h i).val))).work≤
      recordCharge q r C (Instruction.record q ((is[i]?).getD .initial)) := by
    intro i hi
    let prior:=(recordSteps UniformBatching.width r tape ((k,I),bank) h i).val
    have shape:=recordSteps_preserved UniformBatching.width r tape ((k,I),bank) h i
    have same : prior=((k,I),prior.2) := Prod.ext shape.1 rfl
    have lookup : tape.look i (Tape.empty ℕ)=DFTModelCacheRecords.dataTape (Instruction.record q is[i]).data := by
      rw [recordTape_lookup rs i (by simp [rs];exact hi)]
      simp only [rs,List.getElem_map]
    rw [lookup]
    change (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(DFTModelCacheRecords.dataTape (Instruction.record q is[i]).data,prior))).work≤_
    rw [same,List.getElem?_eq_getElem hi]
    exact instruction_work q r k C I is[i] _ (DFTModelSavingDirection.dataTape_source _) prior.2 h
      qp hr fits (shape.2.trans len) children
  rw [stream_work,length]
  have sum:=Finset.sum_le_sum (fun i hi=>cap i (Finset.mem_range.mp hi))
  have lookupSum:=sum_range_lookup is Instruction.initial
    (fun i=>recordCharge q r C (Instruction.record q i))
  rw [lookupSum] at sum
  have mapEq : (is.map (fun i=>recordCharge q r C (Instruction.record q i))).sum=
      (rs.map (recordCharge q r C)).sum := by simp only [rs,List.map_map,Function.comp_def]
  rw [mapEq,sum_recordCharge] at sum
  simpa only [Nat.add_assoc] using Nat.add_le_add_left sum (12+22*is.length)

def streamUnit : ℕ := 12+22*baseSchedule.length+
  recordUnit m UniformBatching.width*tapeWeight baseSchedule

/-- Actual Code prints its seed, then executes every genuine fixed record.
The exact recursive coefficient is S, including the actual unit padding. -/
theorem actual_stream_work (q r k C : ℕ) (I : ℂ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1≤q) (hr : r < m) (fits : UniformBatching.roleBits≤q*(m-1)+r)
    (len : bank.len=UniformBatching.width*2^(q*m+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
      (r,((run DFTModelCacheRecords.seed q).val,((k,I),bank)))).work≤
      streamUnit*2^(q*m+r)+UniformFixedNetwork.S*2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  have cap:=typed_stream_work q r k C I instructions bank h qp hr fits len children
  rw [records_actual] at cap
  have count : instructions.length=baseSchedule.length := by
    have eq:=congrArg List.length (records_actual q)
    simpa only [List.length_map,scheduleRecords] using eq
  rw [count,UniformRecursiveRuntimeInventory.schedule_directions] at cap
  have mass : tapeWeight (scheduleRecords q)=tapeWeight baseSchedule := tapeWeight_columns q baseSchedule
  rw [mass] at cap
  rw [DFTModelCacheRecords.seed_value]
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have fixed : 12+22*baseSchedule.length≤(12+22*baseSchedule.length)*2^(q*m+r) :=
    Nat.le_mul_of_pos_right _ vp
  unfold streamUnit
  nlinarith only [cap,fixed]

end
end ExactFourierCircuits.DFTModelSavingCost
