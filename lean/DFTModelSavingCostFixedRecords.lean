import DFTModelSavingCostFixedArithmetic

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.residual
  DFTModelSavingRecords.padding DFTModelSavingScalar.program DFTModelSavingY.program
  DFTModelRecursiveExchange.program DFTModelResidualTable.program
  unitAllowance ExplicitSeedBudget.m

lemma recordWeight_columns (q : ℕ) (r : Record) : recordWeight (r.withColumns q)=recordWeight r := rfl

lemma seedWidth_eq : seedWidth=m := dimension_eq

lemma recordWeight_positive (r : Record) : 1≤recordWeight r := by unfold recordWeight;omega
lemma recordWeight_dimension (r : Record) : r.dimension+1≤recordWeight r := by unfold recordWeight;omega

attribute [local irreducible] recordUnit recordWeight
  UniformRecursiveRuntimeInventory.recursiveDirections fixedBlock

lemma padding_dispatch_bound (q w r k C : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (op : raw.look 0 0=5) (columns : raw.look 1 0=q) (widthEq : w+1=ExplicitSeedBudget.m)
    (qp : 1≤q) (wide : 2≤w) (hr : r<w+1)
    (fits : UniformBatching.roleBits≤q*w+r)
    (len : bank.len=UniformBatching.width*2^(q*(w+1)+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤
      recordUnit (w+1) UniformBatching.width*(raw.look 4 0*(w+1+1)+1)*2^(q*(w+1)+r)+
        (raw.look 4 0*(w+1))*2^(q*w+r-UniformBatching.roleBits)*C := by
  rw [dispatch_work,op]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  have cost:=padding_work q w r k C I raw bank h columns widthEq qp wide fits children
  rw [len] at cost
  have dir:=directionAllowance_bound q (w+1) r UniformBatching.width C hr
  have vp : 1≤2^(q*(w+1)+r) := Nat.two_pow_pos _
  have unit : 51+unitAllowance≤recordUnit (w+1) UniformBatching.width := by unfold recordUnit;omega
  have control : 88≤recordUnit (w+1) UniformBatching.width := by unfold recordUnit;omega
  have scaled:=Nat.mul_le_mul_right (2^(q*(w+1)+r)) unit
  have controlScaled:=Nat.mul_le_mul_right (2^(q*(w+1)+r)) control
  have dirScaled:=Nat.mul_le_mul_right (w+1) dir
  have role : paddingRoleAllowance q (w+1) r (UniformBatching.width*2^(q*(w+1)+r)) C≤
      recordUnit (w+1) UniformBatching.width*(w+1+1)*2^(q*(w+1)+r)+
        (w+1)*2^(q*w+r-UniformBatching.roleBits)*C := by
    unfold paddingRoleAllowance
    simp only [Nat.add_sub_cancel] at dirScaled
    nlinarith
  have roles:=Nat.mul_le_mul_right (raw.look 4 0) role
  nlinarith



def recordCharge (q r C : ℕ) (record : Record) : ℕ :=
  recordUnit m UniformBatching.width*recordWeight record*2^(q*m+r)+
    UniformRecursiveRuntimeInventory.recursiveDirections record*
      2^(q*(m-1)+r-UniformBatching.roleBits)*C

lemma charge_ge (q r C : ℕ) (record : Record) :
    recordUnit m UniformBatching.width*2^(q*m+r)≤recordCharge q r C record := by
  exact charge_at_least_local (recordUnit m UniformBatching.width) (recordWeight record)
    (2^(q*m+r)) _ (recordWeight_positive record)

lemma record_unit_control (q r : ℕ) : 1000≤recordUnit m UniformBatching.width*2^(q*m+r) := by
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have unit : 1000≤recordUnit m UniformBatching.width := (fixed_unit_coefficients m UniformBatching.width).1
  exact unit.trans (Nat.le_mul_of_pos_right _ vp)

lemma marker_record_work (q r k C : ℕ) (I : ℂ) (record : Record) (raw : Tape ℕ)
    (source : RawSource record raw) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (marker : record.opcode=2 ∨ 6≤record.opcode) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤recordCharge q r C record := by
  have op:raw.look 0 0=record.opcode:=(raw_headers _ raw source).1
  have localBound : (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤1000 := by
    rw [dispatch_work,op]
    rcases marker with small|large
    · rw [small];norm_num
    · have a:¬record.opcode=0:=by omega
      have b:¬record.opcode-1=0:=by omega
      have c:¬record.opcode-2=0:=by omega
      have d:¬record.opcode-3=0:=by omega
      have e:¬record.opcode-4=0:=by omega
      have f:¬record.opcode-5=0:=by omega
      rw [ite_eq_right a,ite_eq_right b,ite_eq_right c,ite_eq_right d,ite_eq_right e,ite_eq_right f]
      omega
  exact localBound.trans ((record_unit_control q r).trans (charge_ge q r C record))

lemma scalar_record_work (q r k C : ℕ) (I : ℂ) (record : Record) (raw : Tape ℕ)
    (source : RawSource record raw) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : record.opcode=1) (len : bank.len=UniformBatching.width*2^(q*m+r)) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤recordCharge q r C record := by
  have op:raw.look 0 0=1:=(raw_headers _ raw source).1.trans opcode
  have cap:=scalar_dispatch_work UniformBatching.width r k I raw bank h op
  rw [len] at cap
  have coeff : 127+179*UniformBatching.width≤recordUnit m UniformBatching.width :=
    (fixed_unit_coefficients m UniformBatching.width).2.1
  have scaled:=Nat.mul_le_mul_right (2^(q*m+r)) coeff
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have localBound : 127+179*(UniformBatching.width*2^(q*m+r))≤
      recordUnit m UniformBatching.width*2^(q*m+r) := by nlinarith only [vp,scaled]
  exact cap.trans (localBound.trans (charge_ge q r C record))

lemma translation_record_work (q r k C : ℕ) (I : ℂ) (record : Record) (raw : Tape ℕ)
    (source : RawSource record raw) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : record.opcode=3) (columns : record.columns=q) (width : record.width=m)
    (hr : r < m) (len : bank.len=UniformBatching.width*2^(q*m+r)) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤recordCharge q r C record := by
  have header:=raw_headers record raw source
  have cap:=translation_dispatch_work q m r k I raw bank h (header.1.trans opcode)
    (header.2.1.trans columns) (header.2.2.1.trans width)
    (by norm_num [m,ExplicitSeedBudget.m]) hr len
  rw [header.2.2.2.2.2.2.1] at cap
  have dim:=recordWeight_dimension record
  have weightCap:=Nat.mul_le_mul_right (2^(q*m+r))
    (Nat.mul_le_mul_left (recordUnit m UniformBatching.width) dim)
  exact cap.trans (weightCap.trans (Nat.le_add_right _ _))

lemma exchange_record_work (q r k C : ℕ) (I : ℂ) (record : Record) (raw : Tape ℕ)
    (source : RawSource record raw) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : record.opcode=4) (len : bank.len=UniformBatching.width*2^(q*m+r)) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤recordCharge q r C record := by
  have header:=raw_headers record raw source
  have cap:=exchange_dispatch_work UniformBatching.width r k I raw bank h (header.1.trans opcode)
  rw [len,header.2.2.2.2.2.2.1] at cap
  have dim:=recordWeight_dimension record
  have coeff : 74+131*UniformBatching.width≤recordUnit m UniformBatching.width :=
    (fixed_unit_coefficients m UniformBatching.width).2.2
  have scaled:=Nat.mul_le_mul_right (2^(q*m+r)) coeff
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have row : 74+131*(UniformBatching.width*2^(q*m+r))≤
      recordUnit m UniformBatching.width*2^(q*m+r) := by nlinarith only [vp,scaled]
  have rows:=Nat.mul_le_mul_right record.dimension row
  have control : 90≤recordUnit m UniformBatching.width*2^(q*m+r) :=
    (by omega : 90≤1000).trans (record_unit_control q r)
  have weightCap:=Nat.mul_le_mul_right (2^(q*m+r))
    (Nat.mul_le_mul_left (recordUnit m UniformBatching.width) dim)
  have localBound : 90+(74+131*(UniformBatching.width*2^(q*m+r)))*record.dimension≤
      recordUnit m UniformBatching.width*(record.dimension+1)*2^(q*m+r) := by
    nlinarith only [control,rows]
  exact cap.trans (localBound.trans (weightCap.trans (Nat.le_add_right _ _)))

lemma padding_record_work (q r k C : ℕ) (I : ℂ) (record : Record) (raw : Tape ℕ)
    (source : RawSource record raw) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (opcode : record.opcode=5) (columns : record.columns=q)
    (qp : 1≤q) (hr : r < m) (fits : UniformBatching.roleBits≤q*(m-1)+r)
    (len : bank.len=UniformBatching.width*2^(q*m+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤recordCharge q r C record := by
  have header:=raw_headers record raw source
  have pred : m-1+1=m := Nat.sub_add_cancel (by norm_num [m,ExplicitSeedBudget.m])
  have cap:=padding_dispatch_bound q (m-1) r k C I raw bank h (header.1.trans opcode)
    (header.2.1.trans columns) pred qp (by norm_num [m,ExplicitSeedBudget.m])
    (by rwa [pred]) fits (by rwa [pred]) children
  rw [pred,header.2.2.2.2.1] at cap
  have dirs : UniformRecursiveRuntimeInventory.recursiveDirections record=record.source*m := by
    rw [UniformRecursiveRuntimeInventory.recursiveDirections,opcode]
    norm_num
  have weight : record.source*(m+1)+1≤recordWeight record := by
    unfold recordWeight
    rw [dirs]
    nlinarith
  have weightCap:=Nat.mul_le_mul_right (2^(q*m+r))
    (Nat.mul_le_mul_left (recordUnit m UniformBatching.width) weight)
  unfold recordCharge
  rw [dirs]
  exact cap.trans (Nat.add_le_add_right weightCap _)

end
end ExactFourierCircuits.DFTModelSavingCost
