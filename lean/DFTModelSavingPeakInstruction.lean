import DFTModelSavingPeakRecordBounds
import UniformPaddingRecordProjections

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
open UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingScalar.program
  DFTModelSavingY.program DFTModelRecursiveExchange.program UniformBatching.width
  DFTModelCacheRecords.unitPeak fixedBlock paddingLocal directionLocal paddingCoeff directionCoeff
  Fintype.card

def instructionCoeffOf (roles padding : ℕ) : Instruction→ℕ
 | .initial=>6
 | .boundary _=>6
 | .macro a (.edge _ _ role edge)=>directionCoeff seedWidth ((fixedBlock a).embedding role).val edge.dimension
 | .macro _ (.shear _ _ _ _ _)=>W+7
 | .translation=>4*(W+(8+(m+1)*UniformNativeHandlerSemantics.actualDirections.length)+1)+5
 | .exchange=>W+(8+4*UniformNativeHandlerSemantics.actualPairs.length)+4
 | .padding=>paddingCoeff m roles padding+5

lemma instructionCoeffOf_padding (roles padding : ℕ) :
    instructionCoeffOf roles padding .padding=paddingCoeff m roles padding+5 := rfl

attribute [local irreducible] instructionCoeffOf

def instructionCoeff : Instruction→ℕ := instructionCoeffOf actualRoles (W-actualRoles)

lemma instructionCoeff_padding : instructionCoeff .padding=paddingCoeff m actualRoles (W-actualRoles)+5 :=
  instructionCoeffOf_padding actualRoles (W-actualRoles)

attribute [local irreducible] instructionCoeff
  UniformNativeHandlerSemantics.actualDirections UniformNativeHandlerSemantics.actualPairs

lemma square_one (q r : ℕ) : 1 ≤ 2^(q*m+r)*2^(q*m+r):= (volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])).1

private theorem initial_bound (q r k C : ℕ) (I : ℂ)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q .initial) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (_qp : 1 ≤ q) (_rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (_before : Boolean bank)
    (_preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (_children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff .initial*(2^(q*m+r)*2^(q*m+r))) := by
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff : instructionCoeff .initial=6 := by unfold instructionCoeff instructionCoeffOf;rfl
  have small : 5 ≤ max C (instructionCoeff .initial*(2^(q*m+r)*2^(q*m+r))) := by
    rw [coeff]

    exact (const_mul_bound 5 1 _ one).trans (le_max_right _ _)
  exact (marker_six_peak UniformBatching.width r raw ((k,I),bank) h headers.1).le.trans small


private theorem boundary_bound (q r k C : ℕ) (I : ℂ) (a : Invocation)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q (.boundary a)) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (_qp : 1 ≤ q) (_rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (_before : Boolean bank)
    (_preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (_children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff (.boundary a)*(2^(q*m+r)*2^(q*m+r))) := by
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff : instructionCoeff (.boundary a)=6 := by unfold instructionCoeff instructionCoeffOf;rfl
  have small : 2 ≤ max C (instructionCoeff (.boundary a)*(2^(q*m+r)*2^(q*m+r))) := by
    rw [coeff]

    exact (const_mul_bound 2 4 _ one).trans (le_max_right _ _)
  exact (marker_two_peak UniformBatching.width r raw ((k,I),bank) h headers.1).le.trans small


private theorem edge_bound (q r k C : ℕ) (I : ℂ) (a : Invocation) {old new : Label seedWidth} (role : Fin (fixedBlock a).width) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q (.macro a (.edge old new role edge))) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1 ≤ q) (rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff (.macro a (.edge old new role edge))*(2^(q*m+r)*2^(q*m+r))) := by
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have eq : seedWidth=m:=dimension_eq
  have edgePeak:=edge_peak_pos q r k C (fixedBlock a).embedding role edge raw source I bank h
    (by rw [eq];norm_num [m,ExplicitSeedBudget.m]) qp (by rwa [eq])
    (by simpa only [eq] using len') before preserve children
  have coeff : instructionCoeff (.macro a (.edge old new role edge))=
      directionCoeff seedWidth ((fixedBlock a).embedding role).val edge.dimension := by
    unfold instructionCoeff instructionCoeffOf;rfl
  have boundEq : max C (directionCoeff seedWidth ((fixedBlock a).embedding role).val edge.dimension*
      (2^(q*seedWidth+r)*2^(q*seedWidth+r)))=
      max C (instructionCoeff (.macro a (.edge old new role edge))*(2^(q*m+r)*2^(q*m+r))) := by
    have powEq : 2^(q*seedWidth+r)*2^(q*seedWidth+r)=2^(q*m+r)*2^(q*m+r) :=
      congrArg (fun t : ℕ=>2^(q*t+r)*2^(q*t+r)) eq
    rw [coeff,powEq]
  exact edgePeak.trans_eq boundEq


private theorem scalar_bound (q r k C : ℕ) (I : ℂ) (a : Invocation) (d src : Fin (fixedBlock a).width) (ne : d≠src) (c : Fin 5) (hc : UniformFixedCoefficientCodec.decode c≠0)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q (.macro a (.shear d src ne c hc))) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (_qp : 1 ≤ q) (_rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (_before : Boolean bank)
    (_preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (_children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff (.macro a (.shear d src ne c hc))*(2^(q*m+r)*2^(q*m+r))) := by
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff : instructionCoeff (.macro a (.shear d src ne c hc))=W+7 := by unfold instructionCoeff instructionCoeffOf;rfl
  have aw : actualRoles ≤ W:=by
    rw [show W=2^ExplicitSeedBudget.roleBits from ExplicitSeedBudget.padding.1]
    exact MasterBudget.seed_actual_padding
  have dp : ((fixedBlock a).embedding d).val<W:=lt_of_lt_of_le ((fixedBlock a).embedding d).isLt aw
  have sp : ((fixedBlock a).embedding src).val<W:=lt_of_lt_of_le ((fixedBlock a).embedding src).isLt aw
  have cap:=DFTModelSavingScalar.program_peak W (2^k) _ _ k (W*2^k+7) I raw bank
    (by positivity) positive (by simpa only [wm] using len) dp sp (by omega) (by omega)
    headers.2.2.2.1 headers.2.2.2.2.1 (by rw [headers.2.2.2.2.2.2.2];exact Nat.le_of_lt_succ c.isLt)
  have selected:=(scalar_dispatch_peak UniformBatching.width r raw ((k,I),bank) h headers.1).trans
    (congrArg (fun R=>max (run (DFTModelSavingScalar.program R) (raw,((k,I),bank))).peak 1) wm)
  apply selected.le.trans
  refine max_le (cap.trans (le_trans ?_ (le_max_right _ _))) ?_
  · rw [coeff]
    change W*2^k+7 ≤ (W+7)*(2^(q*m+r)*2^(q*m+r))
    rw [shape]
    exact scalar_local_bound W _ _ one volumes.2.1
  · apply le_trans _ (le_max_right _ _)
    rw [coeff]
    change 1 ≤ (W+7)*(2^(q*m+r)*2^(q*m+r))
    exact scalar_const_bound W _ one


private theorem translation_bound (q r k C : ℕ) (I : ℂ)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q .translation) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1 ≤ q) (rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (_preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (_children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff .translation*(2^(q*m+r)*2^(q*m+r))) := by
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff : instructionCoeff .translation=4*(W+(8+(m+1)*UniformNativeHandlerSemantics.actualDirections.length)+1)+5 := by unfold instructionCoeff instructionCoeffOf;rfl
  have eqr:=UniformNativeHandlerSemantics.translation_record q
  change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=_ at eqr
  have recordSource : DFTModelSavingY.RecordSource q UniformNativeHandlerSemantics.actualDirections raw :=
    Eq.mpr (congrArg (fun rec : Record=>RawSource rec raw) eqr) source
  let size:=8+(m+1)*UniformNativeHandlerSemantics.actualDirections.length
  let B:=W*2^k+size+2^k*2^k
  have padded : 2^(q*(m+r)) ≤ B:=by
    clear source eqr recordSource coeff
    have exp : q*(m+r) ≤ 2*k:=by rw [shape];nlinarith only [Nat.mul_le_mul_left q (Nat.le_of_lt rp)]
    have power:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) exp
    have powerEq : (2:ℕ)^(2*k)=2^k*2^k := by rw [Nat.mul_comm 2 k,pow_mul,pow_two]
    exact power.trans (powerEq.le.trans (Nat.le_add_left _ _))
  have square : 2^q*2^q ≤ B:=by
    clear source eqr recordSource coeff
    have mp : 1 ≤ m:=by norm_num [m,ExplicitSeedBudget.m]
    have ex : q ≤ k:= ((Nat.le_mul_of_pos_right q mp).trans (Nat.le_add_right _ r)).trans_eq shape.symm
    have p:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) ex
    exact (Nat.mul_le_mul p p).trans (Nat.le_add_left _ _)
  have extent : W*2^k ≤ B := (Nat.le_add_right _ size).trans (Nat.le_add_right _ (2^k*2^k))
  have recordFit : size ≤ B := (Nat.le_add_left size (W*2^k)).trans (Nat.le_add_right _ (2^k*2^k))
  have cap:=y_peak q r k B I raw UniformNativeHandlerSemantics.actualDirections recordSource bank
    (by simpa only [wm] using len) before positive shape qp extent recordFit padded square
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have op : raw.look 0 0=3 := headers.1.trans (congrArg Record.opcode eqr).symm
  have selected:=(y_dispatch_peak UniformBatching.width r raw ((k,I),bank) h op).trans
    (congrArg (fun R=>max (run (DFTModelSavingY.program R) (r,(raw,((k,I),bank)))).peak 3) wm)
  have bound : 4*B+2 ≤ instructionCoeff .translation*(2^(q*m+r)*2^(q*m+r)) := by
    rw [coeff]
    change 4*B+2 ≤ (4*(W+size+1)+5)*(2^(q*m+r)*2^(q*m+r))
    dsimp only [B]
    rw [shape]
    exact y_local_bound W size _ _ one volumes.2.1 rfl
  have c3 : 3 ≤ instructionCoeff .translation*(2^(q*m+r)*2^(q*m+r)) := by
    rw [coeff]
    change 3 ≤ (4*(W+size+1)+5)*(2^(q*m+r)*2^(q*m+r))
    exact y_const_bound W size _ one
  exact selected.le.trans (max_le (cap.trans (bound.trans (le_max_right _ _)))
    (c3.trans (le_max_right _ _)))


private theorem exchange_bound (q r k C : ℕ) (I : ℂ)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q .exchange) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (_qp : 1 ≤ q) (_rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (_preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (_children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff .exchange*(2^(q*m+r)*2^(q*m+r))) := by
  have one:=square_one q r
  have wm : UniformBatching.width=W:=by rw [UniformBatching.width_eq_pow,UniformBatching.roleBits_eq,W_eq]
  have positive : 0 < W:=by rw [W_eq];positivity
  have volumes:=volume_bounds q m r (by norm_num [m,ExplicitSeedBudget.m])
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff : instructionCoeff .exchange=W+(8+4*UniformNativeHandlerSemantics.actualPairs.length)+4 := by unfold instructionCoeff instructionCoeffOf;rfl
  have eqr:=UniformNativeHandlerSemantics.exchange_record q
  change UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs=_ at eqr
  let size:=8+4*UniformNativeHandlerSemantics.actualPairs.length
  have source' : RawSource (UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs) raw :=
    Eq.mpr (congrArg (fun rec : Record=>RawSource rec raw) eqr) source
  have cap:=exchange_peak_raw q m k (W*2^k+size) UniformNativeHandlerSemantics.actualPairs I raw source' bank
    (by simpa only [wm] using len) before positive (Nat.le_add_left size (W*2^k)) (Nat.le_add_right _ size)
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have op : raw.look 0 0=4 := headers.1.trans (congrArg Record.opcode eqr).symm
  have selected:=(exchange_dispatch_peak UniformBatching.width r raw ((k,I),bank) h op).trans
    (congrArg (fun R=>max (run (DFTModelRecursiveExchange.program R) (raw,((k,I),bank))).peak 4) wm)
  have bound : W*2^k+size ≤ instructionCoeff .exchange*(2^(q*m+r)*2^(q*m+r)) := by
    rw [coeff]
    change W*2^k+size ≤ (W+size+4)*(2^(q*m+r)*2^(q*m+r))
    rw [shape]
    exact exchange_local_bound W size _ _ one volumes.2.1
  have c4 : 4 ≤ instructionCoeff .exchange*(2^(q*m+r)*2^(q*m+r)) := by
    rw [coeff]
    change 4 ≤ (W+size+4)*(2^(q*m+r)*2^(q*m+r))
    exact exchange_const_bound W size _ one
  exact selected.le.trans (max_le (cap.trans (bound.trans (le_max_right _ _)))
    (c4.trans (le_max_right _ _)))


private theorem padding_bound (q r k C : ℕ) (I : ℂ)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q .padding) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1 ≤ q) (rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff .padding*(2^(q*m+r)*2^(q*m+r))) := by
  have len':bank.len=UniformBatching.width*2^(q*m+r):=by rw [←shape];exact len
  have coeff := instructionCoeff_padding
  have headers:=DFTModelSavingCost.raw_headers _ raw source
  have cap:=padding_dispatch_bound q r k C actualRoles (W-actualRoles) I raw bank h
    (headers.1.trans (UniformPaddingRecordProjections.opcode q))
    (headers.2.1.trans (UniformPaddingRecordProjections.columns q))
    (headers.2.2.2.1.trans (UniformPaddingRecordProjections.dest q))
    (headers.2.2.2.2.1.trans (UniformPaddingRecordProjections.source q)) qp rp len' before preserve children
  exact cap.trans_eq (congrArg (fun t=>max C (t*(2^(q*m+r)*2^(q*m+r)))) coeff.symm)

theorem instruction_peak (q r k C : ℕ) (I : ℂ) (i : Instruction)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q i) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1 ≤ q) (rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (instructionCoeff i*(2^(q*m+r)*2^(q*m+r))) := by
  cases i with
  | initial=>exact initial_bound q r k C I raw source bank h qp rp shape len before preserve children
  | boundary a=>exact boundary_bound q r k C I a raw source bank h qp rp shape len before preserve children
  | «macro» a v=>
    cases v with
    | edge old new role edge=>exact edge_bound q r k C I a role edge raw source bank h qp rp shape len before preserve children
    | shear d src ne c hc=>exact scalar_bound q r k C I a d src ne c hc raw source bank h qp rp shape len before preserve children
  | translation=>exact translation_bound q r k C I raw source bank h qp rp shape len before preserve children
  | exchange=>exact exchange_bound q r k C I raw source bank h qp rp shape len before preserve children
  | padding=>exact padding_bound q r k C I raw source bank h qp rp shape len before preserve children

end
end ExactFourierCircuits.DFTModelSavingPeak
