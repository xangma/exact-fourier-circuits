import UniformRecursiveV2CostAllowance
import UniformRecursiveCoreSchedule
import UniformPaddingRecordProjections

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveTypedCostAllowance
open UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open UniformRecursiveTypedBody UniformRecursiveCoreSchedule
noncomputable section

lemma m_three : 3  ≤  m := by decide
lemma m_pred : m-1+1=m := Nat.sub_add_cancel (by decide)

/-- Padding's actual charged loop cost, including all same-q unit directions. -/
def paddingTicks (q rest : ℕ) (cost : ℕ→ℕ) : ℕ :=
 73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost)

def chargedTicks (q rest : ℕ) (cost : ℕ→ℕ) : Instruction→ℕ
 | .padding => paddingTicks q rest cost
 | i => ticks q rest cost i

lemma charged_padding (q rest : ℕ) (cost : ℕ→ℕ) :
 chargedTicks q rest cost .padding=paddingTicks q rest cost := rfl

lemma charged_nonpadding (q rest : ℕ) (cost : ℕ→ℕ) (i : Instruction) (h : NoPadding i) :
 chargedTicks q rest cost i=ticks q rest cost i := by
 cases i with
 | initial => rfl
 | boundary _ => rfl
 | «macro» _ v => cases v <;> rfl
 | translation => rfl
 | exchange => rfl
 | padding => exact False.elim h

lemma opcode_lt (q : ℕ) (i : Instruction) : (Instruction.record q i).opcode<7 := by
 cases i with
 | initial => change 6<7;decide
 | boundary _ => change 2<7;decide
 | «macro» _ v => cases v <;> first | change 0<7;decide | change 1<7;decide
 | translation => change 3<7;decide
 | exchange => change 4<7;decide
 | padding => change 5<7;decide

lemma translation_rows (q : ℕ) :
 UniformNativeHandlerSemantics.actualDirections.length ≤ (Instruction.record q .translation).data.length := by
 have eq:=UniformNativeHandlerSemantics.translation_record q
 change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=_ at eq
 rw [←eq,UniformNativeYRecordMachine.record_length]
 have h : 1 ≤ m+1 := by omega
 have mul:=Nat.le_mul_of_pos_left UniformNativeHandlerSemantics.actualDirections.length h
 omega

lemma exchange_pairs (q : ℕ) :
 UniformNativeHandlerSemantics.actualPairs.length ≤ (Instruction.record q .exchange).data.length := by
 rw [←UniformNativeHandlerSemantics.exchange_record,UniformNativeExchangeRecordMachine.record_length]
 omega

lemma marker_for_record (m k groups child : ℕ) (r : Record)
 (dirs : UniformRecursiveRuntimeInventory.recursiveDirections r=0)
 (hh : UniformFixedNetworkOpcodeMachine.headCost r ≤ 38)
 (hd : UniformRecursiveRecordControl.dispatchCost r.opcode ≤ 94) :
 6+2*UniformFixedNetworkOpcodeMachine.headCost r+UniformRecursiveRecordControl.dispatchCost r.opcode ≤
 UniformRecursiveLocalAllowance.recordAllowance m k r+
 UniformRecursiveRuntimeInventory.recursiveDirections r*groups*child := by
 simp only [UniformRecursiveLocalAllowance.recordAllowance,dirs,Nat.zero_mul,Nat.add_zero]
 exact UniformRecursiveV2CostAllowance.marker_record_bound m k 0 r.data.length _ _ hh hd

lemma padding_at_width (q w width rest header roles data : ℕ) (cost : ℕ→ℕ)
 (eq : w+1=width) (hq : 1 ≤ q) (hm : 3 ≤ width) (hr : rest < width) (hh : header ≤ 38) :
 73+roles*(64+width*UniformRecursiveResidualDirectionLoop.directionCost q w rest header cost) ≤
 1000*(width+1)*(roles*width+data+1)*2^(q*width+rest)+
 (roles*width)*UniformRecursiveBatchGroupMachine.groupCount q w rest*(cost q+169) := by
 have cap:=UniformRecursiveV2CostAllowance.padding_record_bound q w rest header roles data cost
  hq (by rwa [eq]) (by rwa [eq]) hh
 rwa [eq] at cap

lemma padding_for_record (q rest : ℕ) (cost : ℕ→ℕ) (r : Record)
 (hq : 1 ≤ q) (hr : rest < m) (op : r.opcode=5) :
 73+r.source*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost) ≤
 UniformRecursiveLocalAllowance.recordAllowance m (q*m+rest) r+
 UniformRecursiveRuntimeInventory.recursiveDirections r*
 UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 have cap:=padding_at_width q (m-1) m rest 32 r.source r.data.length cost m_pred hq m_three hr (by decide)
 simpa only [UniformRecursiveLocalAllowance.recordAllowance,
  UniformRecursiveRuntimeInventory.recursiveDirections,op,show ¬(5:ℕ)=0 by decide,
  ite_false,ite_true] using cap

lemma padding_named (q rest : ℕ) (cost : ℕ→ℕ) (r : Record) (total roles : ℕ)
 (hq : 1 ≤ q) (hr : rest < m) (op : r.opcode=5) (source : r.source=roles)
 (value : total=73+roles*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost)) :
 total ≤ UniformRecursiveLocalAllowance.recordAllowance m (q*m+rest) r+
 UniformRecursiveRuntimeInventory.recursiveDirections r*
 UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 rw [value,←source]
 exact padding_for_record q rest cost r hq hr op

/-- Each actual typed handler cost fits its record's reserve; the precise
recursive coefficient is retained rather than absorbed or assumed. -/
theorem instruction_bound (q rest : ℕ) (cost : ℕ→ℕ) (hq : 1 ≤ q) (hr : rest < m)
 (i : Instruction) :
 chargedTicks q rest cost i ≤ 
 UniformRecursiveLocalAllowance.recordAllowance m (q*m+rest) (Instruction.record q i)+
 UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q i)*
 UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 cases i with
 | initial =>
  apply marker_for_record
  · rfl
  · change 38 ≤ 38;exact le_rfl
  · change 12 ≤ 94;decide
 | boundary a =>
  apply marker_for_record
  · rfl
  · change 34 ≤ 38;decide
  · change 5 ≤ 94;decide
 | «macro» a v =>
  cases v with
  | edge old new role edge =>
   have cap:=UniformRecursiveV2CostAllowance.residual_record_bound q (m-1) rest 32 edge.dimension
    (Instruction.record q (.«macro» a (.edge old new role edge))).data.length cost hq
    (by rw [m_pred];exact m_three) (by rwa [m_pred]) (by decide)
   rw [m_pred] at cap
   have dirs : UniformRecursiveRuntimeInventory.recursiveDirections
    (Instruction.record q (.«macro» a (.edge old new role edge)))=edge.dimension := rfl
   have header : UniformFixedNetworkOpcodeMachine.headCost
    (Instruction.record q (.«macro» a (.edge old new role edge)))=32 := rfl
   change edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
    (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q (.«macro» a (.edge old new role edge)))) cost+53 ≤ _
   rw [header,UniformRecursiveLocalAllowance.recordAllowance,dirs]
   exact (Nat.add_comm (edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost) 53).le.trans cap
  | shear d src ne c hc =>
   have cap:=UniformRecursiveLocalAllowance.scalar_record_bound m (q*m+rest)
    (UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q (.«macro» a (.shear d src ne c hc))))
    (Instruction.record q (.«macro» a (.shear d src ne c hc))).data.length c.val c.isLt
   have dirs : UniformRecursiveRuntimeInventory.recursiveDirections
    (Instruction.record q (.«macro» a (.shear d src ne c hc)))=0 := rfl
   change 10*2^(q*m+rest)+4*(q*m+rest)+c.val+102 ≤ _
   simpa only [UniformRecursiveLocalAllowance.recordAllowance,dirs,Nat.zero_mul,Nat.add_zero] using cap
 | translation =>
  have cap:=UniformRecursiveV2CostAllowance.translation_record_bound q m rest
   (UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q .translation))
   (Instruction.record q .translation).data.length UniformNativeHandlerSemantics.actualDirections.length
   m_three hr (translation_rows q)
  have op : (Instruction.record q .translation).opcode=3 := rfl
  have dirs : UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q .translation)=0 := by
   simp only [UniformRecursiveRuntimeInventory.recursiveDirections,op];rfl
  change UniformNativeYRecordMachine.runtime q m rest (q*m+rest) UniformNativeHandlerSemantics.actualDirections.length+51 ≤ _
  simpa only [UniformRecursiveLocalAllowance.recordAllowance,dirs,Nat.zero_mul,Nat.add_zero] using cap
 | exchange =>
  have cap:=UniformRecursiveLocalAllowance.exchange_record_bound m (q*m+rest)
   (UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q .exchange))
   (Instruction.record q .exchange).data.length UniformNativeHandlerSemantics.actualPairs.length (exchange_pairs q)
  have op : (Instruction.record q .exchange).opcode=4 := rfl
  have dirs : UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q .exchange)=0 := by
   simp only [UniformRecursiveRuntimeInventory.recursiveDirections,op];rfl
  change (10*2^(q*m+rest)+21)*UniformNativeHandlerSemantics.actualPairs.length+4*(q*m+rest)+99 ≤ _
  simpa only [UniformRecursiveLocalAllowance.recordAllowance,dirs,Nat.zero_mul,Nat.add_zero] using cap
 | padding =>
  exact padding_named q rest cost (Instruction.record q .padding) (paddingTicks q rest cost) (W-actualRoles)
   hq hr (UniformPaddingRecordProjections.opcode q) (UniformPaddingRecordProjections.source q) rfl

lemma sum_map_bound {α : Type*} (is : List α) (f g : α→ℕ)
 (bound : ∀i ∈ is,f i ≤ g i) : (is.map f).sum ≤ (is.map g).sum := by
 induction is with
 | nil => exact le_rfl
 | cons i is ih =>
  simp only [List.map_cons,List.sum_cons]
  exact Nat.add_le_add (bound i (by simp)) (ih (by intro j hj;exact bound j (by simp [hj])))

/-- Every finite typed list is bounded using its actual erased record inventory. -/
theorem list_bound (q rest : ℕ) (cost : ℕ→ℕ) (hq : 1 ≤ q) (hr : rest < m) (is : List Instruction) :
 (is.map (chargedTicks q rest cost)).sum ≤ 
 UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest) (is.map (Instruction.record q))+
 UniformRecursiveRuntimeInventory.directions (is.map (Instruction.record q))*
 UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 rw [←UniformRecursiveV2CostAllowance.sum_charge_formula]
 simp only [List.map_map,Function.comp_def]
 exact sum_map_bound _ _ _ (fun i _=>instruction_bound q rest cost hq hr i)

lemma sum_append_one {α : Type*} (is : List α) (f : α→ℕ) (i : α) :
 ((is++[i]).map f).sum=(is.map f).sum+f i := by
 simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

lemma core_padding_of_inventory (q rest : ℕ) (cost : ℕ→ℕ) (hq : 1 ≤ q) (hr : rest < m)
 (is : List Instruction) (rs : List Record) (S : ℕ)
 (noPadding : ∀i ∈ is,NoPadding i)
 (erasure : (is++[Instruction.padding]).map (Instruction.record q)=rs)
 (inventory : UniformRecursiveRuntimeInventory.directions rs=S) :
 (is.map (ticks q rest cost)).sum+paddingTicks q rest cost ≤
 UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest) rs+
 S*UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 have cap:=list_bound q rest cost hq hr (is++[Instruction.padding])
 have eq : is.map (chargedTicks q rest cost)=is.map (ticks q rest cost) := by
  apply List.map_congr_left
  intro i hi
  exact charged_nonpadding q rest cost i (noPadding i hi)
 have lhs:=(sum_append_one is (chargedTicks q rest cost) Instruction.padding).trans
  (congrArg₂ (fun a b : ℕ=>a+b) (congrArg List.sum eq) (charged_padding q rest cost))
 have rhs:=congrArg₂ (fun a b : ℕ=>a+b*UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169))
  (congrArg (UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest)) erasure)
  ((congrArg UniformRecursiveRuntimeInventory.directions erasure).trans inventory)
 exact lhs.symm.le.trans (cap.trans_eq rhs)

/-- The exact nonpadding core sum plus actual padding cost fits the full static
 tape reserve with precisely S same-q directions. No execution premise is used. -/
theorem core_padding_bound (q rest : ℕ) (cost : ℕ→ℕ) (hq : 1 ≤ q) (hr : rest < m) :
 (coreInstructions.map (ticks q rest cost)).sum+paddingTicks q rest cost ≤
 UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest) (scheduleRecords q)+
 UniformFixedNetwork.S*UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*(cost q+169) := by
 exact core_padding_of_inventory q rest cost hq hr coreInstructions (scheduleRecords q) UniformFixedNetwork.S
  core_noPadding
  ((congrArg (List.map (Instruction.record q)) instructions_core.symm).trans (records_actual q))
  (UniformRecursiveRuntimeInventory.schedule_directions q)

end
end ExactFourierCircuits.UniformRecursiveTypedCostAllowance
