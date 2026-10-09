import UniformRecursiveRuntimeInventory
import UniformRecursiveRuntimeBridge
import UniformFixedNetworkOpcodeMachine
import UniformRecursiveSavingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveLocalAllowance
open UniformFixedNetworkScheduleMachine
namespace I
export UniformRecursiveRuntimeInventory (recursiveDirections directions schedule_directions)
end I
namespace R
export UniformRecursiveRuntimeBridge (localUnit preparationTicks)
end R
noncomputable section

/-- Static allowance; execution contracts must still supply their actual ticks. -/
def recordAllowance (m k : ℕ) (r : Record) : ℕ :=
 1000*(m+1)*(I.recursiveDirections r+r.data.length+1)*2^k
def tapeAllowance (m k : ℕ) (rs : List Record) : ℕ :=
 (rs.map (recordAllowance m k)).sum

lemma serialized_length (rs : List Record) :
 (serialize rs).length=(rs.map (fun r=>r.data.length)).sum := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [serialize,List.map_cons,List.flatten_cons,List.length_append] at ih ⊢
                 simp only [List.sum_cons];rw [ih]

lemma count_le_serialized (rs : List Record) : rs.length ≤ (serialize rs).length := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>
   have size:1 ≤ r.data.length:=by rw [Record.data_length];omega
   simp only [serialize,List.map_cons,List.flatten_cons,List.length_append] at ih ⊢
   simp only [List.length_cons]
   omega

lemma tape_formula (m k : ℕ) (rs : List Record) :
 tapeAllowance m k rs=1000*(m+1)*(I.directions rs+(serialize rs).length+rs.length)*2^k := by
 induction rs with
 | nil=>simp [tapeAllowance,I.directions,UniformRecursiveRuntimeInventory.directions,serialize]
 | cons r rs ih=>
   simp only [tapeAllowance,List.map_cons,List.sum_cons] at ih ⊢
   rw [ih]
   simp only [UniformRecursiveRuntimeInventory.directions,List.map_cons,List.sum_cons,
    serialize,List.map_cons,List.flatten_cons,List.length_append,List.length_cons]
   unfold recordAllowance
   ring

lemma tape_bound (m k : ℕ) (rs : List Record) :
 tapeAllowance m k rs ≤ 2000*(m+1)*(I.directions rs+(serialize rs).length)*2^k := by
 rw [tape_formula]
 have h:=count_le_serialized rs
 have mass:I.directions rs+(serialize rs).length+rs.length ≤
  2*(I.directions rs+(serialize rs).length):=by omega
 have scaled:=Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul_left (1000*(m+1)) mass)
 nlinarith

theorem schedule_allowance (q k : ℕ) :
 tapeAllowance UniformFixedNetwork.m k (scheduleRecords q) ≤
 2000*(UniformFixedNetwork.m+1)*(UniformFixedNetwork.S+(serialize baseSchedule).length)*2^k := by
 have h:=tape_bound UniformFixedNetwork.m k (scheduleRecords q)
 rw [I.schedule_directions] at h
 have len:(serialize (scheduleRecords q)).length=(serialize baseSchedule).length:=
  schedule_size_independent q
 rw [len] at h
 exact h

lemma affine_reserve (m d data V a b : ℕ) (_hp:1 ≤ V)
 (coef:a ≤ 1000*(m+1)) (fixed:b ≤ 1000*(m+1)) :
 b*V+d*(a*V) ≤ 1000*(m+1)*(d+data+1)*V := by
 have term:=Nat.mul_le_mul_left d (Nat.mul_le_mul_right V coef)
 have extra:=Nat.mul_le_mul_right V fixed
 calc
  b*V+d*(a*V) ≤ 1000*(m+1)*V+d*(1000*(m+1)*V) := Nat.add_le_add extra term
  _ = 1000*(m+1)*(d+1)*V := by ring
  _ ≤ 1000*(m+1)*(d+data+1)*V :=
    Nat.mul_le_mul_right V (Nat.mul_le_mul_left (1000*(m+1)) (by omega))

/-- True direction branch, gather, boot, final group branch, optional inverse,
 scatter and directionNext. The group's final negative branch costs one. -/
def directionTicks (q m rest header : ℕ) : ℕ :=
 1+(header+18+UniformResidualGeneralPreparation.runtimeBound q m rest+
 11*2^(q*m+rest)+11)+5+1+1+14+
 ((17*(m+rest)+25)*2^(q*m+rest)+13)+(10*2^(q*m+rest)+11)+2

lemma direction_bound (q m rest header : ℕ) (hq:1 ≤ q) (hm:3 ≤ m)
 (hr:rest < m) (hh:header ≤ 38) :
 directionTicks q m rest header ≤ (92*m+430)*2^(q*m+rest) := by
 have gather:=UniformRecursiveRuntimeBridge.gather_bound q m rest hq hm hr header hh
 have inverse:=UniformRecursiveRuntimeBridge.inverse_bound q m rest hr
 have hp:1 ≤ 2^(q*m+rest):=Nat.two_pow_pos _
 unfold directionTicks
 nlinarith

lemma residual_record_bound (m k d data localTicks : ℕ)
 (work:localTicks ≤ (92*m+430)*2^k) :
 53+d*localTicks ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have b:=affine_reserve m d data (2^k) (92*m+430) 53 hp (by omega) (by omega)
 have runs:=Nat.mul_le_mul_left d work
 nlinarith

/-- All padding calls use the same q-child: exactly roles*m directions. -/
lemma padding_record_bound (m k roles data localTicks : ℕ) (hm:1 ≤ m)
 (work:localTicks ≤ (92*m+430)*2^k) :
 73+roles*(64+m*localTicks) ≤
 1000*(m+1)*(roles*m+data+1)*2^k := by
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have roles_le:roles ≤ roles*m:=Nat.le_mul_of_pos_right _ hm
 have runs:=Nat.mul_le_mul_left (roles*m) work
 have control:64*roles ≤ 64*(roles*m)*2^k:=by nlinarith
 have cap:=affine_reserve m (roles*m) data (2^k) (92*m+494) 73 hp (by omega) (by omega)
 nlinarith

lemma scalar_record_bound (m k d data c : ℕ) (hc:c<5) :
 10*2^k+4*k+c+102 ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have h:=UniformRecursiveRuntimeBridge.scalar_bound k c hc
 have cap:=affine_reserve m 0 (d+data) (2^k) 0 120
  (Nat.two_pow_pos _) (by omega) (by omega)
 nlinarith

lemma exchange_record_bound (m k d data pairs : ℕ) (hp:pairs ≤ data) :
 (10*2^k+21)*pairs+4*k+99 ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have h:=UniformRecursiveRuntimeBridge.exchange_bound k pairs
 have more:=Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul_left 31 hp)
 have cap:=affine_reserve m data d (2^k) 31 103
  (Nat.two_pow_pos _) (by omega) (by omega)
 nlinarith

lemma translation_record_bound (q m rest d data rows : ℕ) (hm:3 ≤ m)
 (hr:rest < m) (rows_le:rows ≤ data) :
 UniformNativeYRecordMachine.runtime q m rest (q*m+rest) rows+47 ≤
 1000*(m+1)*(d+data+1)*2^(q*m+rest) := by
 have h:=UniformRecursiveRuntimeBridge.translation_bound q m rest rows hm hr
 have more:=Nat.mul_le_mul_right (2^(q*m+rest)) (Nat.mul_le_mul_left (34*m+101) rows_le)
 have cap:=affine_reserve m data d (2^(q*m+rest)) (34*m+101) 103
  (Nat.two_pow_pos _) (by omega) (by omega)
 nlinarith

lemma marker_record_bound (m k d data ticks : ℕ) (h:ticks ≤ 94) :
 ticks ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have cap:=affine_reserve m 0 (d+data) (2^k) 0 94
  (Nat.two_pow_pos _) (by omega) (by omega)
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 simp only [Nat.zero_mul,Nat.zero_add] at cap
 exact (h.trans (Nat.le_mul_of_pos_right 94 hp)).trans cap

lemma translation_rows_le_data (r : Record)
 (good:UniformFixedNetworkOpcodeMachine.WellFormed r) (op:r.opcode=3) :
 r.dimension ≤ r.data.length := by
 have h:=good.2
 simp [UniformFixedNetworkOpcodeMachine.bodyLength,op] at h
 have positive:1 ≤ r.width+1:=by omega
 have dim:=Nat.le_mul_of_pos_right r.dimension positive
 rw [Record.data_length,h]
 omega

lemma exchange_pairs_le_data (r : Record)
 (good:UniformFixedNetworkOpcodeMachine.WellFormed r) (op:r.opcode=4) :
 r.dimension ≤ r.data.length := by
 have h:=good.2
 simp [UniformFixedNetworkOpcodeMachine.bodyLength,op] at h
 rw [Record.data_length,h]
 omega

lemma producer_bound (L N m : ℕ) :
 (3*L+3*N+7)+12+(3*(8+m*m)+4)+15+50 ≤
 3*L+3*N+3*(8+m^2)+1000 := by
 rw [pow_two]
 omega

lemma suffix_bound (k b W m : ℕ) (hb:b ≤ k) (hw:1 ≤ W) (hr:k-b < m) :
 4*b+W*UniformBinarySpectatorCMachine.arrayCost k b+21 ≤
 1000*(m+1)*(W+1)*2^k := by
 have h:=UniformBinarySpectatorCMachine.remainder_runtime_bound hb hw hr
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have coeff:36*m+22 ≤ 1000*(m+1):=by omega
 have p:=Nat.mul_le_mul_right (W*2^k) coeff
 have room:21 ≤ 1000*(m+1)*2^k:=by nlinarith
 nlinarith

lemma node_bound (P m S L W V producer tape suffix : ℕ)
 (hp:1 ≤ V) (hw:1 ≤ W) (produced:producer ≤ P)
 (records:tape ≤ 2000*(m+1)*(S+L)*V)
 (ended:suffix ≤ 1000*(m+1)*(W+1)*V) :
 producer+tape+suffix ≤
 (P+2000*(m+1)*(S+L+W+1))*(W*V) := by
 have prep:producer ≤ P*V:=produced.trans (Nat.le_mul_of_pos_right _ hp)
 have cap:producer+tape+suffix ≤ (P+2000*(m+1)*(S+L+W+1))*V:=by nlinarith
 exact cap.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hw))

end
end ExactFourierCircuits.UniformRecursiveLocalAllowance
