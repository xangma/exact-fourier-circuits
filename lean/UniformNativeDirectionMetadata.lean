import UniformNativeTerminalY
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeDirectionMetadata
open BinaryFrames UniformFixedNetworkScheduleMachine UniformBinaryXorCoordinates
noncomputable section

lemma bitWords_cast {a b : ℕ} (h:a=b) (v : Vec (Fin a)) :
 bitWords (fun j:Fin b=>v (Fin.cast h.symm j))=bitWords v := by
 subst b
 rfl

/-- The terminal printer's one-column descriptor contains exactly the original
width bits; this does not enumerate the seed's million-bit vector. -/
theorem direction_one_words {n : ℕ} (u : Vec (Fin n)) :
 bitWords (ColumnTerminalFlat.direction 1 u)=bitWords u := by
 have cast:(fun j:Fin n=>ColumnTerminalFlat.direction 1 u (Fin.cast (Nat.one_mul n).symm j))=u := by
  funext j
  have index:Fin.cast (Nat.one_mul n).symm j=finProdFinEquiv ((0:Fin 1),j) := by
   apply Fin.ext
   simp [finProdFinEquiv]
  rw [index,repeated_direction_bit]
 exact (bitWords_cast (Nat.one_mul n) (ColumnTerminalFlat.direction 1 u)).symm.trans
  (congrArg bitWords cast)

lemma padded_role_value {α : Type*} {w : ℕ} (p : ℕ) (hw:w≤2^p)
 (e : α↪Fin w) (a : α) :
 ((e.trans (UniformNativeRecordRoles.paddingRole w p hw)) a).val=(e a).val :=
 UniformNativeRecordRoles.paddingRole_value w p hw (e a)

/-- Generic erasure first: no concrete seed list or chosen role enumeration is reduced. -/
theorem exchange_record_model {δ β : Type*} {w : ℕ}
 (e : TerminalWords.Role δ β≃Fin w) (p q n : ℕ) (hw:w≤2^p) (L : List δ) :
 UniformNativeExchangeRecordMachine.record q n (UniformNativeTerminalExchange.pairs
  (e.toEmbedding.trans (UniformNativeRecordRoles.paddingRole w p hw)) L)=
 ⟨4,q,n,0,0,0,(L.map (fun d=>((e (.inl (0,d))).val,(e (.inl (1,d))).val))).length,0,
  ((L.map (fun d=>((e (.inl (0,d))).val,(e (.inl (1,d))).val))).map
   (fun a=>[a.1,a.2,4,0])).flatten⟩ := by
 have data:UniformNativeExchangeRecordMachine.Pair.data ∘
  UniformNativeTerminalExchange.pair (e.toEmbedding.trans (UniformNativeRecordRoles.paddingRole w p hw))=
  (fun a:ℕ×ℕ=>[a.1,a.2,4,0]) ∘ (fun d=>((e (.inl (0,d))).val,(e (.inl (1,d))).val)) := by
  funext d
  simp only [Function.comp_apply,UniformNativeExchangeRecordMachine.Pair.data,
   UniformNativeTerminalExchange.pair,padded_role_value,Equiv.toEmbedding_apply]
 simp only [UniformNativeExchangeRecordMachine.record,UniformNativeExchangeRecordMachine.body,
  UniformNativeTerminalExchange.pairs,List.length_map,List.map_map,data]

theorem translation_record_model {δ β : Type*} {w : ℕ}
 (e : TerminalWords.Role δ β≃Fin w) (p q n : ℕ) (hw:w≤2^p)
 (u : δ→Vec (Fin n)) (L : List δ) :
 UniformNativeYRecordMachine.record q n (UniformNativeTerminalY.directions
  (e.toEmbedding.trans (UniformNativeRecordRoles.paddingRole w p hw)) u L)=
 ⟨3,q,n,0,0,0,(L.map (fun d=>((e (.inl (0,d))).val,(e (.inl (1,d))).val))).length,0,
  (L.map (fun d=>(e (.inl (1,d))).val::bitWords (ColumnTerminalFlat.direction 1 (u d)))).flatten⟩ := by
 have data:UniformNativeYRecordMachine.Direction.data ∘ UniformNativeTerminalY.direction
  (e.toEmbedding.trans (UniformNativeRecordRoles.paddingRole w p hw)) u=
  (fun d=>(e (.inl (1,d))).val::bitWords (ColumnTerminalFlat.direction 1 (u d))) := by
  funext d
  simp only [Function.comp_apply,UniformNativeYRecordMachine.Direction.data,
   UniformNativeTerminalY.direction,padded_role_value,Equiv.toEmbedding_apply,direction_one_words]
 simp only [UniformNativeYRecordMachine.record,UniformNativeYRecordMachine.body,
  UniformNativeTerminalY.directions,List.length_map,List.map_map,data]

end
end ExactFourierCircuits.UniformNativeDirectionMetadata
