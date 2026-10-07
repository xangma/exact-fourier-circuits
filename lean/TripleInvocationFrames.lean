import GateFrames

set_option autoImplicit false
namespace ExactFourierCircuits.TripleInvocationFrames
open ScalarNetwork TripleNetwork BinaryFrames BinaryComplement BinaryTensor BinaryResiduals StageFrames GateFrames
noncomputable section
variable {h : ℕ}

def pairCoordinates (h : ℕ) : (Fin 2 → Fin h) ≃ (Fin h × Fin h) where
  toFun x := (x 0, x 1)
  invFun xy := ![xy.1, xy.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv xy := rfl

lemma pair_tensor (S T : Triple (Fin h)) :
    coordinates (pairCoordinates h) (tripleTensor 2 h ![S.val, T.val]) = tensor (t S) (t T) := by
  ext xy
  simp [coordinates, pairCoordinates, tripleTensor, tensorFamily, tensor, t,
    Fin.prod_univ_succ]
  rfl

lemma pair_complement (S T : Triple (Fin h)) (hh : 7 ≤ h) :
    HasONBasis (perp (tensor (t S) (t T))) := by
  have hb := hasONBasis_space (pairCoordinates h)
    (hasONBasis_tripleTensor_perp 2 h ![S.val, T.val]
      (by intro i; fin_cases i
          · exact S.property
          · exact T.property) hh)
  rw [space_perp, pair_tensor] at hb
  exact hb

abbrev Prefix (h : ℕ) : Fin 3 → Type
  | 0 => EmptyCoordinates h
  | 1 => Fin h
  | 2 => Fin h × Fin h

abbrev Future (h : ℕ) : Fin 3 → Type
  | 0 => Fin h × Fin h
  | 1 => Fin h
  | 2 => EmptyCoordinates h

instance prefixFintype (h : ℕ) : (p : Fin 3) → Fintype (Prefix h p)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
instance futureFintype (h : ℕ) : (p : Fin 3) → Fintype (Future h p)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

def invocationData : (p : Fin 3) → Profile (Fin h) p → (7 ≤ h) →
    Data (Prefix h p) (Future h p) h
  | 0, profile, hh => {
      prefixVector := emptyVector h
      prefix_norm := emptyVector_norm
      prefix_complement := by rw [emptyVector_perp]; exact hasONBasis_bot
      future := tensor (t (profile ⟨1, by decide⟩)) (t (profile ⟨2, by decide⟩))
      future_norm := by rw [dot_tensor, t_norm, t_norm]; rfl
      future_complement := pair_complement _ _ hh
      large := hh }
  | 1, profile, hh => {
      prefixVector := t (profile ⟨0, by decide⟩)
      prefix_norm := t_norm _
      prefix_complement := hasONBasis_triple_perp _ hh
      future := t (profile ⟨2, by decide⟩)
      future_norm := t_norm _
      future_complement := hasONBasis_triple_perp _ hh
      large := hh }
  | 2, profile, hh => {
      prefixVector := tensor (t (profile ⟨0, by decide⟩)) (t (profile ⟨1, by decide⟩))
      prefix_norm := by rw [dot_tensor, t_norm, t_norm]; rfl
      prefix_complement := pair_complement _ _ hh
      future := emptyVector h
      future_norm := emptyVector_norm
      future_complement := by rw [emptyVector_perp]; exact hasONBasis_bot
      large := hh }

def invocationCoordinates : (p : Fin 3) → (h : ℕ) →
    ((Prefix h p × Fin h) × Future h p) ≃ PhysicalCoordinates h
  | 0, h => (firstCoordinates h).trans (tripleCoordinates h)
  | 1, h => tripleCoordinates h
  | 2, h => (lastCoordinates h).trans (tripleCoordinates h)

def physicalFin (h : ℕ) : PhysicalCoordinates h ≃ Fin (h ^ 3) :=
  Fintype.equivFinOfCardEq (by simp [PhysicalCoordinates])

def invocationAddressCoordinates (p : Fin 3) (h : ℕ) :
    ((Prefix h p × Fin h) × Future h p) ≃ Fin (h ^ 3) :=
  (invocationCoordinates p h).trans (physicalFin h)

def bank (p : Fin 3) (profile : Profile (Fin h) p) (T : Triple (Fin h)) : Bank (Fin h) :=
  (axisCoordinates p).symm (T, profile)

def bankVectors (d : Bank (Fin h)) : Fin 3 → Vec (Fin h) := fun i => t (d i)

set_option maxHeartbeats 1000000 in
theorem entry_X (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) (T : Triple (Fin h)) :
    ((invocationData p profile hh).labels (invocationAddressCoordinates p h) 0 (.x T)).space =
      space (physicalFin h) (physicalIncomingX (bankVectors (bank p profile T)) p) := by
  fin_cases p <;>
    simp [Data.labels, labelOfBasis, invocationAddressCoordinates, invocationCoordinates,
      ← space_trans, Data.at, Data.localAt, Data.entry, invocationData,
      physicalIncomingX, incomingX, bankVectors, bank, axisCoordinates, Equiv.funSplitAt]

set_option maxHeartbeats 1000000 in
theorem entry_Y (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) (T : Triple (Fin h)) :
    ((invocationData p profile hh).labels (invocationAddressCoordinates p h) 0 (.y T)).space =
      space (physicalFin h) (physicalIncomingY (bankVectors (bank p profile T)) p) := by
  fin_cases p <;>
    simp [Data.labels, labelOfBasis, invocationAddressCoordinates, invocationCoordinates,
      ← space_trans, Data.at, Data.localAt, Data.entry, Data.B, invocationData, label0,
      physicalIncomingY, incomingY, bankVectors, bank, axisCoordinates, Equiv.funSplitAt]

set_option maxHeartbeats 1000000 in
theorem final_X (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) (T : Triple (Fin h)) :
    ((invocationData p profile hh).finalLabels (invocationAddressCoordinates p h) (.x T)).space =
      space (physicalFin h) (physicalOutgoingX (bankVectors (bank p profile T)) p) := by
  fin_cases p <;>
    simp [Data.finalLabels, labelOfBasis, invocationAddressCoordinates, invocationCoordinates,
      ← space_trans, Data.finalSpace, Data.at, Data.localAt, rowLabel, Data.B, Data.P, invocationData,
      physicalOutgoingX, outgoingX, bankVectors, bank, axisCoordinates, Equiv.funSplitAt]

set_option maxHeartbeats 1000000 in
theorem final_Y (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) (T : Triple (Fin h)) :
    ((invocationData p profile hh).finalLabels (invocationAddressCoordinates p h) (.y T)).space =
      space (physicalFin h) (physicalOutgoingY (bankVectors (bank p profile T)) p) := by
  fin_cases p <;>
    simp [Data.finalLabels, labelOfBasis, invocationAddressCoordinates, invocationCoordinates,
      ← space_trans, Data.finalSpace, Data.at, Data.localAt, rowLabel, Data.B, Data.P, invocationData,
      physicalOutgoingY, outgoingY, bankVectors, bank, axisCoordinates, Equiv.funSplitAt]

def bankProfile (p : Fin 3) (d : Bank (Fin h)) : Profile (Fin h) p :=
  (axisCoordinates p d).2

@[simp] lemma bank_reassemble (p : Fin 3) (d : Bank (Fin h)) :
    bank p (bankProfile p d) (d p) = d := by
  change (axisCoordinates p).symm (axisCoordinates p d) = d
  simp

def bankDirection (d : Bank (Fin h)) : Vec (Fin (h ^ 3)) :=
  coordinates (physicalFin h) (tripleTensor 3 h (fun i => (d i).val))

lemma bankDirection_norm (d : Bank (Fin h)) : dot (bankDirection d) (bankDirection d) = 1 := by
  rw [bankDirection, coordinates_dot]
  exact tripleTensor_norm 3 h _ (fun i => (d i).property)

lemma entry_bank (p : Fin 3) (d : Bank (Fin h)) (hh : 7 ≤ h) :
    ((invocationData p (bankProfile p d) hh).labels (invocationAddressCoordinates p h) 0 (.x (d p))).space =
      space (physicalFin h) (physicalIncomingX (bankVectors d) p) ∧
    ((invocationData p (bankProfile p d) hh).labels (invocationAddressCoordinates p h) 0 (.y (d p))).space =
      space (physicalFin h) (physicalIncomingY (bankVectors d) p) := by
  constructor <;> simp only [entry_X, entry_Y, bank_reassemble]

lemma final_bank (p : Fin 3) (d : Bank (Fin h)) (hh : 7 ≤ h) :
    ((invocationData p (bankProfile p d) hh).finalLabels (invocationAddressCoordinates p h) (.x (d p))).space =
      space (physicalFin h) (physicalOutgoingX (bankVectors d) p) ∧
    ((invocationData p (bankProfile p d) hh).finalLabels (invocationAddressCoordinates p h) (.y (d p))).space =
      space (physicalFin h) (physicalOutgoingY (bankVectors d) p) := by
  constructor <;> simp only [final_X, final_Y, bank_reassemble]

/-- Actual initial spaces: one bank direction on X and no Y frame. -/
lemma source_bank (d : Bank (Fin h)) (hh : 7 ≤ h) :
    ((invocationData 0 (bankProfile 0 d) hh).labels (invocationAddressCoordinates 0 h) 0 (.x (d 0))).space =
      line (bankDirection d) ∧
    ((invocationData 0 (bankProfile 0 d) hh).labels (invocationAddressCoordinates 0 h) 0 (.y (d 0))).space = ⊥ := by
  have hs := physical_source (fun i => (d i).val)
  have hb : bankVectors d = directions (fun i => (d i).val) := rfl
  rw [(entry_bank 0 d hh).1, (entry_bank 0 d hh).2, hb, hs.1, hs.2, space_line, space_bot]
  exact ⟨rfl, rfl⟩

/-- Actual final bank spaces: full X and the perpendicular to its triple direction on Y. -/
lemma sink_bank (d : Bank (Fin h)) (hh : 7 ≤ h) :
    ((invocationData 2 (bankProfile 2 d) hh).finalLabels (invocationAddressCoordinates 2 h) (.x (d 2))).space = ⊤ ∧
    ((invocationData 2 (bankProfile 2 d) hh).finalLabels (invocationAddressCoordinates 2 h) (.y (d 2))).space =
      perp (bankDirection d) := by
  have hs := physical_sink (fun i => (d i).val) (fun i => (d i).property)
  have hb : bankVectors d = directions (fun i => (d i).val) := rfl
  rw [(final_bank 2 d hh).1, (final_bank 2 d hh).2, hb, hs.1, hs.2, space_top, space_perp]
  exact ⟨rfl, rfl⟩

/-- Consecutive actual labels have identical spaces, although their chosen bases can differ. -/
lemma consecutive_bank (p : Fin 2) (d : Bank (Fin h)) (hh : 7 ≤ h) :
    ((invocationData p.castSucc (bankProfile p.castSucc d) hh).finalLabels
      (invocationAddressCoordinates p.castSucc h) (.x (d p.castSucc))).space =
    ((invocationData p.succ (bankProfile p.succ d) hh).labels
      (invocationAddressCoordinates p.succ h) 0 (.x (d p.succ))).space ∧
    ((invocationData p.castSucc (bankProfile p.castSucc d) hh).finalLabels
      (invocationAddressCoordinates p.castSucc h) (.y (d p.castSucc))).space =
    ((invocationData p.succ (bankProfile p.succ d) hh).labels
      (invocationAddressCoordinates p.succ h) 0 (.y (d p.succ))).space := by
  have hs := consecutive_boundaries (bankVectors d) (fun i => t_norm (d i)) p
  rw [(final_bank _ d hh).1, (entry_bank _ d hh).1,
    (final_bank _ d hh).2, (entry_bank _ d hh).2, hs.1, hs.2]
  exact ⟨rfl, rfl⟩

end
end ExactFourierCircuits.TripleInvocationFrames
