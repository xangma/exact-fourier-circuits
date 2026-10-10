import DFTModelSavingShape
import DFTModelSavingResidualBoolean

set_option autoImplicit false

/-! Boolean dependency flags for the executed saving stream. The invariant
allows every flag pattern; no matrix equality is used to identify flags. -/
namespace ExactFourierCircuits.DFTModelSavingShapeBoolean
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
noncomputable section

attribute [local irreducible] DFTModelRecursiveExchange.decode
  DFTModelRecursiveExchange.pairsProgram

lemma steps_boolean (x : Node.T) (f : ℕ→Node.T→Bill Node.T)
    (before : Boolean x.2) (hf : ∀i z,Boolean z.2 → Boolean (f i z).val.2) (n : ℕ) :
    Boolean (Bill.steps x f n).val.2 := by
  induction n with
  | zero=>exact before
  | succ n ih=>exact hf n _ ih

lemma residual_boolean (h : Handler ChildPort) (x : DFTModelSavingResidualSetup.Input.T)
    (before : Boolean x.2.2.2.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean (DFTModelSavingResidual.program.run h x).val.2 := by
  rcases x with ⟨ctx,a,raw,⟨k,I⟩,v⟩
  apply (boolean_iff _).mpr
  apply program_booleanTape_of_child h ctx a raw k I v ((boolean_iff _).mp before)
  intro J v hv
  exact (boolean_iff _).mp (children _ ((boolean_iff _).mpr hv))

lemma direction_boolean (h : Handler ChildPort) (x : DFTModelSavingRecords.Iter.T)
    (before : Boolean x.2.2.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean (DFTModelSavingRecords.direction.run h x).val.2 := by
  rcases x with ⟨⟨rest,raw,old⟩,i,node⟩
  rw [DFTModelSavingRecords.direction,DFTModelClockBatch.code_comp_value]
  change Boolean (DFTModelSavingResidual.program.run h
    (run DFTModelSavingRecords.directionArgs ((rest,(raw,old)),(i,node))).val).val.2
  rw [DFTModelSavingRecords.directionArgs_value]
  exact residual_boolean h _ before children

lemma residual_loop_boolean (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T)
    (before : Boolean x.2.2.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean (DFTModelSavingRecords.residual.run h x).val.2 := by
  rw [DFTModelSavingRecords.residual,DFTModelSavingRecords.code_loop_value]
  exact steps_boolean _ _ before (fun _ _ hz=>direction_boolean h _ hz children) _

lemma padding_boolean (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T)
    (before : Boolean x.2.2.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean (DFTModelSavingRecords.padding.run h x).val.2 := by
  rw [DFTModelSavingRecords.padding,DFTModelSavingRecords.code_loop_value]
  apply steps_boolean _ _ before
  intro i z hz
  rw [DFTModelSavingRecords.paddingBody,DFTModelClockBatch.code_comp_value]
  exact residual_loop_boolean h _ hz children

lemma scalar_boolean (R : ℕ) (raw : Tape ℕ) (node : Node.T) (before : Boolean node.2) :
    Boolean (run (DFTModelSavingScalar.program R) (raw,node)).val.2 := by
  rcases node with ⟨⟨k,I⟩,v⟩
  rw [DFTModelSavingScalar.program_value]
  apply tab_boolean
  intro j _
  unfold DFTModelRecursiveScalar.result
  split
  · change (if (v.look j Tagged.blank).1=0 then
      (v.look _ Tagged.blank).1 else 1)<2
    split
    · exact look_boolean before _
    · decide
  · exact look_boolean before _

lemma movement_boolean (x : (DFTModelRecursiveYMovement.Input Tagged).T)
    (before : Boolean x.2.2.2.2) :
    Boolean (run (DFTModelRecursiveYMovement.program Tagged) x).val := by
  change Boolean (Bill.tab x.2.2.2.2.len Tagged.blank
    (fun j=>run (DFTModelRecursiveYMovement.cell Tagged) (x,j))).val
  rw [ModelEquivalenceInterpreter.tab_value]
  apply tab_boolean
  intro j _
  change (x.2.2.2.2.look (run (DFTModelRecursiveYMovement.address Tagged) (x,j)).val
    Tagged.blank).1<2
  exact look_boolean before _

lemma y_direction_boolean (R : ℕ) (x : DFTModelRecursiveYDirection.Input.T)
    (before : Boolean x.2.2.2) :
    Boolean (run (DFTModelRecursiveYDirection.program R) x).val.2 := by
  change Boolean (run (DFTModelRecursiveYMovement.program Tagged)
    (run (DFTModelRecursiveYDirection.ready R) x).val).val
  exact movement_boolean _ before

lemma y_body_boolean (R : ℕ) (x : DFTModelSavingY.Body.T) (before : Boolean x.2.2.2) :
    Boolean (run (DFTModelSavingY.body R) x).val.2 := by
  change Boolean (run (DFTModelRecursiveYDirection.program R)
    (run DFTModelSavingY.arguments x).val).val.2
  exact y_direction_boolean R _ before

lemma y_boolean (R : ℕ) (x : DFTModelSavingY.Input.T) (before : Boolean x.2.2.2) :
    Boolean (run (DFTModelSavingY.program R) x).val.2 := by
  rw [DFTModelSavingY.program_run]
  exact steps_boolean _ _ before (fun _ _ hz=>y_body_boolean R _ hz) _

lemma exchange_body_boolean (R : ℕ) (x : DFTModelRecursiveExchange.Body.T)
    (before : Boolean x.2.2.2) :
    Boolean (run (DFTModelRecursiveExchange.body R) x).val.2 := by
  rcases x with ⟨⟨ps,old⟩,i,⟨k,I⟩,v⟩
  rw [DFTModelRecursiveExchange.body_run]
  obtain ⟨d,s⟩ := ps.look i DFTModelRecursiveExchange.PairNat.blank
  change Boolean (run (DFTModelRecursiveExchange.pairProgram R) ((d,s),((k,I),v))).val.2
  rw [DFTModelRecursiveExchange.pair_value]
  apply tab_boolean
  intro j _
  unfold DFTModelRecursiveExchange.result
  split
  · exact look_boolean before _
  · split
    · exact look_boolean before _
    · exact look_boolean before _

lemma exchange_pairs_boolean (R : ℕ) (ps : Tape DFTModelRecursiveExchange.PairNat.T)
    (node : Node.T) (before : Boolean node.2) :
    Boolean (run (DFTModelRecursiveExchange.pairsProgram R) (ps,node)).val.2 := by
  rw [DFTModelRecursiveExchange.pairs_run]
  exact steps_boolean _ _ before (fun _ _ hz=>exchange_body_boolean R _ hz) _

lemma exchange_boolean (R : ℕ) (raw : Tape ℕ) (node : Node.T) (before : Boolean node.2) :
    Boolean (run (DFTModelRecursiveExchange.program R) (raw,node)).val.2 := by
  rw [DFTModelRecursiveExchange.program_run]
  change Boolean (run (DFTModelRecursiveExchange.pairsProgram R)
    ((run DFTModelRecursiveExchange.decode raw).val,node)).val.2
  exact exchange_pairs_boolean R _ node before

attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

lemma ifz_boolean {s : Ty} (test : Code false ChildPort s w)
    (f g : Code false ChildPort s Node) (h : Handler ChildPort) (x : s.T)
    (hf : Boolean (f.run h x).val.2) (hg : Boolean (g.run h x).val.2) :
    Boolean ((Code.ifz test f g).run h x).val.2 := by
  change Boolean (if (test.run h x).val=0 then f.run h x else g.run h x).val.2
  split_ifs <;> assumption

theorem dispatch_boolean (R : ℕ) (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T)
    (before : Boolean x.2.2.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean ((DFTModelSavingRecords.dispatch R).run h x).val.2 := by
  unfold DFTModelSavingRecords.dispatch
  apply ifz_boolean
  · exact residual_loop_boolean h x before children
  · apply ifz_boolean
    · rw [DFTModelClockBatch.code_comp_value]
      exact scalar_boolean R x.2.1 x.2.2 before
    · apply ifz_boolean
      · exact before
      · apply ifz_boolean
        · exact y_boolean R x before
        · apply ifz_boolean
          · rw [DFTModelClockBatch.code_comp_value]
            exact exchange_boolean R x.2.1 x.2.2 before
          · apply ifz_boolean
            · exact padding_boolean h x before children
            · exact before

theorem stream_boolean (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler ChildPort) (before : Boolean node.2)
    (children : ∀z : Node.T,Boolean z.2 → Boolean (h z).val) :
    Boolean ((DFTModelSavingRecords.stream R).run h (rest,(rs,node))).val.2 := by
  rw [DFTModelSavingRecords.stream_value]
  exact steps_boolean _ _ before (fun _ _ hz=>dispatch_boolean R h _ hz children) _

end
end ExactFourierCircuits.DFTModelSavingShapeBoolean
