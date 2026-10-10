import DFTModelSavingRecords
import DFTModelSavingResidualGeometry

set_option autoImplicit false

/-! Shape invariants for the concrete chronological interpreter. These facts
hold for arbitrary runtime records and child handlers. In particular, the
proof never replaces the actual dependency flags by a canonical tensor tag. -/
namespace ExactFourierCircuits.DFTModelSavingShape
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
noncomputable section
attribute [local irreducible] DFTModelRecursiveExchange.decode
  DFTModelRecursiveExchange.pairsProgram

def Preserves (x y : Node.T) : Prop := y.1=x.1 ∧ y.2.len=x.2.len

lemma preserves_refl (x : Node.T) : Preserves x x := ⟨rfl,rfl⟩
lemma preserves_trans {x y z : Node.T} (a : Preserves x y) (b : Preserves y z) :
    Preserves x z := ⟨b.1.trans a.1,b.2.trans a.2⟩

lemma steps_preserves (x : Node.T) (f : ℕ→Node.T→Bill Node.T)
    (hf : ∀i z,Preserves z (f i z).val) (n : ℕ) :
    Preserves x (Bill.steps x f n).val := by
  induction n with
  | zero=>exact preserves_refl x
  | succ n ih=>exact preserves_trans ih (hf n _)

lemma residual_preserves (h : Handler ChildPort) (x : DFTModelSavingResidualSetup.Input.T) :
    Preserves x.2.2.2 (DFTModelSavingResidual.program.run h x).val := by
  rcases x with ⟨ctx,a,raw,⟨k,I⟩,v⟩
  exact DFTModelSavingResidualGeometry.preserved h ctx a raw k I v

lemma direction_preserves (h : Handler ChildPort) (x : DFTModelSavingRecords.Iter.T) :
    Preserves x.2.2 (DFTModelSavingRecords.direction.run h x).val := by
  rcases x with ⟨⟨rest,raw,old⟩,i,node⟩
  rw [DFTModelSavingRecords.direction,DFTModelClockBatch.code_comp_value]
  change Preserves node (DFTModelSavingResidual.program.run h
    (run DFTModelSavingRecords.directionArgs ((rest,(raw,old)),(i,node))).val).val
  rw [DFTModelSavingRecords.directionArgs_value]
  exact residual_preserves h _

lemma residual_loop_preserves (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T) :
    Preserves x.2.2 (DFTModelSavingRecords.residual.run h x).val := by
  rw [DFTModelSavingRecords.residual,DFTModelSavingRecords.code_loop_value]
  exact steps_preserves _ _ (fun _ _=>direction_preserves h _) _

lemma paddingArgs_node (x : DFTModelSavingRecords.Iter.T) :
    (run DFTModelSavingRecords.paddingArgs x).val.2.2=x.2.2 := rfl

lemma padding_preserves (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T) :
    Preserves x.2.2 (DFTModelSavingRecords.padding.run h x).val := by
  rw [DFTModelSavingRecords.padding,DFTModelSavingRecords.code_loop_value]
  apply steps_preserves
  intro i z
  rw [DFTModelSavingRecords.paddingBody,DFTModelClockBatch.code_comp_value]
  exact residual_loop_preserves h _

lemma scalar_preserves (R : ℕ) (raw : Tape ℕ) (node : Node.T) :
    Preserves node (run (DFTModelSavingScalar.program R) (raw,node)).val := by
  rcases node with ⟨⟨k,I⟩,v⟩
  rw [DFTModelSavingScalar.program_value]
  exact ⟨rfl,rfl⟩

lemma movement_length (x : (DFTModelRecursiveYMovement.Input Tagged).T) :
    (run (DFTModelRecursiveYMovement.program Tagged) x).val.len=x.2.2.2.2.len := by
  change (Bill.tab x.2.2.2.2.len Tagged.blank
    (fun j=>run (DFTModelRecursiveYMovement.cell Tagged) (x,j))).val.len=_
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

lemma y_direction_preserves (R : ℕ) (x : DFTModelRecursiveYDirection.Input.T) :
    Preserves x.2.2 (run (DFTModelRecursiveYDirection.program R) x).val := by
  constructor
  · rfl
  · change (run (DFTModelRecursiveYMovement.program Tagged)
      (run (DFTModelRecursiveYDirection.ready R) x).val).val.len=_
    rw [movement_length]
    rfl

lemma y_body_preserves (R : ℕ) (x : DFTModelSavingY.Body.T) :
    Preserves x.2.2 (run (DFTModelSavingY.body R) x).val := by
  change Preserves x.2.2 (run (DFTModelRecursiveYDirection.program R)
    (run DFTModelSavingY.arguments x).val).val
  exact y_direction_preserves R _

lemma y_preserves (R : ℕ) (x : DFTModelSavingY.Input.T) :
    Preserves x.2.2 (run (DFTModelSavingY.program R) x).val := by
  rw [DFTModelSavingY.program_run]
  exact steps_preserves _ _ (fun _ _=>y_body_preserves R _) _

lemma exchange_body_preserves (R : ℕ) (x : DFTModelRecursiveExchange.Body.T) :
    Preserves x.2.2 (run (DFTModelRecursiveExchange.body R) x).val := by
  rcases x with ⟨⟨ps,old⟩,i,⟨k,I⟩,v⟩
  rw [DFTModelRecursiveExchange.body_run]
  obtain ⟨d,s⟩ := ps.look i DFTModelRecursiveExchange.PairNat.blank
  change Preserves ((k,I),v) (run (DFTModelRecursiveExchange.pairProgram R)
    ((d,s),((k,I),v))).val
  rw [DFTModelRecursiveExchange.pair_value]
  exact ⟨rfl,rfl⟩

lemma exchange_pairs_preserves (R : ℕ) (ps : Tape DFTModelRecursiveExchange.PairNat.T)
    (node : Node.T) :
    Preserves node (run (DFTModelRecursiveExchange.pairsProgram R) (ps,node)).val := by
  rw [DFTModelRecursiveExchange.pairs_run]
  exact steps_preserves _ _ (fun _ _=>exchange_body_preserves R _) _

lemma exchange_preserves (R : ℕ) (raw : Tape ℕ) (node : Node.T) :
    Preserves node (run (DFTModelRecursiveExchange.program R) (raw,node)).val := by
  rw [DFTModelRecursiveExchange.program_run]
  change Preserves node (run (DFTModelRecursiveExchange.pairsProgram R)
    ((run DFTModelRecursiveExchange.decode raw).val,node)).val
  exact exchange_pairs_preserves R (run DFTModelRecursiveExchange.decode raw).val node

attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

lemma ifz_preserves {s : Ty} (test : Code false ChildPort s w)
    (f g : Code false ChildPort s Node) (h : Handler ChildPort) (x : s.T) (old : Node.T)
    (hf : Preserves old (f.run h x).val) (hg : Preserves old (g.run h x).val) :
    Preserves old ((Code.ifz test f g).run h x).val := by
  change Preserves old (if (test.run h x).val=0 then f.run h x else g.run h x).val
  split_ifs <;> assumption

lemma dispatch_preserves (R : ℕ) (h : Handler ChildPort) (x : DFTModelSavingRecords.Input.T) :
    Preserves x.2.2 ((DFTModelSavingRecords.dispatch R).run h x).val := by
  unfold DFTModelSavingRecords.dispatch
  apply ifz_preserves
  · exact residual_loop_preserves h x
  · apply ifz_preserves
    · rw [DFTModelClockBatch.code_comp_value]
      exact scalar_preserves R x.2.1 x.2.2
    · apply ifz_preserves
      · exact preserves_refl x.2.2
      · apply ifz_preserves
        · exact y_preserves R x
        · apply ifz_preserves
          · rw [DFTModelClockBatch.code_comp_value]
            exact exchange_preserves R x.2.1 x.2.2
          · apply ifz_preserves
            · exact padding_preserves h x
            · exact preserves_refl x.2.2

theorem stream_preserves (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler ChildPort) :
    Preserves node ((DFTModelSavingRecords.stream R).run h (rest,(rs,node))).val := by
  rw [DFTModelSavingRecords.stream_value]
  exact steps_preserves _ _ (fun _ _=>dispatch_preserves R h _) _

end
end ExactFourierCircuits.DFTModelSavingShape
