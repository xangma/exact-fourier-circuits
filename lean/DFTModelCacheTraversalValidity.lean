import DFTModelCacheTraversalStructure

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- A syntactic check, not a runtime validity oracle. -/
def indexCode {r s t} : Code false r s t → Bool
  | .atom .inv => false
  | .atom _ => true
  | .comp f g | .fork f g => indexCode f && indexCode g
  | .ifz q f g => indexCode q && indexCode f && indexCode g
  | .loop n f g => indexCode n && indexCode f && indexCode g
  | .tab n f => indexCode n && indexCode f
  | .importClosed f => indexCode f
  | .sow _ _ _ | .call | .descend _ _ => false

theorem and_true (a b : Bool) : (a && b)=true ↔ a=true ∧ b=true := by
  cases a <;> cases b <;> decide

theorem steps_valid {α : Type} (x : α) (f : ℕ → α → Bill α)
    (hf : ∀i a,(f i a).valid) (j : ℕ) : (Bill.steps x f j).valid := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨ih,hf j _⟩

theorem indexCode_valid {r s t} (f : Code false r s t) (h : indexCode f=true)
    (handler : Handler r) (x : s.T) : (f.run handler x).valid := by
  induction f with
  | atom op =>
    cases op with
    | inv => simp [indexCode] at h
    | int op => cases x with | mk i j => cases op <;> trivial
    | cross impossible => cases impossible
    | scale paint => cases x;trivial
    | add paint => cases x;trivial
    | sub paint => cases x;trivial
    | look => cases x;trivial
    | lit n => trivial
    | cz paint => trivial
    | cone => trivial
    | id => trivial
    | fst => trivial
    | snd => trivial
    | len => trivial
  | comp f g ihf ihg =>
    obtain ⟨hf,hg⟩:=(and_true _ _).mp h
    exact ⟨ihf hf handler x,ihg hg handler _⟩
  | fork f g ihf ihg =>
    obtain ⟨hf,hg⟩:=(and_true _ _).mp h
    exact ⟨ihf hf handler x,ihg hg handler x,trivial⟩
  | ifz q f g ihq ihf ihg =>
    obtain ⟨⟨hq,hf⟩,hg⟩:=(and_true _ _).mp h |>.imp_left (and_true _ _).mp
    change (q.run handler x).valid ∧
      (if (q.run handler x).val=0 then f.run handler x else g.run handler x).valid
    refine ⟨ihq hq handler x,?_⟩
    split_ifs
    · exact ihf hf handler x
    · exact ihg hg handler x
  | loop n init body ihn ihi ihb =>
    obtain ⟨⟨hn,hi⟩,hb⟩:=(and_true _ _).mp h |>.imp_left (and_true _ _).mp
    exact ⟨ihn hn handler x,ihi hi handler x,
      steps_valid _ _ (fun i a=>ihb hb handler (x,(i,a))) _⟩
  | tab n body ihn ihb =>
    obtain ⟨hn,hb⟩:=(and_true _ _).mp h
    exact ⟨ihn hn handler x,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
      (fun i _=>ihb hb handler (x,i))⟩
  | importClosed f ih => exact ih h () x
  | sow => simp [indexCode] at h
  | call => simp [indexCode] at h
  | descend => simp [indexCode] at h

theorem finish_valid (x : FrameT.T) : (run finish x).valid :=
  indexCode_valid finish (by decide) () x

end
end ExactFourierCircuits.DFTModelCacheTraversal
