import DFTModelCacheHeightValues
import DFTModelCacheTraversalValidity

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeight
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Finite expression syntax: its work bound is independent of its input. -/
def straight {r s t} : Code false r s t → Bool
  | .atom _ => true
  | .comp f g | .fork f g => straight f && straight g
  | .ifz q f g => straight q && straight f && straight g
  | .importClosed f => straight f
  | _ => false

def straightWork {r s t} : Code false r s t → ℕ
  | .atom _ => 1
  | .comp f g | .fork f g => straightWork f+straightWork g+1
  | .ifz q f g => straightWork q+max (straightWork f) (straightWork g)+1
  | .importClosed f => straightWork f+1
  | _ => 0

theorem straight_work {r s t} (f:Code false r s t) (h:straight f=true)
    (handler:Handler r) (x:s.T) : (f.run handler x).work ≤ straightWork f := by
  induction f with
  | atom op =>
    cases op with
    | int op => cases x;cases op <;> rfl
    | cross impossible => cases impossible
    | scale paint => cases x;rfl
    | add paint => cases x;rfl
    | sub paint => cases x;rfl
    | look => cases x;rfl
    | fst => cases x;rfl
    | snd => cases x;rfl
    | inv => rfl
    | lit n => rfl
    | cz paint => rfl
    | cone => rfl
    | id => rfl
    | len => rfl
  | comp f g ihf ihg =>
    obtain ⟨hf,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h
    exact Nat.add_le_add_right (Nat.add_le_add (ihf hf handler x) (ihg hg handler _)) 1
  | fork f g ihf ihg =>
    obtain ⟨hf,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h
    change (f.run handler x).work+((g.run handler x).work+1) ≤ _
    have a:=ihf hf handler x
    have b:=ihg hg handler x
    change _ ≤ straightWork f+straightWork g+1
    omega
  | ifz q f g ihq ihf ihg =>
    obtain ⟨⟨hq,hf⟩,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h |>.imp_left (DFTModelCacheTraversal.and_true _ _).mp
    have a:=ihq hq handler x
    have b:=ihf hf handler x
    have c:=ihg hg handler x
    change (q.run handler x).work+(if (q.run handler x).val=0 then f.run handler x else g.run handler x).work+1 ≤ _
    change _ ≤ straightWork q+max (straightWork f) (straightWork g)+1
    split_ifs <;> omega
  | importClosed f ih => exact Nat.add_le_add_right (ih h () x) 1
  | loop | tab | sow | call | descend => simp [straight] at h

theorem step_valid (x:Input.T) (q j:ℕ) (s:State.T) :
    (run step ((x,q),(j,s))).valid :=
  DFTModelCacheTraversal.indexCode_valid step (by decide) () _

theorem step_work (x:Input.T) (q j:ℕ) (s:State.T) :
    (run step ((x,q),(j,s))).work ≤ 1000 := by
  exact (straight_work step (by decide) () _).trans (by decide)

theorem slots_work (x:Input.T) : (run slots x).work ≤ 100 :=
  (straight_work slots (by decide) () x).trans (by decide)

theorem slots_valid (x:Input.T) : (run slots x).valid :=
  DFTModelCacheTraversal.indexCode_valid slots (by decide) () x

/-- Bounds every integer cell, including array lengths. Scalar values are unrestricted. -/
def Words : (t:Ty) → ℕ → t.T → Prop
  | w, B, x => x ≤ B
  | c _, _, _ => True
  | p s t, B, x => Words s B x.1 ∧ Words t B x.2
  | Ty.a t, B, x => x.len ≤ B ∧ ∀i,Words t B (x.pos i)

theorem words_mono (t:Ty) {A B:ℕ} (h:A ≤ B) (x:t.T) :
    Words t A x → Words t B x := by
  induction t with
  | w => exact fun hx=>hx.trans h
  | c => exact id
  | p s t ihs iht => exact fun hx=>⟨ihs x.1 hx.1,iht x.2 hx.2⟩
  | a t ih => exact fun hx=>⟨hx.1.trans h,fun i=>ih _ (hx.2 i)⟩

theorem words_blank (t:Ty) (B:ℕ) : Words t B t.blank := by
  induction t with
  | w => exact Nat.zero_le _
  | c => trivial
  | p s t ihs iht => exact ⟨ihs,iht⟩
  | a t => refine ⟨Nat.zero_le _,?_⟩;intro i;exact Fin.elim0 i

theorem words_look (t:Ty) (B:ℕ) (xs:Tape t.T) (hx:Words (Ty.a t) B xs) (i:ℕ) :
    Words t B (xs.look i t.blank) := by
  by_cases hi:i<xs.len
  · rw [Tape.look_of_lt _ _ hi];exact hx.2 _
  · rw [Tape.look_of_le _ _ (Nat.le_of_not_gt hi)];exact words_blank _ _

def atomDegree {r s} : Atom false r s → ℕ
  | .int _ => 2
  | _ => 1

def atomLiteral {r s} : Atom false r s → ℕ
  | .lit n => n
  | _ => 0

def degree {r s t} : Code false r s t → ℕ
  | .atom op => atomDegree op
  | .comp f g => degree f*degree g
  | .fork f g => max (degree f) (degree g)
  | .ifz q f g => max (degree q) (max (degree f) (degree g))
  | .importClosed f => degree f
  | _ => 1

def literals {r s t} : Code false r s t → ℕ
  | .atom op => atomLiteral op
  | .comp f g | .fork f g => max (literals f) (literals g)
  | .ifz q f g => max (literals q) (max (literals f) (literals g))
  | .importClosed f => literals f
  | _ => 0

theorem degree_positive {r s t} (f:Code false r s t) : 1 ≤ degree f := by
  induction f with
  | atom op => cases op <;> simp [degree,atomDegree]
  | comp f g ihf ihg => change 1 ≤ degree f*degree g;simpa only [Nat.one_mul] using Nat.mul_le_mul ihf ihg
  | fork f g ihf => exact ihf.trans (le_max_left _ _)
  | ifz q f g ihq => exact ihq.trans (le_max_left _ _)
  | importClosed f ih => exact ih
  | loop | tab | sow | call | descend => exact le_refl _

private theorem pow_grows (B d:ℕ) (hB:2 ≤ B) (hd:1 ≤ d) : B ≤ B^d :=
  le_self_pow (by omega) (by omega)

private theorem add_square (B i j:ℕ) (hB:2 ≤ B) (hi:i ≤ B) (hj:j ≤ B) : i+j ≤ B^2 := by
  nlinarith

private theorem atom_words {s t} (op:Atom false s t) (B:ℕ) (hB:2 ≤ B)
    (hl:atomLiteral op ≤ B) (x:s.T) (hx:Words s B x) :
    Words t (B^atomDegree op) (op.run x).val ∧ (op.run x).peak ≤ B^atomDegree op := by
  have hsq:B ≤ B^2:=pow_grows B 2 hB (by decide)
  cases op with
  | lit n => change n ≤ B at hl;change n ≤ B^1 ∧ n ≤ B^1;simpa only [pow_one] using And.intro hl hl
  | int op =>
    rcases x with ⟨i,j⟩
    change i ≤ B ∧ j ≤ B at hx
    have hv:(op.run (i,j)).val ≤ B^2 := by
      cases op with
      | add => exact add_square B i j hB hx.1 hx.2
      | sub => exact (Nat.sub_le i j).trans (hx.1.trans hsq)
      | mul => exact (Nat.mul_le_mul hx.1 hx.2).trans (by rw [pow_two])
      | div => exact (Nat.div_le_self i j).trans (hx.1.trans hsq)
      | mod => exact (Nat.mod_le i j).trans (hx.1.trans hsq)
      | lt => change (if i<j then 1 else 0) ≤ _;split_ifs <;> omega
    exact ⟨hv,by cases op <;>exact hv⟩
  | cz => exact ⟨trivial,Nat.zero_le _⟩
  | cone => exact ⟨trivial,Nat.zero_le _⟩
  | add => exact ⟨trivial,Nat.zero_le _⟩
  | sub => exact ⟨trivial,Nat.zero_le _⟩
  | scale => exact ⟨trivial,Nat.zero_le _⟩
  | inv => exact ⟨trivial,Nat.zero_le _⟩
  | cross impossible => cases impossible
  | id => change Words _ (B^1) x ∧ 0 ≤ B^1;simpa only [pow_one] using And.intro hx (Nat.zero_le B)
  | fst => change Words _ (B^1) x.1 ∧ 0 ≤ B^1;simpa only [pow_one] using And.intro hx.1 (Nat.zero_le B)
  | snd => change Words _ (B^1) x.2 ∧ 0 ≤ B^1;simpa only [pow_one] using And.intro hx.2 (Nat.zero_le B)
  | len => change x.len ≤ B^1 ∧ x.len ≤ B^1;simpa only [pow_one] using And.intro hx.1 hx.1
  | @look t => change Words t (B^1) (x.1.look x.2 t.blank) ∧ 0 ≤ B^1;simpa only [pow_one] using And.intro (words_look t B x.1 hx.1 x.2) (Nat.zero_le B)

/-- A fixed polynomial word bound for a genuine finite expression, not a value oracle. -/
theorem straight_words {r s t} (f:Code false r s t) (h:straight f=true)
    (handler:Handler r) (B:ℕ) (hB:2 ≤ B) (hl:literals f ≤ B)
    (x:s.T) (hx:Words s B x) :
    Words t (B^degree f) (f.run handler x).val ∧ (f.run handler x).peak ≤ B^degree f := by
  induction f generalizing B with
  | atom op => exact atom_words op B hB hl x hx
  | comp f g ihf ihg =>
    obtain ⟨hf,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h
    have hb:=pow_grows B (degree f) hB (degree_positive f)
    have a:=ihf hf handler B hB ((le_max_left _ _).trans hl) x hx
    have b:=ihg hg handler (B^degree f) (hB.trans hb)
      (((le_max_right _ _).trans hl).trans hb) _ a.1
    rw [←pow_mul] at b
    have dg:0<degree g:=degree_positive g
    have dd:degree f ≤ degree f*degree g:=Nat.le_mul_of_pos_right _ dg
    change Words _ _ _ ∧ max (max (f.run handler x).peak (g.run handler (f.run handler x).val).peak) 0 ≤ _
    exact ⟨b.1,max_le (max_le (a.2.trans (Nat.pow_le_pow_right (by omega) dd)) b.2) (Nat.zero_le _)⟩
  | fork f g ihf ihg =>
    obtain ⟨hf,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h
    have a:=ihf hf handler B hB ((le_max_left _ _).trans hl) x hx
    have b:=ihg hg handler B hB ((le_max_right _ _).trans hl) x hx
    have af:B^degree f ≤ B^max (degree f) (degree g):=Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have bg:B^degree g ≤ B^max (degree f) (degree g):=Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    exact ⟨⟨words_mono _ af _ a.1,words_mono _ bg _ b.1⟩,max_le (a.2.trans af) (max_le (b.2.trans bg) (Nat.zero_le _))⟩
  | ifz q f g ihq ihf ihg =>
    obtain ⟨⟨hq,hf⟩,hg⟩:=DFTModelCacheTraversal.and_true _ _ |>.mp h |>.imp_left (DFTModelCacheTraversal.and_true _ _).mp
    have a:=ihq hq handler B hB ((le_max_left _ _).trans hl) x hx
    have b:=ihf hf handler B hB (((le_max_left _ _).trans (le_max_right _ _)).trans hl) x hx
    have c:=ihg hg handler B hB (((le_max_right _ _).trans (le_max_right _ _)).trans hl) x hx
    have aq:B^degree q ≤ B^degree (.ifz q f g):=Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have bf:B^degree f ≤ B^degree (.ifz q f g):=Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_right _ _))
    have cg:B^degree g ≤ B^degree (.ifz q f g):=Nat.pow_le_pow_right (by omega) ((le_max_right _ _).trans (le_max_right _ _))
    change Words _ _ (if (q.run handler x).val=0 then f.run handler x else g.run handler x).val ∧
      max (max (q.run handler x).peak (if (q.run handler x).val=0 then f.run handler x else g.run handler x).peak) 0 ≤ _
    split_ifs
    · exact ⟨words_mono _ bf _ b.1,max_le (max_le (a.2.trans aq) (b.2.trans bf)) (Nat.zero_le _)⟩
    · exact ⟨words_mono _ cg _ c.1,max_le (max_le (a.2.trans aq) (c.2.trans cg)) (Nat.zero_le _)⟩
  | importClosed f ih =>
    have hh:=ih h () B hB hl x hx
    exact ⟨hh.1,max_le hh.2 (Nat.zero_le _)⟩
  | loop | tab | sow | call | descend => simp [straight] at h

end
end ExactFourierCircuits.DFTModelCacheHeight
