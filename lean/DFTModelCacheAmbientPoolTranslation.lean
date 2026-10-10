import DFTModelCacheRectangleMixedMatching
import UniformTranslatedMatchingRows

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheAmbientPool
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
open DFTModelCacheSelectedCoefficients (Row)
noncomputable section

abbrev TranslationInput := p w (Ty.a Row)
abbrev TranslationCell := p TranslationInput w

def atRow : Prog false TranslationCell Row :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def offset : Prog false TranslationCell w := .comp (.atom .fst) (.atom .fst)
def translatedCell : Prog false TranslationCell Row :=
 .fork (.comp (.fork offset (.comp atRow (.atom .fst))) (.atom (.int .add)))
  (.fork (.comp (.fork offset (.comp atRow (.comp (.atom .snd) (.atom .fst)))) (.atom (.int .add)))
   (.comp atRow (.comp (.atom .snd) (.atom .snd))))
/-- Endpoints are translated by the runtime subtree offset. The coefficient
address is copied unchanged, in the original occurrence order. -/
def translate : Prog false TranslationInput (Ty.a Row) :=
 .tab (.comp (.atom .snd) (.atom .len)) translatedCell

def shifted (o : ℕ) (row : Row.T) : Row.T := (o+row.1,(o+row.2.1,row.2.2))
def translatedTape (o : ℕ) (rs : Tape Row.T) : Tape Row.T :=
 Tape.tab rs.len (fun j=>shifted o (rs.look j Row.blank))

theorem translatedCell_run (o j : ℕ) (rs : Tape Row.T) :
 run translatedCell ((o,rs),j)=
 ⟨shifted o (rs.look j Row.blank),45,
  max (o+(rs.look j Row.blank).1) (o+(rs.look j Row.blank).2.1),True⟩ := by
 simp [translatedCell,offset,atRow,shifted,run,Code.run,Atom.run,
  NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem translate_value (o : ℕ) (rs : Tape Row.T) :
 (run translate (o,rs)).val=translatedTape o rs := by
 rw [translate,DFTModelCacheMatchingNat.tab_value_code]
 change Tape.tab rs.len (fun j=>(run translatedCell ((o,rs),j)).val)=_
 rfl

theorem translate_length (o : ℕ) (rs : Tape Row.T) :
 (run translate (o,rs)).val.len=rs.len := by rw [translate_value];rfl

theorem translate_lookup (o : ℕ) (rs : Tape Row.T) (j : ℕ) (hj:j<rs.len) :
 (run translate (o,rs)).val.look j Row.blank=shifted o (rs.look j Row.blank) := by
 rw [translate_value]
 exact Tape.look_of_lt (translatedTape o rs) Row.blank hj

theorem translate_run (o : ℕ) (rs : Tape Row.T) :
 run translate (o,rs)=
 (Bill.tab rs.len Row.blank (fun j=>run translatedCell ((o,rs),j))).pay 4 rs.len := by
 simp [translate,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
  max_comm,Ty.blank]
 omega

theorem translate_valid (o : ℕ) (rs : Tape Row.T) : (run translate (o,rs)).valid := by
 rw [translate_run]
 change (Bill.tab rs.len Row.blank (fun j=>run translatedCell ((o,rs),j))).valid
 rw [ModelEquivalenceInterpreter.tab_valid]
 intro j _
 rw [translatedCell_run]
 trivial

theorem translate_work (o : ℕ) (rs : Tape Row.T) :
 (run translate (o,rs)).work=49*rs.len+6 := by
 rw [translate_run]
 change (Bill.tab rs.len Row.blank (fun j=>run translatedCell ((o,rs),j))).work+4=_
 rw [ModelEquivalenceInterpreter.tab_work]
 have hw:∀j,(run translatedCell ((o,rs),j)).work=45:=fun j=>
  congrArg Bill.work (translatedCell_run o j rs)
 simp_rw [hw]
 simp
 omega

theorem translate_peak (o v : ℕ) (rs : Tape Row.T)
 (range:∀j,j<rs.len→(rs.look j Row.blank).1<v ∧ (rs.look j Row.blank).2.1<v) :
 (run translate (o,rs)).peak≤ max rs.len (o+v) := by
 have cells:(Finset.range rs.len).sup (fun j=>(run translatedCell ((o,rs),j)).peak)≤o+v := by
  apply Finset.sup_le
  intro j hj
  obtain ⟨hl,hr⟩:=range j (Finset.mem_range.mp hj)
  rw [translatedCell_run]
  change max (o+(rs.look j Row.blank).1) (o+(rs.look j Row.blank).2.1)≤o+v
  exact max_le (Nat.add_le_add_left (Nat.le_of_lt hl) o)
   (Nat.add_le_add_left (Nat.le_of_lt hr) o)
 rw [translate_run]
 change max (Bill.tab rs.len Row.blank (fun j=>run translatedCell ((o,rs),j))).peak rs.len≤_
 rw [ModelEquivalenceInterpreter.tab_peak]
 exact max_le (max_le (le_max_left _ _) (cells.trans (le_max_right _ _))) (le_max_left _ _)

end
end ExactFourierCircuits.DFTModelCacheAmbientPool
