import DFTModelGlobalSectorPreparationHandoff
import DFTModelSectorTransposeSaving
import DFTModelSectorMaterializationBounds
import DFTModelSavingClosedBoolean

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean DFTModelResidualCore
open scoped BigOperators
noncomputable section

abbrev MoveInput := p w (p w (p (Ty.a w) (Ty.a Tagged)))
abbrev MoveCell := p MoveInput w
def moveRoles : Prog false MoveInput w := .atom .fst
def moveVolume : Prog false MoveInput w := .comp (.atom .snd) (.atom .fst)
def moveMap : Prog false MoveInput (Ty.a w) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def moveBank : Prog false MoveInput (Ty.a Tagged) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def moveSize : Prog false MoveInput w := binary .mul moveRoles moveVolume
def moveIndex : Prog false MoveCell w :=
 binary .add
  (binary .mul (binary .div (.atom .snd) (.comp (.atom .fst) moveVolume))
    (.comp (.atom .fst) moveVolume))
  (.comp (.fork (.comp (.atom .fst) moveMap)
    (binary .mod (.atom .snd) (.comp (.atom .fst) moveVolume))) (.atom .look))
def moveCell : Prog false MoveCell Tagged :=
 .comp (.fork (.comp (.atom .fst) moveBank) moveIndex) (.atom .look)
/-- A single whole-bank tab; maps are compact relative coordinates. -/
def move : Prog false MoveInput (Ty.a Tagged) := .tab moveSize moveCell

def moved (W V : ℕ) (p : Tape ℕ) (v : Tape Tagged.T) : Tape Tagged.T :=
 Tape.tab (W*V) (fun j=>v.look ((j/V)*V+p.look (j%V) 0) Tagged.blank)

theorem moveSize_run (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 run moveSize (W,(V,(p,v)))=⟨W*V,7,W*V,True⟩ := by
 simp [moveSize,moveRoles,moveVolume,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem moveIndex_run (W V j : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 run moveIndex ((W,(V,(p,v))),j)=
 ⟨(j/V)*V+p.look (j%V) 0,39,
   max (j/V) (max ((j/V)*V) (max (j%V) ((j/V)*V+p.look (j%V) 0))),True⟩ := by
 simp [moveIndex,moveVolume,moveMap,binary,run,Code.run,Atom.run,NOp.run,
  Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,max_comm,max_left_comm]

theorem moveCell_run (W V j : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 run moveCell ((W,(V,(p,v))),j)=
 ⟨v.look ((j/V)*V+p.look (j%V) 0) Tagged.blank,49,
   max (j/V) (max ((j/V)*V) (max (j%V) ((j/V)*V+p.look (j%V) 0))),True⟩ := by
 simp only [moveCell,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [show Code.run moveIndex () ((W,(V,(p,v))),j)=_ from moveIndex_run W V j p v]
 simp [moveBank,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem move_run (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 run move (W,(V,(p,v)))=
 (Bill.tab (W*V) Tagged.blank (fun j=>run moveCell ((W,(V,(p,v))),j))).pay 8 (W*V) := by
 rw [move,DFTModelSectorMap.tab_run,moveSize_run]
 simp only [Bill.pass,Bill.pay,true_and]
 congr 1 <;> omega

attribute [local irreducible] moveCell move

theorem move_value (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 (run move (W,(V,(p,v)))).val=moved W V p v := by
 rw [move_run]
 change (Bill.tab _ _ _).val=_
 rw [ModelEquivalenceInterpreter.tab_value]
 exact congrArg (Tape.tab (W*V)) (funext (fun j=>congrArg Bill.val (moveCell_run W V j p v)))

theorem move_work (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 (run move (W,(V,(p,v)))).work=53*(W*V)+10 := by
 rw [move_run]
 change (Bill.tab _ _ _).work+8=_
 rw [ModelEquivalenceInterpreter.tab_work]
 have h:(fun j=>(run moveCell ((W,(V,(p,v))),j)).work)=fun _=>49:=
  funext (fun j=>congrArg Bill.work (moveCell_run W V j p v))
 rw [h];simp;omega

theorem move_valid (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) :
 (run move (W,(V,(p,v)))).valid := by
 rw [move_run]
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro j _;rw [moveCell_run];trivial

theorem move_boolean (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T) (before:Boolean v) :
 Boolean (run move (W,(V,(p,v)))).val := by
 rw [move_value]
 exact tab_boolean _ _ (fun _ _=>look_boolean before _)

theorem move_peak (W V : ℕ) (p:Tape ℕ) (v:Tape Tagged.T)
 (bounds:∀j,j<V→p.look j 0<V) :
 (run move (W,(V,(p,v)))).peak≤W*V := by
 rw [move_run]
 change max (Bill.tab _ _ _).peak (W*V)≤_
 rw [ModelEquivalenceInterpreter.tab_peak]
 refine max_le (max_le le_rfl ?_) le_rfl
 apply Finset.sup_le
 intro j hj
 have small: j<W*V:=Finset.mem_range.mp hj
 have vp:0<V:=by nlinarith
 have rem:j%V<V:=Nat.mod_lt j vp
 have pb:=bounds (j%V) rem
 have product:(j/V)*V≤j:=Nat.div_mul_le_self j V
 have role:j/V<W:=(Nat.div_lt_iff_lt_mul vp).2 (by simpa [Nat.mul_comm] using small)
 have total:(j/V)*V+p.look (j%V) 0<W*V:=by nlinarith
 rw [moveCell_run]
 change max (j/V) (max ((j/V)*V) (max (j%V) ((j/V)*V+p.look (j%V) 0)))≤_
 have div:=Nat.div_le_self j V
 exact max_le (div.trans small.le) (max_le (product.trans small.le)
  (max_le ((Nat.mod_le j V).trans small.le) total.le))

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly
