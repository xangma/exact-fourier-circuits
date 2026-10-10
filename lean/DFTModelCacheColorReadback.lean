import DFTModelCacheColorExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open DFTModelCacheMatchingNat (tab_value_code tab_run)
open scoped BigOperators
noncomputable section
abbrev ExtractInput := p Input Local
abbrev ExtractIndexed := p ExtractInput w
abbrev Output := p Local (Ty.a w)

def extractLength : Prog false ExtractInput w := .comp (.atom .fst) count
def extractAddress : Prog false ExtractIndexed w :=
  nat .add (.comp (.atom .fst) (.comp (.atom .fst) colorBase)) (.atom .snd)
def extractHeap : Prog false ExtractIndexed (Ty.a (p w w)) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def extractCell : Prog false ExtractIndexed w :=
  .comp (.comp (.fork extractHeap extractAddress) (.atom .look)) (.atom .snd)
def extract : Prog false ExtractInput (Ty.a w) := .tab extractLength extractCell

/-- The public result keeps the actual finite native state and returns its
freshly read color tape in the source's exact order. -/
def colored : Prog false Input Output :=
  .comp (.fork (.atom .id) compiled) (.fork (.atom .snd) extract)

theorem extractCell_run (r : ℕ) (z : Tape Row.T) (v : LocalValue) (j : ℕ) :
    run extractCell (((r,z),v),j)=
      ⟨(v.2.2.look (C z.len+j) (0,0)).2,27,
        max (max 3 z.len) (C z.len+j),True⟩ := by
  simp [extractCell,extractHeap,extractAddress,colorBase,count,nat,DFTModelCacheMatchingNat.count,
    DFTModelCacheMatchingNat.nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,C]

theorem extract_value (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    (run extract ((r,z),v)).val=Tape.tab z.len
      (fun j=>(v.2.2.look (C z.len+j) (0,0)).2) := by
  rw [extract,tab_value_code]
  simp only [extractLength,count,DFTModelCacheMatchingNat.count,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  exact congrArg (Tape.tab z.len) (funext (fun j=>congrArg Bill.val (extractCell_run r z v j)))

theorem extractLength_run (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    run extractLength ((r,z),v)=⟨z.len,5,z.len,True⟩ := by
  simp [extractLength,count,DFTModelCacheMatchingNat.count,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] Code.run

theorem extract_bounds (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    (run extract ((r,z),v)).valid ∧ (run extract ((r,z),v)).work=31*z.len+8 ∧
      (run extract ((r,z),v)).peak≤ max z.len (max 3 (C z.len+z.len)) := by
  rw [extract,tab_run,extractLength_run]
  dsimp only [Bill.pass,Bill.pay]
  have valid: (Bill.tab z.len w.blank (fun j=>run extractCell (((r,z),v),j))).valid := by
    apply (ModelEquivalenceInterpreter.tab_valid _ _ _).mpr
    intro j hj;rw [extractCell_run];trivial
  have work:(Bill.tab z.len w.blank (fun j=>run extractCell (((r,z),v),j))).work=2+31*z.len := by
    rw [ModelEquivalenceInterpreter.tab_work]
    have sum : (∑j∈Finset.range z.len,(run extractCell (((r,z),v),j)).work)=z.len*27 := by
      calc
        _=∑_j∈Finset.range z.len,27 := Finset.sum_congr rfl (fun j _=>
          congrArg Bill.work (extractCell_run r z v j))
        _=z.len*27 := by simp
    rw [sum]
    omega
  have pk:(Bill.tab z.len w.blank (fun j=>run extractCell (((r,z),v),j))).peak≤
      max z.len (max 3 (C z.len+z.len)) := by
    rw [ModelEquivalenceInterpreter.tab_peak]
    apply max_le (le_max_left _ _)
    apply Finset.sup_le
    intro j hj
    rw [extractCell_run]
    dsimp only [Bill.peak]
    have index:=Finset.mem_range.mp hj
    unfold C
    omega
  exact ⟨⟨trivial,valid⟩,by omega,by simpa only [zero_max,max_zero] using max_le (le_max_left z.len (max 3 (C z.len+z.len))) pk⟩

/-- Retain the original Row3 input, including coefficient labels, alongside
actual finite native state and freshly read native color cells. -/
def program : Prog false Input (p Input Output) := .fork (.atom .id) colored

theorem colored_run (r : ℕ) (z : Tape Row.T) :
    run colored (r,z)=
      ⟨((run compiled (r,z)).val,(run extract ((r,z),(run compiled (r,z)).val)).val),
       (run compiled (r,z)).work+(run extract ((r,z),(run compiled (r,z)).val)).work+5,
       max (run compiled (r,z)).peak (run extract ((r,z),(run compiled (r,z)).val)).peak,
       (run compiled (r,z)).valid ∧ (run extract ((r,z),(run compiled (r,z)).val)).valid⟩ := by
  simp only [colored,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
    zero_max,max_zero,true_and,and_true]
  congr 1;omega

theorem program_run (r : ℕ) (z : Tape Row.T) :
    run program (r,z)=
      ⟨((r,z),(run colored (r,z)).val),(run colored (r,z)).work+2,
        (run colored (r,z)).peak,(run colored (r,z)).valid⟩ := by
  simp only [program,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,
    zero_max,max_zero,true_and,and_true]
  congr 1;omega

end
end ExactFourierCircuits.DFTModelCacheColor
