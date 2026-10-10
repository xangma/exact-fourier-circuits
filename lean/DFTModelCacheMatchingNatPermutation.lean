import DFTModelCacheMatchingNatExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
open UniformMatchingAxisTableMachine
noncomputable section
abbrev ExtractInput := p Input Local
abbrev ExtractIndexed := p ExtractInput w
abbrev Output := p Local (Ty.a w)

def extractLength : Prog false ExtractInput w := .comp (.atom .fst) radix
def extractAddress : Prog false ExtractIndexed w :=
  nat .add (.comp (.atom .fst) (.comp (.atom .fst) permutationBase)) (.atom .snd)
def extractHeap : Prog false ExtractIndexed (Ty.a (p w w)) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def extractCell : Prog false ExtractIndexed w :=
  .comp (.comp (.fork extractHeap extractAddress) (.atom .look)) (.atom .snd)
def extract : Prog false ExtractInput (Ty.a w) := .tab extractLength extractCell

/-- The public result keeps the actual finite native state and returns its
freshly read permutation tape in the source's exact order. -/
def program : Prog false Input Output :=
  .comp (.fork (.atom .id) compiled) (.fork (.atom .snd) extract)

theorem extractCell_run (r : ℕ) (z : Tape Row.T) (v : LocalValue) (j : ℕ) :
    run extractCell (((r,z),v),j)=
      ⟨(v.2.2.look (P z.len+j) (0,0)).2,27,
        max (max 3 z.len) (P z.len+j),True⟩ := by
  simp [extractCell,extractHeap,extractAddress,permutationBase,count,nat,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,P]

theorem extract_value (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    (run extract ((r,z),v)).val=Tape.tab r
      (fun j=>(v.2.2.look (P z.len+j) (0,0)).2) := by
  rw [extract,tab_value_code]
  simp only [extractLength,radix,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  exact congrArg (Tape.tab r) (funext (fun j=>congrArg Bill.val (extractCell_run r z v j)))

theorem extractLength_run (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    run extractLength ((r,z),v)=⟨r,3,0,True⟩ := by
  simp [extractLength,radix,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] Code.run

theorem extract_bounds (r : ℕ) (z : Tape Row.T) (v : LocalValue) :
    (run extract ((r,z),v)).valid ∧ (run extract ((r,z),v)).work=31*r+6 ∧
      (run extract ((r,z),v)).peak≤ max r (max 3 (P z.len+r)) := by
  rw [extract,tab_run,extractLength_run]
  dsimp only [Bill.pass,Bill.pay]
  have valid: (Bill.tab r w.blank (fun j=>run extractCell (((r,z),v),j))).valid := by
    apply (ModelEquivalenceInterpreter.tab_valid _ _ _).mpr
    intro j hj;rw [extractCell_run];trivial
  have work:(Bill.tab r w.blank (fun j=>run extractCell (((r,z),v),j))).work=2+31*r := by
    rw [ModelEquivalenceInterpreter.tab_work]
    have sum : (∑j∈Finset.range r,(run extractCell (((r,z),v),j)).work)=r*27 := by
      calc
        _=∑_j∈Finset.range r,27 := Finset.sum_congr rfl (fun j _=>
          congrArg Bill.work (extractCell_run r z v j))
        _=r*27 := by simp
    rw [sum]
    omega
  have pk:(Bill.tab r w.blank (fun j=>run extractCell (((r,z),v),j))).peak≤
      max r (max 3 (P z.len+r)) := by
    rw [ModelEquivalenceInterpreter.tab_peak]
    apply max_le (le_max_left _ _)
    apply Finset.sup_le
    intro j hj
    rw [extractCell_run]
    dsimp only [Bill.peak]
    have index:=Finset.mem_range.mp hj
    unfold P
    omega
  exact ⟨⟨trivial,valid⟩,by omega,by simpa only [zero_max,max_zero] using pk⟩

/-- Native readback uses the same produced ordered bank, including unused
singletons, and does not introduce a semantic permutation callback. -/
theorem extracted_ordered {M : ℕ} (r : ℕ) (z : Tape Row.T) (v : LocalValue)
    (u : UniformMachine.State) (E : Fin M→UniformColoring.Edge)
    (hm : Matching E) (hr : InRange r E) (length : v.2.2.len=heapSize r z.len)
    (rep : Represents v u) (bank : Bank (P z.len) (ordered r E) u) :
    (run extract ((r,z),v)).val.len=r ∧
    ∀j : Fin r,(run extract ((r,z),v)).val.look j.val 0=
      (ordered r E)[j.val]'(by rw [ordered_length r E hm hr];exact j.isLt) := by
  rw [extract_value]
  refine ⟨rfl,?_⟩
  intro j
  rw [Tape.look_of_lt _ _ (by exact j.isLt)]
  change (v.2.2.look (P z.len+j.val) (0,0)).2=_
  have inside:P z.len+j.val<v.2.2.len := by
    rw [length];unfold heapSize wordBound A U W;omega
  have produced:=bank j.val (by rw [ordered_length r E hm hr];exact j.isLt)
  have represented:=rep.heap (P z.len+j.val) inside
  rw [produced] at represented
  unfold cell at represented
  unfold ModelEquivalenceInterpreter.decodeNatCell at represented
  split at represented
  · cases represented
  · exact Option.some.inj represented

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
