import DFTModelCacheTopologyExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheNatControl
noncomputable section

abbrev Computed := p Config Local
abbrev Output := p w (p w (Ty.a w))
def resultHeap : Prog false Computed (Ty.a Cell) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def rowLength : Prog false Computed w := nat .mul (.atom (.lit 5))
  (.comp (.atom .fst) crossCount)
def readCell : Prog false (p Computed w) w :=
  .comp (.comp (.fork (.comp (.atom .fst) resultHeap)
    (nat .add (.comp (.comp (.atom .fst) (.atom .fst)) destination) (.atom .snd)))
      (.atom .look)) (.atom .snd)
def extract : Prog false Computed (Ty.a w) := .tab rowLength readCell
def readback : Prog false Computed Output := .fork (.comp (.atom .fst) k)
  (.fork (.comp (.atom .fst) crossCount) extract)
def computed : Prog false Config Computed := .fork (.atom .id) compiled
def body : Prog false Config Output := .comp computed readback
def program : Prog false Input Output := .comp prepare body

def outputValue (K a _e : ℕ) (v : LocalValue) : Output.T :=
  (K,(C K a,Tape.tab (5*C K a) (fun j=>(v.2.2.look (D K+j) (0,0)).2)))

theorem readCell_run (K a e j : ℕ) (v : LocalValue) :
    run readCell ((config K a e,v),j)=
      ⟨(v.2.2.look (D K+j) (0,0)).2, (run destination (config K a e)).work+20,
        max (run destination (config K a e)).peak (D K+j),
        (run destination (config K a e)).valid ∧ True⟩ := by
  simp only [readCell,resultHeap,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,destination_value,true_and,and_true,
    max_zero,zero_max]
  congr 1

theorem extract_value (K a e : ℕ) (v : LocalValue) :
    (run extract (config K a e,v)).val=
      Tape.tab (5*C K a) (fun j=>(v.2.2.look (D K+j) (0,0)).2) := by
  rw [extract,DFTModelCacheMatchingNat.tab_value_code]
  have len:(run rowLength (config K a e,v)).val=5*C K a := by
    rw [rowLength,nat_value]
    simp only [run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,crossCount_value]
  rw [len]
  exact congrArg (Tape.tab (5*C K a)) (funext (fun j=>congrArg Bill.val (readCell_run K a e j v)))

theorem readback_value (K a e : ℕ) (v : LocalValue) :
    (run readback (config K a e,v)).val=outputValue K a e v := by
  rw [readback,DFTModelCacheMatchingNat.fork_value,DFTModelCacheMatchingNat.fork_value]
  change (_,((run crossCount (config K a e)).val,(run extract (config K a e,v)).val))=_
  rw [crossCount_value,extract_value];rfl

/-- Every read is from the genuine terminal native five-field bank. -/
theorem copied_topology (K a e : ℕ) (v : LocalValue) (u : UniformMachine.State)
    (len : v.2.2.len=H K a e) (rep : Represents v u)
    (rows : UniformToeplitzCrossTopologyMachine.RowTable
      (UniformToeplitzCrossTopologyMachine.crossRows K a e) (D K) u) :
    DFTModelCacheDAGDepth.CopiedTopology (C K a) (D K)
      (run readback (config K a e,v)).val.2.2 u := by
  rw [readback_value]
  refine ⟨le_rfl,?_⟩
  intro j hj
  have sizes:(UniformToeplitzCrossTopologyMachine.crossRows K a e).length=C K a :=
    UniformToeplitzCrossTopologyMachine.crossRows_length K a e
  have present:=UniformToeplitzCrossTopologyMachine.rowTable_present rows j (by simpa only [sizes] using hj)
  obtain ⟨value,hvalue⟩:=present
  have room:=UniformToeplitzCrossTopologyMachine.budget_tape K a e 0 (D K)
  have inside:D K+j<v.2.2.len := by rw [len];unfold H B C G at *;omega
  have represented:=rep.heap (D K+j) inside
  rw [hvalue] at represented
  unfold cell ModelEquivalenceInterpreter.decodeNatCell at represented
  have equal:(v.2.2.look (D K+j) (0,0)).2=value := by
    split at represented
    · cases represented
    · exact Option.some.inj represented
  change u.natHeap (D K+j)=some ((Tape.tab (5*C K a) _).look j 0)
  rw [Tape.look_of_lt _ _ hj]
  exact hvalue.trans (congrArg some equal.symm)

theorem encoded_tape (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K)
    (u : UniformMachine.State)
    (rows : UniformToeplitzCrossTopologyMachine.RowTable
      (UniformToeplitzCrossTopologyMachine.crossRows K a e) (D K) u) :
    UniformDAGDepthMachine.EncodedTape (UniformToeplitzCrossDAG.crossDAG K a e ha he).program (D K) u := by
  change UniformToeplitzCrossTopologyMachine.RowTable _ (D K) u
  rw [←UniformToeplitzCrossTopologyMachine.crossRows_typed K a e ha he]
  exact rows

theorem typed_count (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K) :
    (UniformToeplitzCrossDAG.crossDAG K a e ha he).size=C K a := by
  rw [UniformToeplitzCrossDAG.crossDAG_size]
  simp only [C,G_formula,UniformRadixTwoDAG.width_eq]

end
end ExactFourierCircuits.DFTModelCacheTopology
