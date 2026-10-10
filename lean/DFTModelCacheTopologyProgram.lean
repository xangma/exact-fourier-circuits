import DFTModelCacheNatDispatchFinite
import DFTModelCacheNatProjectionTyped
import DFTModelCacheMatchingNatBounds
import DFTModelCacheDescriptorLog
import DFTModelCacheDAGDepthSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

abbrev Input := p w w
/-- Ordinary raw dimensions paired with the charged logarithm result (K,N). -/
abbrev Config := p Input (p w w)
abbrev Indexed := p Config w

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def a : Prog false Config w := .comp (.atom .fst) (.atom .fst)
def e : Prog false Config w := .comp (.atom .fst) (.atom .snd)
def k : Prog false Config w := .comp (.atom .snd) (.atom .fst)
def n : Prog false Config w := .comp (.atom .snd) (.atom .snd)
def target : Prog false Input w := nat .mul (.atom (.lit 2))
  (nat .add (.atom .fst) (.atom .snd))
def prepare : Prog false Input Config :=
  .fork (.atom .id) (.comp target DFTModelCacheDescriptor.logarithm)

def fftCount : Prog false Config w := nat .div
  (nat .mul (nat .mul (.atom (.lit 3)) k) n) (.atom (.lit 2))
def gates : Prog false Config w := nat .add
  (nat .mul (nat .mul (.atom (.lit 3)) k) n) (nat .mul (.atom (.lit 2)) n)
def destination : Prog false Config w := nat .mul (.atom (.lit 5)) gates
def square {s : Ty} (f : Prog false s w) : Prog false s w := nat .mul f f
def cap : Prog false Config w := nat .add
  (nat .mul (.atom (.lit 100)) (square
    (nat .add (nat .add (nat .add n fftCount) k) (.atom (.lit 1))))) (.atom (.lit 200))
def sum : Prog false Config w := nat .add
  (nat .add (nat .add (nat .add (nat .add n gates) a) e) k) (.atom (.lit 1))
def allocation : Prog false Config w := nat .add
  (nat .add (nat .add destination
    (nat .mul (.atom (.lit 5))
      (nat .add (nat .mul (.atom (.lit 7)) gates) (nat .mul (.atom (.lit 2)) a)))) cap)
  (nat .mul (.atom (.lit 10000)) (square sum))
def heapLength : Prog false Config w := nat .add allocation (.atom (.lit 1))
def fuel : Prog false Config w := nat .add
  (nat .add (nat .add (nat .mul (.atom (.lit 4)) k) (.atom (.lit 113)))
    (nat .mul (nat .add (nat .mul (.atom (.lit 19)) k) (.atom (.lit 344))) gates))
  (nat .mul (.atom (.lit 40)) a)
def crossCount : Prog false Config w := nat .add
  (nat .mul (.atom (.lit 6)) gates) (nat .mul (.atom (.lit 2)) a)

def registerCell : Prog false Indexed w :=
  DFTModelCacheMatchingNat.select (.atom .snd) 560 (.comp (.atom .fst) k)
  (DFTModelCacheMatchingNat.select (.atom .snd) 561 (.comp (.atom .fst) a)
  (DFTModelCacheMatchingNat.select (.atom .snd) 562 (.comp (.atom .fst) e)
  (DFTModelCacheMatchingNat.select (.atom .snd) 564 (.comp (.atom .fst) destination)
    (.atom (.lit 0)))))
def emptyCell : Prog false Indexed Cell := .fork (.atom (.lit 0)) (.atom (.lit 0))
def initializeProgram : Prog false Config Local := .fork (.atom (.lit 0))
  (.fork (.tab (.atom (.lit 600)) registerCell) (.tab heapLength emptyCell))
def instructions := DFTModelCacheNatProjection.code UniformToeplitzCrossTopologyMachine.program
def compiled : Prog false Config Local := .comp (.fork fuel initializeProgram)
  (DFTModelCacheNatDispatch.fuelProgram instructions)

/-- The complete native 271-instruction syntax, not a supplied topology table. -/
theorem instructions_length : instructions.length=271 := by
  rw [instructions,DFTModelCacheNatProjection.code_length,
    UniformToeplitzCrossTopologyMachine.program_length]
private theorem native_map (p : UniformMachine.Program)
    (safe : ∀i∈p,UniformToeplitzCrossTopologyMachine.safe i) :
    DFTModelCacheNatDispatch.native (DFTModelCacheNatProjection.code p)=p := by
  apply List.ext_getElem?
  intro j
  simp only [DFTModelCacheNatDispatch.native,List.getElem?_map,
    DFTModelCacheNatProjection.code,List.getElem?_mapIdx]
  cases h:p[j]? with
  | none=>rfl
  | some i=>
    have si:=safe i (List.mem_of_getElem? h)
    cases i <;> simp_all [UniformToeplitzCrossTopologyMachine.safe,
      DFTModelCacheNatProjection.instruction,Instruction.native]

theorem instructions_native : DFTModelCacheNatDispatch.native instructions=
    UniformToeplitzCrossTopologyMachine.program :=
  native_map _ UniformToeplitzCrossTopologyMachine.program_safe

private def nativeFoot (R L : ℕ) : UniformMachine.Instruction→Prop
  | .natLiteral d v=>d<R ∧ v≤L
  | .natBinary _ d l r=>d<R ∧ l<R ∧ r<R
  | .loadNat d a=>d<R ∧ a<R
  | .storeNat a s=>a<R ∧ s<R
  | .branchLT l r y n=>l<R ∧ r<R ∧ y≤L ∧ n≤L
  | .jump t=>t≤L
  | .halt=>True
  | _=>False
private instance (R L : ℕ) (i : UniformMachine.Instruction) : Decidable (nativeFoot R L i) := by
  cases i <;> unfold nativeFoot <;> infer_instance

private theorem relocate_foot {R L M base ret : ℕ} (i : UniformMachine.Instruction)
    (h : nativeFoot R L i) (target : base+L≤M) (back : ret≤M) (le : L≤M) :
    nativeFoot R M (UniformAssembly.relocate base ret i) := by
  cases i <;> simp_all [nativeFoot,UniformAssembly.relocate] <;> omega

private theorem embed_foot {R L M base ret : ℕ} (head body tail : UniformMachine.Program)
    (hh : ∀i∈head,nativeFoot R M i) (hb : ∀i∈body,nativeFoot R L i)
    (ht : ∀i∈tail,nativeFoot R M i) (hlen : head.length=base)
    (target : base+L≤M) (back : ret≤M) (le : L≤M) :
    ∀i∈UniformAssembly.embed head body tail ret,nativeFoot R M i := by
  intro i hi
  simp only [UniformAssembly.embed,List.mem_append,List.mem_map] at hi
  rcases hi with (left|⟨old,member,rfl⟩)|right
  · exact hh i left
  · rw [hlen];exact relocate_foot old (hb old member) target back le
  · exact ht i right

private theorem decoder_footprint : ∀i∈UniformRadixInstructionMachine.program,
    nativeFoot 600 72 i := by decide
private theorem convolution_footprint : ∀i∈UniformConvolutionTopologyMachine.program,
    nativeFoot 600 154 i := by
  exact embed_foot _ _ _ (by decide) decoder_footprint (by decide)
    UniformConvolutionTopologyMachine.head_length (by decide) (by decide) (by decide)
private theorem native_footprint : ∀i∈UniformToeplitzCrossTopologyMachine.program,nativeFoot 600 600 i := by
  exact embed_foot _ _ _ (by decide) convolution_footprint (by decide)
    UniformToeplitzCrossTopologyMachine.head_length (by decide) (by decide) (by decide)

/-- Every operand, literal and branch is checked, including embedded decoder72. -/
theorem instructions_footprint : ∀i∈instructions,
    DFTModelCacheNatDispatchFinite.Footprint 600 600 i := by
  intro i hi
  obtain ⟨j,selected⟩ := List.mem_iff_getElem?.mp hi
  simp only [instructions,DFTModelCacheNatProjection.code,List.getElem?_mapIdx] at selected
  cases h:UniformToeplitzCrossTopologyMachine.program[j]? with
  | none=>simp [h] at selected
  | some q=>
    simp only [h,Option.map_some,Option.some.injEq] at selected
    subst i
    have foot:=native_footprint q (List.mem_of_getElem? h)
    cases q <;> simp_all [nativeFoot,DFTModelCacheNatProjection.instruction,
      DFTModelCacheNatDispatchFinite.Footprint]

def G (K : ℕ) := UniformToeplitzCrossTopologyMachine.G K
def D (K : ℕ) := 5*G K
def B (K a e : ℕ) := UniformToeplitzCrossTopologyMachine.budget K a e 0 (D K)
def H (K a e : ℕ) := B K a e+1
def T (K a : ℕ) := 4*K+113+(19*K+344)*G K+40*a
def C (K a : ℕ) := 6*G K+2*a
def config (K a e : ℕ) : Config.T := ((a,e),(K,UniformRadixTwoDAG.width K))
def regValue (K a e j : ℕ) := if j=560 then K else if j=561 then a
  else if j=562 then e else if j=564 then D K else 0
def initialValue (K a e : ℕ) : LocalValue :=
  (0,(Tape.tab 600 (regValue K a e),Tape.tab (H K a e) (fun _=>(0,0))))
def sourceState (K a e : ℕ) : UniformMachine.State :=
  { UniformMachine.initial with natReg:=regValue K a e }

end
end ExactFourierCircuits.DFTModelCacheTopology
