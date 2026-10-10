import DFTModelSavingRecords
import DFTModelSavingBinarySuffixProgram
import DFTModelCacheRecords

set_option autoImplicit false

/-! A closed recursive saving program in the unchanged upstream syntax.
The seed/unit tapes are produced by actual Code, records execute in order,
and each residual group invokes the one paired child port once. Correctness
and recurrence bounds are separate obligations, not fields of this syntax. -/
namespace ExactFourierCircuits.DFTModelSavingProgram
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelResidualCore
noncomputable section

abbrev Large := p w (p w Node)
abbrev Finished := p Large Node

def bits : Prog false Node w := .comp (.atom .fst) (.atom .fst)
def quotient : Prog false Node w := binary .div bits (.atom (.lit UniformFixedNetwork.m))
def remainder : Prog false Node w := binary .mod bits (.atom (.lit UniformFixedNetwork.m))
/-- q and the spectator remainder are computed once and retained. -/
def setup : Prog false Node Large := .fork quotient (.fork remainder (.atom .id))
def q : Prog false Large w := .atom .fst
def rest : Prog false Large w := .comp (.atom .snd) (.atom .fst)
def node : Prog false Large Node := .comp (.atom .snd) (.atom .snd)
def seedArgs : Prog false Large DFTModelSavingRecords.StreamInput := .fork rest
  (.fork (.comp q DFTModelCacheRecords.seed) node)

def suffixArgs : Prog false Finished DFTModelSavingBinarySuffix.Input := .fork
  (binary .mul (.comp (.atom .fst) q) (.atom (.lit UniformFixedNetwork.m)))
  (.atom .snd)
def large : Code false ChildPort Node Result :=
  .comp (.importClosed setup)
    (.comp (.fork (.atom .id)
      (.comp (.importClosed seedArgs) (DFTModelSavingRecords.stream UniformBatching.width)))
      (.comp (.importClosed suffixArgs)
        (.comp (.importClosed DFTModelSavingBinarySuffix.program) (.atom .snd))))

def ordinary : Prog false Node Result := DFTModelRecursiveBinary.program
/-- Zero means the saving branch; positive means the genuine finite base. -/
def small : Prog false Node w := binary .lt bits (.atom (.lit UniformRecursiveSavingProgram.threshold))
def body : Code false ChildPort Node Result :=
  .ifz (.importClosed small) large (.importClosed ordinary)
/-- One fixed closed syntax tree; recursion is exclusively internal descend. -/
def program : Prog false Node Result :=
  .comp (.fork bits (.atom .id)) (.descend ordinary body)

attribute [local irreducible] ordinary body large DFTModelCacheRecords.seed
  DFTModelSavingRecords.stream DFTModelSavingBinarySuffix.program

theorem bits_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run bits ((k,I),v)=⟨k,3,0,True⟩ := by
  simp [bits,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem setup_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run setup ((k,I),v)=
      ⟨(k/UniformFixedNetwork.m,(k%UniformFixedNetwork.m,((k,I),v))),
        17,max UniformFixedNetwork.m (k/UniformFixedNetwork.m),True⟩ := by
  simp [setup,quotient,remainder,binary,bits,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  have hm : k%UniformFixedNetwork.m≤UniformFixedNetwork.m :=
    Nat.le_of_lt (Nat.mod_lt _ (by decide))
  omega

theorem seedArgs_value (q rest : ℕ) (nodeValue : Node.T) :
    (run seedArgs (q,(rest,nodeValue))).val=
      (rest,(DFTModelCacheRecords.recordTape
        (UniformFixedNetworkScheduleMachine.scheduleRecords q),nodeValue)) := by
  simp only [seedArgs,DFTModelRecursiveScalarCore.fork_run,
    DFTModelRecursiveScalarCore.comp_run,DFTModelSavingProgram.q,DFTModelSavingProgram.rest,node,
    DFTModelRecursiveScalarCore.atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelCacheRecords.seed_value]

theorem small_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run small ((k,I),v)=
      ⟨if k<UniformRecursiveSavingProgram.threshold then 1 else 0,
        7,UniformRecursiveSavingProgram.threshold,True⟩ := by
  simp [small,binary,bits,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  have ht:1≤UniformRecursiveSavingProgram.threshold:=by decide
  split_ifs <;> omega

/-- The executable recursion uses actual input k as bounded fuel. The fuel
charge contributes k to peak, not k work. No child handler is a program input. -/
theorem program_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run program ((k,I),v)=
      (depthRun (ordinary.run ()) body.run k ((k,I),v)).pay 7 k := by
  simp only [program,run,Code.run,bits,Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [max_zero,zero_max,true_and,and_true]
  congr 1
  omega

end
end ExactFourierCircuits.DFTModelSavingProgram
