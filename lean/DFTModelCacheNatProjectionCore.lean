import DFTModelCacheNatDispatchSource
import UniformMachineRuns

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatProjection
open UniformMachine
noncomputable section

/-- Static exclusion: input length must already be in ordinary Nat metadata. -/
def NoLength (p : Program) : Prop := ∀dst,Instruction.length dst∉p

/-- Scalar instructions retain one charged slot but have no Nat effect. The
length case is unreachable under `NoLength`, not a supported translation. -/
def instruction (pc : ℕ) : Instruction→DFTModelCacheNatControl.Instruction
  | .natLiteral d v=>.literal d v
  | .natBinary op d l r=>.binary op d l r
  | .loadNat d a=>.load d a
  | .storeNat a s=>.store a s
  | .branchLT l r y n=>.branch l r y n
  | .jump t=>.jump t
  | .halt=>.halt
  | .length _ | .scalarLiteral _ _ | .fieldBinary _ _ _ _ | .input _ _ |
      .root _ _ | .loadScalar _ _ | .storeScalar _ _ | .output _ _=>.jump (pc+1)

/-- A fixed mixed program is compiled once; no runtime code or output oracle. -/
def code (p : Program) : List DFTModelCacheNatControl.Instruction := p.mapIdx instruction

def project (p : Program) : Program := DFTModelCacheNatDispatch.native (code p)

/-- Keep the original scalar state while following the current Nat state. -/
def state (base current : State) : State :=
  {base with pc:=current.pc,natReg:=current.natReg,natHeap:=current.natHeap}

@[simp] theorem code_length (p : Program) : (code p).length=p.length := by
  simp only [code,List.length_mapIdx]

@[simp] theorem project_length (p : Program) : (project p).length=p.length := by
  simp only [project,DFTModelCacheNatDispatch.native,List.length_map,code_length]

theorem code_at (p : Program) (pc : ℕ) (i : Instruction)
    (selected : p[pc]?=some i) : (code p)[pc]?=some (instruction pc i) := by
  simp only [code,List.getElem?_mapIdx,selected,Option.map_some]

theorem project_at (p : Program) (pc : ℕ) (i : Instruction)
    (selected : p[pc]?=some i) : (project p)[pc]?=some (instruction pc i).native := by
  simp only [project,DFTModelCacheNatDispatch.native,List.getElem?_map,code_at p pc i selected,Option.map_some]

theorem no_length_at {p : Program} (h : NoLength p) (pc dst : ℕ) :
    p[pc]?≠some (.length dst) := by
  intro selected
  exact h dst (List.mem_of_getElem? selected)

@[simp] theorem state_self (s : State) : state s s=s := by cases s;rfl

@[simp] theorem state_state (base a b : State) : state base (state a b)=state base b := rfl

theorem state_wordBound {B : ℕ} {base current : State}
    (initial : WordBound B base) (now : WordBound B current) : WordBound B (state base current) :=
  ⟨now.1,now.2.1,now.2.2.1,initial.2.2.2.1,initial.2.2.2.2.1,initial.2.2.2.2.2⟩

/-- Explicit final equalities: no scalar, output or root computation is claimed. -/
theorem state_fields (base current : State) :
    (state base current).pc=current.pc ∧ (state base current).natReg=current.natReg ∧
    (state base current).natHeap=current.natHeap ∧
    (state base current).scalarReg=base.scalarReg ∧
    (state base current).scalarHeap=base.scalarHeap ∧
    (state base current).outputs=base.outputs ∧
    (state base current).rootOrders=base.rootOrders := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end ExactFourierCircuits.DFTModelCacheNatProjection
