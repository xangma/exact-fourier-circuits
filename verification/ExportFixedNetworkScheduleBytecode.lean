import UniformFixedNetworkScheduleMachine
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformFixedNetworkScheduleMachine Lean

/-- Small printer diagnostics, not a materialization of the astronomical seed.
The universal fixed_execution theorem supplies the actual fixed-seed result. -/
def fixtureRecords (q : ℕ) : List Record :=
 [⟨6,q,3,7,8,0,3,0,[]⟩,
  ⟨2,q,3,0,4,0,0,0,[0,2,4,6]⟩,
  ⟨0,q,3,2,0,0,2,0,[1,0,1,0,1,0]⟩,
  ⟨1,q,3,2,4,0,0,0,[]⟩,
  ⟨1,q,3,0,6,0,0,1,[]⟩,
  ⟨0,q,3,6,0,1,1,0,[1,1,0]⟩,
  ⟨1,q,3,6,0,0,0,3,[]⟩,
  ⟨1,q,3,4,2,0,0,4,[]⟩,
  ⟨3,q,3,0,0,0,2,0,[2,1,0,1,6,0,1,1]⟩,
  ⟨4,q,3,0,0,0,2,0,[0,2,4,0,4,6,4,0]⟩,
  ⟨5,q,3,7,1,0,0,0,[]⟩]

def fixtures : List (String × List ℕ) :=
 [("empty",[]),("q0",serialize (fixtureRecords 0)),("q1",serialize (fixtureRecords 1)),
  ("q3",serialize (fixtureRecords 3)),("integerBounds",[0,1,4,71,1000000,2361183241434822606848])]
def instructionJson : Instruction → Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary .add d l r=>.arr #[.str "add",toJson d,toJson l,toJson r]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .halt=>.arr #[.str "halt"]
 | _=>.str "UNEXPECTED"

def fixturePrograms : Json := Json.mkObj (fixtures.map (fun (name,data)=>
 (name,.arr ((program data).map instructionJson).toArray)))
def fixtureSpecs : Json := .arr ((fixtures.map (fun (name,data)=>Json.mkObj
 [("name",toJson name),("data",toJson data),("steps",toJson (3*data.length+4)),
  ("inputBaseRegister",toJson (2600:ℕ)),("scratchRegisters",toJson ([2601,2602,2603,2604]:List ℕ)),
  ("scope",toJson "generic literal printer only; no full fixed-seed materialization/child execution")])).toArray)
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-schedule/programs.json" (Json.compress fixturePrograms)
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-schedule/spec.json" (Json.compress fixtureSpecs)
example : (serialize (fixtureRecords 0)).length=(serialize (fixtureRecords 3)).length := by decide
example : program []=[.natLiteral 2603 1,.natLiteral 2604 0,.natBinary .add 2601 2600 2604,.halt] := rfl
example : (program [1,0,4]).length=13 := rfl
example : ((fixtureRecords 3)[2]'(by decide)).data=[0,3,3,2,0,0,2,0,1,0,1,0,1,0] := rfl
