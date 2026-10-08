import UniformFixedNetworkOpcodeMachine
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformFixedNetworkScheduleMachine UniformFixedNetworkOpcodeMachine Lean
/-- Small diagnostics; actual seed remains symbolic. -/
def opcodeRows : List Record :=
 [⟨6,0,3,7,8,0,3,0,[]⟩,⟨2,0,3,0,4,0,0,0,[0,2,4,6]⟩,
  ⟨0,0,3,2,0,0,2,0,[1,0,1,0,1,0]⟩,⟨1,0,3,2,4,0,0,0,[]⟩,
  ⟨1,0,3,0,6,0,0,1,[]⟩,⟨1,0,3,0,6,0,0,2,[]⟩,
  ⟨0,0,3,6,0,1,1,0,[1,1,0]⟩,⟨1,0,3,6,0,0,0,3,[]⟩,
  ⟨1,0,3,4,2,0,0,4,[]⟩,⟨3,0,3,0,0,0,2,0,[2,1,0,1,6,0,1,1]⟩,
  ⟨4,0,3,0,0,0,2,0,[0,2,4,0,4,6,4,0]⟩,⟨5,0,3,7,1,0,0,0,[]⟩]
def emptyBodyRows : List Record :=
 [⟨0,9,0,2,0,1,5,0,[]⟩,⟨0,8,7,0,0,0,0,0,[]⟩,
  ⟨2,7,2,0,0,0,0,0,[]⟩,⟨3,6,0,0,0,0,2,0,[1,3]⟩,
  ⟨4,5,0,0,0,0,0,0,[]⟩,⟨5,4,0,3,0,0,0,0,[]⟩,⟨6,3,0,2,4,0,2,0,[]⟩]
def opcodeTemplates : List (String×List Record) :=
 [("empty",[]),("allOpcodes",opcodeRows),("emptyBodies",emptyBodyRows),
  ("largeFields",[⟨6,0,1000000,2361183241434822606848,2361183241434822606847,0,71,4,[]⟩])]
def opcodeInstructionJson : Instruction→Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary .add d l r=>.arr #[.str "add",toJson d,toJson l,toJson r]
 | .natBinary .mul d l r=>.arr #[.str "mul",toJson d,toJson l,toJson r]
 | .natBinary .div d l r=>.arr #[.str "div",toJson d,toJson l,toJson r]
 | .loadNat d a=>.arr #[.str "getnat",toJson d,toJson a]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .branchLT l r y no=>.arr #[.str "branch",toJson l,toJson r,toJson y,toJson no]
 | .jump target=>.arr #[.str "jump",toJson target]
 | .halt=>.arr #[.str "halt"]
 | _=>.str "UNEXPECTED"
def opcodePrograms : Json :=
 let ps : List (String×Program):=[("head",headProgram),("loop",loopProgram)]++
   opcodeTemplates.map (fun pair=>(pair.1,callerProgram pair.2))
 Json.mkObj (ps.map (fun pair=>(pair.1,.arr (pair.2.map opcodeInstructionJson).toArray)))
def opcodeRecordJson (r:Record) : Json := Json.mkObj
 [("header",toJson r.header),("body",toJson r.directions),("bodyLength",toJson (bodyLength r)),("headSteps",toJson (headCost r))]
def opcodeSpecs : Json := .arr (opcodeTemplates.map (fun (name,rs)=>Json.mkObj
 [("name",toJson name),("records",.arr (rs.map opcodeRecordJson).toArray),
  ("data",toJson (serialize rs)),("recordLengths",toJson (rs.map (fun r=>r.data.length))),
  ("steps",toJson (callerEntry rs+4+loopCost rs+1)),("printerSteps",toJson (callerEntry rs)),
  ("loopBase",toJson (callerLoop rs)),("codeSize",toJson (callerProgram rs).length)])).toArray
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-opcode/programs.json" (Json.compress opcodePrograms)
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-opcode/spec.json" (Json.compress opcodeSpecs)
example : ∀r∈opcodeRows,WellFormed r := by norm_num [opcodeRows,WellFormed,bodyLength]
example : ∀r∈emptyBodyRows,WellFormed r := by norm_num [emptyBodyRows,WellFormed,bodyLength]
example : headProgram.length=52 := rfl
example : loopProgram.length=56 := rfl
example : (callerProgram []).length=68 := rfl
example : callerEntry []+4+loopCost []+1=14 := rfl
