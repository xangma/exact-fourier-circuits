import UniformFixedNetworkLiteralDecoderMachine
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformFixedNetworkScheduleMachine Lean

/-- Small generic templates only; the actual huge seed is verified symbolically. -/
def decoderTemplates : List (String × List Record) :=
 [("empty",[]),
  ("ragged",[⟨0,19,3,2,0,0,1,0,[1,0,1]⟩,⟨1,17,3,0,2,0,0,4,[]⟩,
     ⟨2,13,3,0,4,0,0,0,[0,2,4,6]⟩]),
  ("seedShape",[⟨6,0,3,7,8,0,3,0,[]⟩,⟨2,0,3,0,4,0,0,0,[0,2,4,6]⟩,
   ⟨0,0,3,2,0,0,2,0,[1,0,1,0,1,0]⟩,⟨1,0,3,2,4,0,0,0,[]⟩,
   ⟨1,0,3,0,6,0,0,1,[]⟩,⟨0,0,3,6,0,1,1,0,[1,1,0]⟩,
   ⟨1,0,3,6,0,0,0,3,[]⟩,⟨1,0,3,4,2,0,0,4,[]⟩,
   ⟨3,0,3,0,0,0,2,0,[2,1,0,1,6,0,1,1]⟩,
   ⟨4,0,3,0,0,0,2,0,[0,2,4,0,4,6,4,0]⟩,⟨5,0,3,7,1,0,0,0,[]⟩]),
  ("largeFields",[⟨6,31,1000000,2361183241434822606848,2361183241434822606847,0,71,4,[]⟩])]
def decoderInstructionJson : Instruction → Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary .add d l r=>.arr #[.str "add",toJson d,toJson l,toJson r]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .jump target=>.arr #[.str "jump",toJson target]
 | .halt=>.arr #[.str "halt"]
 | _=>.str "UNEXPECTED"
def decoderPrograms : Json := Json.mkObj (decoderTemplates.map (fun (name,rs)=>
 (name,.arr ((UniformFixedNetworkLiteralDecoderMachine.program rs).map decoderInstructionJson).toArray)))
def decoderSpecs : Json := .arr ((decoderTemplates.map (fun (name,rs)=>Json.mkObj
 [("name",toJson name),("data",toJson (serialize rs)),("recordLengths",toJson (rs.map (fun r=>r.data.length))),
  ("steps",toJson (3*(serialize rs).length+3*rs.length+7)),("qRegister",toJson (2599:ℕ)),
  ("baseRegister",toJson (2600:ℕ)),("scratchRegisters",toJson ([2601,2602,2603,2604,2700,2701]:List ℕ))])).toArray)
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-literal-decoder/programs.json" (Json.compress decoderPrograms)
#eval IO.FS.writeFile "../logs/uniform-bytecode/fixed-network-literal-decoder/spec.json" (Json.compress decoderSpecs)
example : (UniformFixedNetworkLiteralDecoderMachine.program []).length=7 := rfl
example : (UniformFixedNetworkLiteralDecoderMachine.program [⟨0,0,2,0,0,0,1,0,[1,0]⟩]).length=40 := rfl
