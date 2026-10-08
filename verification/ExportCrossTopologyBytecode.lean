import UniformToeplitzCrossTopologyMachine
open ExactFourierCircuits UniformMachine Lean

def natOpName : NatOp→String
 | .add=>"add" | .sub=>"sub" | .mul=>"mul" | .div=>"div" | .mod=>"mod"
def insJson : Instruction→Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary op d l r=>.arr #[.str (natOpName op),toJson d,toJson l,toJson r]
 | .loadNat d a=>.arr #[.str "getnat",toJson d,toJson a]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .branchLT l r y n=>.arr #[.str "branch",toJson l,toJson r,toJson y,toJson n]
 | .jump j=>.arr #[.str "jump",toJson j]
 | .halt=>.arr #[.str "halt"]
 | _=>.str "UNEXPECTED INSTRUCTION"
def rowJson (r : UniformConvolutionTopologyMachine.Row) : Json := toJson [r.opcode,r.left,r.right,r.kind,r.payload]
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-topology/program.json"
 (Json.compress (.arr (UniformToeplitzCrossTopologyMachine.program.map insJson).toArray))
#eval IO.FS.writeFile "../logs/uniform-bytecode/cross-topology/record-fixtures.json"
 (Json.compress (Json.mkObj [
  ("0,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 0 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("0,1,1",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 0 1 1 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("0,1,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 0 1 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("0,0,1",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 0 0 1 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("1,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 1 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("1,2,2",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 1 2 2 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("1,1,1",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 1 1 1 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("2,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 2 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("2,4,4",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 2 4 4 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("2,3,2",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 2 3 2 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("2,2,3",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 2 2 3 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("3,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 3 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("3,8,8",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 3 8 8 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("3,7,4",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 3 7 4 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("3,4,7",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 3 4 7 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("4,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 4 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("4,16,16",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 4 16 16 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("4,15,8",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 4 15 8 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("4,8,15",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 4 8 15 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("5,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 5 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("5,32,32",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 5 32 32 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("5,31,16",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 5 31 16 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("5,16,31",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 5 16 31 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("6,0,0",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 6 0 0 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("6,64,64",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 6 64 64 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("6,63,32",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 6 63 32 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray),
  ("6,32,63",.arr ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG 6 32 63 (by decide) (by decide)).program).map (fun g=>rowJson (UniformConvolutionTopologyMachine.encode g))).toArray)]))
