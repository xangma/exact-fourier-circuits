import UniformConjugateLocalPreparation
open ExactFourierCircuits UniformMachine UniformConjugateLocalPreparation
open UniformInitialPreparation (ell len copyBase)

def natCode : NatOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3 | .mod=>4

def fieldCode : FieldOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3

def encodeInstruction : Instruction→String
  | .natLiteral d v=>s!"[0,{d},{v}]"
  | .natBinary op d a b=>s!"[1,{natCode op},{d},{a},{b}]"
  | .loadNat d a=>s!"[2,{d},{a}]"
  | .storeNat a r=>s!"[3,{a},{r}]"
  | .branchLT a b y n=>s!"[4,{a},{b},{y},{n}]"
  | .jump t=>s!"[5,{t}]"
  | .halt=>"[6]"
  | .loadScalar d a=>s!"[7,{d},{a}]"
  | .storeScalar a r=>s!"[8,{a},{r}]"
  | .scalarLiteral d v=>s!"[9,{d},{v.num},{v.den}]"
  | .fieldBinary op d a b=>s!"[10,{fieldCode op},{d},{a},{b}]"
  | _=>"[99]"

#eval IO.FS.writeFile "../logs/uniform-bytecode/conjugate-local/program.json" ("["++String.intercalate "," (program.map encodeInstruction)++"]")
#eval IO.println s!"[{UniformReciprocalMachine.completeRuntime 1+32},{UniformReciprocalMachine.completeRuntime 2+32},{UniformReciprocalMachine.completeRuntime 4+32}]"
#eval IO.println s!"[{ell 1},{len 1},{copyBase 1},{UniformMasterRootMachine.order 1},{UniformWorkingLength.nextPrime 1}]"
#eval IO.println s!"[{ell 5},{len 5},{copyBase 5},{UniformMasterRootMachine.order 5},{UniformWorkingLength.nextPrime 5}]"
