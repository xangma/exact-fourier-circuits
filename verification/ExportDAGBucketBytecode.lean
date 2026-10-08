import UniformDAGBucketMachine
open ExactFourierCircuits UniformMachine

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
  | .length d=>s!"[11,{d}]"
  | .root d q=>s!"[12,{d},{q}]"
  | .input d j=>s!"[13,{d},{j}]"
  | .output j s=>s!"[14,{j},{s}]"

#eval IO.FS.writeFile "../logs/uniform-bytecode/dag-bucket/program.json"
  ("["++String.intercalate "," (UniformDAGBucketMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/dag-bucket/orders.json"
  ("["++String.intercalate "," ((List.range 17).flatMap (fun G=>
    (List.range 6).map (fun seed=>
      let depth:=fun i=>(i*i+seed*i+3*seed)%(G+3)
      let values:=UniformDAGBucketMachine.order G depth
      let offsets:=(List.range (G+2)).map (fun d=>UniformDAGBucketMachine.offset G d depth)
      "["++toString G++","++toString seed++","++toString values++","++toString offsets++"]")))++"]")
