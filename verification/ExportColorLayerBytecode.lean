import UniformColorLayerTableMachine
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


def row (i : ℕ) : UniformInPlaceMachine.Row := ⟨7*i+1,7*i+2,700+i⟩
def color (family i : ℕ) := if family=0 then i%3 else if family=1 then 2 else (i*7+3)%11
#eval IO.FS.writeFile "../logs/uniform-bytecode/color-layer/program.json"
  ("["++String.intercalate "," (UniformColorLayerTableMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/color-layer/specs.json"
  ("["++String.intercalate "," ((List.range 21).flatMap (fun M=>
    (List.range 3).flatMap (fun family=>
      (List.range 5).map (fun k=>
        let values:=(List.range M).map (color family)
        let rows:=(List.range M).map (fun i=>[ (row i).dst,(row i).src,(row i).coefficient ])
        let ords:=UniformColorLayerTableMachine.selected M k (color family)
        "["++toString M++","++toString family++","++toString k++","++toString values++","++
          toString rows++","++toString ords++","++toString (ords.map (fun i=>[(row i).dst,(row i).src,(row i).coefficient]))++"]"))))++"]")
