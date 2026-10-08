import UniformInverseShearTableMachine
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



def address (C P m family i : ℕ) :=
  if family=0 then C+i%m else if family=1 then P+i%3 else
  match i%4 with | 0=>C+i%m | 1=>P | 2=>P+1 | _=>P+2

def row (C P m family i : ℕ) : UniformInPlaceMachine.Row :=
  ⟨7*i+1,7*i+2,address C P m family i⟩

#eval IO.FS.writeFile "../logs/uniform-bytecode/inverse-shear/program.json"
  ("["++String.intercalate "," (UniformInverseShearTableMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/inverse-shear/specs.json"
  ("["++String.intercalate "," ((List.range 25).flatMap (fun M=>
    (List.range 7).flatMap (fun K=>
      (List.range 3).map (fun family=>
        let m:=7*2^K
        let C:=29
        let T:=C+m+11
        let P:=T+m+17
        let rows:=(List.range M).map (row C P m family)
        let result:=UniformInverseShearTableMachine.inverseRows C T P rows
        let encoded:=rows.map (fun r=>[r.dst,r.src,r.coefficient])
        let out:=result.map (fun r=>[r.dst,r.src,r.coefficient])
        "["++toString M++","++toString K++","++toString family++","++toString C++","++
          toString T++","++toString P++","++toString encoded++","++toString out++"]"))))++"]")
