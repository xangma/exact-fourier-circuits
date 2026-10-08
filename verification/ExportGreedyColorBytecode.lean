import UniformGreedyColorMachine
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


def edge (a b : ℕ) : UniformColoring.Edge :=
  if h:a=b then ⟨a,b+1,by omega⟩ else ⟨a,b,h⟩

def fixtureEdge (family i : ℕ) : UniformColoring.Edge :=
  match family with
  | 0=>edge 1 2
  | 1=>edge i (i+1)
  | 2=>edge 0 (i+1)
  | 3=>if i%2=0 then edge i (i+1) else edge (i+1) i
  | 4=>edge ((7*i*i+i+3)%13) ((10*i+7)%13)
  | _=>edge ((i*i+3*i+1)%11) ((3*i*i+7)%11)

#eval IO.FS.writeFile "../logs/uniform-bytecode/greedy-color/program.json"
  ("["++String.intercalate "," (UniformGreedyColorMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/greedy-color/specs.json"
  ("["++String.intercalate "," ((List.range 7).flatMap (fun M=>
    (List.range 6).map (fun f=>
      let E:=fun i:Fin M=>fixtureEdge f i.val
      let endpoints:=(List.finRange M).map (fun i=>"["++toString (E i).left++","++toString (E i).right++"]")
      let colors:=(List.finRange M).map (fun i=>UniformColoring.greedy E 11 M i.val)
      "["++toString M++","++toString f++",["++String.intercalate "," endpoints++"],"++toString colors++"]")))++"]")
