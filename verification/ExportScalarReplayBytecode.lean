import UniformScalarReplayMachine
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



def sampleRow (family i : ℕ) : UniformInPlaceMachine.Row :=
  ⟨(7*i+family)%9,(5*i+family+1)%9,(i+family)%7⟩
structure Z where
  re : ℚ
  im : ℚ
  dependent : Bool

def initialZ (family j : ℕ) : Z :=
  ⟨((j*j+family)%13:ℤ)/3-2,((j+2*family)%11:ℤ)/5-1,decide (j%3=family%3)⟩
def coeffZ (family j : ℕ) : Z :=
  if j=0 then ⟨0,0,false⟩ else ⟨(j:ℚ)/7-3/7,((j+family)%5:ℚ)/11-2/11,false⟩
instance : Inhabited Z := ⟨⟨0,0,false⟩⟩
def stepZ (family : ℕ) (v : Array Z) (r : UniformInPlaceMachine.Row) : Array Z :=
  let a:=v[r.dst]!;let b:=v[r.src]!;let c:=coeffZ family r.coefficient
  v.set! r.dst ⟨a.re+c.re*b.re-c.im*b.im,a.im+c.re*b.im+c.im*b.re,a.dependent || b.dependent⟩

def encodeZ (z : Z) : String :=
  s!"[{z.re.num},{z.re.den},{z.im.num},{z.im.den},{z.dependent}]"
#eval IO.FS.writeFile "../logs/uniform-bytecode/scalar-replay/program.json"
  ("["++String.intercalate "," (UniformScalarReplayMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/scalar-replay/specs.json"
  ("["++String.intercalate "," ((List.range 33).flatMap (fun M=>
    (List.range 7).map (fun family=>
      let rows:=(List.range M).map (sampleRow family)
      let init:=((List.range 9).map (initialZ family)).toArray
      let result:=rows.foldl (stepZ family) init
      "["++toString M++","++toString family++","++toString (rows.map (fun r=>[r.dst,r.src,r.coefficient]))++","++
        "["++String.intercalate "," (init.toList.map encodeZ)++"],"++
        "["++String.intercalate "," ((List.range 7).map (encodeZ ∘ coeffZ family))++"],"++
        "["++String.intercalate "," (result.toList.map encodeZ)++"]]")))++"]")
