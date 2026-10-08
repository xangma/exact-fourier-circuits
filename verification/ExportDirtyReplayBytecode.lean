import UniformDirtyReplayMachine
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




namespace Fresh
structure Z where
  re : ℚ
  im : ℚ
  dependent : Bool
instance : Inhabited Z := ⟨⟨0,0,false⟩⟩
def coefficient (K family q : ℕ) : Z :=
  if q=7 then ⟨1,0,false⟩ else if q=8 then ⟨-1,0,false⟩
  else if q=9 then ⟨(1:ℚ)/(2^K),0,false⟩ else
  if q=0 then ⟨0,0,false⟩ else ⟨((q+family:ℕ):ℚ)/7-3/7,((q+2*family)%5:ℚ)/11-2/11,false⟩
def initial (family j : ℕ) : Z :=
  ⟨((j*j+family)%13:ℚ)/3-2,((j+2*family)%11:ℚ)/5-1,decide (j%3=family%3)⟩
def row (family i : ℕ) : UniformInPlaceMachine.Row :=
  let dst:=(7*i+family)%9
  ⟨dst,(dst+1+(i%7))%9,(i+family)%10⟩
def act (K family : ℕ) (inverse : Bool) (v : Array Z) (r : UniformInPlaceMachine.Row) : Array Z :=
  let a:=v[r.dst]!;let b:=v[r.src]!;let c:=coefficient K family r.coefficient
  let sign:ℚ:=if inverse then -1 else 1
  v.set! r.dst ⟨a.re+sign*(c.re*b.re-c.im*b.im),a.im+sign*(c.re*b.im+c.im*b.re),a.dependent || b.dependent⟩
def encode (z : Z) : String :=
  s!"[{z.re.num},{z.re.den},{z.im.num},{z.im.den},{z.dependent}]"
def physical (C P : ℕ) (r : UniformInPlaceMachine.Row) : UniformInPlaceMachine.Row :=
  ⟨r.dst,r.src,if r.coefficient<7 then C+r.coefficient else P+(r.coefficient-7)⟩
#eval IO.FS.writeFile "../logs/uniform-bytecode/dirty-replay/program.json"
 ("["++String.intercalate "," (UniformDirtyReplayMachine.program.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/dirty-replay/specs.json"
 ("["++String.intercalate "," ((List.range 4).flatMap (fun K=>(List.range 33).flatMap (fun M=>(List.range 3).map (fun family=>
  let rows:=(List.range M).map (row family)
  let init:=((List.range 9).map (initial family)).toArray
  let forward:=rows.foldl (act K family false) init
  let final:=rows.reverse.foldl (act K family true) forward
  let inv:=UniformDirtyReplayMachine.inverseRows 100 200 300 (rows.map (physical 100 300))
  "["++toString K++","++toString M++","++toString family++","++toString (rows.map (fun r=>[r.dst,r.src,r.coefficient]))++","++
  "["++String.intercalate "," (init.toList.map encode)++"],"++
  "["++String.intercalate "," ((List.range 10).map (encode ∘ coefficient K family))++"],"++
  "["++String.intercalate "," (final.toList.map encode)++"],"++toString (inv.map (fun r=>[r.dst,r.src,r.coefficient]))++"]"))))++"]")
end Fresh
