import UniformSectorMetadataMachine
open ExactFourierCircuits UniformMachine UniformSectorMetadataMachine

def natOpName : NatOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
def fieldOpName : FieldOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
def encode : Instruction → String
  | .natLiteral d v => s!"[\"natLiteral\",{d},{v}]"
  | .natBinary op d l r => s!"[\"natBinary\",\"{natOpName op}\",{d},{l},{r}]"
  | .scalarLiteral d q => s!"[\"scalarLiteral\",{d},{q.num},{q.den}]"
  | .fieldBinary op d l r => s!"[\"fieldBinary\",\"{fieldOpName op}\",{d},{l},{r}]"
  | .loadNat d a => s!"[\"loadNat\",{d},{a}]"
  | .storeNat a r => s!"[\"storeNat\",{a},{r}]"
  | .loadScalar d a => s!"[\"loadScalar\",{d},{a}]"
  | .storeScalar a r => s!"[\"storeScalar\",{a},{r}]"
  | .branchLT l r y n => s!"[\"branchLT\",{l},{r},{y},{n}]"
  | .jump d => s!"[\"jump\",{d}]"
  | .halt => "[\"halt\"]"
  | _ => "[\"unsupported\"]"
def codeJson (p : Program) : String := s!"[{String.intercalate "," (p.map encode)}]"
#eval IO.println (codeJson program)

open UniformSectorPacking
def blockJson (s : BlockState) : String := s!"[{s.start},{s.width},{s.pairs}]"
def axes0 : List UniformSectorPacking.Axis := []
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes0).map blockJson) ++ "]")
def axes1 : List UniformSectorPacking.Axis := [(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes1).map blockJson) ++ "]")
def axes2 : List UniformSectorPacking.Axis := [(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes2).map blockJson) ++ "]")
def axes3 : List UniformSectorPacking.Axis := [(⟨[2,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes3).map blockJson) ++ "]")
def axes4 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes4).map blockJson) ++ "]")
def axes5 : List UniformSectorPacking.Axis := [(⟨[1,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes5).map blockJson) ++ "]")
def axes6 : List UniformSectorPacking.Axis := [(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes6).map blockJson) ++ "]")
def axes7 : List UniformSectorPacking.Axis := [(⟨[2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes7).map blockJson) ++ "]")
def axes8 : List UniformSectorPacking.Axis := [(⟨[1,2,2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes8).map blockJson) ++ "]")
def axes9 : List UniformSectorPacking.Axis := [(⟨[2,2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes9).map blockJson) ++ "]")
def axes10 : List UniformSectorPacking.Axis := [(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes10).map blockJson) ++ "]")
def axes11 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes11).map blockJson) ++ "]")
def axes12 : List UniformSectorPacking.Axis := [(⟨[2,2,2,2,2,2,2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes12).map blockJson) ++ "]")
def axes13 : List UniformSectorPacking.Axis := [(⟨[1,2,1,2,1,2,1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes13).map blockJson) ++ "]")
def axes14 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
#eval IO.println ("[" ++ String.intercalate "," ((sectorStates axes14).map blockJson) ++ "]")
