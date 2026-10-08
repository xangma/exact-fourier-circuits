import UniformSectorPackingMachine

open ExactFourierCircuits UniformMachine UniformSectorPackingMachine
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
def listNatJson (xs:List ℕ):String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def axes0_0:List UniformSectorPacking.Axis := []
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes0_0).prod => (unpackingPermutation axes0_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes0_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes0_1:List UniformSectorPacking.Axis := []
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes0_1).prod => (unpackingPermutation axes0_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes0_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes1_0:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes1_0).prod => (unpackingPermutation axes1_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes1_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes1_1:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) ⟨1,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes1_1).prod => (unpackingPermutation axes1_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes1_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes2_0:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes2_0).prod => (unpackingPermutation axes2_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes2_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes2_1:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes2_1).prod => (unpackingPermutation axes2_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes2_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes3_0:List UniformSectorPacking.Axis := [(⟨[2, 1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes3_0).prod => (unpackingPermutation axes3_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes3_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes3_1:List UniformSectorPacking.Axis := [(⟨[2, 1, 1],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes3_1).prod => (unpackingPermutation axes3_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes3_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes4_0:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes4_0).prod => (unpackingPermutation axes4_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes4_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes4_1:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes4_1).prod => (unpackingPermutation axes4_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes4_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes5_0:List UniformSectorPacking.Axis := [(⟨[1, 1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes5_0).prod => (unpackingPermutation axes5_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes5_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes5_1:List UniformSectorPacking.Axis := [(⟨[1, 1, 1],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes5_1).prod => (unpackingPermutation axes5_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes5_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes6_0:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes6_0).prod => (unpackingPermutation axes6_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes6_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes6_1:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 1, 1],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes6_1).prod => (unpackingPermutation axes6_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes6_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes7_0:List UniformSectorPacking.Axis := [(⟨[2, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes7_0).prod => (unpackingPermutation axes7_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes7_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes7_1:List UniformSectorPacking.Axis := [(⟨[2, 1],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes7_1).prod => (unpackingPermutation axes7_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes7_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes8_0:List UniformSectorPacking.Axis := [(⟨[1, 2, 2, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes8_0).prod => (unpackingPermutation axes8_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes8_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes8_1:List UniformSectorPacking.Axis := [(⟨[1, 2, 2, 1],by decide,by decide,Equiv.swap (0:Fin 6) ⟨5,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 1, 2],by decide,by decide,Equiv.swap (0:Fin 5) ⟨4,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes8_1).prod => (unpackingPermutation axes8_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes8_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes9_0:List UniformSectorPacking.Axis := [(⟨[2, 2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes9_0).prod => (unpackingPermutation axes9_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes9_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes9_1:List UniformSectorPacking.Axis := [(⟨[2, 2, 2],by decide,by decide,Equiv.swap (0:Fin 6) ⟨5,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes9_1).prod => (unpackingPermutation axes9_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes9_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes10_0:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes10_0).prod => (unpackingPermutation axes10_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes10_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes10_1:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) ⟨1,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) ⟨1,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) ⟨1,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) ⟨1,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes10_1).prod => (unpackingPermutation axes10_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes10_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes11_0:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 1],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes11_0).prod => (unpackingPermutation axes11_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes11_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes11_1:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 1],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,Equiv.swap (0:Fin 3) ⟨2,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes11_1).prod => (unpackingPermutation axes11_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes11_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes12_0:List UniformSectorPacking.Axis := [(⟨[2, 2, 2, 2, 2, 2, 2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes12_0).prod => (unpackingPermutation axes12_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes12_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes12_1:List UniformSectorPacking.Axis := [(⟨[2, 2, 2, 2, 2, 2, 2, 2],by decide,by decide,Equiv.swap (0:Fin 16) ⟨15,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes12_1).prod => (unpackingPermutation axes12_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes12_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes13_0:List UniformSectorPacking.Axis := [(⟨[1, 2, 1, 2, 1, 2, 1, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes13_0).prod => (unpackingPermutation axes13_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes13_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes13_1:List UniformSectorPacking.Axis := [(⟨[1, 2, 1, 2, 1, 2, 1, 2],by decide,by decide,Equiv.swap (0:Fin 12) ⟨11,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes13_1).prod => (unpackingPermutation axes13_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes13_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes14_0:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.refl _⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes14_0).prod => (unpackingPermutation axes14_0 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes14_0).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
def axes14_1:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,Equiv.swap (0:Fin 4) ⟨3,by decide⟩⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes14_1).prod => (unpackingPermutation axes14_1 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes14_1).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes0_2:List UniformSectorPacking.Axis := []
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes0_2).prod => (unpackingPermutation axes0_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes0_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes1_2:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) (1:Fin 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes1_2).prod => (unpackingPermutation axes1_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes1_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes2_2:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes2_2).prod => (unpackingPermutation axes2_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes2_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes3_2:List UniformSectorPacking.Axis := [(⟨[2, 1, 1],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes3_2).prod => (unpackingPermutation axes3_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes3_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes4_2:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes4_2).prod => (unpackingPermutation axes4_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes4_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes5_2:List UniformSectorPacking.Axis := [(⟨[1, 1, 1],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes5_2).prod => (unpackingPermutation axes5_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes5_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes6_2:List UniformSectorPacking.Axis := [(⟨[1, 2],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 1, 1],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes6_2).prod => (unpackingPermutation axes6_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes6_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes7_2:List UniformSectorPacking.Axis := [(⟨[2, 1],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes7_2).prod => (unpackingPermutation axes7_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes7_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes8_2:List UniformSectorPacking.Axis := [(⟨[1, 2, 2, 1],by decide,by decide,(Equiv.swap (0:Fin 6) 1).trans (Equiv.swap (1:Fin 6) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 1, 2],by decide,by decide,(Equiv.swap (0:Fin 5) 1).trans (Equiv.swap (1:Fin 5) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes8_2).prod => (unpackingPermutation axes8_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes8_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes9_2:List UniformSectorPacking.Axis := [(⟨[2, 2, 2],by decide,by decide,(Equiv.swap (0:Fin 6) 1).trans (Equiv.swap (1:Fin 6) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes9_2).prod => (unpackingPermutation axes9_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes9_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes10_2:List UniformSectorPacking.Axis := [(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) (1:Fin 2)⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) (1:Fin 2)⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) (1:Fin 2)⟩:UniformSectorPacking.Axis),(⟨[1, 1],by decide,by decide,Equiv.swap (0:Fin 2) (1:Fin 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes10_2).prod => (unpackingPermutation axes10_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes10_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes11_2:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 1],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis),(⟨[1, 2],by decide,by decide,(Equiv.swap (0:Fin 3) 1).trans (Equiv.swap (1:Fin 3) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes11_2).prod => (unpackingPermutation axes11_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes11_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes12_2:List UniformSectorPacking.Axis := [(⟨[2, 2, 2, 2, 2, 2, 2, 2],by decide,by decide,(Equiv.swap (0:Fin 16) 1).trans (Equiv.swap (1:Fin 16) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes12_2).prod => (unpackingPermutation axes12_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes12_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes13_2:List UniformSectorPacking.Axis := [(⟨[1, 2, 1, 2, 1, 2, 1, 2],by decide,by decide,(Equiv.swap (0:Fin 12) 1).trans (Equiv.swap (1:Fin 12) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes13_2).prod => (unpackingPermutation axes13_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes13_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")

def axes14_2:List UniformSectorPacking.Axis := [(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis),(⟨[2, 2],by decide,by decide,(Equiv.swap (0:Fin 4) 1).trans (Equiv.swap (1:Fin 4) 2)⟩:UniformSectorPacking.Axis)]
#eval IO.println (listNatJson (List.ofFn (fun i:Fin (radices axes14_2).prod => (unpackingPermutation axes14_2 i).val)))
#eval IO.println ("[" ++ String.intercalate "," ((axes14_2).map (fun a=>listNatJson (List.ofFn (fun i:Fin a.widths.sum=>(a.originalPermutation i).val)))) ++ "]")
