import UniformMultiAxisSectorMetadataPreparation
import Lean
open ExactFourierCircuits UniformMachine Lean
def natOpName : NatOp→String
 | .add=>"add" | .sub=>"sub" | .mul=>"mul" | .div=>"div" | .mod=>"mod"
def fieldOpName : FieldOp→String
 | .add=>"fadd" | .sub=>"fsub" | .mul=>"fmul" | .div=>"fdiv"
def insJson : Instruction→Json
 | .natLiteral d v=>.arr #[.str "lit",toJson d,toJson v]
 | .natBinary op d l r=>.arr #[.str (natOpName op),toJson d,toJson l,toJson r]
 | .loadNat d a=>.arr #[.str "getnat",toJson d,toJson a]
 | .storeNat a r=>.arr #[.str "putnat",toJson a,toJson r]
 | .scalarLiteral d q=>.arr #[.str "rat",toJson d,toJson q.num,toJson q.den]
 | .fieldBinary op d l r=>.arr #[.str (fieldOpName op),toJson d,toJson l,toJson r]
 | .loadScalar d a=>.arr #[.str "getscalar",toJson d,toJson a]
 | .storeScalar a r=>.arr #[.str "putscalar",toJson a,toJson r]
 | .branchLT l r y n=>.arr #[.str "branch",toJson l,toJson r,toJson y,toJson n]
 | .jump j=>.arr #[.str "jump",toJson j]
 | .halt=>.arr #[.str "halt"]
 | .length d=>.arr #[.str "length",toJson d]
 | .root d r=>.arr #[.str "root",toJson d,toJson r]
 | .input d j=>.arr #[.str "input",toJson d,toJson j]
 | .output j r=>.arr #[.str "output",toJson j,toJson r]



def axes0 : List UniformSectorPacking.Axis := []
def axes1 : List UniformSectorPacking.Axis := [(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes2 : List UniformSectorPacking.Axis := [(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes3 : List UniformSectorPacking.Axis := [(⟨[2,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes4 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes5 : List UniformSectorPacking.Axis := [(⟨[1,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes6 : List UniformSectorPacking.Axis := [(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes7 : List UniformSectorPacking.Axis := [(⟨[2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes8 : List UniformSectorPacking.Axis := [(⟨[1,2,2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes9 : List UniformSectorPacking.Axis := [(⟨[2,2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes10 : List UniformSectorPacking.Axis := [(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes11 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,1],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes12 : List UniformSectorPacking.Axis := [(⟨[2,2,2,2,2,2,2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes13 : List UniformSectorPacking.Axis := [(⟨[1,2,1,2,1,2,1,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def axes14 : List UniformSectorPacking.Axis := [(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis),(⟨[2,2],by decide,by decide,Equiv.refl _⟩ : UniformSectorPacking.Axis)]
def stateJson (s:UniformSectorPacking.BlockState):Json:=toJson [s.start,s.width,s.pairs]
def model (as:List UniformSectorPacking.Axis):Json:=Json.mkObj [
 ("widths",toJson (as.map UniformSectorPacking.Axis.widths)),
 ("expected",.arr ((UniformSectorPacking.sectorStates as).map stateJson).toArray)]
#eval IO.FS.createDirAll "../logs/uniform-bytecode/multi-axis-sector-metadata"
#eval IO.FS.writeFile "../logs/uniform-bytecode/multi-axis-sector-metadata/programs.json"
 (Json.compress (Json.mkObj [
 ("projection",.arr (UniformMultiAxisSectorMetadataPreparation.projection.map insJson).toArray),
 ("metadata",.arr (UniformMultiAxisSectorMetadataPreparation.program.map insJson).toArray)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/multi-axis-sector-metadata/spec.json"
 (Json.compress (Json.mkObj [("models",.arr #[model axes1,model axes2,model axes3,model axes4,
 model axes5,model axes6,model axes7,model axes8,model axes9,model axes10,model axes11,model axes12,
 model axes13,model axes14]),("emptySector",model axes0)]))
example:UniformMultiAxisSectorMetadataPreparation.projection.length=23:=
 UniformMultiAxisSectorMetadataPreparation.projection_length
example:UniformMultiAxisSectorMetadataPreparation.program.length=124:=
 UniformMultiAxisSectorMetadataPreparation.program_length
