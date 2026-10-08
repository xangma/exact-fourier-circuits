import UniformZeroFreePairShearMachine
import Lean
set_option autoImplicit false
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


#eval IO.FS.createDirAll "../logs/uniform-bytecode/zero-free-pair-shear"
#eval IO.FS.writeFile "../logs/uniform-bytecode/zero-free-pair-shear/programs.json" (Json.compress (Json.mkObj [
 ("joined",.arr (UniformZeroFreePairShearMachine.program.map insJson).toArray),
 ("hadamard",.arr (UniformHadamardPairMachine.program.map insJson).toArray),
 ("diagonal",.arr (UniformPairDiagonalMachine.program.map insJson).toArray),
 ("C",.arr (UniformPairMachine.program.map insJson).toArray)]))

def coefficients : List (ℚ×ℚ):=[(0,0),(1,0),(-1,0),(0,1),(0,-1),(1/2,1/3),(17,-11),(1/2,0),(1,1)]
#eval IO.FS.writeFile "../logs/uniform-bytecode/zero-free-pair-shear/spec.json" (Json.compress (.arr
 (coefficients.map (fun q=>Json.mkObj [("reNum",toJson q.1.num),("reDen",toJson q.1.den),
 ("imNum",toJson q.2.num),("imDen",toJson q.2.den)])).toArray))
example : UniformZeroFreePairShearMachine.program.length=359:=UniformZeroFreePairShearMachine.program_length
example : UniformZeroFreePairShearMachine.kernelCalls UniformZeroFreePairShearMachine.phases=6:=
 UniformZeroFreePairShearMachine.six_kernel_calls
example : UniformLocalShear.kappa (0:ℂ)≠0:=UniformLocalShear.kappa_ne_zero 0
example : (0:ℂ)-UniformLocalShear.kappa 0≠0:=UniformLocalShear.second_ne_zero 0
