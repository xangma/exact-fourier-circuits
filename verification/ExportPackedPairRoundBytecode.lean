import UniformPackedPairRoundMachine
import Lean

open ExactFourierCircuits UniformMachine Lean
namespace PackedPairRoundExport
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

#eval IO.FS.createDirAll "../logs/uniform-packed-c-round-agent-20261008"
#eval IO.FS.writeFile "../logs/uniform-packed-c-round-agent-20261008/program.json"
  (Json.compress (.arr (UniformPackedPairRoundMachine.program.map insJson).toArray))

example : UniformPackedPairRoundMachine.program.length=23 :=
  UniformPackedPairRoundMachine.program_length
example (m : ℕ) : 17*m+7≤24*(m+1) := UniformPackedPairRoundMachine.runtime_linear m
example (t : Fin 2) :
    UniformPackedPairRoundMachine.transformed (fun _=>Scalar.zero) t=Scalar.zero := by
  fin_cases t <;> simp [UniformPackedPairRoundMachine.transformed,
    UniformPairMachine.combine,Scalar.zero]
example : UniformPackedPairRoundMachine.transformed
    ![⟨Complex.I,true⟩,⟨1,false⟩] 0=⟨0,true⟩ := by
  simp [UniformPackedPairRoundMachine.transformed,UniformPairMachine.combine,
    UniformPackedPairRoundMachine.diagonalCoefficient,
    UniformPackedPairRoundMachine.offDiagonalCoefficient,a,b]
  ring_nf
  simp
example : UniformPackedPairRoundMachine.transformed
    ![⟨Complex.I,true⟩,⟨1,false⟩] 1=⟨1+Complex.I,true⟩ := by
  simp [UniformPackedPairRoundMachine.transformed,UniformPairMachine.combine,
    UniformPackedPairRoundMachine.diagonalCoefficient,
    UniformPackedPairRoundMachine.offDiagonalCoefficient,a,b]
  ring_nf
  simp
  all_goals norm_num
  all_goals ring
end PackedPairRoundExport
