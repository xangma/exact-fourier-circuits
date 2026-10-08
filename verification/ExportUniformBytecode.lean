import UniformDyadicConvolutionMachine
import UniformInitialTraversalPreparation
import UniformCRTTransferMachine
import UniformZeroFreeDiagonalMachine
import UniformPreparedZeroFreeDAGMachine
import UniformContiguousPowerBankMachine
open ExactFourierCircuits UniformMachine UniformRadixTwoDAG UniformPreparationMachine
open Lean

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
def rowJson (row:Row) : Json:=.arr #[toJson (opcode row.op),toJson row.left,toJson row.right]
def fixture (k:ℕ) : Json:=Json.mkObj [("height",toJson k),("width",toJson (width k)),("count",toJson (count k)),
 ("runtime",toJson (UniformDyadicConvolutionMachine.runtime (4*width k) k)),
 ("normRuntime",toJson (UniformNormalizationMachine.runtime (width k))),
 ("layouts",.arr (#[(1024,8192),(32768,262144)].map (fun (a,d)=>Json.mkObj [
    ("arena",toJson a),("table",toJson d),("wordBudget",toJson (UniformDyadicConvolutionMachine.wordBudget k a d))]))),
 ("rows",.arr ((List.finRange (count k)).map (fun j=>rowJson (UniformRadixTwoMachine.row k j))).toArray)]
def programJson (p:Program) : Json:=.arr (p.map insJson).toArray
#eval IO.FS.writeFile "../logs/uniform-bytecode/programs.json" (Json.compress (Json.mkObj [
  ("convolution",programJson UniformDyadicConvolutionMachine.program),
  ("seedStartup",programJson UniformAllAxisSeedPreparation.fullProgram),
  ("traversalStartup",programJson UniformInitialTraversalPreparation.program),
  ("transfer",programJson UniformCRTTransferMachine.program),
  ("zeroFree",programJson UniformZeroFreeDiagonalMachine.program),
  ("preparedZeroFree",programJson UniformPreparedZeroFreeDAGMachine.program),
  ("contiguousPower",programJson UniformContiguousPowerBankMachine.program)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/expected.json"
  (Json.compress (.arr ((List.range 7).map fixture).toArray))

namespace ConjugateDAGFixtures
open UniformOffsetPreparationMachine (DProgram)
def p0 : DProgram 1 0 := .nil
def pRoot : DProgram 1 1 := .step .nil (.root 0)
def pRat : DProgram 1 1 := .step .nil (.rational (-7/3))
def p1 : DProgram 1 1 := .step .nil (.rational (-1/2))
def p2 : DProgram 1 2 := .step p1 (.root 0)
def p3 : DProgram 1 3 := .step p2 (.add 0 1)
def p4 : DProgram 1 4 := .step p3 (.rational 0)
def p5 : DProgram 1 5 := .step p4 (.mul 1 2)
def p6 : DProgram 1 6 := .step p5 (.divide 4 0)
def p7 : DProgram 1 7 := .step p6 (.sub 5 3)
def p8 : DProgram 1 8 := .step p7 (.add 2 6)
def p9 : DProgram 1 9 := .step p8 (.mul 7 0)
def p10 : DProgram 1 10 := .step p9 (.divide 8 0)
def zero1 : DProgram 1 1 := .step .nil (.rational 0)
def zero2 : DProgram 1 2 := .step zero1 (.rational 1)
def zero3 : DProgram 1 3 := .step zero2 (.mul 0 1)
def zero4 : DProgram 1 4 := .step zero3 (.divide 2 1)

def rationalChain : (k : ℕ) → DProgram 1 k
 | 0 => .nil
 | k+1 => .step (rationalChain k) (.rational (k%9 : ℚ))

def literalJson (q : ℚ) : Json:=.arr #[toJson q.num.natAbs,toJson q.den,toJson (if q.num < 0 then 1 else 0 : ℕ)]
def spec {k : ℕ} (name : String) (p : DProgram 1 k) : Json := Json.mkObj [
 ("name",toJson name),("rootCount",toJson (1:ℕ)),("nodeCount",toJson k),
 ("nodes",.arr ((List.ofFn (UniformPreparationRowTableMachine.nodes p)).map (fun v=>.arr #[toJson v.tag,toJson v.left,toJson v.right])).toArray),
 ("rationals",.arr ((List.range k).map (fun j=>literalJson (UniformDAGLeafPreparationMachine.literalNat p j))).toArray),
 ("runtime",toJson (UniformPreparedZeroFreeDAGMachine.runtime p 100 200 400 500))]
#eval IO.FS.writeFile "../logs/uniform-bytecode/prepared-zero-free-specs.json"
 (Json.compress (.arr #[spec "empty" p0,spec "root" pRoot,spec "rational" pRat,
 spec "shared-all-operations" p10,spec "retained-zero" zero4,spec "rational-chain32" (rationalChain 32)]))

theorem p0_valid (roots : Fin 1→ℂ) : p0.Admissible roots := trivial
theorem pRoot_valid (roots : Fin 1→ℂ) : pRoot.Admissible roots := ⟨trivial,trivial⟩
theorem pRat_valid (roots : Fin 1→ℂ) : pRat.Admissible roots := ⟨trivial,trivial⟩
theorem p10_valid (roots : Fin 1→ℂ) : p10.Admissible roots := by
 norm_num [p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,
   UniformScalarPreparation.Program.Admissible,UniformScalarPreparation.Instruction.Admissible,
   UniformScalarPreparation.Program.eval,UniformScalarPreparation.Instruction.eval,Fin.snoc]
theorem zero4_valid (roots : Fin 1→ℂ) : zero4.Admissible roots := by
 norm_num [zero4,zero3,zero2,zero1,
   UniformScalarPreparation.Program.Admissible,UniformScalarPreparation.Instruction.Admissible,
   UniformScalarPreparation.Program.eval,UniformScalarPreparation.Instruction.eval,Fin.snoc]
theorem rationalChain_valid (k : ℕ) (roots : Fin 1→ℂ) : (rationalChain k).Admissible roots := by
 induction k with
 | zero => trivial
 | succ k ih => exact ⟨ih,trivial⟩
theorem unit_i : ‖Complex.I‖=1 := by simp
theorem unit_minus_i : ‖-Complex.I‖=1 := by simp
end ConjugateDAGFixtures
