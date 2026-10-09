import UniformGlobalTensorDiagonalLoop
import Lean
set_option autoImplicit false
open ExactFourierCircuits UniformMachine UniformTensorMonomialMachine Lean
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



def axis (r:ℕ) (h:0 < r) (reverse:Bool):Axis where
 radix:=r
 positive:=h
 permutation:=if reverse then ({toFun:=Fin.rev,invFun:=Fin.rev,left_inv:=Fin.rev_rev,right_inv:=Fin.rev_rev}:Equiv.Perm (Fin r)) else Equiv.refl _
 coefficient:=fun _=>0
 permutationBase:=0
 coefficientBase:=0
def fixtures:List (List Axis):=
 [[],[axis 1 (by decide) false],[axis 2 (by decide) true],
 [axis 2 (by decide) false,axis 3 (by decide) true],
 [axis 3 (by decide) true,axis 2 (by decide) false,axis 1 (by decide) true],
 [axis 1 (by decide) true,axis 1 (by decide) true,axis 2 (by decide) true],
 [axis 2 (by decide) true,axis 2 (by decide) false,axis 3 (by decide) true],
 [axis 5 (by decide) true,axis 1 (by decide) false]]
def spec (axes:List Axis):Json:=Json.mkObj
 [("radices",toJson (radices axes)),("treeCost",toJson (treeCost (radices axes))),
  ("permutations",toJson (axes.map (fun a=>List.ofFn (fun i:Fin a.radix=>(a.permutation i).val)))),
  ("tensorPermutation",toJson (List.ofFn (fun i:Fin (radices axes).prod=>(tensorPermutation axes i).val)))]
#eval IO.FS.createDirAll "../logs/uniform-bytecode/operational-kernels/tensor-bytecode"
#eval IO.FS.writeFile "../logs/uniform-bytecode/operational-kernels/tensor-bytecode/programs.json"
 (Json.compress (toJson ([1,2,3,5].map (fun W=>Json.mkObj [("W",toJson W),
  ("code",toJson ((UniformGlobalTensorDiagonalMachine.programFor W).map insJson))]))))
#eval IO.FS.writeFile "../logs/uniform-bytecode/operational-kernels/tensor-bytecode/specs.json"
 (Json.compress (toJson (fixtures.map spec)))
