import UniformProducedSectorPaddingPreparation
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



def fixtureAxis (pairs singles:ℕ) (h:2 ≤ 2*pairs+singles):UniformSectorPacking.Axis where
 widths:=List.replicate pairs 2++List.replicate singles 1
 widths_one_two:=by
  intro q mem
  rcases List.mem_append.mp mem with mem|mem
  · exact Or.inr (List.mem_replicate.mp mem).2
  · exact Or.inl (List.mem_replicate.mp mem).2
 radix_two:=by
  simpa only[List.sum_append,List.sum_replicate,smul_eq_mul,Nat.mul_comm pairs 2,
   Nat.mul_one] using h
 originalPermutation:=Equiv.refl _
def a0:=fixtureAxis 0 2 (by decide)
def a1:=fixtureAxis 1 0 (by decide)
def a2:=fixtureAxis 1 1 (by decide)
def a3:=fixtureAxis 2 1 (by decide)
def a4:=fixtureAxis 1 2 (by decide)
def fixtures:List (List UniformSectorPacking.Axis):=
 [[],[a0],[a1],[a2],[a3],[a4]]++
 ([a0,a1,a2,a3,a4].flatMap (fun a=>[a0,a1,a2,a3,a4].map (fun b=>[a,b])))++
 [[a0,a0,a0],[a1,a1,a1],[a2,a1,a0],[a3,a2,a1],[a2,a2,a2],[a0,a2,a4,a1]]
def spec (axes:List UniformSectorPacking.Axis):Json:=Json.mkObj
 [("widths",toJson (axes.map UniformSectorPacking.Axis.widths)),
  ("volume",toJson (UniformSectorPacking.radices axes).prod),
  ("sectors",toJson ((UniformSectorPacking.sectorStates axes).map (fun s=>[s.start,s.width,s.pairs]))),
  ("treeCost",toJson (UniformSectorMetadataMachine.treeCost (UniformSectorPacking.blockCounts axes)))]
def programs (W:ℕ):Json:=Json.mkObj
 [("W",toJson W),
  ("directory33",toJson ((UniformSectorBatchDirectoryMachine.programFor W).map insJson)),
  ("producer158",toJson ((UniformProducedSectorBatchPreparation.programFor W).map insJson)),
  ("padding25",toJson ((UniformSectorPaddingMachine.programFor W).map insJson)),
  ("padding37",toJson ((UniformSectorPaddingPreparation.programFor W).map insJson)),
  ("padding44",toJson ((UniformAllSectorPaddingMachine.programFor W).map insJson)),
  ("continuous205",toJson ((UniformProducedSectorPaddingPreparation.programFor W).map insJson))]
#eval IO.FS.createDirAll "../logs/uniform-bytecode/sector-padding-preparation/sector-bytecode"
#eval IO.FS.writeFile "../logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/programs.json"
 (Json.compress (Json.mkObj [("specializations",toJson ([1,2,3,5].map programs)),
  ("fixedDirectory33",toJson (UniformSectorBatchDirectoryMachine.program.map insJson)),
  ("fixedProducer158",toJson (UniformProducedSectorBatchPreparation.program.map insJson)),
  ("fixedW",toJson ExplicitSeedBudget.paddedRoles)]))
#eval IO.FS.writeFile "../logs/uniform-bytecode/sector-padding-preparation/sector-bytecode/specs.json"
 (Json.compress (toJson (fixtures.map spec)))
