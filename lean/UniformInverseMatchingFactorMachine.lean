import UniformInverseMatchingFactorGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
def inverseSetup:List Op:=[.literal 4461 0,.add 980 894 4461,.add 981 4422 4461,
 .add 982 4460 4461,.add 983 1060 4461,.add 984 4429 4461,.add 985 1062 4461]
def factorSetup:List Op:=[.add 2100 1060 4461,.add 2101 4429 4461,.add 2102 1062 4461,
 .add 2103 4428 4461,.add 2106 4426 4461,.add 2107 4427 4461,.add 2140 4460 4461,
 .add 2141 4461 4461,.add 4330 4424 4461,.add 4331 4425 4461]
def beforeFactors:Program:=inverseSetup.map Op.code++
 UniformInverseShearTableMachine.program.map (relocate 7 43)++factorSetup.map Op.code
def program:Program:=beforeFactors++UniformGlobalMatchingPoolPreparation.program.map (relocate 53 192)++[.halt]
lemma inverseSetup_length:inverseSetup.length=7:=rfl
lemma factorSetup_length:factorSetup.length=10:=rfl
lemma beforeFactors_length:beforeFactors.length=53:=by
 simp[beforeFactors,inverseSetup_length,factorSetup_length,UniformInverseShearTableMachine.program_length]
lemma program_length:program.length=193:=by
 simp[program,beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length]
lemma inverseSetup_code:BlockAt inverseSetup program 0:=by
 intro i hi;change i<7 at hi;interval_cases i <;>rfl
lemma factorSetup_code:BlockAt factorSetup program 43:=by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma inverse_code:CodeAt UniformInverseShearTableMachine.program program 7 43:=by
 let after:=factorSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 53 192)++[.halt]
 have eq:program=inverseSetup.map Op.code++UniformInverseShearTableMachine.program.map (relocate 7 43)++after:=by
  simp[program,beforeFactors,after,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code (inverseSetup.map Op.code) after _ 7 43
  (by rw[List.length_map,inverseSetup_length])
lemma factor_code:CodeAt UniformGlobalMatchingPoolPreparation.program program 53 192:=
 UniformChunkRowTableMachine.segment_code beforeFactors [.halt] _ 53 192 beforeFactors_length
lemma halt_at:program[192]?=some .halt:=by
 rw[program,List.getElem?_append_right (by simp[beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length])]
 simp only[List.length_append,List.length_map,beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length];rfl
lemma inverseSetup_heap (s:State):(applyBlock inverseSetup s).natHeap=s.natHeap ∧
 (applyBlock inverseSetup s).scalarHeap=s.scalarHeap ∧(applyBlock inverseSetup s).outputs=s.outputs ∧
 (applyBlock inverseSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma factorSetup_heap (s:State):(applyBlock factorSetup s).natHeap=s.natHeap ∧
 (applyBlock factorSetup s).scalarHeap=s.scalarHeap ∧(applyBlock factorSetup s).outputs=s.outputs ∧
 (applyBlock factorSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma inverseSetup_nat (s:State) (q:ℕ) (lo:q<980 ∨985<q) (z:q≠4461):
 (applyBlock inverseSetup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma factorSetup_nat (s:State) (q:ℕ) (h0:q<2100 ∨2103<q) (h1:q<2106 ∨2107<q)
 (h2:q<2140 ∨2141<q) (h3:q<4330 ∨4331<q):(applyBlock factorSetup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[factorSetup,applyBlock,Op.apply,writeNat,next]
lemma inverseSetup_safe {s:State} {B:ℕ} (wb:WordBound B s):readable inverseSetup s ∧peak inverseSetup s≤B:=by
 have a:=wb.2.1 894;have b:=wb.2.1 4422;have c:=wb.2.1 4460
 have d:=wb.2.1 1060;have e:=wb.2.1 4429;have f:=wb.2.1 1062
 simp[inverseSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
lemma factorSetup_safe {s:State} {B:ℕ} (zero:s.natReg 4461=0) (wb:WordBound B s):
 readable factorSetup s ∧peak factorSetup s≤B:=by
 have a:=wb.2.1 1060;have b:=wb.2.1 4429;have c:=wb.2.1 1062
 have d:=wb.2.1 4428;have e:=wb.2.1 4426;have f:=wb.2.1 4427
 have g:=wb.2.1 4460;have h:=wb.2.1 4424;have i:=wb.2.1 4425
 simp[factorSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero]
 omega
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
