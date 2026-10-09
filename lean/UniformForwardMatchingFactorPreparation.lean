import UniformGlobalMatchingPoolPreparation
import UniformGlobalMatchingScaleBankBridge
import UniformTranslatedMatchingRows
import UniformMatchingCoefficientValueBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace Ch
abbrev Parameters:=UniformChunkMatchingPreparation.Parameters
abbrev Layout:=UniformChunkMatchingPreparation.Layout
end Ch
noncomputable section
/-- The real five-field descriptor for a nonbroadcast forward slot. -/
def Slot (A:ℕ) (p:Ch.Parameters) (s:State):Prop:=
 s.natHeap A=some 0 ∧ s.natHeap (A+1)=some (if p.height.enabled then 1 else 0) ∧
 s.natHeap (A+2)=some 0 ∧ s.natHeap (A+3)=some p.depth ∧ s.natHeap (A+4)=some p.color
structure Config where
 chunk:Ch.Parameters
 slot:ℕ
 translated:ℕ
 offset:ℕ
 pool:ℕ
 ambient:ℕ
 mu:ℕ
 conjugate:ℕ
 negative:ℕ
 conjugates:ℕ
/-- Physical original Height header and ordinary allocation registers only. -/
structure Header (c:Config) (s:State):Prop where
 height:UniformCrossHeightPreparationMachine.Header c.chunk.height s
 radix:s.natReg 4410=c.chunk.radix
 source:s.natReg 4411=c.chunk.source
 target:s.natReg 4412=c.chunk.target
 borrowed:s.natReg 4413=c.chunk.borrowed
 selected:s.natReg 4414=c.chunk.selected
 ordinals:s.natReg 4415=c.chunk.ordinals
 mapped:s.natReg 4416=c.chunk.mapped
 permutation:s.natReg 4417=c.chunk.permutation
 widths:s.natReg 4418=c.chunk.widths
 markers:s.natReg 4419=c.chunk.markers
 axis:s.natReg 4420=c.chunk.axis
 slot:s.natReg 4421=c.slot
 translated:s.natReg 4422=c.translated
 offset:s.natReg 4423=c.offset
 pool:s.natReg 4424=c.pool
 ambient:s.natReg 4425=c.ambient
 mu:s.natReg 4426=c.mu
 conjugate:s.natReg 4427=c.conjugate
 conjugates:s.natReg 4428=c.conjugates
 negative:s.natReg 4429=c.negative
structure Layout (c:Config) (B:ℕ):Prop where
 chunk:Ch.Layout c.chunk B
 translatedFresh:c.chunk.axis+4≤c.translated
 translatedBound:c.translated+6*UniformCrossHeightPreparationMachine.gates c.chunk.height≤B
 extent:c.offset+c.chunk.radix≤c.ambient
 coefficient:UniformMatchingConjugateLoadMachine.Layout
  (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)
  c.chunk.height.C c.negative c.chunk.height.P c.conjugates c.mu c.conjugate B
 low:6≤c.mu
 poolFresh:c.conjugate<c.pool
 poolBound:c.pool+9*c.ambient≤B
 code:415≤B

def chunkSetup:List Op:=[.literal 4430 0,
 .add 1180 4410 4430,.add 1181 4411 4430,.add 1182 4412 4430,.add 1183 4413 4430,
 .add 1184 4414 4430,.add 1185 4415 4430,.add 1186 4416 4430,.add 1187 4417 4430,
 .add 1188 4418 4430,.add 1189 4419 4430,.add 1190 4420 4430,
 .add 4431 4421 4430,.getNat 4432 4431,.literal 4434 1,.add 4431 4431 4434,
 .getNat 1061 4431,.add 4431 4431 4434,.getNat 4433 4431,.add 4431 4431 4434,
 .getNat 1191 4431,.add 4431 4431 4434,.getNat 1192 4431]
def translationSetup:List Op:=[.add 4990 894 4430,.add 4991 1186 4430,
 .add 4992 4422 4430,.add 4993 4423 4430]
def factorSetup:List Op:=[.add 2100 1060 4430,.add 2101 4429 4430,.add 2102 1062 4430,
 .add 2103 4428 4430,.add 2106 4426 4430,.add 2107 4427 4430,.add 2140 4422 4430,
 .add 2141 4430 4430,.add 4330 4424 4430,.add 4331 4425 4430]
def beforeTranslate:Program:=chunkSetup.map Op.code++
 UniformChunkMatchingPreparation.program.map (relocate 23 238)++translationSetup.map Op.code
def beforeFactors:Program:=beforeTranslate++
 UniformTranslatedMatchingRows.program.map (relocate 242 265)++factorSetup.map Op.code
def program:Program:=beforeFactors++
 UniformGlobalMatchingPoolPreparation.program.map (relocate 275 414)++[.halt]
lemma chunkSetup_length:chunkSetup.length=23:=rfl
lemma translationSetup_length:translationSetup.length=4:=rfl
lemma factorSetup_length:factorSetup.length=10:=rfl
lemma beforeTranslate_length:beforeTranslate.length=242:=by
 simp[beforeTranslate,chunkSetup_length,UniformChunkMatchingPreparation.program_length,translationSetup_length]
lemma beforeFactors_length:beforeFactors.length=275:=by
 simp[beforeFactors,beforeTranslate_length,UniformTranslatedMatchingRows.program_length,factorSetup_length]
lemma program_length:program.length=415:=by
 simp[program,beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length]
lemma chunk_code:CodeAt UniformChunkMatchingPreparation.program program 23 238:=by
 let after:=translationSetup.map Op.code++UniformTranslatedMatchingRows.program.map (relocate 242 265)++
  factorSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 275 414)++[.halt]
 have eq:program=chunkSetup.map Op.code++UniformChunkMatchingPreparation.program.map (relocate 23 238)++after:=by
  simp[program,beforeFactors,beforeTranslate,after,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code (chunkSetup.map Op.code) after _ 23 238
  (by rw[List.length_map,chunkSetup_length])
lemma translation_code:CodeAt UniformTranslatedMatchingRows.program program 242 265:=by
 let after:=factorSetup.map Op.code++UniformGlobalMatchingPoolPreparation.program.map (relocate 275 414)++[.halt]
 have eq:program=beforeTranslate++UniformTranslatedMatchingRows.program.map (relocate 242 265)++after:=by
  simp[program,beforeFactors,after,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code beforeTranslate after _ 242 265 beforeTranslate_length
lemma factor_code:CodeAt UniformGlobalMatchingPoolPreparation.program program 275 414:=by
 exact UniformChunkRowTableMachine.segment_code beforeFactors [.halt] _ 275 414 beforeFactors_length
lemma chunkSetup_code:BlockAt chunkSetup program 0:=by
 intro i hi;change i<23 at hi;interval_cases i <;>rfl
lemma translationSetup_code:BlockAt translationSetup program 238:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma factorSetup_code:BlockAt factorSetup program 265:=by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma halt_at:program[414]?=some .halt:=by
 rw[program,List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length];omega)]
 simp only[List.length_append,List.length_map,beforeFactors_length,UniformGlobalMatchingPoolPreparation.program_length];rfl
lemma setup_header {c:Config} {s:State} (h:Header c s) (slot:Slot c.slot c.chunk s):
 UniformChunkMatchingPreparation.Header c.chunk (applyBlock chunkSetup s):=by
 rcases slot with ⟨bc,en,inv,dep,col⟩
 constructor
 · constructor <;>simp[chunkSetup,applyBlock,Op.apply,writeNat,next,h.slot,
    h.height.exponent,h.height.targets,h.height.inputs,h.height.tape,h.height.order,
    h.height.sourceDirectory,h.height.rows,h.height.colors,h.height.palette,h.height.directory,
    h.height.coefficients,h.height.constants,en,Nat.add_assoc]
 all_goals simp[chunkSetup,applyBlock,Op.apply,writeNat,next,h.radix,h.source,h.target,h.borrowed,
  h.selected,h.ordinals,h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,dep,col,Nat.add_assoc]
lemma setup_heaps (s:State):(applyBlock chunkSetup s).natHeap=s.natHeap ∧
 (applyBlock chunkSetup s).scalarHeap=s.scalarHeap ∧(applyBlock chunkSetup s).outputs=s.outputs ∧
 (applyBlock chunkSetup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma setup_nat (s:State) (q:ℕ) (h0:q<1061 ∨1061<q) (h1:q<1180 ∨1192<q)
 (h2:q<4430 ∨4434<q):(applyBlock chunkSetup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[chunkSetup,applyBlock,Op.apply,writeNat,next]
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
