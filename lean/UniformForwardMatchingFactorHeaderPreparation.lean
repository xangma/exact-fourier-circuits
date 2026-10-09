import UniformForwardMatchingFactorValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorHeaderPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace F
abbrev Config:=UniformForwardMatchingFactorPreparation.Config
end F
noncomputable section
/-- Ordinary persistent allocation fields. Their actual reload is charged;
no current low Height header is required. -/
structure HeightArgs (p:UniformCrossHeightPreparationMachine.Parameters) (s:State):Prop where
 exponent:s.natReg 4440=p.K
 targets:s.natReg 4441=p.a
 inputs:s.natReg 4442=p.e
 tape:s.natReg 4443=p.T
 order:s.natReg 4444=p.Q
 sourceDirectory:s.natReg 4445=p.R
 rows:s.natReg 4446=p.D
 colors:s.natReg 4447=p.F
 palette:s.natReg 4448=p.U
 directory:s.natReg 4449=p.J
 coefficients:s.natReg 4450=p.C
 enabled:s.natReg 4451=if p.enabled then 1 else 0
 constants:s.natReg 4452=p.P
structure Args (c:F.Config) (s:State):Prop where
 height:HeightArgs c.chunk.height s
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

def setup:List Op:=[.literal 4453 0,
 .add 1050 4440 4453,
 .add 1051 4441 4453,
 .add 1052 4442 4453,
 .add 1053 4443 4453,
 .add 1054 4444 4453,
 .add 1055 4445 4453,
 .add 1056 4446 4453,
 .add 1057 4447 4453,
 .add 1058 4448 4453,
 .add 1059 4449 4453,
 .add 1060 4450 4453,
 .add 1061 4451 4453,
 .add 1062 4452 4453]
def program:Program:=setup.map Op.code++UniformForwardMatchingFactorPreparation.program.map (relocate 14 429)++[.halt]
lemma setup_length:setup.length=14:=rfl
lemma program_length:program.length=430:=by
 simp[program,setup_length,UniformForwardMatchingFactorPreparation.program_length]
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<14 at hi;interval_cases i <;>rfl
lemma body_code:CodeAt UniformForwardMatchingFactorPreparation.program program 14 429:=by
 exact UniformChunkRowTableMachine.segment_code (setup.map Op.code) [.halt] _ 14 429
  (by rw[List.length_map,setup_length])
lemma halt_at:program[429]?=some .halt:=by
 rw[program,List.getElem?_append_right (by simp[setup_length,UniformForwardMatchingFactorPreparation.program_length])]
 simp only[List.length_append,List.length_map,setup_length,UniformForwardMatchingFactorPreparation.program_length];rfl
lemma setup_heaps (s:State):(applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧(applyBlock setup s).outputs=s.outputs ∧
 (applyBlock setup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma setup_nat (s:State) (q:ℕ) (lo:q<1050 ∨1062<q) (zero:q≠4453):
 (applyBlock setup s).natReg q=s.natReg q:=by
 simp (disch:=omega)[setup,applyBlock,Op.apply,writeNat,next]
lemma setup_header {c:F.Config} {s:State} (h:Args c s):
 UniformForwardMatchingFactorPreparation.Header c (applyBlock setup s):=by
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.height.exponent,h.height.targets,h.height.inputs,h.height.tape,h.height.order,h.height.sourceDirectory,h.height.rows,h.height.colors,h.height.palette,h.height.directory,h.height.coefficients,h.height.enabled,h.height.constants]
 all_goals simp[setup,applyBlock,Op.apply,writeNat,next,h.radix,h.source,h.target,h.borrowed,h.selected,h.ordinals,h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,h.translated,h.offset,h.pool,h.ambient,h.mu,h.conjugate,h.conjugates,h.negative]
lemma coreHeaderWithPC {c:F.Config} {s:State}
 (h:UniformForwardMatchingFactorPreparation.Header c s) (pc:ℕ):
 UniformForwardMatchingFactorPreparation.Header c (setPC s pc):=
 ⟨h.height.withPC pc,h.radix,h.source,h.target,h.borrowed,h.selected,h.ordinals,
  h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,h.translated,h.offset,
  h.pool,h.ambient,h.mu,h.conjugate,h.conjugates,h.negative⟩
lemma setup_header_zero {c:F.Config} {s:State} (h:Args c s):
 UniformForwardMatchingFactorPreparation.Header c (setPC (applyBlock setup s) 0):=
 coreHeaderWithPC (setup_header h) 0
lemma setup_safe {s:State} {B:ℕ} (h:WordBound B s):readable setup s ∧peak setup s≤B:=by
 have a:=h.2.1 4440;have b:=h.2.1 4441;have c:=h.2.1 4442;have d:=h.2.1 4443
 have e:=h.2.1 4444;have f:=h.2.1 4445;have g:=h.2.1 4446;have i:=h.2.1 4447
 have j:=h.2.1 4448;have k:=h.2.1 4449;have l:=h.2.1 4450;have m:=h.2.1 4451;have n:=h.2.1 4452
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
end
end ExactFourierCircuits.UniformForwardMatchingFactorHeaderPreparation
