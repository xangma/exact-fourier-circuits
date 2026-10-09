import UniformRecursiveResidualGatherRecordMachine
import UniformRecursiveBatchGroupMachine
import UniformNativeYRecordMachine
import UniformNativeScalarRecordMachine
import UniformNativeExchangeRecordMachine
import UniformBinarySpectatorCMachine
import UniformFixedNetworkLiteralDecoderMachine
import UniformFixedNetworkMarkerMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSavingProgram
open UniformMachine UniformAssembly
noncomputable section

/-- This is a literal linker; sizes are fixed constants, never runtime handlers. -/
def offset {α : Type*} [DecidableEq α] (size : α→ℕ) : List α→α→ℕ
 | [],_=>0
 | a::as,b=>if a=b then 0 else size a+offset size as b

def Slice (code : Program) (p : Program) (start : ℕ) : Prop :=
 ∀i,i<code.length→p[start+i]?=code[i]?
lemma linked_slice {α : Type*} [DecidableEq α] (size : α→ℕ) (code : α→Program)
 (sizes : ∀a,(code a).length=size a) (ls : List α) (a : α) (mem : a∈ls) :
 Slice (code a) (ls.flatMap code) (offset size ls a) :=by
 induction ls with
 | nil=>simp at mem
 | cons b bs ih=>
  by_cases eq:b=a
  · subst b
    intro i hi
    simp only [offset,ite_true,List.flatMap_cons,Nat.zero_add]
    exact List.getElem?_append_left hi
  · have tail:a∈bs:=by rcases List.mem_cons.mp mem with h|h;exact False.elim (eq h.symm);exact h
    intro i hi
    simp only [offset,eq,ite_false,List.flatMap_cons]
    rw [List.getElem?_append_right (by rw [sizes];omega),sizes,
      show size b+offset size bs a+i-size b=offset size bs a+i by omega]
    exact ih tail i hi

/-- Original seed payload, independent of the runtime column count. -/
def seedLength : ℕ := (UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length
def seedPrinterLength : ℕ := 3*seedLength+3*UniformFixedNetworkScheduleMachine.baseSchedule.length+7
/-- The one unit-frame table is printed once per recursive node. No q-bit
address table or child outputs are hidden in this fixed finite payload. -/
def unitRecord : UniformFixedNetworkScheduleMachine.Record :=
 ⟨0,0,ExplicitSeedBudget.m,0,0,0,ExplicitSeedBudget.m,0,
  List.ofFn (fun i:Fin (ExplicitSeedBudget.m*ExplicitSeedBudget.m)=>
   if i.val/ExplicitSeedBudget.m=i.val%ExplicitSeedBudget.m then 1 else 0)⟩
def unitLength : ℕ := 8+ExplicitSeedBudget.m*ExplicitSeedBudget.m
def unitPrinterLength : ℕ := 3*unitLength+4

def threshold : ℕ := ExplicitSeedBudget.bits

inductive Part where
 | entry | rootAllocate | readyEntry | smallSetup | base | largeSetup | seedPrinter | unitSetup | unitPrinter | nodeReady
 | loop | reader | dispatch | residualMark | residualInit | gather | bootGroups | groupTest | call
 | inverseTest | inverseSetup | inverse | scatterSetup | scatter | directionNext | directionTest
 | edgeDone | recordAdvance | scalar | translation | exchange | marker
 | paddingInit | paddingTest | paddingPatch | paddingReader | paddingNext | paddingFinish
 | spectatorSetup | spectator | finish | returnSite | restored | halt
 deriving DecidableEq

def order : List Part := [.entry,.rootAllocate,.readyEntry,.smallSetup,.base,.largeSetup,.seedPrinter,.unitSetup,.unitPrinter,.nodeReady,
 .loop,.reader,.dispatch,.residualMark,.residualInit,.gather,.bootGroups,.groupTest,.call,
 .inverseTest,.inverseSetup,.inverse,.scatterSetup,.scatter,.directionNext,.directionTest,
 .edgeDone,.recordAdvance,.scalar,.translation,.exchange,.marker,
 .paddingInit,.paddingTest,.paddingPatch,.paddingReader,.paddingNext,.paddingFinish,
 .spectatorSetup,.spectator,.finish,.returnSite,.restored,.halt]

/-- The size table does not inspect any vector or input-dependent value. -/
def size : Part→ℕ
 | .entry=>4 | .rootAllocate=>6 | .readyEntry=>2 | .smallSetup=>4 | .base=>54 | .largeSetup=>7
 | .seedPrinter=>seedPrinterLength | .unitSetup=>12 | .unitPrinter=>unitPrinterLength | .nodeReady=>15
 | .loop=>4 | .reader=>52 | .dispatch=>12 | .residualMark=>4 | .residualInit=>5 | .gather=>366
 | .bootGroups=>5 | .groupTest=>1 | .call=>83 | .inverseTest=>1 | .inverseSetup=>14 | .inverse=>52
 | .scatterSetup=>7 | .scatter=>16 | .directionNext=>2 | .directionTest=>1 | .edgeDone=>4
 | .recordAdvance=>2 | .scalar=>106 | .translation=>197 | .exchange=>98 | .marker=>54
 | .paddingInit=>11 | .paddingTest=>6 | .paddingPatch=>10 | .paddingReader=>52 | .paddingNext=>6 | .paddingFinish=>4
 | .spectatorSetup=>6 | .spectator=>69 | .finish=>1 | .returnSite=>76 | .restored=>9 | .halt=>1

def address (a : Part) : ℕ := offset size order a
/-- Metadata is immediately before this node's direction/gather workspace.
All recursive descendants use the strictly later generated frontier. -/
def metaAddress (field : ℕ) : Program := [.natLiteral 4179 (6-field),.natBinary .sub 4178 4123 4179]

def piece : Part→Program
 | .entry=>[.natLiteral 4153 1,.natBinary .mul 5300 4120 4153,
   .natBinary .mul 3300 4121 4153,.branchLT 4151 4153 (address .rootAllocate) (address .readyEntry)]
 | .rootAllocate=>[.natBinary .mul 4150 4123 4153,.natBinary .add 4177 4120 4153,
   .natLiteral 4178 34,.natBinary .mul 4177 4177 4178,.natBinary .add 4123 4123 4177,
   .jump (address .readyEntry)]
 | .readyEntry=>[.natLiteral 4177 threshold,.branchLT 4120 4177 (address .smallSetup) (address .largeSetup)]
 | .smallSetup=>[.natBinary .mul 4900 4120 4153,.natLiteral 4901 UniformRecursiveSelfCallMachine.W,
   .natBinary .mul 4902 4121 4153,.natBinary .mul 4903 4122 4153]
 | .base=>UniformBinaryBatchCMachine.program.map (relocate (address .base) (address .finish))
 | .largeSetup=>[.natLiteral 4061 ExplicitSeedBudget.m,.natBinary .div 4060 4120 4061,
   .natBinary .mod 4127 4120 4061,.natBinary .mul 5301 4127 4153,
   .natBinary .mul 2599 4060 4153,.natBinary .mul 2600 4123 4153,.natBinary .mul 3304 4122 4153]
 | .seedPrinter=>UniformFixedNetworkLiteralDecoderMachine.fixedProgram.map (relocate (address .seedPrinter) (address .unitSetup))
 | .unitSetup=>[.natLiteral 4170 seedLength,.natBinary .add 2600 2600 4170,
   .natLiteral 4171 (unitLength+6),.natBinary .add 4123 2600 4171,
   .natLiteral 4179 2,.natBinary .sub 4178 4123 4179,.storeNat 4178 2600,
   .natLiteral 4179 1,.natBinary .sub 4178 4123 4179,.storeNat 4178 2600,
   .natLiteral 4179 6,.natBinary .sub 4178 4123 4179]
 | .unitPrinter=> (UniformFixedNetworkScheduleMachine.program unitRecord.data).map
   (relocate (address .unitPrinter) (address .nodeReady))
 | .nodeReady=>[.natLiteral 4179 2,.natBinary .sub 4178 4123 4179,.loadNat 4170 4178,
   .natLiteral 4171 seedLength,.natBinary .sub 2850 4170 4171,
   .natLiteral 4171 1,.natBinary .add 4178 4170 4171,.storeNat 4178 4060,
   .natLiteral 4171 3,.natBinary .mul 4172 4122 4171,.natBinary .add 3389 4123 4172,
   .natLiteral 4171 4,.natBinary .mul 4172 4122 4171,.natBinary .add 3364 4123 4172,.jump (address .loop)]
 | .loop=>metaAddress 5++[.loadNat 3301 4178,.branchLT 2850 3301 (address .reader) (address .spectatorSetup)]
 | .reader=>UniformFixedNetworkOpcodeMachine.headProgram.map (relocate (address .reader) (address .dispatch))
 | .dispatch=>[.branchLT 2851 4153 (address .residualMark) (address .dispatch+1),
   .natLiteral 4177 2,.branchLT 2851 4177 (address .scalar) (address .dispatch+3),
   .natLiteral 4177 3,.branchLT 2851 4177 (address .marker) (address .dispatch+5),
   .natLiteral 4177 4,.branchLT 2851 4177 (address .translation) (address .dispatch+7),
   .natLiteral 4177 5,.branchLT 2851 4177 (address .exchange) (address .dispatch+9),
   .natLiteral 4177 6,.branchLT 2851 4177 (address .paddingInit) (address .dispatch+11),.jump (address .marker)]
 | .residualMark=>metaAddress 0++[.natLiteral 4177 0,.storeNat 4178 4177]
 | .residualInit=>[.natLiteral 4134 0,.natBinary .mul 4132 2857 4153,
   .natBinary .mul 4130 2865 4153,.natBinary .mul 4131 2856 4153,.jump (address .directionTest)]
 | .gather=>UniformRecursiveResidualGatherRecordMachine.program.map (relocate (address .gather) (address .bootGroups))
 | .bootGroups=>UniformRecursiveBatchGroupMachine.bootGroups.map UniformNatBlockMachine.Op.code
 | .groupTest=>[.branchLT 4125 4126 (address .call) (address .inverseTest)]
 | .call=>UniformRecursiveSelfCallMachine.callCode (address .call)
 | .inverseTest=>[.branchLT 4131 4153 (address .scatterSetup) (address .inverseSetup)]
 | .inverseSetup=>[.natBinary .mul 3360 4091 4153,.natBinary .mul 3364 4090 4153,
   .natBinary .add 3361 4061 4127,.natBinary .mul 3362 4122 4153,
   .natBinary .sub 3363 4124 4153,.natBinary .mul 3353 4124 4153,
   .natBinary .mul 3354 4068 4153,.natBinary .mul 3421 4068 4153,
   .natBinary .mul 4069 4153 4153,.natBinary .mul 4015 4124 4153,
   .natBinary .mul 4023 4122 4153,.natBinary .mul 5300 4120 4153,
   .natBinary .mul 5301 4127 4153,.jump (address .inverse)]
 | .inverse=>UniformResidualNativeTranslationMachine.program.map (relocate (address .inverse) (address .scatterSetup))
 | .scatterSetup=>[.natBinary .mul 4072 4091 4153,.natBinary .mul 4073 4090 4153,
   .natBinary .mul 4070 4122 4153,.natBinary .mul 4071 4067 4153,
   .natLiteral 4074 1,.natBinary .mul 4069 4153 4153,.jump (address .scatter)]
 | .scatter=>UniformResidualArrayCopyMachine.program.map (relocate (address .scatter) (address .directionNext))
 | .directionNext=>[.natBinary .add 4134 4134 4153,.jump (address .directionTest)]
 | .directionTest=>[.branchLT 4134 4132 (address .gather) (address .edgeDone)]
 | .edgeDone=>metaAddress 0++[.loadNat 4177 4178,.branchLT 4177 4153 (address .recordAdvance) (address .paddingNext)]
 | .recordAdvance=>[.natBinary .mul 2850 4130 4153,.jump (address .loop)]
 | .scalar=>UniformNativeScalarRecordMachine.scalarProgram.map (relocate (address .scalar) (address .loop))
 | .translation=>UniformNativeYRecordMachine.program.map (relocate (address .translation) (address .loop))
 | .exchange=>UniformNativeExchangeRecordMachine.program.map (relocate (address .exchange) (address .loop))
 | .marker=>UniformFixedNetworkMarkerMachine.program.map (relocate (address .marker) (address .loop))
 | .paddingInit=>metaAddress 0++[.storeNat 4178 4153,.natBinary .add 4178 4178 4153,.storeNat 4178 2865,
   .natBinary .add 4178 4178 4153,.storeNat 4178 2854,
   .natBinary .add 4178 4178 4153,.natBinary .add 4177 2854 2855,.storeNat 4178 4177,
   .jump (address .paddingTest)]
 | .paddingTest=>metaAddress 2++[.loadNat 4175 4178,.natBinary .add 4178 4178 4153,
   .loadNat 4176 4178,.branchLT 4175 4176 (address .paddingPatch) (address .paddingFinish)]
 | .paddingPatch=>metaAddress 4++[.loadNat 2850 4178,.natLiteral 4177 3,.natBinary .add 4178 2850 4177,
   .storeNat 4178 4175,.natBinary .add 4178 2850 4153,.storeNat 4178 4060,
   .natBinary .mul 5300 4120 4153,.jump (address .paddingReader)]
 | .paddingReader=>UniformFixedNetworkOpcodeMachine.headProgram.map (relocate (address .paddingReader) (address .residualInit))
 | .paddingNext=>metaAddress 2++[.loadNat 4175 4178,.natBinary .add 4175 4175 4153,.storeNat 4178 4175,.jump (address .paddingTest)]
 | .paddingFinish=>metaAddress 1++[.loadNat 2850 4178,.jump (address .loop)]
 | .spectatorSetup=>[.natBinary .mul 5200 4120 4153,.natLiteral 5201 UniformRecursiveSelfCallMachine.W,
   .natBinary .mul 5202 4121 4153,.natBinary .mul 5203 4122 4153,
   .natBinary .mul 5204 4060 4061,.jump (address .spectator)]
 | .spectator=>UniformBinarySpectatorCMachine.program.map (relocate (address .spectator) (address .finish))
 | .finish=>[.branchLT 4151 4153 (address .halt) (address .returnSite)]
 | .returnSite=>UniformRecursiveSelfCallMachine.returnCode (address .returnSite) (address .restored)
 | .restored=>[.natBinary .mul 4015 4124 4153,.natBinary .mul 4023 4122 4153,
   .natBinary .mul 4069 4153 4153,.natBinary .mul 5300 4120 4153,
   .natBinary .mul 5301 4127 4153,.natBinary .mul 3300 4121 4153,
   .natBinary .mul 2852 4060 4153,.natBinary .mul 2853 4061 4153,.jump (address .groupTest)]
 | .halt=>[.halt]

lemma unitRecord_length : unitRecord.data.length=unitLength:=by
 simp only [unitRecord,UniformFixedNetworkScheduleMachine.Record.data_length,List.length_ofFn,unitLength]
lemma seedPrinter_length : UniformFixedNetworkLiteralDecoderMachine.fixedProgram.length=seedPrinterLength:=by
 rw [UniformFixedNetworkLiteralDecoderMachine.fixedProgram,UniformFixedNetworkLiteralDecoderMachine.program_length]
 rfl
lemma unitPrinter_length : (UniformFixedNetworkScheduleMachine.program unitRecord.data).length=unitPrinterLength:=by
 rw [UniformFixedNetworkScheduleMachine.program_length,unitRecord_length]
 rfl
lemma piece_size (a : Part) : (piece a).length=size a:=by
 cases a <;> simp only [piece,size,List.length_append,List.length_map,metaAddress,
  UniformBinaryBatchCMachine.program_length,seedPrinter_length,unitPrinter_length,
  UniformFixedNetworkOpcodeMachine.headProgram_length,UniformRecursiveResidualGatherRecordMachine.program_length,
  UniformRecursiveBatchGroupMachine.bootGroups,UniformRecursiveSelfCallMachine.callCode_length,
  UniformResidualNativeTranslationMachine.program,UniformXorTranslationMachine.program_length,
  UniformResidualArrayCopyMachine.program_length,UniformNativeScalarRecordMachine.scalarProgram_length,
  UniformNativeYRecordMachine.program_length,UniformNativeExchangeRecordMachine.program_length,
  UniformFixedNetworkMarkerMachine.program_length,UniformBinarySpectatorCMachine.program_length,
  UniformRecursiveSelfCallMachine.returnCode_length,List.length_cons,List.length_nil]
 <;> rfl

/-- One finite bytecode, independent of k,q,n and scalar inputs. This
construction alone does not assert its whole operational induction. -/
def program : Program := order.flatMap piece
lemma part_slice (a : Part) : Slice (piece a) program (address a):=by
 apply linked_slice size piece piece_size order a
 cases a <;> simp [order]
lemma part_child {a : Part} {child : Program} {ret : ℕ}
 (eq : piece a=child.map (relocate (address a) ret)) : CodeAt child program (address a) ret:=by
 intro i hi
 rw [←List.length_map (f:=relocate (address a) ret),←eq] at hi
 rw [part_slice a i hi,eq,List.getElem?_map]
lemma gather_code : CodeAt UniformRecursiveResidualGatherRecordMachine.program program (address .gather) (address .bootGroups):=
 part_child rfl
lemma scalar_code : CodeAt UniformNativeScalarRecordMachine.scalarProgram program (address .scalar) (address .loop):=
 part_child rfl
lemma translation_code : CodeAt UniformNativeYRecordMachine.program program (address .translation) (address .loop):=
 part_child rfl
lemma exchange_code : CodeAt UniformNativeExchangeRecordMachine.program program (address .exchange) (address .loop):=
 part_child rfl
lemma marker_code : CodeAt UniformFixedNetworkMarkerMachine.program program (address .marker) (address .loop):=
 part_child rfl
lemma base_code : CodeAt UniformBinaryBatchCMachine.program program (address .base) (address .finish):=
 part_child rfl
lemma spectator_code : CodeAt UniformBinarySpectatorCMachine.program program (address .spectator) (address .finish):=
 part_child rfl
lemma printer_code : CodeAt UniformFixedNetworkLiteralDecoderMachine.fixedProgram program (address .seedPrinter) (address .unitSetup):=
 part_child rfl
lemma call_code : UniformRecursiveSelfCallMachine.CallAt program (address .call):=by
 intro i hi
 apply part_slice .call i
 simpa only [piece,UniformRecursiveSelfCallMachine.callCode_length] using hi
end
end ExactFourierCircuits.UniformRecursiveSavingProgram
