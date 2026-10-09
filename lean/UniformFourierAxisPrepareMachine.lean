import UniformFourierAxisPrepareFooter
import UniformAxisCacheClockLookupExecution
import UniformEpochSelectorMachine
import UniformBoundaryDiagonalCaller
import UniformCacheRangeSelectorMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
noncomputable section
namespace Lookup
abbrev program:=UniformAxisCacheClockLookup.program
end Lookup
namespace Epoch
abbrev program:=UniformEpochSelectorMachine.program
end Epoch
namespace Ranges
abbrev program:=UniformCacheRangeSelector.program
end Ranges
namespace Boundary
abbrev program:=UniformBoundaryDiagonalCaller.program
end Boundary

def decision:Program:=[.natLiteral 7081 1,.branchLT 7080 7081 142 140,
 .natLiteral 7081 2,.branchLT 7080 7081 232 370]
def beforeWorkspace:Program:=Lookup.program.map (relocate 0 69)
def beforeEpoch:Program:=beforeWorkspace++UniformFourierAxisWorkspaceHeader.block.map Op.code
def beforeDecision:Program:=beforeEpoch++Epoch.program.map (relocate 97 138)
def beforeRanges:Program:=beforeDecision++decision
def beforeBoundary:Program:=beforeRanges++Ranges.program.map (relocate 142 370)
def beforeFooter:Program:=beforeBoundary++Boundary.program.map (relocate 232 370)
/-- One finite literal389 program: real lookup, workspace allocation, duration
read, epoch branch, actual cache ranges or boundary coefficients, common footer. -/
def program:Program:=beforeFooter++UniformFourierAxisPrepareFooter.block.map Op.code++[.halt]
lemma program_length:program.length=389:=by
 simp only[program,beforeFooter,beforeBoundary,beforeRanges,beforeDecision,beforeEpoch,beforeWorkspace,
 Lookup.program,Epoch.program,Ranges.program,Boundary.program,List.length_append,List.length_map,
 UniformAxisCacheClockLookup.program_length,UniformEpochSelectorMachine.program_length,
 UniformCacheRangeSelector.program_length,UniformBoundaryDiagonalCaller.program_length,
 UniformFourierAxisWorkspaceHeader.block_length,UniformFourierAxisPrepareFooter.block_length]
 rfl
lemma beforeWorkspace_length:beforeWorkspace.length=69:=by simp only[beforeWorkspace,List.length_map,Lookup.program,UniformAxisCacheClockLookup.program_length]
lemma beforeEpoch_length:beforeEpoch.length=97:=by simp only[beforeEpoch,List.length_append,List.length_map,beforeWorkspace_length,UniformFourierAxisWorkspaceHeader.block_length]
lemma beforeDecision_length:beforeDecision.length=138:=by simp only[beforeDecision,List.length_append,List.length_map,beforeEpoch_length,Epoch.program,UniformEpochSelectorMachine.program_length]
lemma beforeRanges_length:beforeRanges.length=142:=by simp only[beforeRanges,List.length_append,beforeDecision_length,decision,List.length_cons,List.length_nil]
lemma beforeBoundary_length:beforeBoundary.length=232:=by simp only[beforeBoundary,List.length_append,List.length_map,beforeRanges_length,Ranges.program,UniformCacheRangeSelector.program_length]
lemma beforeFooter_length:beforeFooter.length=370:=by simp only[beforeFooter,List.length_append,List.length_map,beforeBoundary_length,Boundary.program,UniformBoundaryDiagonalCaller.program_length]

lemma nat_segment_block (b:List Op)(pre tail:Program)(start:ℕ)(len:pre.length=start):
 BlockAt b (pre++b.map Op.code++tail) start:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment pre (b.map Op.code) tail i (by simpa only[List.length_map] using hi)
 simpa only[len,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h

lemma lookup_code:CodeAt Lookup.program program 0 69:=by
 have h:=UniformRankCrossPreparationMachine.segment_code []
  (UniformFourierAxisWorkspaceHeader.block.map Op.code++Epoch.program.map (relocate 97 138)++decision++
   Ranges.program.map (relocate 142 370)++Boundary.program.map (relocate 232 370)++
   UniformFourierAxisPrepareFooter.block.map Op.code++[.halt]) Lookup.program 0 69 rfl
 simpa only[program,beforeFooter,beforeBoundary,beforeRanges,beforeDecision,beforeEpoch,beforeWorkspace,
 List.nil_append,List.append_assoc] using h
lemma workspace_code:BlockAt UniformFourierAxisWorkspaceHeader.block program 69:=by
 have h:=nat_segment_block UniformFourierAxisWorkspaceHeader.block
  beforeWorkspace (Epoch.program.map (relocate 97 138)++decision++Ranges.program.map (relocate 142 370)++
  Boundary.program.map (relocate 232 370)++UniformFourierAxisPrepareFooter.block.map Op.code++[.halt])
  69 beforeWorkspace_length
 simpa only[program,beforeFooter,beforeBoundary,beforeRanges,beforeDecision,beforeEpoch,List.append_assoc] using h
lemma epoch_code:CodeAt Epoch.program program 97 138:=by
 have h:=UniformRankCrossPreparationMachine.segment_code beforeEpoch
  (decision++Ranges.program.map (relocate 142 370)++Boundary.program.map (relocate 232 370)++
   UniformFourierAxisPrepareFooter.block.map Op.code++[.halt]) Epoch.program 97 138 beforeEpoch_length
 simpa only[program,beforeFooter,beforeBoundary,beforeRanges,beforeDecision,List.append_assoc] using h
lemma ranges_code:CodeAt Ranges.program program 142 370:=by
 have h:=UniformRankCrossPreparationMachine.segment_code beforeRanges
  (Boundary.program.map (relocate 232 370)++UniformFourierAxisPrepareFooter.block.map Op.code++[.halt])
  Ranges.program 142 370 beforeRanges_length
 simpa only[program,beforeFooter,beforeBoundary,List.append_assoc] using h
lemma boundary_code:CodeAt Boundary.program program 232 370:=by
 have h:=UniformRankCrossPreparationMachine.segment_code beforeBoundary
  (UniformFourierAxisPrepareFooter.block.map Op.code++[.halt]) Boundary.program 232 370 beforeBoundary_length
 simpa only[program,beforeFooter,List.append_assoc] using h
lemma footer_code:BlockAt UniformFourierAxisPrepareFooter.block program 370:=by
 exact nat_segment_block _ beforeFooter [.halt] 370 beforeFooter_length
lemma code_138:program[138]?=some (.natLiteral 7081 1):=rfl
lemma code_139:program[139]?=some (.branchLT 7080 7081 142 140):=rfl
lemma code_140:program[140]?=some (.natLiteral 7081 2):=rfl
lemma code_141:program[141]?=some (.branchLT 7080 7081 232 370):=rfl
lemma halt_at:program[388]?=some .halt:=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeFooter++UniformFourierAxisPrepareFooter.block.map Op.code) [.halt] [] 0 (by decide)
 simpa only[List.length_append,List.length_map,beforeFooter_length,UniformFourierAxisPrepareFooter.block_length,
  Nat.add_zero,List.getElem?_cons_zero,List.append_nil,program,List.append_assoc] using h
end
end ExactFourierCircuits.UniformFourierAxisPrepareMachine
