import UniformAllAxisSeedPreparation
import UniformLocalMatchingSlotDirectory
import UniformGlobalScalePoolMachine
import UniformSyntacticNatFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Ordinary selected seed-directory cell7000, lane7001 and fresh Nat arena7051.
The time5920 and reserved top scalar slab6020 are read from their real callers. -/
structure Args (seedCell lane time pool arena:ℕ) (s:State):Prop where
 seed:s.natReg 7000=seedCell
 lane:s.natReg 7001=lane
 time:s.natReg 5920=time
 pool:s.natReg 6020=pool
 arena:s.natReg 7051=arena

def head:List Op:=[.literal 7002 0,.literal 7003 1,.getNat 7006 7000,
 .add 7008 7000 7003,.getNat 7007 7008,.add 4330 6020 7002,.add 4331 7007 7002]
def copySetup:List Op:=[.literal 146 1,.add 147 7007 7002,
 .mul 7009 7001 7007,.add 148 7006 7009,.add 149 6020 7002]
def slotSetup:List Op:=[.literal 894 0,.add 5840 5920 7002,.add 5841 7007 7002,
 .add 5842 6020 7002,.add 5843 7051 7002,.add 5844 5843 7007,
 .add 5845 5844 7007,.add 5846 5845 7007,.add 5847 5843 7002,
 .literal 7010 4,.add 5848 5846 7010,.literal 5849 1]
/-- Every helper halt is a charged jump in this literal127. No C call occurs. -/
def program:Program:=head.map Op.code++
 UniformGlobalScalePoolMachine.program.map (relocate 7 18)++copySetup.map Op.code++
 UniformLocalSeedTableMachine.Strided.program.map (relocate 23 34)++slotSetup.map Op.code++
 UniformLocalMatchingSlotDirectory.program.map (relocate 46 126)++[.halt]
lemma head_length:head.length=7:=rfl
lemma copySetup_length:copySetup.length=5:=rfl
lemma slotSetup_length:slotSetup.length=12:=rfl
lemma program_length:program.length=127:=by
 simp only[program,List.length_append,List.length_map,head_length,copySetup_length,slotSetup_length,
  UniformGlobalScalePoolMachine.program_length,UniformLocalSeedTableMachine.Strided.program_length,
  UniformLocalMatchingSlotDirectory.program_length,List.length_cons,List.length_nil]
lemma head_code:BlockAt head program 0:=by intro i hi;change i<7 at hi;interval_cases i <;>rfl
lemma pool_code:CodeAt UniformGlobalScalePoolMachine.program program 7 18:=by
 have h:=UniformRankCrossPreparationMachine.segment_code (head.map Op.code)
  (copySetup.map Op.code++UniformLocalSeedTableMachine.Strided.program.map (relocate 23 34)++
   slotSetup.map Op.code++UniformLocalMatchingSlotDirectory.program.map (relocate 46 126)++[.halt])
  UniformGlobalScalePoolMachine.program 7 18 rfl
 simpa only[program,List.append_assoc] using h
lemma copySetup_code:BlockAt copySetup program 18:=by
 have h:=UniformRankCrossPreparationMachine.block_of_segment copySetup
  (head.map Op.code++UniformGlobalScalePoolMachine.program.map (relocate 7 18))
  (UniformLocalSeedTableMachine.Strided.program.map (relocate 23 34)++slotSetup.map Op.code++
   UniformLocalMatchingSlotDirectory.program.map (relocate 46 126)++[.halt]) 18 rfl
 simpa only[program,List.append_assoc] using h
lemma copy_code:CodeAt UniformLocalSeedTableMachine.Strided.program program 23 34:=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (head.map Op.code++UniformGlobalScalePoolMachine.program.map (relocate 7 18)++copySetup.map Op.code)
  (slotSetup.map Op.code++UniformLocalMatchingSlotDirectory.program.map (relocate 46 126)++[.halt])
  UniformLocalSeedTableMachine.Strided.program 23 34 rfl
 simpa only[program,List.append_assoc] using h
lemma slotSetup_code:BlockAt slotSetup program 34:=by
 have h:=UniformRankCrossPreparationMachine.block_of_segment slotSetup
  (head.map Op.code++UniformGlobalScalePoolMachine.program.map (relocate 7 18)++copySetup.map Op.code++
   UniformLocalSeedTableMachine.Strided.program.map (relocate 23 34))
  (UniformLocalMatchingSlotDirectory.program.map (relocate 46 126)++[.halt]) 34 rfl
 simpa only[program,List.append_assoc] using h
lemma slot_code:CodeAt UniformLocalMatchingSlotDirectory.program program 46 126:=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (head.map Op.code++UniformGlobalScalePoolMachine.program.map (relocate 7 18)++copySetup.map Op.code++
   UniformLocalSeedTableMachine.Strided.program.map (relocate 23 34)++slotSetup.map Op.code)
  [.halt] UniformLocalMatchingSlotDirectory.program 46 126 rfl
 simpa only[program,List.append_assoc] using h
lemma halt_at:program[126]?=some .halt:=rfl

def emptyEdges:Fin 0→UniformColoring.Edge:=Fin.elim0
lemma empty_matching:UniformMatchingAxisTableMachine.Matching emptyEdges:=by intro i;exact Fin.elim0 i
lemma empty_range (r:ℕ):UniformMatchingAxisTableMachine.InRange r emptyEdges:=by intro i;exact Fin.elim0 i
def axis (r arena:ℕ) (positive:2≤r):UniformSectorPackingMachine.PhysicalAxis:=
 UniformMatchingAxisTableMachine.physicalAxis r (arena+r) arena emptyEdges empty_matching (empty_range r) positive

def written:List ℕ:=[146,147,148,149,150,151,152,153,154,840,841,842,843,844,845,846,
 850,851,852,853,854,855,856,857,858,859,860,861,894,4330,4331,4356,4357,4358,4359,
 5840,5841,5842,5843,5844,5845,5846,5847,5848,5849,5850,5851,5852,5853,
 7002,7003,7006,7007,7008,7009,7010]
lemma written_checked:program.all (fun i=>(UniformSyntacticNatFrame.natDst i).all (fun d=>decide (d∈written)))=true:=by decide +kernel
lemma avoids (j:ℕ) (hj:j∉written):UniformSyntacticNatFrame.Avoids program j:=by
 intro i hi bad
 have h:=List.all_eq_true.mp written_checked i hi
 rw[bad] at h
 simp only[Option.all_some,decide_eq_true_eq] at h
 exact hj h
lemma nat_frame {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u) (j:ℕ) (hj:j∉written):u.natReg j=s.natReg j:=
 UniformSyntacticNatFrame.boundedExecution_preserves (avoids j hj) run
end
end ExactFourierCircuits.UniformBoundaryDiagonalMachine
