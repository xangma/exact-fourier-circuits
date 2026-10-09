import UniformLocalCacheTimingExecution
import UniformLocalCacheTimingPlacement
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingConductor
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheTreeExecution UniformLocalCacheTimingMetadata
open UniformLocalCacheTimingInitialization UniformLocalCacheTimingExecution
open UniformLocalCacheTimingPlacement

/-- Durable ordinary allocation pointers, disjoint from the cache context
6160..6172. The outer allocator still owns installation of these three words. -/
structure Allocation (U V T:ℕ)(s:State):Prop where
 durations:s.natReg 6175=U
 starts:s.natReg 6176=V
 requests:s.natReg 6177=T

def installer:List Op:=[.literal 6508 0,.add 6500 4273 6508,.add 6501 4274 6508,
 .add 6502 6175 6508,.add 6503 6176 6508,.add 6504 6177 6508]

noncomputable section
/-- One literal program, with a charged producer continuation and pointer
installation. The timing segment keeps its genuine final halt. -/
def program:Program:=UniformLocalCacheTreeMachine.program.map (relocate 0 173)++
 installer.map Op.code++UniformCacheTimingProgram.program.map (terminalRelocate 179)
lemma program_length:program.length=301:=by
 simp only [program,List.length_append,List.length_map,
  UniformLocalCacheTreeMachine.program_length,UniformCacheTimingProgram.program_length]
 rfl
lemma producer_code:CodeAt UniformLocalCacheTreeMachine.program program 0 173:=by
 have h:=embed_code [] UniformLocalCacheTreeMachine.program
  (installer.map Op.code++UniformCacheTimingProgram.program.map (terminalRelocate 179)) 173
 simpa only [embed,List.length_nil,List.nil_append,List.append_assoc,program] using h
lemma installer_code:BlockAt installer program 173:=by
 intro i hi
 change i<6 at hi
 interval_cases i <;>rfl
lemma timing_code:TerminalCodeAt UniformCacheTimingProgram.program program 179:=by
 intro i hi
 have len:(UniformLocalCacheTreeMachine.program.map (relocate 0 173)++installer.map Op.code).length=179:=by
  simp only [List.length_append,List.length_map,UniformLocalCacheTreeMachine.program_length]
  rfl
 rw [program,List.getElem?_append_right (by omega)]
 rw [len,Nat.add_sub_cancel_left,List.getElem?_map]

local instance keepsDec(q:ℕ)(ins:Instruction):Decidable (UniformNewtonTableMachine.KeepsNat q ins):=by
 cases ins <;>simp only [UniformNewtonTableMachine.KeepsNat] <;>infer_instance
lemma producer_keeps_sources(q:ℕ)(hq:q=4273∨q=4274):
 ∀ins∈UniformLocalCacheTreeMachine.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 rcases hq with rfl|rfl
 · have checked:UniformLocalCacheTreeMachine.program.all (fun ins=>decide (UniformNewtonTableMachine.KeepsNat 4273 ins))=true:=by decide
   exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
 · have checked:UniformLocalCacheTreeMachine.program.all (fun ins=>decide (UniformNewtonTableMachine.KeepsNat 4274 ins))=true:=by decide
   exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)

lemma installer_addresses (D R U V T:ℕ)(s:State)
 (d:s.natReg 4273=D)(r:s.natReg 4274=R)(h:Allocation U V T s):
 Addresses D R U V T (applyBlock installer s):=by
 constructor <;>simp [installer,applyBlock,Op.apply,writeNat,next,d,r,h.durations,h.starts,h.requests]
lemma installer_heap(s:State):(applyBlock installer s).natHeap=s.natHeap:=rfl
lemma installer_nodes(s:State):(applyBlock installer s).natReg 4281=s.natReg 4281:=rfl
lemma installer_end(s:State):(applyBlock installer s).natReg 4282=s.natReg 4282:=rfl
lemma installer_source_tables {visits:List UniformLocalCacheTreeMachine.Visit}{D:ℕ}{s:State}
 (dir:Directory D 0 visits s)(rows:RequestTables visits s):
 Directory D 0 visits (applyBlock installer s)∧RequestTables visits (applyBlock installer s):=by
 have hd:∀(L:List UniformLocalCacheTreeMachine.Visit) start,Directory D start L s→Directory D start L (applyBlock installer s):=by
  intro L start h
  induction L generalizing start with
  | nil=>trivial
  | cons q qs ih=>exact ⟨h.1,ih _ h.2⟩
 exact ⟨hd visits 0 dir,fun q hq big positive=>rows q hq big positive⟩

lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · rcases List.mem_append.mp hi with hi|hi
   · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
     have allowed:=UniformLocalCacheTreeExecution.program_natOnly a ha
     cases a <;>simp_all [relocate,UniformLocalRectangleDescriptors.NatOnly]
   · have checked:(installer.map Op.code).all (fun ins=>decide (UniformLocalRectangleDescriptors.NatOnly ins))=true:=by decide
     exact of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have allowed:=UniformCacheTimingControl.program_natOnly a ha
   cases a <;>simp_all [terminalRelocate,relocate,UniformLocalRectangleDescriptors.NatOnly]
def destinations(ins:Instruction):Prop:=match ins with
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>
   (290≤d∧d<4295)∨(6500≤d∧d<6600)
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by
 cases ins <;>simp [destinations] <;>infer_instance
lemma program_destinations:∀ins∈program,destinations ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · rcases List.mem_append.mp hi with hi|hi
   · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
     have bounds:=UniformLocalCacheTreeExecution.program_destinations a ha
     cases a <;>simp_all [relocate,destinations,UniformLocalCacheTreeExecution.destinations]
   · have checked:(installer.map Op.code).all (fun ins=>decide (destinations ins))=true:=by decide
     exact of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have bounds:=UniformCacheTimingControl.program_destinations a ha
   cases a <;>simp_all [terminalRelocate,relocate,destinations,UniformCacheTimingControl.destinations]
lemma program_keeps(q:ℕ)(producer:q<290∨4295≤q)(timing:q<6500∨6600≤q):
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have bounds:=program_destinations ins hi
 have allowed:=program_natOnly ins hi
 cases ins <;>simp only [destinations] at bounds
 all_goals simp only [UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega

/-- The actual173→6 charged address operations→actual122 path, in one301-cell
program. No freely initialized6500..6504 register or PC-reset premise remains.
Allocation6175..6177 is ordinary address input, not a ready timing bank. -/
theorem execution (n v o W D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (header:UniformLocalCacheTreeIteration.Header v o W D R s)
 (producerLayout:UniformLocalCacheTreeExecution.Layout v o W D R B)
 (allocation:Allocation U V T s)
 (timingLayout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃ta t u,
 BoundedExecution program n x B s (ta+6+t) u∧
 ta≤(2*v+1)*nodeBudget v+18∧t≤printerBudget v o R∧Printed v o R U V T u∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀r,(r<290∨4295≤r)→(r<6500∨6600≤r)→u.natReg r=s.natReg r)∧
 (∀q,q<W→(q<U∨U+nodeCount v o R≤q)→(q<V∨V+nodeCount v o R≤q)→
  (q<T∨T+requestCount v o R≤q)→u.natHeap q=s.natHeap q):=by
 have code:301≤B:=by nlinarith [Nat.zero_le v]
 obtain ⟨a,ta,producer,time,ap,dir,rows,nodes,requests,low⟩:=
  UniformLocalCacheTreeExecution.execution n v o W D R B x s header producerLayout hp hs
 have placedProducer:BoundedRuns program n x B s ta (setPC a 173):=by
  simpa only [placed,Nat.zero_add,setPC] using UniformAssembly.BoundedExecution.placed producer_code (by omega) (by omega) producer
 have da:a.natReg 4273=D:=
  (UniformNewtonTableMachine.Executes.keeps_nat producer.executes (producer_keeps_sources 4273 (Or.inl rfl))).trans header.directory
 have ra:a.natReg 4274=R:=
  (UniformNewtonTableMachine.Executes.keeps_nat producer.executes (producer_keeps_sources 4274 (Or.inr rfl))).trans header.requests
 have aa:Allocation U V T (setPC a 173):=
  ⟨(execution_natFrame producer 6175 (by omega)).trans allocation.durations,
   (execution_natFrame producer 6176 (by omega)).trans allocation.starts,
   (execution_natFrame producer 6177 (by omega)).trans allocation.requests⟩
 have installing:=block_runs installer program 173 n B x (setPC a 173) installer_code rfl
  placedProducer.final_bound (by change 173+6≤B;omega)
  (by simp [installer,readable,Op.readable]) (by
   have h0:=producer.final_bound.2.1 4273
   have h1:=producer.final_bound.2.1 4274
   have h2:=producer.final_bound.2.1 6175
   have h3:=producer.final_bound.2.1 6176
   have h4:=producer.final_bound.2.1 6177
   simp [installer,peak,Op.peak,Op.apply,writeNat,next,setPC]
   all_goals omega)
 let b:=applyBlock installer (setPC a 173)
 have bp:b.pc=179:=by rw [applyBlock_pc];rfl
 have bdir:=installer_source_tables (dir.withPC 173) (rows.withPC 173)
 have bb:WordBound B (setPC b 0):=⟨by simp [setPC],installing.final_bound.2⟩
 obtain ⟨t,u,timing,budget,printed,frame,scalars,registers⟩:=execute_from_printed n v o D R U V T B x (setPC b 0)
  ((installer_addresses D R U V T (setPC a 173) da ra aa).withPC 0)
  (bdir.1.withPC 0) (bdir.2.withPC 0) nodes requests timingLayout source duration rowWord rfl bb
 have placedTiming:BoundedExecution program n x B b t (placed 179 u):=by
  have hh:=terminal_execution timing_code (by rw [UniformCacheTimingProgram.program_length];omega) timing
  have start:placed 179 (setPC b 0)=b:=by simp [placed,setPC,←bp]
  rw [start] at hh
  exact hh
 have whole:=placedProducer.executes (installing.executes placedTiming)
 refine ⟨ta,t,placed 179 u,?_,time,budget,?_,
  UniformLocalRectangleDescriptors.natOnly_execution program_natOnly whole.executes,?_,?_⟩
 · have length:installer.length=6:=rfl
   simpa only [length,Nat.add_assoc] using whole
 · exact ⟨printed.durations,printed.nodes,printed.requests⟩
 · intro r producerReg timingReg
   exact UniformNewtonTableMachine.Executes.keeps_nat whole.executes (program_keeps r producerReg timingReg)
 · intro q hq hU hV hT
   exact (frame q hU hV hT).trans (low q hq)
end
end ExactFourierCircuits.UniformLocalCacheTimingConductor
