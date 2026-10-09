import UniformRecursiveNodePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNodeJoin
open UniformMachine UniformAssembly BinaryFrames UniformRecursiveNodePreparation
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords serialize)
namespace P
export UniformRecursiveSavingProgram (Part program address size seedLength unitLength unitRecord seedPrinterLength unitPrinterLength)
end P
noncomputable section

lemma printed_transport (A : ℕ) (data : List ℕ) (s u : State) (h:Printed A data s)
 (same:∀z,A≤z→z<A+data.length→u.natHeap z=s.natHeap z) : Printed A data u:=by
 intro j hj
 rw [same (A+j) (by omega) (by omega)]
 exact h j hj
lemma records_transport (A : ℕ) (rs : List Record) (s u : State) (h:PrintedRecords A rs s)
 (same:∀z,A≤z→z<A+(serialize rs).length→u.natHeap z=s.natHeap z) : PrintedRecords A rs u:=by
 induction rs generalizing A with
 | nil=>trivial
 | cons r rs ih=>
   have len:(serialize (r::rs)).length=r.data.length+(serialize rs).length:=by
    simp only [serialize,List.map_cons,List.flatten_cons,List.length_append]
   exact ⟨printed_transport A r.data s u h.1 (by intro z hz hu;exact same z hz (by rw [len];omega)),
    ih (A+r.data.length) h.2 (by intro z hz hu;exact same z (by omega) (by rw [len];omega))⟩

/-- Every register changed by the four physical preparation phases. -/
def Changed (i : ℕ) : Prop := i=2600∨i=2601∨i=2602∨i=2603∨i=2604∨i=2700∨i=2701∨
 i=4170∨i=4171∨i=4172∨i=4178∨i=4179∨i=4123∨i=2850∨i=3389∨i=3364
structure Frame (F J : ℕ) (s u : State) : Prop where
 natHeap:∀z,z<F∨J≤z→u.natHeap z=s.natHeap z
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬Changed i→u.natReg i=s.natReg i

/-- A continuous run of the held common Program generates its entire fixed
record tape, unit-frame table and local metadata. No produced bank is an entry
premise; all scalar data and all outside Nat cells are retained. -/
theorem execution (n B F M l q V : ℕ) (x : Fin n→ℂ) (s : State)
 (eqM:M=P.seedLength) (eql:l=P.unitLength)
 (pc:s.pc=P.address .seedPrinter) (base:s.natReg 2600=F) (columns:s.natReg 2599=q)
 (logicalColumns:s.natReg 4060=q) (volume:s.natReg 4122=V)
 (bound:WordBound B s) (code:P.program.length≤B) (m:ExplicitSeedBudget.m≤B)
 (literals:UniformFixedNetworkScheduleMachine.literalCap (serialize UniformFixedNetworkScheduleMachine.baseSchedule)≤B)
 (pool:workBase F M l+4*V≤B) : ∃u,
 BoundedRuns P.program n x B s (P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady) u ∧
 u.pc=P.address .loop ∧ u.natReg 2850=F ∧ u.natReg 4123=workBase F M l ∧
 u.natReg 3389=workBase F M l+3*V ∧ u.natReg 3364=workBase F M l+4*V ∧
 u.natHeap (workBase F M l-2)=some (unitBase F M) ∧
 u.natHeap (workBase F M l-1)=some (unitBase F M) ∧
 PrintedRecords F (UniformFixedNetworkScheduleMachine.scheduleRecords q) u ∧
 Printed (unitBase F M) (P.unitRecord.withColumns q).data u ∧
 (∀j:Fin ExplicitSeedBudget.m,UniformRepeatedMaskMachine.Source
  (unitBase F M+8+j.val*ExplicitSeedBudget.m) (unit j) u) ∧ Frame F (workBase F M l) s u:=by
 have coordinate:workBase F M l=unitBase F M+l+6:=rfl
 have unitCoord:unitBase F M=F+M:=rfl
 have seedExtent:F+P.seedLength+1≤B:=by rw [←eqM];rw [coordinate,unitCoord] at pool;omega
 obtain ⟨a,r1,p1,bank1,out1,frame1⟩:=seed_execution n B F q x s pc base columns bound code literals seedExtent
 have aBase:a.natReg 2600=F:=(frame1.natReg 2600 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans base
 have setupEnd:workBase F M l≤B:=by omega
 have setupCode:UniformNatBlockMachine.BlockAt (unitSetupOps M l) P.program (P.address .unitSetup):=by
  rw [eqM,eql];exact unitSetup_code
 have setupExtent:P.address .unitSetup+12≤B:=by
  have h:=(UniformRecursiveSavingExecution.part_bound .unitSetup).trans code
  simpa only [UniformRecursiveSavingProgram.size] using h
 obtain ⟨r2,p2,frame2⟩:=unitSetup_generic_execution P.program (P.address .unitSetup) n B F M l x a
  p1 aBase r1.final_bound setupCode setupExtent setupEnd
 let b:=UniformNatBlockMachine.applyBlock (unitSetupOps M l) a
 obtain ⟨bBase,bFresh,meta2,meta1⟩:=unitSetup_values F M l a aBase
 have bPC:b.pc=P.address .unitPrinter:=p2.trans unitSetup_follow
 have unitExtent:unitBase F M+P.unitLength≤B:=by rw [←eql,coordinate] at *;omega
 obtain ⟨c,r3,p3,bank3,out3,frame3⟩:=unit_execution n B (unitBase F M) x b bPC bBase r2.final_bound code m unitExtent
 have cFresh:c.natReg 4123=workBase F M l:=
  (frame3.natReg 4123 (by omega) (by omega) (by omega) (by omega)).trans bFresh
 have cVolume:c.natReg 4122=V:=
  (frame3.natReg 4122 (by omega) (by omega) (by omega) (by omega)).trans
  ((frame2.natReg 4122 (by unfold UnitSetupChanged;omega)).trans
   ((frame1.natReg 4122 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans volume))
 have cColumns:c.natReg 4060=q:=
  (frame3.natReg 4060 (by omega) (by omega) (by omega) (by omega)).trans
  ((frame2.natReg 4060 (by unfold UnitSetupChanged;omega)).trans
   ((frame1.natReg 4060 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans logicalColumns))
 have out3':∀z,z<unitBase F M∨unitBase F M+l≤z→c.natHeap z=b.natHeap z:=by
  rw [eql];exact out3
 have cMeta2:c.natHeap (workBase F M l-2)=some (unitBase F M):=
  (out3' _ (Or.inr (by rw [coordinate];omega))).trans meta2
 have cMeta1:c.natHeap (workBase F M l-1)=some (unitBase F M):=
  (out3' _ (Or.inr (by rw [coordinate];omega))).trans meta1
 obtain ⟨u,r4,p4,cursor,table,buffer,field,frame4⟩:=nodeReady_execution n B F M l V q x c eqM p3 cFresh cVolume cColumns cMeta2 r3.final_bound code pool
 have mainLength:(serialize (UniformFixedNetworkScheduleMachine.scheduleRecords q)).length=M:=by
  change (UniformFixedNetworkScheduleMachine.scheduleData q).length=M
  rw [UniformFixedNetworkScheduleMachine.schedule_size_independent]
  exact eqM.symm
 have main:PrintedRecords F (UniformFixedNetworkScheduleMachine.scheduleRecords q) u:=by
  apply records_transport F _ a u bank1
  intro z lower upper
  rw [mainLength] at upper
  rw [frame4.natHeap z (by rw [unitCoord];omega),out3' z (Or.inl (by rw [unitCoord];omega)),
   frame2.natHeap z (Or.inl (by rw [unitCoord];omega))]
 have unitBank:Printed (unitBase F M) (P.unitRecord.withColumns q).data u:=
  printed_patch_columns _ q _ c u bank3 field frame4.natHeap
 have sources:∀j:Fin ExplicitSeedBudget.m,UniformRepeatedMaskMachine.Source
  (unitBase F M+8+j.val*ExplicitSeedBudget.m) (unit j) u:=by
  intro j i
  rw [frame4.natHeap _ (by omega)]
  exact unit_source (unitBase F M) j c bank3 i
 have finalMeta2:u.natHeap (workBase F M l-2)=some (unitBase F M):=
  (frame4.natHeap _ (by rw [coordinate];omega)).trans cMeta2
 have finalMeta1:u.natHeap (workBase F M l-1)=some (unitBase F M):=
  (frame4.natHeap _ (by rw [coordinate];omega)).trans cMeta1
 have finalFresh:u.natReg 4123=workBase F M l:=
  (frame4.natReg 4123 (by unfold NodeReadyChanged;omega)).trans cFresh
 refine ⟨u,((r1.trans r2).trans r3).trans r4,p4,cursor,finalFresh,table,buffer,finalMeta2,finalMeta1,main,unitBank,sources,?_⟩
 refine ⟨?_,frame4.scalarHeap.trans (frame3.scalarHeap.trans (frame2.scalarHeap.trans frame1.scalarHeap)),
  frame4.scalarReg.trans (frame3.scalarReg.trans (frame2.scalarReg.trans frame1.scalarReg)),
  frame4.outputs.trans (frame3.outputs.trans (frame2.outputs.trans frame1.outputs)),
  frame4.roots.trans (frame3.roots.trans (frame2.roots.trans frame1.roots)),?_⟩
 · intro z hz
   have upper:unitBase F M+l+6≤z∨z<F:=by rw [←coordinate];exact hz.elim Or.inr Or.inl
   rw [frame4.natHeap z (by rw [unitCoord] at *;omega),
    out3' z (by rw [unitCoord] at *;omega),frame2.natHeap z (by rw [unitCoord] at *;omega),
    out1 z (by rw [←eqM];rw [unitCoord] at *;omega)]
 · intro i hi
   unfold Changed at hi
   rw [frame4.natReg i (by unfold NodeReadyChanged;omega),
    frame3.natReg i (by omega) (by omega) (by omega) (by omega),
    frame2.natReg i (by unfold UnitSetupChanged;omega),
    frame1.natReg i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
end
end ExactFourierCircuits.UniformRecursiveNodeJoin
