import UniformSixCDepthColorController
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCBroadcast
open UniformMachine UniformAssembly UniformReplayPrint
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

def borrowedSetup : List Op := [.literal 3000 0,
 .add 261 1181 3000,.add 262 1052 3000,.add 263 1182 3000,
 .add 264 1051 3000,.add 265 1072 3000,.add 266 1183 3000]
def broadcastSetup (positive:Bool) : List Op := [.literal 3030 (if positive then 1 else 0),
 .add 3100 1051 3000,.add 3101 1072 3000,.add 3102 1182 3000,
 .add 3103 1183 3000,.add 3104 3005 3000,.add 3105 3008 3030]
def beforeBroadcast : Program := borrowedSetup.map Op.code ++
 UniformBorrowedCoordinateMachine.program.map (relocate 7 24)
def beforeInverse (positive:Bool) : Program := beforeBroadcast ++ (broadcastSetup positive).map Op.code ++
 UniformCrossBroadcastTableMachine.program.map (relocate 31 51) ++
 UniformSixCDepthColorController.inverseInstall.map Op.code
def program (positive:Bool) : Program := beforeInverse positive ++
 UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]
lemma borrowedSetup_length : borrowedSetup.length=7:=rfl
lemma broadcastSetup_length (positive:Bool) : (broadcastSetup positive).length=7:=rfl
lemma beforeBroadcast_length : beforeBroadcast.length=24:=by
 simp [beforeBroadcast,borrowedSetup_length,UniformBorrowedCoordinateMachine.program_length]
lemma beforeInverse_length (positive:Bool) : (beforeInverse positive).length=70:=by
 simp [beforeInverse,beforeBroadcast_length,broadcastSetup_length,UniformCrossBroadcastTableMachine.program_length,
  UniformSixCDepthColorController.inverseInstall_length]
lemma program_length (positive:Bool) : (program positive).length=754:=by
 simp [program,beforeInverse_length,UniformSixCInverseMatchingPreparation.program_length]
lemma borrowed_code (positive:Bool) : CodeAt UniformBorrowedCoordinateMachine.program (program positive) 7 24:=by
 let tail := (broadcastSetup positive).map Op.code ++
  UniformCrossBroadcastTableMachine.program.map (relocate 31 51) ++
  UniformSixCDepthColorController.inverseInstall.map Op.code ++
  UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]
 have eqn:program positive=borrowedSetup.map Op.code ++
  UniformBorrowedCoordinateMachine.program.map (relocate 7 24) ++ tail:=by
  simp [program,beforeInverse,beforeBroadcast,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code _ tail _ 7 24 (by simp [borrowedSetup_length])
lemma broadcast_code (positive:Bool) : CodeAt UniformCrossBroadcastTableMachine.program (program positive) 31 51:=by
 let pre:=beforeBroadcast ++ (broadcastSetup positive).map Op.code
 let tail:=UniformSixCDepthColorController.inverseInstall.map Op.code ++
  UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]
 have eqn:program positive=pre ++ UniformCrossBroadcastTableMachine.program.map (relocate 31 51) ++ tail:=by
  simp [program,beforeInverse,pre,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code pre tail _ 31 51 (by simp [pre,beforeBroadcast_length,broadcastSetup_length])
lemma inverse_code (positive:Bool) : CodeAt UniformSixCInverseMatchingPreparation.program (program positive) 70 753:=
 UniformChunkRowTableMachine.segment_code _ [.halt] _ 70 753 (beforeInverse_length positive)
lemma borrowedSetup_code (positive:Bool) : BlockAt borrowedSetup (program positive) 0:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (borrowedSetup.map Op.code)
  (UniformBorrowedCoordinateMachine.program.map (relocate 7 24) ++ (broadcastSetup positive).map Op.code ++
   UniformCrossBroadcastTableMachine.program.map (relocate 31 51) ++
   UniformSixCDepthColorController.inverseInstall.map Op.code ++
   UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]) i (by simpa using hi)
 simpa only [program,beforeInverse,beforeBroadcast,List.append_assoc,List.length_nil,Nat.zero_add,List.nil_append,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma broadcastSetup_code (positive:Bool) : BlockAt (broadcastSetup positive) (program positive) 24:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment beforeBroadcast ((broadcastSetup positive).map Op.code)
  (UniformCrossBroadcastTableMachine.program.map (relocate 31 51) ++
   UniformSixCDepthColorController.inverseInstall.map Op.code ++
   UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]) i (by simpa using hi)
 simpa only [program,beforeInverse,List.append_assoc,beforeBroadcast_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma install_code (positive:Bool) : BlockAt UniformSixCDepthColorController.inverseInstall (program positive) 51:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeBroadcast ++ (broadcastSetup positive).map Op.code ++
   UniformCrossBroadcastTableMachine.program.map (relocate 31 51))
  (UniformSixCDepthColorController.inverseInstall.map Op.code)
  (UniformSixCInverseMatchingPreparation.program.map (relocate 70 753) ++ [.halt]) i (by simpa using hi)
 simpa only [program,beforeInverse,List.append_assoc,List.length_append,List.length_map,beforeBroadcast_length,
  broadcastSetup_length,UniformCrossBroadcastTableMachine.program_length,List.getElem?_map,
  List.getElem?_eq_getElem hi,Option.map_some] using h
lemma halt_at (positive:Bool) : (program positive)[753]?=some .halt:=by
 have len:((beforeInverse positive)++UniformSixCInverseMatchingPreparation.program.map (relocate 70 753)).length=753:=by
  simp [beforeInverse_length,UniformSixCInverseMatchingPreparation.program_length]
 unfold program
 rw [List.getElem?_append,ite_eq_right (by rw [len];omega),len];rfl

noncomputable section
structure Geometry where
 volume : ℕ
 source : ℕ
 inputs : ℕ
 target : ℕ
 targets : ℕ
 gates : ℕ
 borrowed : ℕ
 fit : gates+inputs+targets≤volume
 ag : targets≤gates
 targetEnd : target+targets≤volume
 sourceEnd : source+inputs≤volume

def Geometry.borrowedAt (g:Geometry) (i:ℕ) : ℕ := if h:i<g.gates then
 (UniformBorrowedCoordinateMachine.embedding g.volume g.source g.inputs g.target g.targets g.gates g.fit ⟨i,h⟩).val else 0

def word (positive:Bool) (g:Geometry) (R:ℕ) : List (ShearCode ℕ R) :=
 (List.finRange g.targets).map (fun j=>
  ⟨g.target+j.val,g.borrowedAt (g.gates-g.targets+j.val),by
   have hj:g.gates-g.targets+j.val<g.gates:=by have:=j.isLt;have:=g.ag;omega
   have eligible:=UniformBorrowedCoordinateMachine.embedding_eligible g.volume g.source g.inputs g.target g.targets g.gates g.fit ⟨_,hj⟩
   simp only [Geometry.borrowedAt,dite_eq_left hj]
   unfold UniformBorrowedCoordinateMachine.Eligible at eligible
   have:=j.isLt;omega,
   .rational (if positive then -1 else 1)⟩)
lemma word_length (positive:Bool) (g:Geometry) (R:ℕ) : (word positive g R).length=g.targets:=by simp [word]
lemma word_good (positive:Bool) (g:Geometry) (R K:ℕ) :
 ∀row∈word positive g R,UniformMatchingCoefficientValueBridge.ForwardLeaf K row.coefficient:=by
 intro row h
 obtain ⟨j,_,rfl⟩:=List.mem_map.mp h
 cases positive
 · exact Or.inl rfl
 · exact Or.inr (Or.inl rfl)
lemma word_edges (positive:Bool) (g:Geometry) (R:ℕ) (i:Fin (word positive g R).length) :
 UniformSixCInverseMatchingPreparation.forwardEdges (word positive g R) i=
 UniformCrossBroadcastTableMachine.actualEdges g.volume g.source g.inputs g.target g.targets g.gates g.fit g.ag
  ⟨i.val,by simpa [word_length] using i.isLt⟩:=by
 have hi:i.val<g.targets:=by simpa [word_length] using i.isLt
 have hb:g.gates-g.targets+i.val<g.gates:=by have:=g.ag;omega
 simp [UniformSixCInverseMatchingPreparation.forwardEdges,word,List.getElem_map,List.getElem_finRange,
  UniformCrossBroadcastTableMachine.actualEdges,UniformCrossBroadcastTableMachine.outputBorrowed,Geometry.borrowedAt,hb]
lemma word_matching (positive:Bool) (g:Geometry) (R:ℕ) :
 UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges (word positive g R)):=by
 intro i j neq
 rw [word_edges,word_edges]
 exact UniformCrossBroadcastTableMachine.actual_matching g.volume g.source g.inputs g.target g.targets g.gates g.fit g.ag
  ⟨i.val,by simpa [word_length] using i.isLt⟩ ⟨j.val,by simpa [word_length] using j.isLt⟩ (by
    intro eq;exact neq (Fin.ext (congrArg (fun z:Fin g.targets=>z.val) eq)))
lemma word_range (positive:Bool) (g:Geometry) (R:ℕ) :
 UniformMatchingAxisTableMachine.InRange g.volume (UniformSixCInverseMatchingPreparation.forwardEdges (word positive g R)):=by
 intro i
 rw [word_edges]
 exact UniformCrossBroadcastTableMachine.actual_inRange _ _ _ _ _ _ g.fit g.ag g.targetEnd _
lemma word_rows (positive:Bool) (g:Geometry) (R C T P:ℕ) :
 UniformSixCInverseMatchingPreparation.forwardRows C T P (word positive g R)=
 UniformCrossBroadcastTableMachine.rowList g.targets g.gates g.target (P+(if positive then 1 else 0)) g.borrowedAt:=by
 cases positive <;>
 simp [UniformSixCInverseMatchingPreparation.forwardRows,word,UniformCrossBroadcastTableMachine.rowList,List.map_map,
  UniformInPlaceMachine.rowOf,UniformInPlaceMachine.Locations.address,UniformCrossShearTableMachine.locations];norm_num

structure Header (g:Geometry) (c:UniformSixCDirtyReplayMachine.Config) (s:State) : Prop where
 dirty : UniformSixCDirtyReplayMachine.Header c s
 source : s.natReg 1181=g.source
 inputs : s.natReg 1052=g.inputs
 target : s.natReg 1182=g.target
 targets : s.natReg 1051=g.targets
 gates : s.natReg 1072=g.gates
 borrowed : s.natReg 1183=g.borrowed

lemma borrowedSetup_header (g:Geometry) (c:UniformSixCDirtyReplayMachine.Config) (s:State)
 (h:Header g c s) : UniformBorrowedCoordinateMachine.Headers g.source g.inputs g.target g.targets g.gates g.borrowed
 (applyBlock borrowedSetup s):=by
 simp [UniformBorrowedCoordinateMachine.Headers,borrowedSetup,applyBlock,Op.apply,writeNat,next,
  h.source,h.inputs,h.target,h.targets,h.gates,h.borrowed]
lemma borrowedSetup_safe (B:ℕ) (s:State) (bound:WordBound B s) :
 readable borrowedSetup s ∧ peak borrowedSetup s≤B:=by
 refine ⟨by simp [borrowedSetup,readable,Op.readable],?_⟩
 simp [borrowedSetup,peak,Op.peak,Op.apply,writeNat,next]
 exact ⟨bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _⟩
lemma setup_nat (positive:Bool) (s:State) (q:ℕ)
 (hs:q<261 ∨ 266<q) (hz:q≠3000) (hb:q<3100 ∨ 3105<q) (hn:q≠3030) :
 (applyBlock borrowedSetup s).natReg q=s.natReg q ∧
 (applyBlock (broadcastSetup positive) s).natReg q=s.natReg q:=by
 constructor <;> simp (disch:=omega) [borrowedSetup,broadcastSetup,applyBlock,Op.apply,writeNat,next]
lemma setup_heap (positive:Bool) (s:State) :
 (applyBlock borrowedSetup s).natHeap=s.natHeap ∧
 (applyBlock borrowedSetup s).scalarHeap=s.scalarHeap ∧
 (applyBlock borrowedSetup s).outputs=s.outputs ∧
 (applyBlock borrowedSetup s).rootOrders=s.rootOrders ∧
 (applyBlock (broadcastSetup positive) s).natHeap=s.natHeap ∧
 (applyBlock (broadcastSetup positive) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (broadcastSetup positive) s).outputs=s.outputs ∧
 (applyBlock (broadcastSetup positive) s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma borrowedSetup_zero (s:State) : (applyBlock borrowedSetup s).natReg 3000=0:=by
 simp [borrowedSetup,applyBlock,Op.apply,writeNat,next]
lemma Header.transport {g:Geometry} {c:UniformSixCDirtyReplayMachine.Config} {s u:State}
 (h:Header g c s) (dirty:∀q,3001≤q→q≤3020→u.natReg q=s.natReg q)
 (low:∀q,q=1181∨q=1052∨q=1182∨q=1051∨q=1072∨q=1183→u.natReg q=s.natReg q) : Header g c u:=by
 refine ⟨h.dirty.transport dirty,?_,?_,?_,?_,?_,?_⟩
 · exact (low _ (by simp)).trans h.source
 · exact (low _ (by simp)).trans h.inputs
 · exact (low _ (by simp)).trans h.target
 · exact (low _ (by simp)).trans h.targets
 · exact (low _ (by simp)).trans h.gates
 · exact (low _ (by simp)).trans h.borrowed
lemma broadcastSetup_header (positive:Bool) (g:Geometry) (c:UniformSixCDirtyReplayMachine.Config)
 (s:State) (h:Header g c s) (zero:s.natReg 3000=0) :
 UniformCrossBroadcastTableMachine.Header g.targets g.gates g.target g.borrowed c.inverse.forward
  (c.inverse.constants+(if positive then 1 else 0)) (applyBlock (broadcastSetup positive) s):=by
 constructor <;> simp [broadcastSetup,applyBlock,Op.apply,writeNat,next,zero,h.targets,h.gates,h.target,
  h.borrowed,h.dirty.rows,h.dirty.constants]
lemma broadcastSetup_safe (positive:Bool) (B:ℕ) (s:State) (bound:WordBound B s)
 (zero:s.natReg 3000=0) (extra:s.natReg 3008+1≤B) :
 readable (broadcastSetup positive) s ∧ peak (broadcastSetup positive) s≤B:=by
 refine ⟨by simp [broadcastSetup,readable,Op.readable],?_⟩
 cases positive <;> simp [broadcastSetup,peak,Op.peak,Op.apply,writeNat,next,zero]
 · exact ⟨bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,by omega⟩
 · exact ⟨bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,bound.2.1 _,extra⟩

attribute [local irreducible] borrowedSetup broadcastSetup UniformSixCDepthColorController.inverseInstall

/-- This signed phase prints its own borrowed-coordinate table and row/count
bank, then invokes the real inverse36/packing/six-C/scatter helper. The sign
in `word` is opposite to the executed broadcast; inverse683 performs the
negation and reversal physically. No borrowed or broadcast table is an entry. -/
theorem execution {R K B n:ℕ} (x:Fin n→ℂ) (positive:Bool) (g:Geometry)
 (c:UniformSixCDirtyReplayMachine.Config)
 (volume:c.inverse.packing.total=g.volume)
 (below:g.borrowed+g.gates≤c.inverse.forward)
 (l:UniformSixCInverseMatchingPreparation.Layout c.inverse g.targets R B)
 (bank:Fin R→ℂ) (v:Fin c.inverse.packing.total→Scalar) (s:State)
 (head:Header g c s)
 (src:UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (source:UniformSectorPackingMachine.SourceReady c.inverse.packing v s)
 (pc:s.pc=0) (bound:WordBound B s) (code:754≤B) :
 ∃ticks u middle,ticks≤461*g.volume+14*g.targets+149 ∧
 BoundedExecution (program positive) n x B s ticks u ∧ u.pc=753 ∧
 UniformSixCInverseMatchingPreparation.Result (K:=K) c.inverse (word positive g R)
  (UniformSixCInverseMatchingPreparation.reverse_matching _ (word_matching positive g R))
  (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total _
   (by rw [volume];exact word_range positive g R))
  l.radix bank v middle (setPC u 682) ∧
 (∀q,3001≤q→q≤3029→u.natReg q=s.natReg q) ∧
 (∀q,UniformSixCDepthColorController.readonly q=true→u.natReg q=s.natReg q) ∧
 (∀q,q<g.borrowed→u.natHeap q=s.natHeap q) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders :=by
 let a:=applyBlock borrowedSetup s
 have ap:a.pc=7:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,borrowedSetup_length]
 have saf:=borrowedSetup_safe B s bound
 have init:=block_runs borrowedSetup (program positive) 0 n B x s (borrowedSetup_code positive) pc bound
  (by rw [borrowedSetup_length];omega) saf.1 saf.2
 let e:=setPC a 0
 have eb:=changePC_bound B a 0 init.final_bound (by omega)
 have eh:UniformBorrowedCoordinateMachine.Headers g.source g.inputs g.target g.targets g.gates g.borrowed e:=borrowedSetup_header g c s head
 have vb:g.volume≤B:=by rw [←volume,←head.dirty.length];exact bound.2.1 _
 have rowsEnd:c.inverse.forward+3*g.targets≤B:=by
  have h:=l.packed.rowsBound
  change c.inverse.inverseRows+3*g.targets≤B at h
  have:=l.forwardBelow;omega
 have borrowedEnd:g.borrowed+g.gates≤B:=by omega
 obtain ⟨t1,z1,run1,cost1,borrow,frame1,out1⟩:=UniformBorrowedCoordinateMachine.physical_embedding n x
  g.volume g.source g.inputs g.target g.targets g.gates g.borrowed B e eh rfl eb (by omega) vb
  (g.sourceEnd.trans vb) (g.targetEnd.trans vb) borrowedEnd g.fit
 have first:=UniformBoundedAssembly.boundedExecution_placed (borrowed_code positive)
  (by rw [UniformBorrowedCoordinateMachine.program_length];omega) (by omega) run1
 rw [show placed 7 e=a by change {a with pc:=7}=a;rw [←ap]] at first
 let b:=setPC z1 24
 have bh:Header g c b:=head.transport
  (fun q lo hi=>(frame1.2.2.2.2 q (by omega)).trans ((setup_nat positive s q (by omega) (by omega) (by omega) (by omega)).1))
  (fun q hq=>(frame1.2.2.2.2 q (by omega)).trans ((setup_nat positive s q (by omega) (by omega) (by omega) (by omega)).1))
 have bz:b.natReg 3000=0:=(frame1.2.2.2.2 _ (by omega)).trans (borrowedSetup_zero s)
 have extra:b.natReg 3008+1≤B:=by
  rw [bh.dirty.constants]
  have h:=l.packed.coefficient
  have hb:=h.bound;have hc:=h.constantsBelow;have hv:=h.conjugatesBelow;have hd:=h.destinations
  change c.inverse.constants+6≤c.inverse.conjugates at hc
  change c.inverse.conjugates+R≤c.inverse.mu at hv
  change c.inverse.mu<c.inverse.conjugateMu at hd
  change c.inverse.conjugateMu≤B at hb
  omega
 have safe2:=broadcastSetup_safe positive B b first.final_bound bz extra
 have install2:=block_runs (broadcastSetup positive) (program positive) 24 n B x b
  (broadcastSetup_code positive) rfl first.final_bound (by rw [broadcastSetup_length];omega) safe2.1 safe2.2
 let d:=applyBlock (broadcastSetup positive) b
 have dp:d.pc=31:=by rw [UniformTensorMonomialMachine.applyBlock_pc,broadcastSetup_length];rfl
 let f:=setPC d 0
 have fb:=changePC_bound B d 0 install2.final_bound (by omega)
 have fh:UniformCrossBroadcastTableMachine.Header g.targets g.gates g.target g.borrowed c.inverse.forward
  (c.inverse.constants+(if positive then 1 else 0)) f:=by
  have h:=broadcastSetup_header positive g c b bh bz
  exact ⟨h.count,h.gates,h.target,h.borrowed,h.output,h.coefficient⟩
 have borrowed:UniformCrossBroadcastTableMachine.Borrowed g.borrowed g.gates g.borrowedAt f:=by
  intro j hj
  change d.natHeap _=_
  rw [(setup_heap positive b).2.2.2.2.1]
  change z1.natHeap _=_
  simpa only [Geometry.borrowedAt,dite_eq_left hj] using borrow ⟨j,hj⟩
 obtain ⟨z2,run2,rows2,bank2,out2,frame2,count2,pc2⟩:=UniformCrossBroadcastTableMachine.execution n B
  g.targets g.gates g.target g.borrowed c.inverse.forward (c.inverse.constants+(if positive then 1 else 0))
  x g.borrowedAt f fh rfl g.ag borrowed below rowsEnd (g.targetEnd.trans vb) fb (by omega)
 have second:=UniformBoundedAssembly.boundedExecution_placed (broadcast_code positive)
  (by rw [UniformCrossBroadcastTableMachine.program_length];omega) (by omega) run2
 rw [show placed 31 f=d by change {d with pc:=31}=d;rw [←dp]] at second
 let h:=setPC z2 51
 have hh:UniformSixCDirtyReplayMachine.Header c h:=bh.dirty.transport (by
  intro q lo hi
  exact (frame2.2.2.2.2 q (by omega) (by omega)).trans
   ((setup_nat positive b q (by omega) (by omega) (by omega) (by omega)).2))
 have safe3:=UniformSixCDepthColorController.inverseInstall_safe B h second.final_bound (by omega)
 have install3:=block_runs UniformSixCDepthColorController.inverseInstall (program positive) 51 n B x h
  (install_code positive) rfl second.final_bound
  (by rw [UniformSixCDepthColorController.inverseInstall_length];omega) safe3.1 safe3.2
 let k:=applyBlock UniformSixCDepthColorController.inverseInstall h
 have kp:k.pc=70:=by rw [UniformTensorMonomialMachine.applyBlock_pc,UniformSixCDepthColorController.inverseInstall_length];rfl
 let m:=setPC k 0
 have mb:=changePC_bound B k 0 install3.final_bound (by omega)
 have mh:UniformSixCInverseMatchingPreparation.Header c.inverse m:=
  (UniformSixCDepthColorController.inverseInstall_args c h hh).transport (fun _ _ _=>rfl)
 have mc:m.natReg 894=(word positive g R).length:=by
  rw [word_length]
  change k.natReg 894=g.targets
  rw [UniformSixCDepthColorController.inverseInstall_count];exact count2
 have mt:UniformInverseShearTableMachine.Rows c.inverse.forward
  (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants (word positive g R)) m:=by
  rw [word_rows]
  intro i hi
  change k.natHeap _=_ ∧ k.natHeap _=_ ∧ k.natHeap _=_
  rw [(UniformSixCDepthColorController.inverseInstall_frame h).1]
  have tab:=UniformCrossBroadcastTableMachine.rows_table rows2
  exact tab i hi
 have scalarEq:m.scalarHeap=s.scalarHeap:=by
  change k.scalarHeap=s.scalarHeap
  rw [(UniformSixCDepthColorController.inverseInstall_frame h).2.1]
  change z2.scalarHeap=s.scalarHeap
  rw [frame2.1]
  change d.scalarHeap=s.scalarHeap
  rw [(setup_heap positive b).2.2.2.2.2.1]
  change z1.scalarHeap=s.scalarHeap
  rw [frame1.1]
  exact (setup_heap positive s).2.1
 have ms:UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank m:=by
  constructor
  · intro i;rw [scalarEq];exact src.positive i
  · intro i;rw [scalarEq];exact src.negative i
  · intro i;rw [scalarEq];exact src.conjugate i
  · intro i hi;rw [scalarEq];exact src.constants i hi
 have mhc:UniformHadamardPairMachine.Constants m:=by
  unfold UniformHadamardPairMachine.Constants;rw [scalarEq];exact constants
 have md:UniformSectorPackingMachine.SourceReady c.inverse.packing v m:=by
  intro i;rw [scalarEq];exact source i
 have wl:(word positive g R).length=g.targets:=word_length positive g R
 have lw:UniformSixCInverseMatchingPreparation.Layout c.inverse (word positive g R).length R B:=by rw [wl];exact l
 have hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total
  (UniformSixCInverseMatchingPreparation.forwardEdges (word positive g R)):=by rw [volume];exact word_range positive g R
 obtain ⟨t3,z3,cost3,run3,res⟩:=UniformSixCInverseMatchingPreparation.execution x c.inverse (word positive g R)
  lw (word_matching positive g R) hr bank v m mh mc mt (word_good positive g R K) ms mhc md rfl mb
 have third:=UniformBoundedAssembly.boundedExecution_placed (inverse_code positive)
  (by rw [UniformSixCInverseMatchingPreparation.program_length];omega) (by omega) run3
 rw [show placed 70 m=k by change {k with pc:=70}=k;rw [←kp]] at third
 let u:=setPC z3 753
 have halt:BoundedExecution (program positive) n x B u 1 u:=.halt third.final_bound
  (by simp [step,u,setPC,halt_at])
 have finalRun:BoundedExecution (program positive) n x B s
  (7+t1+7+(14*g.targets+7)+19+t3+1) u:=by
  simpa only [borrowedSetup_length,broadcastSetup_length,UniformSixCDepthColorController.inverseInstall_length,Nat.add_assoc]
   using init.executes (first.executes (install2.executes (second.executes (install3.executes (third.executes halt)))))
 refine ⟨_,u,m,?_,finalRun,rfl,?_,?_,?_,?_,?_,?_,?_⟩
 · have:=UniformSixCInverseMatchingPreparation.runtime_linear lw
   rw [volume] at this
   omega
 · have eq:setPC u 682=z3:=by change {z3 with pc:=682}=z3;rw [←res.pc]
   rw [eq];exact res
 · intro q lo hi
   have keep:UniformSixCInverseMatchingPreparation.KeepNat q:=Or.inr (Or.inr (by omega))
   exact (res.nats q keep (by omega)).trans
    ((UniformSixCDepthColorController.inverseInstall_high h q lo).trans
     ((frame2.2.2.2.2 q (by omega) (by omega)).trans
      (((setup_nat positive b q (by omega) (by omega) (by omega) (by omega)).2).trans
       ((frame1.2.2.2.2 q (by omega)).trans ((setup_nat positive s q (by omega) (by omega) (by omega) (by omega)).1)))))
 · intro q read
   have range:=read
   simp only [UniformSixCDepthColorController.readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
   have keep: z3.natReg q=m.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat run3.executes
    (UniformSixCDepthColorController.inverse_keeps_readonly q read)
   exact keep.trans ((by
     simp (disch:=omega) [UniformSixCDepthColorController.inverseInstall,UniformSixCDirtyReplayMachine.inverseSetup,
      applyBlock,Op.apply,writeNat,next] : (applyBlock UniformSixCDepthColorController.inverseInstall h).natReg q=h.natReg q).trans
    ((frame2.2.2.2.2 q (by omega) (by omega)).trans
     (((setup_nat positive b q (by omega) (by omega) (by omega) (by omega)).2).trans
      ((frame1.2.2.2.2 q (by omega)).trans ((setup_nat positive s q (by omega) (by omega) (by omega) (by omega)).1)))))
 · intro q hq
   have inv:q<c.inverse.inverseRows:=by have:=l.forwardBelow;omega
   have axis:q<c.inverse.axis:=by have:=l.inverseBelow;have:=l.permutationBelow;have:=l.widthsBelow;have:=l.markersBelow;omega
   have suffix:q<c.inverse.packing.suffix:=by have:=c.inverse.packing.rowsBelow;rw [l.axisRow] at this;omega
   have stack:q<c.inverse.packing.stack:=by have:=c.inverse.packing.suffixBelow;omega
   have inverse:q<c.inverse.packing.inverse:=by have:=c.inverse.packing.stackBelow;omega
   change z3.natHeap q=s.natHeap q
   rw [res.natOutside q (Or.inl inv) (Or.inl suffix) (Or.inl stack) (Or.inl inverse)]
   change k.natHeap q=s.natHeap q
   rw [(UniformSixCDepthColorController.inverseInstall_frame h).1]
   change z2.natHeap q=s.natHeap q
   rw [out2 q (Or.inl (by omega))]
   change d.natHeap q=s.natHeap q
   rw [(setup_heap positive b).2.2.2.2.1]
   change z1.natHeap q=s.natHeap q
   rw [out1 q (Or.inl hq)]
   exact congrFun (setup_heap positive s).1 q
 · intro q stable
   exact (res.scalarHeap q stable).trans (congrFun scalarEq q)
 · exact res.outputs.trans ((UniformSixCDepthColorController.inverseInstall_frame h).2.2.1.trans
   (frame2.2.2.1.trans ((setup_heap positive b).2.2.2.2.2.2.1.trans (frame1.2.2.1.trans (setup_heap positive s).2.2.1))))
 · exact res.rootOrders.trans ((UniformSixCDepthColorController.inverseInstall_frame h).2.2.2.trans
   (frame2.2.2.2.1.trans ((setup_heap positive b).2.2.2.2.2.2.2.trans (frame1.2.2.2.1.trans (setup_heap positive s).2.2.2.1))))

end
end ExactFourierCircuits.UniformSixCBroadcast
