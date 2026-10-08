import UniformChunkMatchingPreparation
import UniformSectorNetworkAction

set_option autoImplicit false

/-! Actual matching-table production followed by charged sector packing.
This module moves tagged input data and computes inverse packing addresses.
It does not execute the six-C matching rounds or restore the packed workspace.
-/
namespace ExactFourierCircuits.UniformMatchingPackingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
abbrev MatchingParameters := UniformChunkMatchingPreparation.Parameters

/-- Caller 1400..1404 supplies ordinary allocation bases, not generated tables.
1405 is a freshly initialized zero. All seven packing headers are installed
by literal charged operations after Matching215 has printed its axis. -/
def setup : List Op := [.literal 1405 0,.literal 600 1,
 .add 601 1190 1405,.add 602 1400 1405,.add 603 1401 1405,
 .add 637 1402 1405,.add 604 1403 1405,.add 605 1404 1405]
def beforePacking : Program :=
 UniformChunkMatchingPreparation.program.map (relocate 0 215) ++ setup.map Op.code
def program : Program := beforePacking ++
 UniformSectorPackingMachine.program.map (relocate 223 360) ++ [.halt]
theorem setup_length : setup.length=8 := rfl
theorem beforePacking_length : beforePacking.length=223 := by
 simp [beforePacking,UniformChunkMatchingPreparation.program_length,setup_length]
theorem program_length : program.length=361 := by
 simp [program,beforePacking_length,UniformSectorPackingMachine.program_length]
theorem matching_code : CodeAt UniformChunkMatchingPreparation.program program 0 215 := by
 let tail:=setup.map Op.code ++ UniformSectorPackingMachine.program.map (relocate 223 360) ++ [.halt]
 have eqn:program=[] ++ UniformChunkMatchingPreparation.program.map (relocate 0 215) ++ tail:=by
  simp [program,beforePacking,tail,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code [] tail _ 0 215 rfl
theorem setup_code : BlockAt setup program 215 := by
 intro i hi
 simp only [program,beforePacking,List.append_assoc,List.getElem?_append,
  List.length_map,UniformChunkMatchingPreparation.program_length]
 rw [ite_eq_right (by omega)]
 simp only [Nat.add_sub_cancel_left]
 rw [ite_eq_left hi]
 rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hi)]
 simp only [List.getElem_map]
theorem packing_code : CodeAt UniformSectorPackingMachine.program program 223 360 := by
 unfold program
 exact UniformChunkRowTableMachine.segment_code beforePacking [.halt] _ 223 360 beforePacking_length
theorem halt_at : program[360]?=some .halt := by
 have len:(beforePacking ++ UniformSectorPackingMachine.program.map (relocate 223 360)).length=360:=by
  simp [beforePacking_length,UniformSectorPackingMachine.program_length]
 unfold program
 rw [List.getElem?_append,ite_eq_right (by rw [len];omega),len]
 rfl

noncomputable section

structure Layout (p : MatchingParameters) (B : ℕ) where
 matching : UniformChunkMatchingPreparation.Layout p B
 packing : UniformSectorPackingMachine.Layout
 bound : packing.B=B
 oneAxis : packing.ell=1
 axisRow : packing.rows=p.axis
 volume : packing.total=p.radix
 code : 361 ≤ B

structure Header {p : MatchingParameters} {B : ℕ} (l : Layout p B) (s : State) : Prop where
 matching : UniformChunkMatchingPreparation.Header p s
 suffix : s.natReg 1400=l.packing.suffix
 stack : s.natReg 1401=l.packing.stack
 inverse : s.natReg 1402=l.packing.inverse
 source : s.natReg 1403=l.packing.source
 destination : s.natReg 1404=l.packing.destination

def Protected (j : ℕ) : Prop := UniformChunkMatchingPreparation.Protected j ∧
 (j<600 ∨ 650≤j) ∧ j≠1405
def Frame (s u : State) : Prop := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,Protected j→u.natReg j=s.natReg j) ∧
 (∀j,j≠70→u.scalarReg j=s.scalarReg j)
def Outside {p : MatchingParameters} {B : ℕ} (l : Layout p B) (s u : State) : Prop :=
 ∀j,(j<p.borrowed ∨ l.packing.inverse+l.packing.total≤j)→u.natHeap j=s.natHeap j

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.1.trans f.1,g.2.1.trans f.2.1,
 fun j h=>(g.2.2.1 j h).trans (f.2.2.1 j h),
 fun j h=>(g.2.2.2 j h).trans (f.2.2.2 j h)⟩
theorem matching_frame {s u : State} (f:UniformChunkMatchingPreparation.Frame s u) : Frame s u :=
 ⟨f.2.2.1,f.2.2.2.1,fun j h=>f.2.2.2.2 j h.1,fun j _=>congrFun f.2.1 j⟩
theorem packing_frame {s u : State} (f:UniformSectorPackingMachine.FinalFrame s u) : Frame s u :=
 ⟨f.1,f.2.1,fun j h=>f.2.2.1 j (by have :=h.2.1;omega),f.2.2.2⟩
theorem setup_frame (s : State) : Frame s (applyBlock setup s) := by
 refine ⟨rfl,rfl,?_,fun _ _=>rfl⟩
 intro j h
 unfold Protected at h
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
theorem setup_heaps (s : State) :
 (applyBlock setup s).natHeap=s.natHeap ∧ (applyBlock setup s).scalarHeap=s.scalarHeap := ⟨rfl,rfl⟩

theorem Header.transport {p : MatchingParameters} {B : ℕ} {l : Layout p B} {s u : State}
 (h:Header l s) (f:Frame s u) : Header l u := by
 refine ⟨⟨h.matching.height.transport_register (fun j lo hi=>f.2.2.1 j
  (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)),
  ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.radix
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.source
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.target
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.borrowed
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.selected
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.ordinals
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.mapped
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.permutation
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.widths
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.markers
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.axis
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.depth
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.matching.color
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.suffix
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.stack
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.inverse
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.source
 | exact (f.2.2.1 _ (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)).trans h.destination

theorem Header.matching_transport {p : MatchingParameters} {B : ℕ} {l : Layout p B} {s u : State}
 (h:Header l s) (f:UniformChunkMatchingPreparation.Frame s u) : Header l u := by
 refine ⟨h.matching.transport f,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (f.2.2.2.2 _ (by unfold UniformChunkMatchingPreparation.Protected;omega)).trans h.suffix
 | exact (f.2.2.2.2 _ (by unfold UniformChunkMatchingPreparation.Protected;omega)).trans h.stack
 | exact (f.2.2.2.2 _ (by unfold UniformChunkMatchingPreparation.Protected;omega)).trans h.inverse
 | exact (f.2.2.2.2 _ (by unfold UniformChunkMatchingPreparation.Protected;omega)).trans h.source
 | exact (f.2.2.2.2 _ (by unfold UniformChunkMatchingPreparation.Protected;omega)).trans h.destination

theorem setup_header {p : MatchingParameters} {B : ℕ} {l : Layout p B} {s : State}
 (h:Header l s) : UniformSectorPackingMachine.Header l.packing (applyBlock setup s) := by
 constructor
 all_goals simp [setup,applyBlock,Op.apply,writeNat,next,h.matching.axis,h.suffix,h.stack,h.inverse,
  h.source,h.destination,l.oneAxis,l.axisRow]

theorem setup_safe {s : State} {B : ℕ} (bound:WordBound B s) (code:361≤B) :
 readable setup s ∧ peak setup s≤B := by
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 repeat' constructor
 all_goals first | exact bound.2.1 _ | omega

variable {r : ℕ}

theorem axis_volume {p : MatchingParameters} {B : ℕ} (l:Layout p B)
 (W : List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 UniformSectorPackingMachine.physicalVolume [UniformChunkMatchingPreparation.axis l.matching W dom degree]=l.packing.total := by
 have cap:=UniformMatchingAxisTableMachine.matching_capacity p.radix
  (UniformChunkMatchingPreparation.physicalEdges l.matching W dom)
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom)
 change (UniformMatchingAxisTableMachine.widths p.radix (UniformChunkMatchingPreparation.indices p W).length).sum*1=l.packing.total
 rw [UniformMatchingAxisTableMachine.widths_sum p.radix _ cap,Nat.mul_one,l.volume]

theorem layout_order {p : MatchingParameters} {B : ℕ} (l:Layout p B) :
 p.axis+4≤l.packing.suffix ∧ l.packing.suffix≤l.packing.stack ∧
 l.packing.stack≤l.packing.inverse := by
 have h:=l.packing.rowsBelow
 rw [l.oneAxis,l.axisRow] at h
 exact ⟨by omega,by have :=l.packing.suffixBelow;omega,by have :=l.packing.stackBelow;omega⟩

theorem axis_below {p : MatchingParameters} {B : ℕ} (l:Layout p B)
 (W : List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 (∀a∈[UniformChunkMatchingPreparation.axis l.matching W dom degree],
   a.widthsBase+a.geometry.widths.length≤l.packing.suffix) ∧
 (∀a∈[UniformChunkMatchingPreparation.axis l.matching W dom degree],
   a.permutationBase+a.geometry.widths.sum≤l.packing.suffix) := by
 have cap:=UniformMatchingAxisTableMachine.matching_capacity p.radix
  (UniformChunkMatchingPreparation.physicalEdges l.matching W dom)
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom)
 have q:=layout_order l
 have f:=l.matching.widthsFresh
 have g:=l.matching.markersFresh
 have h:=l.matching.permutationFresh
 constructor
 · intro a ha
   have eqn:a=UniformChunkMatchingPreparation.axis l.matching W dom degree:=by simpa using ha
   subst a
   change p.widths+(UniformMatchingAxisTableMachine.widths p.radix (UniformChunkMatchingPreparation.indices p W).length).length≤_
   rw [UniformMatchingAxisTableMachine.widths_length _ _ cap]
   omega
 · intro a ha
   have eqn:a=UniformChunkMatchingPreparation.axis l.matching W dom degree:=by simpa using ha
   subst a
   change p.permutation+(UniformMatchingAxisTableMachine.widths p.radix (UniformChunkMatchingPreparation.indices p W).length).sum≤_
   rw [UniformMatchingAxisTableMachine.widths_sum _ _ cap]
   omega

/-- Actual Matching215 followed immediately by generated-address packing137.
All helper halts become charged jumps; no host write occurs between phases.
Only the genuine earlier logical bucket/color cells and input scalars enter.
The packed data is a fresh output; no scratch-restoration claim is made. -/
theorem execution {p : MatchingParameters} {B n : ℕ} {x : Fin n→ℂ}
 (W : List (UniformReplayPrint.ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r)
 (l:Layout p B) (v:Fin l.packing.total→Scalar) (s:State) (h:Header l s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table
  (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃ticks u,
 ticks≤4*p.height.K+393*p.radix+121 ∧ BoundedExecution program n x B s ticks u ∧ u.pc=360 ∧
 Header l u ∧ u.natReg 894=(UniformChunkMatchingPreparation.indices p W).length ∧
 UniformSectorPackingMachine.InverseReady l.packing
  (UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
   l.packing (axis_volume l W dom degree)) u ∧
 (∀i:Fin l.packing.total,u.scalarHeap (l.packing.destination+i.val)=some
  (v (UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
   l.packing (axis_volume l W dom degree) i))) ∧
 (∀i:Fin l.packing.total,u.scalarHeap (l.packing.source+i.val)=s.scalarHeap (l.packing.source+i.val)) ∧
 (∀q,(q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q)→u.scalarHeap q=s.scalarHeap q) ∧
 UniformCrossShearTableMachine.Table p.mapped (UniformChunkMatchingPreparation.mappedRows p l.matching.capacity W loc) u ∧
 Outside l s u ∧ Frame s u := by
 obtain ⟨tm,a,cm,runM,head,count,rows,widths,perms,mapped,outM,frameM⟩:=
  UniformChunkMatchingPreparation.execution (n:=n) (x:=x) W loc s l.matching h.matching
   size record table colors dom degree pc bound
 have movedM:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformChunkMatchingPreparation.program_length];have :=l.code;omega)
  (by have :=l.code;omega) runM
 rw [show placed 0 s=s by cases s;simp [placed]] at movedM
 let a':State:=setPC a 215
 have ha:Header l a':=h.matching_transport frameM
 have hs:=setup_safe movedM.final_bound l.code
 have runS:=block_runs setup program 215 n B x a' setup_code rfl movedM.final_bound
  (by rw [setup_length];have :=l.code;omega) hs.1 hs.2
 let b:=applyBlock setup a'
 have bp:b.pc=223:=by rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
 have hb:=setup_header ha
 have scalar:b.scalarHeap=s.scalarHeap:=frameM.1
 have bSource:UniformSectorPackingMachine.SourceReady l.packing v (setPC b 0):=by
  intro i
  rw [show (setPC b 0).scalarHeap=s.scalarHeap from scalar]
  exact source i
 have bRows:UniformSectorPackingMachine.Rows
  [UniformChunkMatchingPreparation.axis l.matching W dom degree] 0 l.packing.rows (setPC b 0):=by
  rw [l.axisRow]
  exact rows
 have below:=axis_below l W dom degree
 obtain ⟨c,tp,cp,runP,cpPC,inverse,packed,scalarOutside,natOutside,frameP⟩:=
  UniformSectorPackingMachine.execution [UniformChunkMatchingPreparation.axis l.matching W dom degree]
   l.packing n x v (setPC b 0) (by simp [l.oneAxis]) (axis_volume l W dom degree)
   (UniformSectorPackingMachine.header_setPC l.packing b 0 hb) bRows widths perms below.1 below.2 bSource rfl
   (by rw [l.bound];exact changePC_bound B b 0 runS.final_bound (by have :=l.code;omega))
 have movedP:=UniformBoundedAssembly.boundedExecution_placed packing_code
  (by rw [UniformSectorPackingMachine.program_length];rw [l.bound];have :=l.code;omega)
  (by rw [l.bound];have :=l.code;omega) runP
 rw [UniformChunkMatchingPreparation.placed_zero b 223 bp,l.bound] at movedP
 let u:=setPC c 360
 have stop:BoundedExecution program n x B u 1 u:=
  .halt movedP.final_bound (by simp [step,u,setPC,halt_at])
 have heapLow:∀q,q<l.packing.suffix→u.natHeap q=a.natHeap q:=by
  intro q hq
  exact UniformSectorPackingMachine.protected_prefix l.packing (setPC b 0) c natOutside q hq
 have countU:u.natReg 894=(UniformChunkMatchingPreparation.indices p W).length:=by
  rw [show u.natReg 894=b.natReg 894 from frameP.2.2.1 894 (Or.inr (Or.inl (by omega)))]
  simpa [b,a',setup,applyBlock,Op.apply,writeNat,next,setPC] using count
 have fS:=setup_frame a'
 have fP:=packing_frame frameP
 have frame:Frame s u:=(matching_frame frameM).trans (fS.trans fP)
 have outside:Outside l s u:=by
  intro q hq
  have order:=layout_order l
  have lo:=l.matching.borrowFresh
  have lo1:=l.matching.selectedFresh
  have lo2:=l.matching.ordinalFresh
  have lo3:=l.matching.mappedFresh
  have lo4:=l.matching.permutationFresh
  have lo5:=l.matching.widthsFresh
  have lo6:=l.matching.markersFresh
  have se:=l.packing.suffixBelow
  have st:=l.packing.stackBelow
  have one:=l.oneAxis
  have total:=l.volume
  have positive:=l.matching.radixPositive
  have eqn:u.natHeap q=a.natHeap q:=natOutside q (by omega) (by omega) (by omega)
  rw [eqn]
  exact outM q (by omega)
 have outScalar:∀q,(q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q)→
  u.scalarHeap q=s.scalarHeap q:=by
  intro q hq
  exact (scalarOutside q hq).trans (congrFun scalar q)
 have sourceKept:∀i:Fin l.packing.total,u.scalarHeap (l.packing.source+i.val)=s.scalarHeap (l.packing.source+i.val):=by
  intro i
  exact outScalar _ (Or.inl (by have :=l.packing.sourceBelow;have :=i.isLt;omega))
 have mappedU:UniformCrossShearTableMachine.Table p.mapped
  (UniformChunkMatchingPreparation.mappedRows p l.matching.capacity W loc) u:=by
  apply UniformChunkMatchingPreparation.table_transport mapped
  intro q lo hi
  apply heapLow
  have small: (UniformChunkMatchingPreparation.indices p W).length≤2*UniformCrossHeightPreparationMachine.gates p.height:=
   (UniformChunkMatchingPreparation.selected_count p W).trans size
  simp only [UniformChunkMatchingPreparation.mappedRows,UniformChunkMatchingPreparation.selectedRows,List.length_map] at hi
  have order:=layout_order l
  have a:=l.matching.mappedFresh
  have b:=l.matching.permutationFresh
  have c:=l.matching.widthsFresh
  have d:=l.matching.markersFresh
  omega
 refine ⟨tm+8+tp+1,u,?_,?_,rfl,?_,countU,inverse,packed,sourceKept,outScalar,mappedU,outside,frame⟩
 · rw [l.volume] at cp
   omega
 · convert (movedM.trans (runS.trans movedP)).executes stop using 1
   simp only [setup_length]
   omega
 · exact h.transport frame

theorem saved_metadata {s u : State} (f:Frame s u) (j : ℕ) (lo:100≤j) (hi:j≤106) :
 u.natReg j=s.natReg j := f.2.2.1 j (by unfold Protected UniformChunkMatchingPreparation.Protected;omega)

/-- External prepared coefficient banks have exact value and flag retention,
whenever their physical cells lie outside the destination interval. -/
theorem coefficient_retained {p : MatchingParameters} {B : ℕ} {l : Layout p B} {s u : State}
 (outside:∀q,(q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q)→u.scalarHeap q=s.scalarHeap q)
 (q : ℕ) (safe:q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q) :
 u.scalarHeap q=s.scalarHeap q := outside q safe

theorem processed_retained {p : MatchingParameters} {B Z G : ℕ} {l : Layout p B}
 {printed:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize p.height.K) p.height.e G}
 {s u : State} (size:G=UniformCrossHeightPreparationMachine.gates p.height)
 (h:UniformCrossHeightPreparationMachine.Processed p.height Z printed
  (UniformCrossHeightPreparationMachine.height p.height) s)
 (outside:Outside l s u) : UniformCrossHeightPreparationMachine.Processed p.height Z printed
  (UniformCrossHeightPreparationMachine.height p.height) u := by
 intro d hd
 obtain ⟨table,col,rec⟩:=h d hd
 have len: (UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length≤
  2*UniformCrossHeightPreparationMachine.gates p.height:=
  (UniformCrossHeightPreparationMachine.bucket_length printed p.height.enabled d).trans (by rw [size])
 have rr:=l.matching.oldRows
 have cc:=l.matching.oldColors
 have dd:=l.matching.oldDirectory
 have rh:UniformCrossHeightPreparationMachine.rowBase p.height d+
  3*(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.rowBase] at rr ⊢
  nlinarith
 have ch:UniformCrossHeightPreparationMachine.colorBase p.height d+
  (UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.colorBase] at cc ⊢
  nlinarith
 have dh:UniformCrossHeightPreparationMachine.recordBase p.height d+3≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.recordBase] at dd ⊢
  omega
 refine ⟨?_,?_,?_⟩
 · apply UniformChunkMatchingPreparation.table_transport table
   intro q lo hi
   simp only [List.length_map] at hi
   exact outside q (Or.inl (lt_of_lt_of_le hi rh))
 · intro i
   rw [outside _ (Or.inl (by have :=i.isLt;omega))]
   exact col i
 · unfold UniformCrossHeightPreparationMachine.Record
   rw [outside _ (Or.inl (by omega)),outside _ (Or.inl (by omega)),outside _ (Or.inl (by omega))]
   exact rec

/-- Produced operational postconditions; this structure is an output, never
an input readiness/action certificate. -/
structure Result {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r)
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (v:Fin l.packing.total→Scalar) (s u:State) : Prop where
 pc : u.pc=360
 header : Header l u
 count : u.natReg 894=(UniformChunkMatchingPreparation.indices p W).length
 inverse : UniformSectorPackingMachine.InverseReady l.packing
  (UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
   l.packing (axis_volume l W dom degree)) u
 packed : ∀i:Fin l.packing.total,u.scalarHeap (l.packing.destination+i.val)=some
  (v (UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
   l.packing (axis_volume l W dom degree) i))
 source : ∀i:Fin l.packing.total,u.scalarHeap (l.packing.source+i.val)=s.scalarHeap (l.packing.source+i.val)
 scalarOutside : ∀q,(q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q)→u.scalarHeap q=s.scalarHeap q
 mapped : UniformCrossShearTableMachine.Table p.mapped (UniformChunkMatchingPreparation.mappedRows p l.matching.capacity W loc) u
 outside : Outside l s u
 frame : Frame s u

theorem execution_result {p : MatchingParameters} {B n : ℕ} {x : Fin n→ℂ}
 (W : List (UniformReplayPrint.ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r)
 (l:Layout p B) (v:Fin l.packing.total→Scalar) (s:State) (h:Header l s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table
  (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃ticks u,
 ticks≤4*p.height.K+393*p.radix+121 ∧ BoundedExecution program n x B s ticks u ∧
 Result l W loc dom degree v s u := by
 obtain ⟨ticks,u,cost,run,upc,head,count,inverse,packed,src,outScalar,mapped,out,frame⟩:=
  execution W loc l v s h size record table colors dom degree source pc bound
 exact ⟨ticks,u,cost,run,⟨upc,head,count,inverse,packed,src,outScalar,mapped,out,frame⟩⟩

/-- The generated output is the actual canonical sector packing action. -/
theorem Result.packArray {p:MatchingParameters} {B:ℕ} {l:Layout p B}
 {W:List (UniformReplayPrint.ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r}
 {dom:UniformChunkMatchingPreparation.CodesDomain p W}
 {degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6}
 {v:Fin l.packing.total→Scalar} {s u:State} (h:Result l W loc dom degree v s u) (i:Fin l.packing.total) :
 u.scalarHeap (l.packing.destination+i.val)=some
  (UniformSectorPacking.packArray
   (UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree])
   (fun j=>v (finCongr (axis_volume l W dom degree) j)) ((finCongr (axis_volume l W dom degree)).symm i)) :=
 h.packed i

/-- One actual color of one corrected-cross bucket, starting from genuine
Height output and original physical scalar inputs. All matching and packing
banks are computed inside this continuous charged program. -/
theorem cross_execution (p:MatchingParameters) (Z B n:ℕ) (x:Fin n→ℂ)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (l:Layout p B) (v:Fin l.packing.total→Scalar) (s:State) (header:Header l s)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height Z
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) s)
 (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃ticks u,
 ticks≤4*p.height.K+393*p.radix+121 ∧ BoundedExecution program n x B s ticks u ∧
 Result l (UniformChunkMatchingPreparation.crossWord p ha he)
  (UniformChunkMatchingPreparation.crossLocations p Z) (UniformChunkMatchingPreparation.cross_domain p ha he)
  (UniformChunkMatchingPreparation.cross_degree p ha he) v s u ∧
 UniformCrossHeightPreparationMachine.Processed p.height Z
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) u := by
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 obtain ⟨table,col,record⟩:=processed p.depth l.matching.depthBound
 have size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [W,UniformChunkMatchingPreparation.crossWord,UniformCrossHeightPreparationMachine.cross_size p.height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length
    (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled p.depth
 have cols:∀i:Fin W.length,s.natHeap
  (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
   some (UniformChunkMatchingPreparation.colors W i.val):=fun i=>col i
 obtain ⟨ticks,u,cost,run,result⟩:=
  execution_result (n:=n) (x:=x) W (UniformChunkMatchingPreparation.crossLocations p Z) l v s header size record table cols
   (UniformChunkMatchingPreparation.cross_domain p ha he) (UniformChunkMatchingPreparation.cross_degree p ha he)
   source pc bound
 refine ⟨ticks,u,cost,run,result,?_⟩
 exact processed_retained (l:=l)
  (printed:=(UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program)
  (UniformCrossHeightPreparationMachine.cross_size p.height ha he) processed result.outside

/-- Algebraic consequence for the exact axis printed and consumed above.
The packing coordinates separate the C-pair/singleton blocks. This identity
does not charge or assert execution of those C blocks. -/
theorem packing_sector_tensor {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 let axes:=UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree]
 Matrix.reindex (UniformSectorPacking.packingPermutation axes) (UniformSectorPacking.packingPermutation axes)
  (UniformSectorTensor.originalTensor axes)=UniformSectorTensor.packedTensor axes :=
 UniformSectorTensor.packing_tensor _

theorem sector_C_tensor {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (c:UniformSectorPacking.BlockChoices
  (UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree])) :
 let axes:=UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree]
 Matrix.reindex (UniformSectorNetworkAction.networkCoordinates axes c) (UniformSectorNetworkAction.networkCoordinates axes c)
  (UniformSectorTensor.sectorMatrix axes c)=OAI.ExactFourier.tensorPower ExactFourierCircuits.C
   (UniformSectorPacking.sectorPairCount axes c) := UniformSectorNetworkAction.sectorMatrix_network _ _


open ExactFourierCircuits UniformMatchingAxisTableMachine UniformColoring

theorem paired_left {M : ℕ} (E : Fin M→Edge) (i : Fin M) :
 (paired E)[2*i.val]?=some (E i).left := by
 induction M with
 | zero=>exact Fin.elim0 i
 | succ M ih=>
   refine Fin.cases ?_ (fun j=>?_) i
   · simp [paired,List.finRange_succ]
   · simp only [paired,List.finRange_succ,List.flatMap_cons,List.flatMap_map,List.cons_append,List.nil_append,Fin.val_succ]
     rw [show 2*(j.val+1)=(2*j.val+1)+1 by omega]
     simp only [List.getElem?_cons_succ]
     exact ih (fun j=>E j.succ) j

theorem paired_right {M : ℕ} (E : Fin M→Edge) (i : Fin M) :
 (paired E)[2*i.val+1]?=some (E i).right := by
 induction M with
 | zero=>exact Fin.elim0 i
 | succ M ih=>
   refine Fin.cases ?_ (fun j=>?_) i
   · simp [paired,List.finRange_succ]
   · simp only [paired,List.finRange_succ,List.flatMap_cons,List.flatMap_map,List.cons_append,List.nil_append,Fin.val_succ]
     rw [show 2*(j.val+1)+1=((2*j.val+1)+1)+1 by omega]
     simp only [List.getElem?_cons_succ]
     exact ih (fun j=>E j.succ) j
open UniformSectorPacking UniformTraversal

theorem single_packed_value (a:Axis) (b:Fin a.widths.length) (t:Fin (a.widths.get b)) :
 (packedEquiv [a] ⟨(b,()),(t,())⟩).val=blockBefore a.widths b+t.val := by
 rw [packedEquiv_value]
 simp [sectorStart,UniformSectorPacking.radices,sectorRadices,encode]

theorem single_original_value (a:Axis) (b:Fin a.widths.length) (t:Fin (a.widths.get b)) :
 (originalEquiv [a] ⟨(b,()),(t,())⟩).val=(a.originalPermutation (blockEncode a.widths ⟨b,t⟩)).val := by
 change 0+1*(a.originalPermutation (blockEncode a.widths ⟨b,t⟩)).val=_
 simp

theorem ordered_left {M:ℕ} (r:ℕ) (E:Fin M→Edge) (i:Fin M) :
 (ordered r E)[2*i.val]?=some (E i).left := by
 unfold ordered
 rw [List.getElem?_append,ite_eq_left (by rw [paired_length];have :=i.isLt;omega)]
 exact paired_left E i

theorem ordered_right {M:ℕ} (r:ℕ) (E:Fin M→Edge) (i:Fin M) :
 (ordered r E)[2*i.val+1]?=some (E i).right := by
 unfold ordered
 rw [List.getElem?_append,ite_eq_left (by rw [paired_length];have :=i.isLt;omega)]
 exact paired_right E i

def pairBlock {M:ℕ} (r:ℕ) (cap:2*M≤r) (i:Fin M) : Fin (widths r M).length :=
 ⟨i.val,by rw [widths_length _ _ cap];have :=i.isLt;omega⟩

theorem pair_width {M:ℕ} (r:ℕ) (cap:2*M≤r) (i:Fin M) :
 (widths r M).get (pairBlock r cap i)=2 := by
 simp only [List.get_eq_getElem,pairBlock,widths]
 rw [List.getElem_append_left (by simp only [List.length_replicate];exact i.isLt)]
 simp

theorem pair_before {M:ℕ} (r:ℕ) (cap:2*M≤r) (i:Fin M) :
 blockBefore (widths r M) (pairBlock r cap i)=2*i.val := by
 simp only [blockBefore,pairBlock,widths]
 rw [List.take_append_of_le_length (by simp only [List.length_replicate];exact i.isLt.le)]
 simp [List.take_replicate,Nat.mul_comm]
open UniformSectorPacking UniformTraversal

def matchingPosition {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E)
 (hpos:2≤r) (i:Fin M) (t:Fin 2) : BlockPosition (geometry r E hm hr hpos).widths :=
 ⟨pairBlock r (matching_capacity r E hm hr) i,
  finCongr (pair_width r (matching_capacity r E hm hr) i).symm t⟩

theorem matching_position_encode {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E)
 (hpos:2≤r) (i:Fin M) (t:Fin 2) :
 (blockEncode (geometry r E hm hr hpos).widths (matchingPosition r E hm hr hpos i t)).val=2*i.val+t.val := by
 change blockBefore (widths r M) (pairBlock r (matching_capacity r E hm hr) i)+t.val=_
 rw [pair_before]

theorem matching_position_original {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E)
 (hpos:2≤r) (i:Fin M) (t:Fin 2) :
 ((geometry r E hm hr hpos).originalPermutation
 (blockEncode _ (matchingPosition r E hm hr hpos i t))).val=
 if t.val=0 then (E i).left else (E i).right := by
 apply Option.some.inj
 rw [geometry_permutation]
 rw [←List.getElem?_eq_getElem]
 rw [matching_position_encode]
 fin_cases t
 · simpa using ordered_left r E i
 · simpa using ordered_right r E i


open UniformMachine UniformSectorPacking UniformSectorPackingMachine

theorem physicalUnpacking_coordinate (as:List PhysicalAxis) (L:UniformSectorPackingMachine.Layout)
 (hv:physicalVolume as=L.total) (x:SectorPosition (physicalAxes as)) :
 physicalUnpacking as L hv (finCongr hv (packedEquiv (physicalAxes as) x))=
 finCongr hv (originalEquiv (physicalAxes as) x) := by
 change finCongr hv (unpackingPermutation (physicalAxes as)
  ((finCongr hv).symm (finCongr hv (packedEquiv (physicalAxes as) x))))=_
 rw [Equiv.symm_apply_apply,←packingPermutation_original,unpacking_packing]

theorem Result.sectorCoordinates {p:MatchingParameters} {B:ℕ} {l:Layout p B}
 {W:List (UniformReplayPrint.ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r}
 {dom:UniformChunkMatchingPreparation.CodesDomain p W}
 {degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6}
 {v:Fin l.packing.total→Scalar} {s u:State} (h:Result l W loc dom degree v s u)
 (z:SectorPosition (physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree])) :
 u.scalarHeap (l.packing.destination+
  (finCongr (axis_volume l W dom degree) (packedEquiv _ z)).val)=some
  (v (finCongr (axis_volume l W dom degree) (originalEquiv _ z))) := by
 rw [←physicalUnpacking_coordinate]
 exact h.packed _


open UniformMachine UniformSectorPacking UniformSectorPackingMachine UniformTraversal
def pairPosition {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (t:Fin 2) :
 SectorPosition (physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree]) :=
 let pos:=matchingPosition p.radix (UniformChunkMatchingPreparation.physicalEdges l.matching W dom)
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom) l.matching.radixPositive i t
 ⟨(pos.1,()),(pos.2,())⟩

theorem pair_packed_value {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (t:Fin 2) :
 (packedEquiv _ (pairPosition l W dom degree i t)).val=2*i.val+t.val := by
 let E:=UniformChunkMatchingPreparation.physicalEdges l.matching W dom
 let hm:=UniformChunkMatchingPreparation.physical_matching l.matching dom degree
 let hr:=UniformChunkMatchingPreparation.physical_range l.matching dom
 let pos:=matchingPosition p.radix E hm hr l.matching.radixPositive i t
 change (packedEquiv [UniformMatchingAxisTableMachine.geometry p.radix E hm hr l.matching.radixPositive] ⟨(pos.1,()),(pos.2,())⟩).val=_
 rw [single_packed_value]
 change blockBefore (UniformMatchingAxisTableMachine.widths p.radix _) (pairBlock p.radix (UniformMatchingAxisTableMachine.matching_capacity p.radix E hm hr) i)+t.val=_
 rw [pair_before]

def pairSourceCoordinate {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (t:Fin 2) : Fin l.packing.total :=
 finCongr (axis_volume l W dom degree) (originalEquiv _ (pairPosition l W dom degree i t))

theorem pair_source_value {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (t:Fin 2) :
 (pairSourceCoordinate l W dom degree i t).val=
 if t.val=0 then (UniformChunkMatchingPreparation.physicalEdges l.matching W dom i).left
 else (UniformChunkMatchingPreparation.physicalEdges l.matching W dom i).right := by
 change (originalEquiv _ (pairPosition l W dom degree i t)).val=_
 let E:=UniformChunkMatchingPreparation.physicalEdges l.matching W dom
 let hm:=UniformChunkMatchingPreparation.physical_matching l.matching dom degree
 let hr:=UniformChunkMatchingPreparation.physical_range l.matching dom
 let pos:=matchingPosition p.radix E hm hr l.matching.radixPositive i t
 change (originalEquiv [UniformMatchingAxisTableMachine.geometry p.radix E hm hr l.matching.radixPositive] ⟨(pos.1,()),(pos.2,())⟩).val=_
 rw [single_original_value]
 exact matching_position_original _ _ _ _ _ i t

theorem Result.pairCoordinates {p:MatchingParameters} {B:ℕ} {l:Layout p B}
 {W:List (UniformReplayPrint.ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r}
 {dom:UniformChunkMatchingPreparation.CodesDomain p W}
 {degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6}
 {v:Fin l.packing.total→Scalar} {s u:State} (h:Result l W loc dom degree v s u)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (t:Fin 2) :
 u.scalarHeap (l.packing.destination+(2*i.val+t.val))=some (v (pairSourceCoordinate l W dom degree i t)) := by
 have hcoord:=h.sectorCoordinates (pairPosition l W dom degree i t)
 change u.scalarHeap (l.packing.destination+(packedEquiv _ (pairPosition l W dom degree i t)).val)=some (v (pairSourceCoordinate l W dom degree i t)) at hcoord
 rw [pair_packed_value] at hcoord
 exact hcoord


open UniformSectorPacking UniformSectorTensor UniformTraversal UniformMatchingAxisTableMachine

/-- Each actual selected pair is a width-two sector with exactly one C axis.
This is the algebraic block action; this module does not execute C. -/
theorem pair_sector_count {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) :
 sectorPairCount (UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree])
  (pairPosition l W dom degree i 0).1=1 := by
 let E:=UniformChunkMatchingPreparation.physicalEdges l.matching W dom
 let cap:=matching_capacity p.radix E
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom)
 change List.countP (fun q=>q==2) [(widths p.radix _).get (pairBlock p.radix cap i)]=1
 rw [pair_width]
 simp

theorem pair_sector_C {p:MatchingParameters} {B:ℕ} (l:Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ r)) (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) (x y:Fin 2) :
 sectorMatrix (UniformSectorPackingMachine.physicalAxes [UniformChunkMatchingPreparation.axis l.matching W dom degree])
  (pairPosition l W dom degree i 0).1 (pairPosition l W dom degree i x).2 (pairPosition l W dom degree i y).2=C x y := by
 let E:=UniformChunkMatchingPreparation.physicalEdges l.matching W dom
 let cap:=matching_capacity p.radix E
  (UniformChunkMatchingPreparation.physical_matching l.matching dom degree)
  (UniformChunkMatchingPreparation.physical_range l.matching dom)
 change blockEntry ((widths p.radix _).get (pairBlock p.radix cap i)) x.val y.val*1=C x y
 rw [pair_width,mul_one]
 exact blockEntry_two x y

end
end ExactFourierCircuits.UniformMatchingPackingPreparation
