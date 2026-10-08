import UniformPackedPairRoundMachine
import UniformScalarScatterMachine
import UniformSeedChunkPackingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPackedPairScatterPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Ordinary allocations only. Neither helper header nor transformed values
are entry inputs. Caller1600..1606, freshly initialized zero1607. -/
structure Config where
 length : ℕ
 pairs : ℕ
 packed : ℕ
 destination : ℕ
 inverse : ℕ
 diagonal : ℕ
 offDiagonal : ℕ

def roundSetup : List Op := [.literal 1607 0,.add 1280 1602 1607,
 .add 1281 1601 1607,.add 1282 1605 1607,.add 1283 1606 1607]
def scatterSetup : List Op := [.add 1506 1600 1607,.add 1507 1602 1607,
 .add 1508 1603 1607,.add 1509 1604 1607]
def beforeScatter : Program := roundSetup.map Op.code ++
 UniformPackedPairRoundMachine.program.map (relocate 5 28) ++ scatterSetup.map Op.code
def program : Program := beforeScatter ++
 UniformScalarScatterMachine.program.map (relocate 32 44) ++ [.halt]
lemma roundSetup_length : roundSetup.length=5 := rfl
lemma scatterSetup_length : scatterSetup.length=4 := rfl
lemma beforeScatter_length : beforeScatter.length=32 := by
 simp [beforeScatter,roundSetup_length,scatterSetup_length,UniformPackedPairRoundMachine.program_length]
lemma program_length : program.length=45 := by
 simp [program,beforeScatter_length,UniformScalarScatterMachine.program_length]
lemma roundSetup_code : BlockAt roundSetup program 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma round_code : CodeAt UniformPackedPairRoundMachine.program program 5 28 := by
 let tail:=scatterSetup.map Op.code ++ UniformScalarScatterMachine.program.map (relocate 32 44) ++ [.halt]
 have eqn:program=roundSetup.map Op.code ++ UniformPackedPairRoundMachine.program.map (relocate 5 28) ++ tail:=by
  simp [program,beforeScatter,tail,List.append_assoc]
 rw [eqn]
 exact UniformRankCrossPreparationMachine.segment_code _ tail _ 5 28 (by simp [roundSetup_length])
lemma scatterSetup_code : BlockAt scatterSetup program 28 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (roundSetup.map Op.code ++ UniformPackedPairRoundMachine.program.map (relocate 5 28))
  (scatterSetup.map Op.code) (UniformScalarScatterMachine.program.map (relocate 32 44) ++ [.halt]) i
  (by simpa using hi)
 simpa only [program,beforeScatter,List.append_assoc,List.length_append,List.length_map,
  roundSetup_length,UniformPackedPairRoundMachine.program_length,List.getElem?_map,
  List.getElem?_eq_getElem hi,Option.map_some] using h
lemma scatter_code : CodeAt UniformScalarScatterMachine.program program 32 44 :=
 UniformRankCrossPreparationMachine.segment_code beforeScatter [.halt] _ 32 44 beforeScatter_length
lemma halt_at : program[44]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simp [beforeScatter_length,UniformScalarScatterMachine.program_length])]
 simp [beforeScatter_length,UniformScalarScatterMachine.program_length]

noncomputable section
structure Args (c:Config) (s:State) : Prop where
 length : s.natReg 1600=c.length
 pairs : s.natReg 1601=c.pairs
 packed : s.natReg 1602=c.packed
 destination : s.natReg 1603=c.destination
 inverse : s.natReg 1604=c.inverse
 diagonal : s.natReg 1605=c.diagonal
 offDiagonal : s.natReg 1606=c.offDiagonal

structure Layout (c:Config) (B:ℕ) : Prop where
 capacity : 2*c.pairs≤c.length
 disjoint : UniformScalarScatterMachine.Disjoint c.packed c.destination c.length
 packedBound : c.packed+c.length≤B
 destinationBound : c.destination+c.length≤B
 inverseBound : c.inverse+c.length≤B
 diagonalPacked : c.diagonal<c.packed ∨ c.packed+c.length≤c.diagonal
 offDiagonalPacked : c.offDiagonal<c.packed ∨ c.packed+c.length≤c.offDiagonal
 diagonalDestination : c.diagonal<c.destination ∨ c.destination+c.length≤c.diagonal
 offDiagonalDestination : c.offDiagonal<c.destination ∨ c.destination+c.length≤c.offDiagonal
 code : 45≤B

/-- The exact original contiguous tagged bank is an honest physical premise. -/
def Source (c:Config) (v:Fin c.length→Scalar) (s:State) :=
 ∀j,s.scalarHeap (c.packed+j.val)=some (v j)

def pairInput {c:Config} (h:2*c.pairs≤c.length) (v:Fin c.length→Scalar)
 (i:Fin c.pairs) (t:Fin 2) : Scalar := v ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩

def afterRound {c:Config} (h:2*c.pairs≤c.length) (v:Fin c.length→Scalar) (j:Fin c.length) : Scalar :=
 if hj:j.val<2*c.pairs then UniformPackedPairRoundMachine.transformed
  (pairInput h v ⟨j.val/2,by omega⟩) ⟨j.val%2,Nat.mod_lt _ (by decide)⟩ else v j

lemma pair_source {c:Config} (h:2*c.pairs≤c.length) {v:Fin c.length→Scalar} {s:State}
 (src:Source c v s) : UniformPackedPairRoundMachine.Source c.packed c.pairs (pairInput h v) s :=
 by
 intro i t
 simpa only [UniformPackedPairRoundMachine.address,pairInput,Nat.add_assoc] using
  src ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩

lemma round_source {c:Config} (cap:2*c.pairs≤c.length) {v:Fin c.length→Scalar} {s u:State}
 (src:Source c v s) (bank:∀i t,u.scalarHeap (UniformPackedPairRoundMachine.address c.packed i.val t)=
  some (UniformPackedPairRoundMachine.transformed (pairInput cap v i) t))
 (outside:UniformPackedPairRoundMachine.Outside c.packed c.pairs s u) : Source c (afterRound cap v) u := by
 intro j
 by_cases hj:j.val<2*c.pairs
 · let i:Fin c.pairs:=⟨j.val/2,by omega⟩
   let t:Fin 2:=⟨j.val%2,Nat.mod_lt _ (by decide)⟩
   have idx:2*i.val+t.val=j.val:=by dsimp [i,t];omega
   have hb:=bank i t
   rw [UniformPackedPairRoundMachine.address,Nat.add_assoc,idx] at hb
   simpa only [afterRound,dite_eq_left hj] using hb
 · rw [outside _ (Or.inr (by omega)),afterRound,dite_eq_right hj]
   exact src j

lemma afterRound_pair {c:Config} (cap:2*c.pairs≤c.length) (v:Fin c.length→Scalar)
 (i:Fin c.pairs) (t:Fin 2) :
 afterRound cap v ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩=
 UniformPackedPairRoundMachine.transformed (pairInput cap v i) t := by
 have ht:=t.isLt;have hi:=i.isLt
 have hpair:2*i.val+t.val<2*c.pairs:=by omega
 simp only [afterRound,dite_eq_left hpair]
 congr 1
 · congr 1;apply Fin.ext;change (2*i.val+t.val)/2=i.val;omega
 · apply Fin.ext;change (2*i.val+t.val)%2=t.val;omega
lemma afterRound_tail {c:Config} (cap:2*c.pairs≤c.length) (v:Fin c.length→Scalar)
 (j:Fin c.length) (tail:2*c.pairs≤j.val) : afterRound cap v j=v j := by
 simp [afterRound,show ¬j.val<2*c.pairs by omega]

lemma roundSetup_spec {c:Config} {s:State} (h:Args c s) :
 UniformPackedPairRoundMachine.Header c.packed c.pairs c.diagonal c.offDiagonal (applyBlock roundSetup s) := by
 constructor
 all_goals simp [roundSetup,applyBlock,Op.apply,writeNat,next,h.pairs,h.packed,h.diagonal,h.offDiagonal]
lemma roundSetup_safe {s:State} {B:ℕ} (h:WordBound B s) :
 readable roundSetup s ∧ peak roundSetup s≤B := by
 simp [roundSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 exact ⟨h.2.1 1602,h.2.1 1601,h.2.1 1605,h.2.1 1606⟩

lemma roundSetup_args {c:Config} {s:State} (h:Args c s) : Args c (applyBlock roundSetup s) := by
 cases h;constructor <;> simp_all [roundSetup,applyBlock,Op.apply,writeNat,next]
lemma roundSetup_zero (s:State) : (applyBlock roundSetup s).natReg 1607=0 := by
 simp [roundSetup,applyBlock,Op.apply,writeNat,next]
lemma round_args {c:Config} {s u:State} (h:Args c s) (f:UniformPackedPairRoundMachine.Frame s u) : Args c u := by
 constructor
 all_goals first
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.length
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.pairs
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.packed
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.destination
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.inverse
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.diagonal
 | exact (f.natReg _ (by omega) (by omega) (by omega)).trans h.offDiagonal

lemma scatterSetup_spec {c:Config} {s:State} (h:Args c s) (z:s.natReg 1607=0) :
 (applyBlock scatterSetup s).natReg 1506=c.length ∧
 (applyBlock scatterSetup s).natReg 1507=c.packed ∧
 (applyBlock scatterSetup s).natReg 1508=c.destination ∧
 (applyBlock scatterSetup s).natReg 1509=c.inverse := by
 simp [scatterSetup,applyBlock,Op.apply,writeNat,next,z,h.length,h.packed,h.destination,h.inverse]
lemma scatterSetup_safe {s:State} {B:ℕ} (h:WordBound B s) (z:s.natReg 1607=0) :
 readable scatterSetup s ∧ peak scatterSetup s≤B := by
 simp [scatterSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,z]
 exact ⟨h.2.1 1600,h.2.1 1602,h.2.1 1603,h.2.1 1604⟩

/-- Actual Nat/scalar footprints of both loops and both charged header blocks. -/
structure Frame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 natReg : ∀q,q≠0→q≠1→(q<1280 ∨ 1288≤q)→(q<1506 ∨ 1517≤q)→q≠1607→u.natReg q=s.natReg q
 scalarReg : ∀q,8≤q→q≠90→u.scalarReg q=s.scalarReg q

lemma Frame.trans {s u v:State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.natHeap.trans h.natHeap,h'.outputs.trans h.outputs,h'.rootOrders.trans h.rootOrders,
 fun q h0 h1 h2 h3 h4=>(h'.natReg q h0 h1 h2 h3 h4).trans (h.natReg q h0 h1 h2 h3 h4),
 fun q h0 h1=>(h'.scalarReg q h0 h1).trans (h.scalarReg q h0 h1)⟩
lemma roundSetup_frame (s:State) : Frame s (applyBlock roundSetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _=>rfl⟩
 intro q h0 h1 h2 h3 h4
 simp (disch:=omega) [roundSetup,applyBlock,Op.apply,writeNat,next]
lemma scatterSetup_frame (s:State) : Frame s (applyBlock scatterSetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _=>rfl⟩
 intro q h0 h1 h2 h3 h4
 simp (disch:=omega) [scatterSetup,applyBlock,Op.apply,writeNat,next]
lemma round_frame {s u:State} (h:UniformPackedPairRoundMachine.Frame s u) : Frame s u :=
 ⟨h.natHeap,h.outputs,h.rootOrders,fun q h0 h1 h2 _ _=>h.natReg q h0 h1 (by omega),
 fun q h0 _=>h.scalarReg q h0⟩
lemma scatter_frame {s u:State} (h:UniformScalarScatterMachine.Frame s u) : Frame s u :=
 ⟨h.1,h.2.1,h.2.2.1,fun q _ _ _ h3 _=>h.2.2.2.2 q (by omega),
 fun q _ hq=>h.2.2.2.1 q hq⟩

/-- Full physical continuation: all header setup and both helper halts are
charged. The supplied inverse table is read by the actual scatter loop. -/
theorem execution (n B:ℕ) (x:Fin n→ℂ) (c:Config) (l:Layout c B)
 (phi:Fin c.length≃Fin c.length) (v:Fin c.length→Scalar) (s:State)
 (args:Args c s) (source:Source c v s)
 (table:UniformGlobalNatPreparation.PermutationBank c.length c.inverse s.natHeap phi)
 (constants:UniformPackedPairRoundMachine.Constants c.diagonal c.offDiagonal s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (17*c.pairs+9*c.length+21) u ∧ u.pc=44 ∧
 (∀j:Fin c.length,u.scalarHeap (c.destination+j.val)=some (afterRound l.capacity v (phi.symm j))) ∧
 (∀j:Fin c.length,u.scalarHeap (c.packed+j.val)=some (afterRound l.capacity v j)) ∧
 (∀q,(q<c.packed ∨ c.packed+2*c.pairs≤q)→
  (q<c.destination ∨ c.destination+c.length≤q)→u.scalarHeap q=s.scalarHeap q) ∧
 UniformPackedPairRoundMachine.Constants c.diagonal c.offDiagonal u ∧ Frame s u := by
 have code:=l.code
 have safe:=roundSetup_safe bound
 have first:=block_runs roundSetup program 0 n B x s roundSetup_code pc bound
  (by rw [roundSetup_length];omega) safe.1 safe.2
 let a:=applyBlock roundSetup s
 have ap:a.pc=5:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,roundSetup_length]
 let entry:=setPC a 0
 have rh:=roundSetup_spec args
 have entryHeader:UniformPackedPairRoundMachine.Header c.packed c.pairs c.diagonal c.offDiagonal entry:=
  ⟨rh.base,rh.count,rh.diagonal,rh.offDiagonal⟩
 obtain ⟨z,roundRun,zpc,bank,outside,rframe⟩:=UniformPackedPairRoundMachine.execution n x
  c.packed c.pairs c.diagonal c.offDiagonal B (pairInput l.capacity v) entry entryHeader
  (pair_source l.capacity source) constants (by have:=l.packedBound;have:=l.capacity;omega)
  (by omega) rfl (changePC_bound B a 0 first.final_bound (by omega))
 have movedRound:=UniformBoundedAssembly.boundedExecution_placed round_code
  (by rw [UniformPackedPairRoundMachine.program_length];omega) (by omega) roundRun
 rw [UniformSeedRankCrossPreparation.placed_zero a 5 ap] at movedRound
 let b:=setPC z 28
 have rf:UniformPackedPairRoundMachine.Frame a b:=
  ⟨rframe.natHeap,rframe.outputs,rframe.rootOrders,rframe.natReg,rframe.scalarReg⟩
 have ba:Args c b:=round_args (roundSetup_args args) rf
 have bz:b.natReg 1607=0:=
  (rframe.natReg 1607 (by omega) (by omega) (by omega)).trans (roundSetup_zero s)
 have setupSafe:=scatterSetup_safe movedRound.final_bound bz
 have middle:=block_runs scatterSetup program 28 n B x b scatterSetup_code rfl
  movedRound.final_bound (by rw [scatterSetup_length];omega) setupSafe.1 setupSafe.2
 let d:=applyBlock scatterSetup b
 have dp:d.pc=32:=by rw [UniformTensorMonomialMachine.applyBlock_pc,scatterSetup_length];rfl
 have hdr:=scatterSetup_spec ba bz
 have fullBank:Source c (afterRound l.capacity v) d:=round_source l.capacity source bank outside
 have inv:UniformGlobalNatPreparation.PermutationBank c.length c.inverse d.natHeap phi:=by
  rw [show d.natHeap=s.natHeap from rframe.natHeap];exact table
 obtain ⟨w,scatterRun,scatterValues,scatterSource,scatterOutside,sframe,_,_⟩:=
  UniformScalarScatterMachine.execution n x c.length c.packed c.destination c.inverse B phi
   (setPC d 0) inv (fun j=>⟨afterRound l.capacity v j,fullBank j⟩) l.disjoint
   l.packedBound l.destinationBound l.inverseBound (by omega) rfl hdr.1 hdr.2.1 hdr.2.2.1 hdr.2.2.2
   (changePC_bound B d 0 middle.final_bound (by omega))
 have movedScatter:=UniformBoundedAssembly.boundedExecution_placed scatter_code
  (by rw [UniformScalarScatterMachine.program_length];omega) (by omega) scatterRun
 rw [UniformSeedRankCrossPreparation.placed_zero d 32 dp] at movedScatter
 let u:=setPC w 44
 have stop:BoundedExecution program n x B u 1 u:=.halt movedScatter.final_bound
  (by simp [step,u,setPC,halt_at])
 have sf:UniformScalarScatterMachine.Frame d u:=
  ⟨sframe.1,sframe.2.1,sframe.2.2.1,sframe.2.2.2.1,sframe.2.2.2.2⟩
 have fullFrame:Frame s u:=((roundSetup_frame s).trans (round_frame rf)).trans
  ((scatterSetup_frame b).trans (scatter_frame sf))
 have scalarOutside:∀q,(q<c.packed ∨ c.packed+2*c.pairs≤q)→
  (q<c.destination ∨ c.destination+c.length≤q)→u.scalarHeap q=s.scalarHeap q:=by
  intro q pairSafe targetSafe
  exact (scatterOutside q targetSafe).trans (outside q pairSafe)
 refine ⟨u,?_,rfl,?_,?_,scalarOutside,?_,fullFrame⟩
 · convert first.executes (movedRound.executes (middle.executes (movedScatter.executes stop))) using 1
   rw [roundSetup_length,scatterSetup_length];omega
 · intro j
   change w.scalarHeap (c.destination+j.val)=_
   rw [UniformScalarScatterMachine.scatter_coordinates scatterValues j]
   exact fullBank (phi.symm j)
 · intro j
   exact (scatterSource j).trans (fullBank j)
 · exact ⟨(scalarOutside _ (by have:=l.diagonalPacked;have:=l.capacity;omega) l.diagonalDestination).trans constants.1,
    (scalarOutside _ (by have:=l.offDiagonalPacked;have:=l.capacity;omega) l.offDiagonalDestination).trans constants.2⟩

structure Result {B:ℕ} (c:Config) (l:Layout c B)
 (phi:Fin c.length≃Fin c.length) (v:Fin c.length→Scalar) (s u:State) : Prop where
 pc : u.pc=44
 destination : ∀j:Fin c.length,u.scalarHeap (c.destination+j.val)=some (afterRound l.capacity v (phi.symm j))
 packed : ∀j:Fin c.length,u.scalarHeap (c.packed+j.val)=some (afterRound l.capacity v j)
 outside : ∀q,(q<c.packed ∨ c.packed+2*c.pairs≤q)→
  (q<c.destination ∨ c.destination+c.length≤q)→u.scalarHeap q=s.scalarHeap q
 constants : UniformPackedPairRoundMachine.Constants c.diagonal c.offDiagonal u
 table : UniformGlobalNatPreparation.PermutationBank c.length c.inverse u.natHeap phi
 frame : Frame s u

theorem execution_result (n B:ℕ) (x:Fin n→ℂ) (c:Config) (l:Layout c B)
 (phi:Fin c.length≃Fin c.length) (v:Fin c.length→Scalar) (s:State)
 (args:Args c s) (source:Source c v s)
 (table:UniformGlobalNatPreparation.PermutationBank c.length c.inverse s.natHeap phi)
 (constants:UniformPackedPairRoundMachine.Constants c.diagonal c.offDiagonal s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (17*c.pairs+9*c.length+21) u ∧ Result c l phi v s u := by
 obtain ⟨u,run,up,values,packed,outside,coef,frame⟩:=execution n B x c l phi v s args source table constants pc bound
 exact ⟨u,run,⟨up,values,packed,outside,coef,by rw [frame.natHeap];exact table,frame⟩⟩

theorem Result.pair_coordinates {B:ℕ} {c:Config} {l:Layout c B}
 {phi:Fin c.length≃Fin c.length} {v:Fin c.length→Scalar} {s u:State}
 (h:Result c l phi v s u) (i:Fin c.pairs) (t:Fin 2) :
 u.scalarHeap (c.destination+(phi ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;have:=l.capacity;omega⟩).val)=
 some (UniformPackedPairRoundMachine.transformed (pairInput l.capacity v i) t) := by
 rw [h.destination,phi.symm_apply_apply,afterRound_pair]

theorem Result.C_values {B:ℕ} {c:Config} {l:Layout c B}
 {phi:Fin c.length≃Fin c.length} {v:Fin c.length→Scalar} {s u:State}
 (h:Result c l phi v s u) (i:Fin c.pairs) (t:Fin 2) :
 u.scalarHeap (c.destination+(phi ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;have:=l.capacity;omega⟩).val)=
 some ⟨C.mulVec (fun j=>(pairInput l.capacity v i j).value) t,
  (pairInput l.capacity v i 0).dependent || (pairInput l.capacity v i 1).dependent⟩ := by
 rw [h.pair_coordinates i t]
 congr 1
 have eta:UniformPackedPairRoundMachine.transformed (pairInput l.capacity v i) t=
  ⟨(UniformPackedPairRoundMachine.transformed (pairInput l.capacity v i) t).value,
   (UniformPackedPairRoundMachine.transformed (pairInput l.capacity v i) t).dependent⟩:=rfl
 rw [eta,UniformPackedPairRoundMachine.transformed_value,UniformPackedPairRoundMachine.transformed_flag]

theorem Result.tail {B:ℕ} {c:Config} {l:Layout c B}
 {phi:Fin c.length≃Fin c.length} {v:Fin c.length→Scalar} {s u:State}
 (h:Result c l phi v s u) (j:Fin c.length) (hj:2*c.pairs≤j.val) :
 u.scalarHeap (c.destination+(phi j).val)=some (v j) ∧
 u.scalarHeap (c.packed+j.val)=some (v j) := by
 constructor
 · rw [h.destination,phi.symm_apply_apply,afterRound_tail _ _ _ hj]
 · rw [h.packed,afterRound_tail _ _ _ hj]

theorem Result.saved_headers {B:ℕ} {c:Config} {l:Layout c B}
 {phi:Fin c.length≃Fin c.length} {v:Fin c.length→Scalar} {s u:State}
 (h:Result c l phi v s u) (q:ℕ) (lo:100≤q) (hi:q≤106) :
 u.natReg q=s.natReg q := h.frame.natReg q (by omega) (by omega) (by omega) (by omega) (by omega)

theorem runtime_linear {c:Config} (cap:2*c.pairs≤c.length) :
 17*c.pairs+9*c.length+21≤30*(c.length+1) := by omega

def wordBudget (c:Config) : ℕ := max (max (c.packed+c.length) (c.destination+c.length))
 (max (c.inverse+c.length) (max (max c.diagonal c.offDiagonal) 45))
lemma wordBudget_polynomial (c:Config) : wordBudget c≤
 45*(c.packed+c.destination+c.inverse+c.length+c.diagonal+c.offDiagonal+1) := by
 unfold wordBudget;omega

/-- Actual Packing137 layout determines the three contiguous banks. -/
def packingConfig (L:UniformSectorPackingMachine.Layout) (m cd co:ℕ) : Config :=
 ⟨L.total,m,L.destination,L.source,L.inverse,cd,co⟩

lemma packing_layout (L:UniformSectorPackingMachine.Layout) (m cd co:ℕ)
 (cap:2*m≤L.total)
 (cdPacked:cd<L.destination ∨ L.destination+L.total≤cd)
 (coPacked:co<L.destination ∨ L.destination+L.total≤co)
 (cdDestination:cd<L.source ∨ L.source+L.total≤cd)
 (coDestination:co<L.source ∨ L.source+L.total≤co) : Layout (packingConfig L m cd co) L.B :=
 ⟨cap,Or.inr L.sourceBelow,L.destinationBound,
  L.sourceBelow.trans (by have:=L.destinationBound;omega),L.inverseBound,
  cdPacked,coPacked,cdDestination,coDestination,by have:=L.code;omega⟩

/-- Genuine generated inverse table and packed values are consumed directly.
No C-transformed scalar bank or supplied Scatter12 header is an entry premise. -/
theorem execution_from_packed {n B:ℕ} {j:Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed:UniformSeedChunkPackingPreparation.Config} (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 {original:Fin p.packing.total→Scalar} {origin s:State}
 (packed:UniformSeedChunkPackingPreparation.Packed p original origin s)
 (m cd co:ℕ) (l:Layout (packingConfig p.packing m cd co) B) (x:Fin n→ℂ)
 (args:Args (packingConfig p.packing m cd co) s)
 (constants:UniformPackedPairRoundMachine.Constants cd co s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (17*m+9*p.packing.total+21) u ∧
 Result (packingConfig p.packing m cd co) l (UniformSeedChunkPackingPreparation.unpacking p)
  (fun i=>original (UniformSeedChunkPackingPreparation.unpacking p i)) s u :=
 execution_result n B x (packingConfig p.packing m cd co) l
  (UniformSeedChunkPackingPreparation.unpacking p)
  (fun i=>original (UniformSeedChunkPackingPreparation.unpacking p i)) s args
  packed.values packed.inverse constants pc bound

/-- Startup's actual retained scalar heap1/heap2 coefficients discharge both
loads. The ordinary driver allocation uses those literal addresses. -/
theorem startup_execution (n B:ℕ) (x:Fin n→ℂ) (c:Config) (l:Layout c B)
 (phi:Fin c.length≃Fin c.length) (v:Fin c.length→Scalar) (s:State)
 (args:Args c s) (source:Source c v s)
 (table:UniformGlobalNatPreparation.PermutationBank c.length c.inverse s.natHeap phi)
 (ops:UniformInitialPreparation.Operands n x s) (cd:c.diagonal=1) (co:c.offDiagonal=2)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s (17*c.pairs+9*c.length+21) u ∧ Result c l phi v s u := by
 apply execution_result n B x c l phi v s args source table _ pc bound
 rw [cd,co]
 exact UniformPackedPairRoundMachine.startup_constants n s ops.constants

end
end ExactFourierCircuits.UniformPackedPairScatterPreparation
