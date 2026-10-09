import UniformProducedSectorPaddingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTensorDiagonalMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (product)
noncomputable section
/-- Real role-major tensor traversal. Actual66 headers are installed inside
each iteration. Physical axis coefficient banks remain an honest entry. -/
def boot (W:ℕ):List Op:=[.literal 4500 W,.literal 4510 0,.literal 4511 1,.literal 4512 0]
def setup:List Op:=[.add 1 4504 4510,.add 5 4505 4510,.add 6 4506 4510,
 .mul 4513 4512 4501,.add 7 4502 4513,.add 15 4503 4513,.add 16 4507 4510]
def programFor (W:ℕ):Program:=(boot W).map Op.code++[.branchLT 4512 4500 5 80]++
 setup.map Op.code++UniformTensorMonomialMachine.program.map (relocate 12 78)++
 [.natBinary .add 4512 4512 4511,.jump 4,.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=81:=by
 simp only[programFor,List.length_append,List.length_map,UniformTensorMonomialMachine.program_length,
  List.length_cons,List.length_nil];rfl
lemma boot_code (W:ℕ):BlockAt (boot W) (programFor W) 0:=by
 intro i hi;change i < 4 at hi;interval_cases i <;>rfl
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 5:=by
 intro i hi;change i < 7 at hi;interval_cases i <;>rfl
lemma tensor_code (W:ℕ):CodeAt UniformTensorMonomialMachine.program (programFor W) 12 78:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((boot W).map Op.code++[.branchLT 4512 4500 5 80]++setup.map Op.code)
  [.natBinary .add 4512 4512 4511,.jump 4,.halt] _ 12 78 rfl
lemma branch_at (W:ℕ):(programFor W)[4]?=some (.branchLT 4512 4500 5 80):=rfl
lemma advance_at (W:ℕ):(programFor W)[78]?=some (.natBinary .add 4512 4512 4511):=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformTensorMonomialMachine.program_length];change 4+1+7+66 ≤ 78;omega)]
 simp only[List.length_append,List.length_map,UniformTensorMonomialMachine.program_length];rfl
lemma jump_at (W:ℕ):(programFor W)[79]?=some (.jump 4):=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformTensorMonomialMachine.program_length];change 4+1+7+66 ≤ 79;omega)]
 simp only[List.length_append,List.length_map,UniformTensorMonomialMachine.program_length];rfl
lemma halt_at (W:ℕ):(programFor W)[80]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformTensorMonomialMachine.program_length];change 4+1+7+66 ≤ 80;omega)]
 simp only[List.length_append,List.length_map,UniformTensorMonomialMachine.program_length];rfl
structure Geometry (W:ℕ) where
 B:ℕ
 ell:ℕ
 row:ℕ
 natStack:ℕ
 scalarStack:ℕ
 source:ℕ
 destination:ℕ
 volume:ℕ
 positive:0 < W
 roles:W ≤ B
 code:81 ≤ B
 rowsBelow:row+3*ell ≤ natStack
 natStackBound:natStack+3*ell ≤ B
 scalarStackBound:scalarStack+ell ≤ B
 sourceBelow:source+W*volume ≤ scalarStack
 destinationAbove:scalarStack+ell ≤ destination
 destinationBound:destination+W*volume ≤ B

def Geometry.layout {W:ℕ} (g:Geometry W) (i:Fin W):UniformTensorMonomialMachine.Layout where
 B:=g.B
 ell:=g.ell
 row:=g.row
 natStack:=g.natStack
 scalarStack:=g.scalarStack
 source:=g.source+i.val*g.volume
 destination:=g.destination+i.val*g.volume
 volume:=g.volume
 codeBound:=by have:=g.code;omega
 rowsBelow:=by have:=g.rowsBelow;omega
 natStackBound:=by have:=g.natStackBound;omega
 scalarStackBound:=g.scalarStackBound
 sourceBelow:=by have h:=g.sourceBelow;have hi:=i.isLt;nlinarith
 destinationAbove:=by have h:=g.destinationAbove;omega
 destinationBound:=by have h:=g.destinationBound;have hi:=i.isLt;nlinarith
structure Header {W:ℕ} (g:Geometry W) (s:State):Prop where
 volume:s.natReg 4501=g.volume
 source:s.natReg 4502=g.source
 destination:s.natReg 4503=g.destination
 axes:s.natReg 4504=g.ell
 rows:s.natReg 4505=g.row
 natStack:s.natReg 4506=g.natStack
 scalarStack:s.natReg 4507=g.scalarStack
structure Cursor {W:ℕ} (g:Geometry W) (i:ℕ) (s:State):Prop extends Header g s where
 roles:s.natReg 4500=W
 zero:s.natReg 4510=0
 one:s.natReg 4511=1
 index:s.natReg 4512=i
lemma Cursor.withPC {W i pc:ℕ} {g:Geometry W} {s:State} (h:Cursor g i s):
 Cursor g i (setPC s pc):=
 ⟨⟨h.volume,h.source,h.destination,h.axes,h.rows,h.natStack,h.scalarStack⟩,
 h.roles,h.zero,h.one,h.index⟩
structure Banks {W:ℕ} (g:Geometry W) (axes:List Axis) (s:State):Prop where
 rows:Rows axes 0 g.row s
 permutation:∀a∈axes,∀j:Fin a.radix,s.natHeap (a.permutationBase+j.val)=some (a.permutation j).val
 coefficient:∀a∈axes,∀j:Fin a.radix,s.scalarHeap (a.coefficientBase+j.val)=some (UniformPairMachine.prepared (a.coefficient j))
 permutationBelow:∀a∈axes,a.permutationBase+a.radix ≤ g.natStack
 coefficientBelow:∀a∈axes,a.coefficientBase+a.radix ≤ g.scalarStack
lemma Banks.forRole {W:ℕ} {g:Geometry W} {axes:List Axis} {s:State}
 (h:Banks g axes s) (i:Fin W):UniformTensorMonomialMachine.Banks axes 0 (g.layout i) s:=
 ⟨h.rows,h.permutation,h.coefficient,h.permutationBelow,h.coefficientBelow⟩
def Source {W:ℕ} (g:Geometry W) (v:ℕ→ℕ→Scalar) (s:State):Prop:=
 ∀i,i < W→∀j,j < g.volume→s.scalarHeap (g.source+i*g.volume+j)=some (v i j)
def RoleOutput {W:ℕ} (g:Geometry W) (axes:List Axis) (v:ℕ→ℕ→Scalar) (i:ℕ) (s:State):Prop:=
 ∀j:Fin (radices axes).prod,s.scalarHeap (g.destination+i*g.volume+(tensorPermutation axes j).val)=
  some (product (tensorCoefficient axes j) (v i j.val))
def Frame (s u:State):Prop:=u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,2 ≤ q→u.scalarReg q=s.scalarReg q) ∧
 ∀q,20 ≤ q→q≠4500→(q < 4510 ∨4514 ≤ q)→u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,fun _ _=>rfl,fun _ _ _ _=>rfl⟩
lemma Frame.trans {s t u:State} (h:Frame s t) (k:Frame t u):Frame s u:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,fun q hq=>(k.2.2.1 q hq).trans (h.2.2.1 q hq),
 fun q h0 h1 h2=>(k.2.2.2 q h0 h1 h2).trans (h.2.2.2 q h0 h1 h2)⟩
lemma setup_frame (s:State):Frame s (applyBlock setup s):=by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_cursor {W i:ℕ} {g:Geometry W} {s:State} (h:Cursor g i s):
 Cursor g i (applyBlock setup s):=by
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,
    h.axes,h.rows,h.natStack,h.scalarStack]
 · simp[setup,applyBlock,Op.apply,writeNat,next,h.roles]
 · simp[setup,applyBlock,Op.apply,writeNat,next,h.zero]
 · simp[setup,applyBlock,Op.apply,writeNat,next,h.one]
 · simp[setup,applyBlock,Op.apply,writeNat,next,h.index]
lemma setup_call {W:ℕ} {g:Geometry W} {s:State} (i:Fin W) (h:Cursor g i.val s):
 Call (g.layout i) (applyBlock setup s):=by
 constructor <;>simp[Geometry.layout,setup,applyBlock,Op.apply,writeNat,next,h.zero,h.volume,
  h.source,h.destination,h.axes,h.rows,h.natStack,h.scalarStack,h.index]
lemma setup_safe {W:ℕ} {g:Geometry W} {s:State} (i:Fin W) (h:Cursor g i.val s):
 readable setup s ∧peak setup s ≤ g.B:=by
 have b0:=g.rowsBelow;have b1:=g.natStackBound;have b2:=g.scalarStackBound
 have b3:=g.sourceBelow;have b4:=g.destinationBound;have hi:=i.isLt
 have off:=Nat.mul_le_mul_right g.volume (Nat.le_of_lt hi)
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.zero,h.volume,
  h.source,h.destination,h.axes,h.rows,h.natStack,h.scalarStack,h.index]
 omega
lemma tensor_cursor {W i:ℕ} {g:Geometry W} {s u:State}
 (h:Cursor g i s) (f:UniformTensorMonomialMachine.Frame s u):Cursor g i u:=by
 constructor
 · constructor
   · exact (f.2.2.1 4501 (by omega)).trans h.volume
   · exact (f.2.2.1 4502 (by omega)).trans h.source
   · exact (f.2.2.1 4503 (by omega)).trans h.destination
   · exact (f.2.2.1 4504 (by omega)).trans h.axes
   · exact (f.2.2.1 4505 (by omega)).trans h.rows
   · exact (f.2.2.1 4506 (by omega)).trans h.natStack
   · exact (f.2.2.1 4507 (by omega)).trans h.scalarStack
 · exact (f.2.2.1 4500 (by omega)).trans h.roles
 · exact (f.2.2.1 4510 (by omega)).trans h.zero
 · exact (f.2.2.1 4511 (by omega)).trans h.one
 · exact (f.2.2.1 4512 (by omega)).trans h.index
lemma tensor_frame {s u:State} (f:UniformTensorMonomialMachine.Frame s u):Frame s u:=
 ⟨f.2.1,f.1,f.2.2.2,fun q h0 _ _=>f.2.2.1 q h0⟩
def tick (s:State):State:=setPC (writeNat (setPC s 78) 4512 (s.natReg 4512+s.natReg 4511)) 4
lemma tick_frame (s:State):Frame s (tick s):=by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega) [tick,setPC,writeNat,next]
lemma tick_cursor {W i:ℕ} {g:Geometry W} {s:State} (h:Cursor g i s):Cursor g (i+1) (tick s):=by
 constructor
 · constructor <;>simp[tick,setPC,writeNat,next,h.volume,h.source,h.destination,h.axes,h.rows,
    h.natStack,h.scalarStack]
 · simp[tick,setPC,writeNat,next,h.roles]
 · simp[tick,setPC,writeNat,next,h.zero]
 · simp[tick,setPC,writeNat,next,h.one]
 · simp[tick,setPC,writeNat,next,h.index,h.one]
lemma iteration {W n:ℕ} (g:Geometry W) (axes:List Axis) (v:ℕ→ℕ→Scalar)
 (x:Fin n→ℂ) (s:State) (i:Fin W) (h:Cursor g i.val s)
 (length:g.ell=axes.length) (volume:g.volume=(radices axes).prod)
 (banks:Banks g axes s) (source:Source g v s) (pc:s.pc=4) (wb:WordBound g.B s):
 ∃u,BoundedRuns (programFor W) n x g.B s (treeCost (radices axes)+20) u ∧u.pc=4 ∧
 RoleOutput g axes v i.val u ∧Cursor g (i.val+1) u ∧Frame s u ∧
 (∀q,q < g.natStack ∨g.natStack+3*g.ell ≤ q→u.natHeap q=s.natHeap q) ∧
 (∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination+i.val*g.volume ∨g.destination+(i.val+1)*g.volume ≤ q)→
  u.scalarHeap q=s.scalarHeap q):=by
 let e:=setPC s 5
 have eb:=changePC_bound g.B s 5 wb (by have:=g.code;omega)
 have branch:BoundedRuns (programFor W) n x g.B s 1 e:=
  .next wb (by simp[step,pc,branch_at,h.roles,h.index,i.isLt,e,setPC]) (.refl eb)
 have setRun:=block_runs setup (programFor W) 5 n g.B x e (setup_code W) rfl eb
  (by have:=g.code;change 5+7 ≤ g.B;omega) (setup_safe i (h.withPC)).1 (setup_safe i (h.withPC)).2
 let ready:=setPC (applyBlock setup e) 0
 have readyB:=changePC_bound g.B (applyBlock setup e) 0 setRun.final_bound (by have:=g.code;omega)
 have heaps:ready.natHeap=s.natHeap ∧ready.scalarHeap=s.scalarHeap:=by constructor <;>rfl
 have readyBanks:UniformTensorMonomialMachine.Banks axes 0 (g.layout i) ready:=by
  refine ⟨?_,?_,?_,banks.permutationBelow,banks.coefficientBelow⟩
  · have hlen:0+axes.length ≤ (g.layout i).ell:=by simp[Geometry.layout,length]
    exact rows_transfer axes 0 (g.layout i) s ready hlen banks.rows (fun q _=>congrFun heaps.1 q)
  · intro a ha j;exact (congrFun heaps.1 _).trans (banks.permutation a ha j)
  · intro a ha j;exact (congrFun heaps.2 _).trans (banks.coefficient a ha j)
 have readySource:SourceAt (g.layout i) ready:=by
  intro j hj;exact ⟨v i.val j,by simpa[Geometry.layout,Nat.add_assoc,heaps.2] using source i.val i.isLt j hj⟩
 have call:=setup_call i (h.withPC (pc:=5))
 have readyCall:Call (g.layout i) ready:=
  ⟨call.axes,call.row,call.natStack,call.source,call.destination,call.scalarStack⟩
 obtain ⟨run,result,values⟩:=tensor_execution axes (g.layout i) n x ready rfl length volume
  readyCall readyBanks readySource readyB
 have moved:=UniformBoundedAssembly.boundedExecution_placed (tensor_code W)
  (by rw[UniformTensorMonomialMachine.program_length];change 12+66 ≤ g.B;have:=g.code;omega)
  (by change 78 ≤ g.B;have:=g.code;omega) run
 have readyPC:placed 12 ready=applyBlock setup e:=by
  have cp:(applyBlock setup e).pc=12:=by rw[applyBlock_pc];rfl
  exact UniformMultiAxisSectorMetadataPreparation.placed_zero _ _ cp
 rw[readyPC] at moved
 let done:=finalState axes ready
 have cursor:=tensor_cursor ((setup_cursor (h.withPC (pc:=5))).withPC (pc:=0)) result.frame
 change Cursor g i.val done at cursor
 let advanced:=writeNat (setPC done 78) 4512 (i.val+1)
 have advanceB:=writeNat_bound g.B (setPC done 78) 4512 (i.val+1) moved.final_bound
  (by have:=g.code;change 78+1 ≤ g.B;omega) (by have hi:=i.isLt;have:=g.roles;omega)
 have advance:BoundedRuns (programFor W) n x g.B (setPC done 78) 1 advanced:=
  .next moved.final_bound (by simp[step,setPC,advance_at,evalNat,cursor.index,cursor.one,advanced]) (.refl advanceB)
 have same:tick done=setPC advanced 4:=by simp[tick,advanced,cursor.index,cursor.one]
 have last:BoundedRuns (programFor W) n x g.B advanced 1 (tick done):=by
  rw[same]
  exact .next advanceB (by rw[step,show advanced.pc=79 from rfl,jump_at];rfl)
   (.refl (changePC_bound g.B advanced 4 advanceB (by have:=g.code;omega)))
 refine ⟨tick done,?_,rfl,?_,tick_cursor cursor,
  (setup_frame e).trans ((tensor_frame result.frame).trans (tick_frame done)),?_,?_⟩
 · convert branch.trans (setRun.trans (moved.trans (advance.trans last))) using 1
   change _ = 1+(7+((treeCost (radices axes)+10)+(1+1)))
   omega
 · intro j
   simpa[done,tick,setPC,writeNat,next,Geometry.layout,Nat.add_assoc] using values j (v i.val j.val)
    (by simpa[Geometry.layout,Nat.add_assoc,heaps.2] using source i.val i.isLt j.val (by rw[volume];exact j.isLt))
 · intro q hq
   simpa[done,tick,setPC,writeNat,next,Geometry.layout,Nat.mul_comm g.ell 3,heaps.1] using result.natFrame q (by simpa[Geometry.layout,Nat.mul_comm] using hq)
 · intro q hs hd
   have hp: q < g.destination+i.val*g.volume ∨g.destination+i.val*g.volume+g.volume ≤ q:=by
    rcases hd with hd|hd
    · exact Or.inl hd
    · exact Or.inr (by nlinarith)
   simpa[done,tick,Geometry.layout,ready,e,setPC,setup,applyBlock,Op.apply,writeNat,next]
    using result.scalarFrame q hs hp
end
end ExactFourierCircuits.UniformGlobalTensorDiagonalMachine
