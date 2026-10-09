import UniformSectorTransposeMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorRestoringScatterPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorTransposeMachine (Geometry Header Source Filled Outside)
/-- First copy the complete original W-role bank into the fresh destination,
then overlay the genuine child sector with reverse34. This actually restores
all spectators from the original source, rather than retaining dirty values in
an unrelated fresh destination. Nat4535 supplies the ordinary original base. -/
def setup (W:ℕ):List Op:=[.literal 4563 1,.literal 4564 0,.literal 4565 W,
 .mul 147 4565 4530,.add 148 4535 4564,.add 149 4531 4564]
def programFor (W:ℕ):Program:=(setup W).map Op.code++UniformScalarCopyMachine.program.map (relocate 6 16)++
 (UniformSectorTransposeMachine.programFor W true).map (relocate 16 50)++[.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=51:=rfl
lemma setup_code (W:ℕ):BlockAt (setup W) (programFor W) 0:=by
 intro i hi;change i < 6 at hi;interval_cases i <;>rfl
lemma copy_code (W:ℕ):CodeAt UniformScalarCopyMachine.program (programFor W) 6 16:=by
 exact UniformRankCrossPreparationMachine.segment_code ((setup W).map Op.code)
  ((UniformSectorTransposeMachine.programFor W true).map (relocate 16 50)++[.halt]) _ 6 16 rfl
lemma transpose_code (W:ℕ):CodeAt (UniformSectorTransposeMachine.programFor W true) (programFor W) 16 50:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((setup W).map Op.code++UniformScalarCopyMachine.program.map (relocate 6 16)) [.halt] _ 16 50 rfl
lemma halt_at (W:ℕ):(programFor W)[50]?=some .halt:=rfl
noncomputable section

def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32 → u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q < 147 ∨154 ≤ q)→(q < 4550 ∨4566 ≤ q)→u.natReg q=s.natReg q
lemma setup_frame (W:ℕ) (s:State):Frame s (applyBlock (setup W) s):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma frame_copy {s u v:State} (h:Frame s u) (k:UniformScalarCopyMachine.Frame u v)
 (nat:UniformScalarCopyMachine.NatFrame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq=>(k.2.2.2 q hq).trans (h.2.2.2.1 q hq),
 fun q h0 h1=>(nat q h0).trans (h.2.2.2.2 q h0 h1)⟩
lemma frame_transpose {s u v:State} (h:Frame s u) (k:UniformSectorTransposeMachine.Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq=>(k.2.2.2.1 q hq).trans (h.2.2.2.1 q hq),
 fun q h0 h1=>(k.2.2.2.2 q h0 (by omega)).trans (h.2.2.2.2 q h0 h1)⟩
lemma setup_headers {W X:ℕ} {g:Geometry W true} {s:State} (h:Header g s) (original:s.natReg 4535=X):
 (applyBlock (setup W) s).natReg 147=W*g.volume ∧
 (applyBlock (setup W) s).natReg 148=X ∧(applyBlock (setup W) s).natReg 149=g.native:=by
 simp[setup,applyBlock,Op.apply,writeNat,next,h.volume,h.native,original]
lemma setup_safe {W X:ℕ} {g:Geometry W true} {s:State} (h:Header g s) (original:s.natReg 4535=X)
 (sep:X+W*g.volume ≤ g.native):readable (setup W) s ∧peak (setup W) s ≤ g.B:=by
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.volume,h.native,original]
 have:=g.nativeFit;have:=g.code;have:=g.roles;omega

/-- Complete charged scatter and spectator restoration from the actual child
bank and original native bank. No transformed array/action certificate occurs
at entry: the child bank consists of arbitrary present Scalars. -/
theorem execution {W n X:ℕ} (g:Geometry W true) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (h:Header g s) (cell:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (source:Source g v s) (original:s.natReg 4535=X)
 (originalSource:UniformScalarCopyMachine.Source (W*g.volume) X s.scalarHeap)
 (sep:X+W*g.volume ≤ g.native) (code:51 ≤ g.B) (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W) n x g.B s (7*(W*g.volume)+W*(7*g.sector.width+12)+28) u ∧u.pc=50 ∧
 Filled g v W u ∧Frame s u ∧
 (∀r,r < W→∀j,j < g.volume→j < g.sector.start ∨g.sector.start+g.sector.width ≤ j→
  u.scalarHeap (g.native+r*g.volume+j)=s.scalarHeap (X+r*g.volume+j)) ∧
 UniformScalarCopyMachine.Outside g.native (W*g.volume) s.scalarHeap u:=by
 have safe:=setup_safe h original sep
 have first:=block_runs (setup W) (programFor W) 0 n g.B x s (setup_code W) pc wb
  (by change 0+6 ≤ g.B;omega) safe.1 safe.2
 let a:=applyBlock (setup W) s
 have ap:a.pc=6:=by rw[applyBlock_pc,pc];rfl
 let copyReady:=setPC a 0
 have headers:=setup_headers h original
 obtain ⟨t,copy,copied,_oldSource,copyOut,copyFrame,copyNat⟩:=UniformScalarCopyMachine.execution n x
  (W*g.volume) X g.native g.B copyReady originalSource sep g.nativeFit (by omega) rfl
  headers.1 headers.2.1 headers.2.2 (changePC_bound g.B a 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (copy_code W)
  (by rw[UniformScalarCopyMachine.program_length];omega) (by omega) copy
 rw[UniformMultiAxisSectorMetadataPreparation.placed_zero a 6 ap] at moved
 have fr:Frame s t:=frame_copy (setup_frame W s) copyFrame copyNat
 let ready:=setPC t 0
 have hdr:Header g ready:=by
  refine ⟨?_,?_,?_,?_⟩
  all_goals first | exact (fr.2.2.2.2 _ (by omega) (by omega)).trans h.volume |
   exact (fr.2.2.2.2 _ (by omega) (by omega)).trans h.native |
   exact (fr.2.2.2.2 _ (by omega) (by omega)).trans h.directory |
   exact (fr.2.2.2.2 _ (by omega) (by omega)).trans h.ordinal
 have table:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector ready:=by
  simpa only[UniformSectorBatchDirectoryMachine.BatchCell,ready,setPC,fr.1] using cell
 have sourceR:Source g v ready:=by
  intro r hr j hj
  have bound:=Nat.mul_le_mul_right g.sector.width (show r+1 ≤ W by omega)
  have fit:=Nat.mul_le_mul_left W g.fit
  have before:UniformSectorTransposeMachine.sourceAddress g r+j < g.native:=by
   change g.buffer+W*g.sector.start+r*g.sector.width+j < g.native
   have separation:g.buffer+W*g.volume ≤ g.native:=g.separation
   nlinarith
  exact (copyOut _ (Or.inl before)).trans (source r hr j hj)
 obtain ⟨u,scatter,up,_cursor,filled,frame,out⟩:=UniformSectorTransposeMachine.execution g v x ready hdr table sourceR rfl
  (changePC_bound g.B (setPC t 16) 0 moved.final_bound (by omega))
 have finalRun:=UniformBoundedAssembly.boundedExecution_placed (transpose_code W)
  (by rw[UniformSectorTransposeMachine.program_length];omega) (by omega) scatter
 rw[show placed 16 ready=setPC t 16 by cases t;rfl] at finalRun
 let z:=setPC u 50
 have stop:BoundedExecution (programFor W) n x g.B z 1 z:=.halt finalRun.final_bound
  (by simp[step,z,setPC,halt_at])
 refine ⟨z,?_,rfl,filled,frame_transpose fr frame,?_,?_⟩
 · convert first.executes (moved.executes (finalRun.executes stop)) using 1
   change 7*(W*g.volume)+W*(7*g.sector.width+12)+28=6+(7*(W*g.volume)+4+(W*(7*g.sector.width+12)+17+1))
   omega
 · intro r hr j hj unused
   have address:r*g.volume+j < W*g.volume:=by
    have:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega);nlinarith
   have baseline:ready.scalarHeap (g.native+r*g.volume+j)=s.scalarHeap (X+r*g.volume+j):=by
    simpa only[ready,setPC,copyReady,a,setup,applyBlock,Op.apply,writeNat,next,Nat.add_assoc] using copied _ address
   exact (UniformSectorTransposeMachine.native_spectators out r j hr hj unused).trans baseline
 · intro address outside
   have scatterOutside:∀r,r < W→address < UniformSectorTransposeMachine.targetAddress g r ∨
    UniformSectorTransposeMachine.targetAddress g r+g.sector.width ≤ address:=by
    intro r hr
    change address < g.native+r*g.volume+g.sector.start ∨g.native+r*g.volume+g.sector.start+g.sector.width ≤ address
    rcases outside with before|after
    · exact Or.inl (by omega)
    · have:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
      exact Or.inr (by have:=g.fit;nlinarith)
   exact (out address scatterOutside).trans (copyOut address outside)
end
end ExactFourierCircuits.UniformSectorRestoringScatterPreparation
