import UniformResidualGeneralGatherFrame
import DFTModelSavingNativePivotGeneral
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualGeneralGatherFrame
open UniformMachine UniformAssembly BinaryFrames UniformBinaryXorCoordinates
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformResidualGeneralGatherPreparation
noncomputable section

/-- Same actual bytecode and original execution contract, retaining the least nonzero pivot fact. -/
theorem execution_frame_first (n B q w r U images stack output table A D:ℕ) (v:Vec (Fin (w+1))) (x:Fin n→ ℂ) (s:State)
 (pc:s.pc=0) (input:UniformResidualPermutationPreparation.Inputs q (w+1) U images stack output table s)
 (rest:s.natReg 4100=r) (qp:1 ≤  q) (nonzero:v≠0) (direction:UniformRepeatedMaskMachine.Source U v s)
 (source:s.natReg 4090=A) (destination:s.natReg 4091=D)
 (data:∀j,j <  2^(q*(w+1)+r)→∃z,s.scalarHeap (A+j)=some z)
 (separate:A+2^(q*(w+1)+r) ≤  D ∨ D+2^(q*(w+1)+r) ≤  A)
 (bound:WordBound B s) (code:295 ≤  B) (sourceEnd:U+(w+1) ≤  images)
 (imagesBefore:images+q*(w+1)+r ≤  stack) (stackBefore:stack+2*(q*(w+1)+r) ≤  output)
 (outputBefore:output+2^(q*(w+1)+r) ≤  table) (tableBound:table+2^q*2^q ≤  B)
 (paddedVolume:2^(q*((w+1)+r)) ≤  B)
 (sourceBound:A+2^(q*(w+1)+r) ≤  B) (destinationBound:D+2^(q*(w+1)+r) ≤  B) :
 ∃p:Fin (w+1),∃hp:v p=1,∃u ticks,BoundedExecution program n x B s ticks u ∧
 ticks ≤  UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+10 ∧ u.pc=294 ∧
 (∀j:Fin (2^(q*(w+1)+r)),u.scalarHeap (D+j.val)=
  s.scalarHeap (A+(UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp) j).val)) ∧
 UniformResidualArrayCopyMachine.Outside (2^(q*(w+1)+r)) D s.scalarHeap u ∧
 (∀j:Fin (2^(q*(w+1)+r)),u.natHeap (output+j.val)=some ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp) j).val)) ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧ u.natReg 4015=2^q ∧
 u.natReg 4023=2^(q*(w+1)+r) ∧ u.natReg 4069=1 ∧ RegFrame s u ∧ u.natReg 4071=output ∧
 UniformXorTableMachine.Entries q table (2^q*2^q) u ∧
 (∀z,z < images ∨ table+2^q*2^q ≤ z→u.natHeap z=s.natHeap z) ∧
 u.natReg 4061=w+1 ∧ u.natReg 4067=output ∧ u.natReg 4068=table ∧
 (∀i:Fin (w+1),i.val<p.val→v i=0) := by
 obtain ⟨p,hp,prepared,pt,pr,pcost,pp,count,bank,retainedDir,entries,outside,sh,sr,ou,ro,one,pointer,nr,qSize,first⟩:=
  UniformResidualGeneralPreparation.execution_first n B q w r U images stack output table v x s pc input rest qp nonzero direction
   bound (by omega) sourceEnd (by simpa only [Nat.add_assoc] using imagesBefore) stackBefore outputBefore tableBound paddedVolume
 have prep:=UniformBoundedAssembly.boundedExecution_placed prepare_code (by rw [UniformResidualGeneralPreparation.program_length];omega) (by omega) pr
 have same:placed 0 s=s:=by simp only [placed,Nat.zero_add]
 rw [same] at prep
 let atSetup:State:={prepared with pc:=273}
 have aa:atSetup.natReg 4090=A:=(nr _ (by omega)).trans source
 have dd:atSetup.natReg 4091=D:=(nr _ (by omega)).trans destination
 -- The output pointer is read-only throughout preparation.
 have outptr:atSetup.natReg 4067=output:=pointer
 have oneSetup:atSetup.natReg 4069=1:=one
 have countSetup:atSetup.natReg 4023=2^(q*(w+1)+r):=count
 have safe:readable setup atSetup ∧ peak setup atSetup ≤  B:=by
  simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,countSetup,oneSetup,aa,dd,outptr]
  have volume:2^(q*(w+1)+r) ≤  B:=(Nat.le_add_left _ A).trans sourceBound
  have outbound:output ≤  B:=(Nat.le_add_right output _).trans (outputBefore.trans ((Nat.le_add_right table _).trans tableBound))
  omega
 have ins:=block_runs setup program 273 n B x atSetup setup_code rfl prep.final_bound (by change 278 ≤  B;omega) safe.1 safe.2
 let installed:=applyBlock setup atSetup
 let child:State:={installed with pc:=0}
 let F:=UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp)
 let f:=UniformResidualArrayCopyMachine.finiteIndex F
 have ch:UniformResidualArrayCopyMachine.Header (2^(q*(w+1)+r)) output A D true child:=by
  constructor <;> simp [child,installed,setup,applyBlock,Op.apply,evalNat,writeNat,next,countSetup,oneSetup,aa,dd,outptr]
 have cb:=changePC_bound B installed 0 ins.final_bound (by omega)
 have physical:∀j,j <  2^(q*(w+1)+r)→ child.natHeap (output+j)=some (f j):=by
  intro j hj
  simpa [child,installed,setup,applyBlock,Op.apply,evalNat,writeNat,next,f,UniformResidualArrayCopyMachine.finiteIndex,hj]
   using bank (⟨j,hj⟩:Fin (2^(q*(w+1)+r)))
 have heap:child.scalarHeap=s.scalarHeap:=sh
 have present:∀j,j <  2^(q*(w+1)+r)→∃z,child.scalarHeap (A+j)=some z:=by rw [heap];exact data
 obtain ⟨copied,cr,cp,values,co,cf⟩:=UniformResidualArrayCopyMachine.execution n B (2^(q*(w+1)+r)) output A D true f x child ch
  (UniformResidualArrayCopyMachine.finiteIndex_small F) (by intro i hi j hj eq;exact UniformResidualArrayCopyMachine.finiteIndex_injective F i j hi hj eq) physical present separate
  sourceBound destinationBound (outputBefore.trans ((Nat.le_add_right table _).trans tableBound)) (by omega) rfl cb
 have copyRun:=UniformBoundedAssembly.boundedExecution_placed copy_code (by change 294 ≤  B;omega) (by omega) cr
 have ip:installed.pc=278:=by simp [installed,setup,applyBlock,Op.apply,writeNat,next,atSetup]
 have eq:placed 278 child=installed:=by change {installed with pc:=278}=installed;rw [←ip]
 rw [eq] at copyRun
 let u:State:={copied with pc:=294}
 have final:BoundedExecution program n x B u 1 u:=.halt copyRun.final_bound (by simp [step,u,halt_at])
 have fullRun:BoundedExecution program n x B s (pt+5+(11*2^(q*(w+1)+r)+4)+1) u:=by
  convert (prep.trans (ins.trans copyRun)).executes final using 1;simp [setup];omega
 refine ⟨p,hp,u,pt+5+(11*2^(q*(w+1)+r)+4)+1,?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,first⟩
 · convert (prep.trans (ins.trans copyRun)).executes final using 1;simp [setup];omega
 · omega
 · intro j
   have val:=values j.val j.isLt
   simpa [f,UniformResidualArrayCopyMachine.sourceIndex,UniformResidualArrayCopyMachine.targetIndex,
    UniformResidualArrayCopyMachine.finiteIndex,j.isLt,u,heap,F] using val
 · simpa [UniformResidualArrayCopyMachine.Outside,u,heap] using co
 · intro j
   rw [cf.natHeap]
   exact bank j
 · exact cf.roots.trans ro
 · exact cf.outputs.trans ou

 · have keep:=cf.natReg 4015 (by omega)
   simpa [child,installed,setup,applyBlock,Op.apply,writeNat,next,atSetup,u] using keep.trans qSize
 · have keep:=cf.natReg 4023 (by omega)
   simpa [child,installed,setup,applyBlock,Op.apply,writeNat,next,atSetup,u] using keep.trans count
 · have keep:=cf.natReg 4069 (by omega)
   simpa [child,installed,setup,applyBlock,Op.apply,writeNat,next,atSetup,u] using keep.trans one
 · intro i hi
   have h:=cf.natReg i (by omega)
   have h':copied.natReg i=prepared.natReg i:=by
    simpa (disch:=omega) [child,installed,setup,applyBlock,Op.apply,writeNat,next,atSetup] using h
   exact h'.trans (nr i (by omega))

 · have h:=cf.natReg 4071 (by omega)
   simpa [child,installed,setup,applyBlock,Op.apply,evalNat,writeNat,next,atSetup,u,pointer,one] using h

 · intro i hi
   exact (congrFun cf.natHeap (table+i)).trans (entries i hi)
 · intro z hz
   exact (congrFun cf.natHeap z).trans (outside z hz)
 · exact (UniformRecursiveRegisterFrames.boundedExecution_keep (gather_avoids 4061 (by simp)) fullRun).trans input.descriptor.width
 · exact (UniformRecursiveRegisterFrames.boundedExecution_keep (gather_avoids 4067 (by simp)) fullRun).trans input.output
 · exact (UniformRecursiveRegisterFrames.boundedExecution_keep (gather_avoids 4068 (by simp)) fullRun).trans input.table

end
end ExactFourierCircuits.UniformResidualGeneralGatherFrame
