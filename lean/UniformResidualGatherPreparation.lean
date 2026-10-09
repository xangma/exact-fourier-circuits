import UniformResidualPermutationPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualGatherPreparation
open UniformMachine UniformAssembly BinaryFrames UniformBinaryXorCoordinates
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section
/-- Parent ordinary input arrays are given at Nat4090; the fresh gathered bank
is Nat4091. The permutation is constructed internally from original bits. -/
def setup : List Op := [.literal 4074 0,.binary .mul 4070 4023 4069,
 .binary .mul 4071 4067 4069,.binary .mul 4072 4090 4069,.binary .mul 4073 4091 4069]
def program : Program := UniformResidualPermutationPreparation.program.map (relocate 0 188)++setup.map Op.code++
 UniformResidualArrayCopyMachine.program.map (relocate 193 209)++[.halt]
theorem program_length : program.length=210 := by
 simp only [program,List.length_append,List.length_map,UniformResidualPermutationPreparation.program_length,
  UniformResidualArrayCopyMachine.program_length,setup,List.length_cons,List.length_nil]
theorem prepare_code : CodeAt UniformResidualPermutationPreparation.program program 0 188 := by
 have h:=embed_code [] UniformResidualPermutationPreparation.program
  (setup.map Op.code++UniformResidualArrayCopyMachine.program.map (relocate 193 209)++[.halt]) 188
 simpa only [embed,List.length_nil,List.nil_append,program,List.append_assoc] using h
lemma setup_code : BlockAt setup program 188 := by intro i hi;change i< 5 at hi;interval_cases i <;> rfl
lemma copy_code : CodeAt UniformResidualArrayCopyMachine.program program 193 209 := by
 let head:=UniformResidualPermutationPreparation.program.map (relocate 0 188)++setup.map Op.code
 have len:head.length=193:=by simp only [head,List.length_append,List.length_map,
  UniformResidualPermutationPreparation.program_length,setup,List.length_cons,List.length_nil]
 have h:=embed_code head UniformResidualArrayCopyMachine.program [.halt] 209
 unfold embed at h
 rw [len] at h
 simpa only [head,program,List.append_assoc] using h
lemma halt_at : program[209]?=some .halt := rfl

/-- Real gather from ordinary arbitrary tagged input data, with no supplied
pivot/mask/basis/permutation/table or copied data postcondition. -/
theorem execution (n B q w U images stack output table A D:ℕ) (v:Vec (Fin (w+1))) (x:Fin n→ ℂ) (s:State)
 (pc:s.pc=0) (input:UniformResidualPermutationPreparation.Inputs q (w+1) U images stack output table s)
 (qp:1≤ q) (nonzero:v≠0) (direction:UniformRepeatedMaskMachine.Source U v s)
 (source:s.natReg 4090=A) (destination:s.natReg 4091=D)
 (data:∀j,j< 2^(q*(w+1))→∃z,s.scalarHeap (A+j)=some z)
 (separate:A+2^(q*(w+1))≤ D ∨ D+2^(q*(w+1))≤ A)
 (bound:WordBound B s) (code:210≤ B) (sourceEnd:U+(w+1)≤ images)
 (imagesBefore:images+q*(w+1)≤ stack) (stackBefore:stack+2*(q*(w+1))≤ output)
 (outputBefore:output+2^(q*(w+1))≤ table) (tableBound:table+2^q*2^q≤ B)
 (sourceBound:A+2^(q*(w+1))≤ B) (destinationBound:D+2^(q*(w+1))≤ B) :
 ∃p:Fin (w+1),∃hp:v p=1,∃u ticks,BoundedExecution program n x B s ticks u ∧
 ticks≤ UniformResidualPermutationPreparation.runtimeBound q (w+1)+11*2^(q*(w+1))+10 ∧ u.pc=209 ∧
 (∀j:Fin (2^(q*(w+1))),u.scalarHeap (D+j.val)=
  s.scalarHeap (A+(UniformResidualPermutation.permutation q w v p hp j).val)) ∧
 UniformResidualArrayCopyMachine.Outside (2^(q*(w+1))) D s.scalarHeap u ∧
 (∀j:Fin (2^(q*(w+1))),u.natHeap (output+j.val)=some ((UniformResidualPermutation.permutation q w v p hp j).val)) ∧
 u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs := by
 obtain ⟨p,hp,prepared,pt,pr,pcost,pp,_,count,one,pointer,bank,entries,retainedDir,outside,sh,sr,ou,ro,nr⟩:=
  UniformResidualPermutationPreparation.execution n B q w U images stack output table v x s pc input qp nonzero direction
   bound (by omega) sourceEnd imagesBefore stackBefore outputBefore tableBound
 have prep:=UniformBoundedAssembly.boundedExecution_placed prepare_code (by rw [UniformResidualPermutationPreparation.program_length];omega) (by omega) pr
 have same:placed 0 s=s:=by simp only [placed,Nat.zero_add]
 rw [same] at prep
 let atSetup:State:={prepared with pc:=188}
 have aa:atSetup.natReg 4090=A:=(nr _ (by omega)).trans source
 have dd:atSetup.natReg 4091=D:=(nr _ (by omega)).trans destination
 -- The output pointer is read-only throughout preparation.
 have outptr:atSetup.natReg 4067=output:=pointer
 have oneSetup:atSetup.natReg 4069=1:=one
 have countSetup:atSetup.natReg 4023=2^(q*(w+1)):=count
 have safe:readable setup atSetup ∧ peak setup atSetup≤ B:=by
  simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,countSetup,oneSetup,aa,dd,outptr]
  have volume:2^(q*(w+1))≤ B:=(Nat.le_add_left _ A).trans sourceBound
  have outbound:output≤ B:=(Nat.le_add_right output _).trans (outputBefore.trans ((Nat.le_add_right table _).trans tableBound))
  omega
 have ins:=block_runs setup program 188 n B x atSetup setup_code rfl prep.final_bound (by change 193≤ B;omega) safe.1 safe.2
 let installed:=applyBlock setup atSetup
 let child:State:={installed with pc:=0}
 let F:=UniformResidualPermutation.permutation q w v p hp
 let f:=UniformResidualArrayCopyMachine.finiteIndex F
 have ch:UniformResidualArrayCopyMachine.Header (2^(q*(w+1))) output A D true child:=by
  constructor <;> simp [child,installed,setup,applyBlock,Op.apply,evalNat,writeNat,next,countSetup,oneSetup,aa,dd,outptr]
 have cb:=changePC_bound B installed 0 ins.final_bound (by omega)
 have physical:∀j,j< 2^(q*(w+1))→ child.natHeap (output+j)=some (f j):=by
  intro j hj
  simpa [child,installed,setup,applyBlock,Op.apply,evalNat,writeNat,next,f,UniformResidualArrayCopyMachine.finiteIndex,hj]
   using bank (⟨j,hj⟩:Fin (2^(q*(w+1))))
 have heap:child.scalarHeap=s.scalarHeap:=sh
 have present:∀j,j< 2^(q*(w+1))→∃z,child.scalarHeap (A+j)=some z:=by rw [heap];exact data
 obtain ⟨copied,cr,cp,values,co,cf⟩:=UniformResidualArrayCopyMachine.execution n B (2^(q*(w+1))) output A D true f x child ch
  (UniformResidualArrayCopyMachine.finiteIndex_small F) (by intro i hi j hj eq;exact UniformResidualArrayCopyMachine.finiteIndex_injective F i j hi hj eq) physical present separate
  sourceBound destinationBound (outputBefore.trans ((Nat.le_add_right table _).trans tableBound)) (by omega) rfl cb
 have copyRun:=UniformBoundedAssembly.boundedExecution_placed copy_code (by change 209≤ B;omega) (by omega) cr
 have ip:installed.pc=193:=by simp [installed,setup,applyBlock,Op.apply,writeNat,next,atSetup]
 have eq:placed 193 child=installed:=by change {installed with pc:=193}=installed;rw [←ip]
 rw [eq] at copyRun
 let u:State:={copied with pc:=209}
 have final:BoundedExecution program n x B u 1 u:=.halt copyRun.final_bound (by simp [step,u,halt_at])
 refine ⟨p,hp,u,pt+5+(11*2^(q*(w+1))+4)+1,?_,?_,rfl,?_,?_,?_,?_,?_⟩
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

end
end ExactFourierCircuits.UniformResidualGatherPreparation
