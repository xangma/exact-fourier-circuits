import UniformResidualBasisExecution
import UniformXorCallerInterface
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualDescriptorBankMachine
open UniformMachine UniformAssembly BinaryFrames
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def pivotSetup : List Op := [.literal 4065 1,.binary .mul 4030 4061 4065,.binary .mul 4031 4062 4065]
def maskSetup : List Op := [.literal 3368 1,.binary .mul 3369 4061 4065,.binary .mul 3370 4062 4065]
def imageSetup : List Op := [.binary .mul 4040 4060 4065,.binary .mul 4041 4061 4065,
 .binary .mul 4042 4034 4065,.binary .mul 4043 3371 4065,.binary .mul 4044 4063 4065]
def tail : List Op := [.binary .mul 4008 4050 4065,.binary .mul 4009 4063 4065,.binary .mul 4014 4061 4065]
/-- One fixed caller physically discovers the pivot, constructs the direction
mask from printed bits, and emits all native basis images. -/
def program : Program := pivotSetup.map Op.code++
 UniformResidualPivotMachine.program.map (relocate 3 14)++maskSetup.map Op.code++
 UniformRepeatedMaskMachine.program.map (relocate 17 33)++imageSetup.map Op.code++
 UniformResidualBasisMachine.program.map (relocate 38 67)++tail.map Op.code++[.halt]
theorem program_length : program.length=71 := rfl
theorem pivot_setup_code : BlockAt pivotSetup program 0 := by intro i hi;change i< 3 at hi;interval_cases i <;> rfl
theorem pivot_code : CodeAt UniformResidualPivotMachine.program program 3 14 := by intro i hi;change i< 11 at hi;interval_cases i <;> rfl
theorem mask_setup_code : BlockAt maskSetup program 14 := by intro i hi;change i< 3 at hi;interval_cases i <;> rfl
theorem mask_code : CodeAt UniformRepeatedMaskMachine.program program 17 33 := by intro i hi;change i< 16 at hi;interval_cases i <;> rfl
theorem image_setup_code : BlockAt imageSetup program 33 := by intro i hi;change i< 5 at hi;interval_cases i <;> rfl
theorem image_code : CodeAt UniformResidualBasisMachine.program program 38 67 := by intro i hi;change i< 29 at hi;interval_cases i <;> rfl
theorem tail_code : BlockAt tail program 67 := by intro i hi;change i< 3 at hi;interval_cases i <;> rfl
theorem halt_at : program[70]?=some .halt := rfl

structure Inputs (q w U images : ℕ) (s : State) : Prop where
 columns : s.natReg 4060=q
 width : s.natReg 4061=w
 direction : s.natReg 4062=U
 images : s.natReg 4063=images

open scoped BigOperators
lemma original_mask (w : ℕ) (v : Vec (Fin w)) :
 UniformRepeatedMaskMachine.maskPrefix v w=(UniformBinaryXorCoordinates.encode v).val := by
 calc
  UniformRepeatedMaskMachine.maskPrefix v w=
   ∑i:Fin w,2^i.val*UniformRepeatedMaskMachine.bits v (i.val%w) :=
    (Fin.sum_univ_eq_sum_range (fun i=>2^i*UniformRepeatedMaskMachine.bits v (i%w)) w).symm
  _=∑i:Fin w,2^i.val*(v i).val := by
   apply Finset.sum_congr rfl
   intro i _
   simp [UniformRepeatedMaskMachine.bits,Nat.mod_eq_of_lt i.isLt,i.isLt]
  _=(UniformBinaryXorCoordinates.encode v).val := (UniformBinaryXorCoordinates.encode_value v).symm

/-- Entry contains original printed bits and ordinary header/allocation operands;
no pivot, mask, basis table or action premise is provided. -/
theorem execution (n B q w U images : ℕ) (v : Vec (Fin w)) (x : Fin n→ ℂ) (s : State)
 (pc : s.pc=0) (input : Inputs q w U images s) (qpositive : 1≤ q) (wp : 0< w)
 (nonzero : v≠0) (source : UniformRepeatedMaskMachine.Source U v s)
 (bound : WordBound B s) (code : 71≤ B) (sourceEnd : U+w≤ images)
 (extent : images+q*w≤ B) (volume : 2^(q*w)≤ B) :
 ∃p : Fin w, ∃u ticks,BoundedExecution program n x B s ticks u ∧
 ticks≤ 20*(q*w)+15*w+40 ∧ u.pc=70 ∧ v p=1 ∧
 u.natReg 4008=q*w ∧ u.natReg 4009=images ∧ u.natReg 4014=w ∧
 (∀c, c< q → u.natHeap (images+c)=some (2^(c*w)*(UniformBinaryXorCoordinates.encode v).val)) ∧
 (∀t, t< q*w → t%w≠p.val → u.natHeap (images+UniformResidualBasisMachine.repSlot q w p.val t)=some (2^t)) ∧
 UniformRepeatedMaskMachine.Source U v u ∧
 (∀z, z< images ∨ images+q*w≤ z → u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have oneVolume : 2^w≤ B := by
  have mul:w≤ q*w:=by have h:=Nat.mul_le_mul_right w qpositive;simpa using h
  exact (Nat.pow_le_pow_right (by omega : 1≤ 2) mul).trans volume
 have wb:w≤ B:=by have h:=bound.2.1 4061;rw [input.width] at h;exact h
 have qb:q≤ B:=by have h:=bound.2.1 4060;rw [input.columns] at h;exact h
 have ub:U≤ B:=by omega
 have ib:images≤ B:=by omega
 have safe : readable pivotSetup s ∧ peak pivotSetup s≤ B := by
  simp [pivotSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,input.width,input.direction]
  omega
 have setup:=block_runs pivotSetup program 0 n B x s pivot_setup_code pc bound (by change 3≤ B;omega) safe.1 safe.2
 let ready:=applyBlock pivotSetup s
 let child:State:={ready with pc:=0}
 have cb:=changePC_bound B ready 0 setup.final_bound (by omega)
 obtain ⟨p,found,pr,pp,pindex,pbit,_,pf⟩:=UniformResidualPivotMachine.execution n B w U v x child nonzero rfl
  (by simp [child,ready,pivotSetup,applyBlock,Op.apply,evalNat,writeNat,next,input.width])
  (by simp [child,ready,pivotSetup,applyBlock,Op.apply,evalNat,writeNat,next,input.direction])
  source cb (by omega) (by omega)
 have placedPivot:=UniformBoundedAssembly.boundedExecution_placed pivot_code (by change 14≤ B;omega) (by omega) pr
 have readyPC:ready.pc=3:=by simp [ready,pivotSetup,applyBlock,Op.apply,writeNat,next,pc]
 have same : placed 3 child=ready := by change {ready with pc:=3}=ready;rw [←readyPC]
 rw [same] at placedPivot
 let atMask:State:={found with pc:=14}
 have one:atMask.natReg 4065=1:=by
  have keep:=pf.natReg 4065 (by simp [UniformResidualPivotMachine.Changed])
  simpa [atMask,child,ready,pivotSetup,applyBlock,Op.apply,writeNat,next] using keep
 have retained (r:ℕ) (hr:4060≤ r ∧ r< 4065) : atMask.natReg r=s.natReg r := by
  have keep:=pf.natReg r (by unfold UniformResidualPivotMachine.Changed;omega)
  simpa (disch:=omega) [atMask,child,ready,pivotSetup,applyBlock,Op.apply,writeNat,next] using keep
 have mw:atMask.natReg 4061=w:=(retained _ (by omega)).trans input.width
 have mU:atMask.natReg 4062=U:=(retained _ (by omega)).trans input.direction
 have safeMask : readable maskSetup atMask ∧ peak maskSetup atMask≤ B := by
  simp [maskSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,mw,mU]
  omega
 have maskReady:=block_runs maskSetup program 14 n B x atMask mask_setup_code rfl placedPivot.final_bound
  (by change 17≤ B;omega) safeMask.1 safeMask.2
 let masked:=applyBlock maskSetup atMask
 let maskChild:State:={masked with pc:=0}
 have mb:=changePC_bound B masked 0 maskReady.final_bound (by omega)
 have sourceNow : UniformRepeatedMaskMachine.Source U v maskChild := by
  intro i
  simpa [maskChild,masked,maskSetup,atMask,child,ready,pivotSetup,applyBlock,Op.apply,evalNat,writeNat,next,pf.natHeap] using source i
 obtain ⟨maskDone,mrun,mp,maskValue,maskVolume,mf⟩:=UniformRepeatedMaskMachine.execution 1 w U B n v x maskChild
  rfl (by simp [maskChild,masked,maskSetup,applyBlock,Op.apply,evalNat,writeNat,next])
  (by simp [maskChild,masked,maskSetup,applyBlock,Op.apply,evalNat,writeNat,next,one,mw])
  (by simp [maskChild,masked,maskSetup,applyBlock,Op.apply,evalNat,writeNat,next,one,mU])
  sourceNow mb (by omega) (by omega) (by simpa using oneVolume)
 have placedMask:=UniformBoundedAssembly.boundedExecution_placed mask_code (by change 33≤ B;omega) (by omega) mrun
 have maskedPC:masked.pc=17:=by simp [masked,maskSetup,applyBlock,Op.apply,writeNat,next,atMask]
 have sameMask:placed 17 maskChild=masked:=by change {masked with pc:=17}=masked;rw [←maskedPC]
 rw [sameMask] at placedMask
 let atImage:State:={maskDone with pc:=33}
 have keepImage (r:ℕ) (hr:3379≤ r) : atImage.natReg r=atMask.natReg r := by
  have keep:=mf.natReg r (by omega)
  simpa (disch:=omega) [atImage,maskChild,masked,maskSetup,applyBlock,Op.apply,evalNat,writeNat,next] using keep
 have iOne:atImage.natReg 4065=1:=(keepImage _ (by omega)).trans one
 have iQ:atImage.natReg 4060=q:=(keepImage _ (by omega)).trans ((retained _ (by omega)).trans input.columns)
 have iW:atImage.natReg 4061=w:=(keepImage _ (by omega)).trans mw
 have iA:atImage.natReg 4063=images:=(keepImage _ (by omega)).trans ((retained _ (by omega)).trans input.images)
 have iPivot:atImage.natReg 4034=p.val:=(keepImage _ (by omega)).trans pindex
 have iMask:atImage.natReg 3371=(UniformBinaryXorCoordinates.encode v).val := by
  have convert : (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction 1 v)).val=
   UniformRepeatedMaskMachine.maskPrefix v w := by
   simpa only [Nat.one_mul] using (UniformRepeatedMaskMachine.maskPrefix_direction 1 w v).symm
  exact maskValue.trans (convert.trans (original_mask w v))
 have smallMask:(UniformBinaryXorCoordinates.encode v).val< 2^w:=(UniformBinaryXorCoordinates.encode v).isLt
 have pb : p.val< w:=p.isLt
 have safeImage : readable imageSetup atImage ∧ peak imageSetup atImage≤ B := by
  simp [imageSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,iOne,iQ,iW,iA,iPivot,iMask]
  omega
 have imageReady:=block_runs imageSetup program 33 n B x atImage image_setup_code rfl placedMask.final_bound
  (by change 38≤ B;omega) safeImage.1 safeImage.2
 let imageInput:=applyBlock imageSetup atImage
 let imageChild:State:={imageInput with pc:=0}
 have imageBound:=changePC_bound B imageInput 0 imageReady.final_bound (by omega)
 have args:UniformResidualBasisExecution.Inputs q w p.val (UniformBinaryXorCoordinates.encode v).val images imageChild := by
  constructor <;> simp [imageChild,imageInput,imageSetup,applyBlock,Op.apply,evalNat,writeNat,next,iOne,iQ,iW,iA,iPivot,iMask]
 obtain ⟨imageDone,imageTicks,ir,ic,ip,lengthValue,selectedBank,repBank,ifr⟩:=UniformResidualBasisExecution.execution
  n B q w p.val (UniformBinaryXorCoordinates.encode v).val images x imageChild rfl args wp p.isLt
  smallMask imageBound (by omega) extent volume
 have placedImages:=UniformBoundedAssembly.boundedExecution_placed image_code (by change 67≤ B;omega) (by omega) ir
 have imageInputPC:imageInput.pc=38:=by simp [imageInput,imageSetup,applyBlock,Op.apply,writeNat,next,atImage]
 have sameImage:placed 38 imageChild=imageInput:=by change {imageInput with pc:=38}=imageInput;rw [←imageInputPC]
 rw [sameImage] at placedImages
 let atTail:State:={imageDone with pc:=67}
 have tOne:atTail.natReg 4065=1:=by
  have keep:=ifr.natReg 4065 (by omega)
  simpa [atTail,imageChild,imageInput,imageSetup,applyBlock,Op.apply,evalNat,writeNat,next,iOne] using keep
 have tA:atTail.natReg 4063=images:=by
  have keep:=ifr.natReg 4063 (by omega)
  simpa [atTail,imageChild,imageInput,imageSetup,applyBlock,Op.apply,evalNat,writeNat,next,iA] using keep
 have tW:atTail.natReg 4061=w:=by
  have keep:=ifr.natReg 4061 (by omega)
  simpa [atTail,imageChild,imageInput,imageSetup,applyBlock,Op.apply,evalNat,writeNat,next,iW] using keep
 have tLength:atTail.natReg 4050=q*w := lengthValue
 have safeTail : readable tail atTail ∧ peak tail atTail≤ B := by
  simp [tail,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,tOne,tA,tW,tLength]
  have length:q*w≤ B:=by have h:q*w< 2^(q*w):=Nat.lt_two_pow_self;omega
  omega
 have finishReady:=block_runs tail program 67 n B x atTail tail_code rfl placedImages.final_bound
  (by change 70≤ B;omega) safeTail.1 safeTail.2
 let u:=applyBlock tail atTail
 have up:u.pc=70:=by simp [u,tail,applyBlock,Op.apply,writeNat,next,atTail]
 have halt : BoundedExecution program n x B u 1 u:=.halt finishReady.final_bound (by simp [step,up,halt_at])
 refine ⟨p,u,3+(6*p.val+8)+3+(9*w+8)+5+imageTicks+3+1,?_,?_,up,pbit,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · convert (setup.trans (placedPivot.trans (maskReady.trans (placedMask.trans (imageReady.trans (placedImages.trans finishReady)))))).executes halt using 1
   simp [pivotSetup,maskSetup,imageSetup,tail]
   omega
 · have psmall:=p.isLt
   omega
 · simp [u,tail,applyBlock,Op.apply,evalNat,writeNat,next,tOne,tLength]
 · simp [u,tail,applyBlock,Op.apply,evalNat,writeNat,next,tOne,tA]
 · simp [u,tail,applyBlock,Op.apply,evalNat,writeNat,next,tOne,tW]
 · exact selectedBank
 · exact repBank
 · intro i
   have f:=ifr.outside (U+i.val) (by left;have h:=i.isLt;omega)
   have old : imageChild.natHeap (U+i.val)=some (v i).val := by
    simpa [imageChild,imageInput,imageSetup,applyBlock,Op.apply,evalNat,writeNat,next,atImage,mf.natHeap] using sourceNow i
   exact f.trans old
 · intro z outside
   have f:=ifr.outside z outside
   have originalHeap : imageChild.natHeap=s.natHeap := mf.natHeap.trans pf.natHeap
   exact f.trans (congrFun originalHeap z)
 · exact ifr.scalarHeap.trans (mf.scalarHeap.trans pf.scalarHeap)
 · exact ifr.scalarReg.trans (mf.scalarReg.trans pf.scalarReg)
 · exact ifr.outputs.trans (mf.outputs.trans pf.outputs)
 · exact ifr.roots.trans (mf.roots.trans pf.roots)
def Safe : Instruction→Prop
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _ =>
   ((3350≤d ∧ d≤3378) ∨ (4000≤d ∧ d≤4065)) ∧ (d<4060 ∨ 4063<d)
 | .storeNat _ _ | .branchLT _ _ _ _ | .jump _ | .halt => True
 | _=>False
instance (q : Instruction) : Decidable (Safe q) := by cases q <;> unfold Safe <;> infer_instance

theorem program_safe : ∀q∈program, Safe q := by
 have all : program.all (fun q=>decide (Safe q))=true := by decide
 intro q hq
 exact of_decide_eq_true ((List.all_eq_true.mp all) q hq)

structure Frame (s u : State) : Prop where
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r, (((r<3350 ∨ 3378<r) ∧ (r<4000 ∨ 4065<r)) ∨ (4060≤r ∧ r≤4063)) → u.natReg r=s.natReg r
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u v : State} (f : Frame s u) (g : Frame u v) : Frame s v :=
 ⟨g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,
  g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma write_frame (s : State) (d v : ℕ) (safe : ((3350≤d ∧ d≤3378) ∨ (4000≤d ∧ d≤4065)) ∧ (d<4060 ∨ 4063<d)) :
 Frame s (writeNat s d v) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r keep
 simp [writeNat,next,Function.update_of_ne (show r≠d by omega)]

theorem step_frame (n : ℕ) (x : Fin n→ℂ) (s u : State)
 (h : step program n x s=.running u) : Frame s u := by
 cases code : program[s.pc]? with
 | none=>simp [step,code] at h
 | some q=>
   have safe:=program_safe q (List.mem_of_getElem? code)
   cases q <;> try {change False at safe;exact False.elim safe}
   case natLiteral d v=>
    simp only [step,code,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case natBinary op d l r=>
    cases value : evalNat op (s.natReg l) (s.natReg r) with
    | none=>simp [step,code,value] at h
    | some v=>simp only [step,code,value,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case loadNat d a=>
    cases value : s.natHeap (s.natReg a) with
    | none=>simp [step,code,value] at h
    | some v=>simp only [step,code,value,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case storeNat a r=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case branchLT l r yes no=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case jump pc=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case halt=>simp [step,code] at h

theorem execution_frame {n t : ℕ} {x : Fin n→ℂ} {s u : State}
 (run : Executes program n x s t u) : Frame s u := by
 induction run with
 | halt _=>exact Frame.refl _
 | next h _ ih=>exact (step_frame _ _ _ _ h).trans ih

end
end ExactFourierCircuits.UniformResidualDescriptorBankMachine
