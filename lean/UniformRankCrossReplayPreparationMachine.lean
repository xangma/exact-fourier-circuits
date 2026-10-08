import UniformRankCrossPreparationMachine
import UniformDAGBucketMachine
import UniformReplayCoefficientMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRankCrossReplayPreparationMachine
open UniformMachine UniformAssembly UniformRadixTwoDAG OAI.ExactFourier
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
open UniformRankCrossPreparationMachine

noncomputable section

/-- Retain the physically computed gate-count register without modifying the
frozen whole722 source or adding any gate-count premise. -/
theorem depth_call_enriched (p : Parameters) (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (header:ReadyHeader p s) (layout:Layout p B)
    (args:UniformDAGDepthMachine.Header p.e (Shape p) p.tape p.depth s)
    (tape:UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape s)
    (hp:s.pc=686) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ UniformDAGDepthMachine.runtimeBudget p.e (Shape p) ∧
    u.pc=721 ∧ ReadyHeader p u ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),u.natHeap (p.depth+i.val)=some
      (UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i)) ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),UniformToeplitzCrossDAG.runDepth
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i ≤ 8*p.K+6) ∧
    UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape u ∧ Frame p s u ∧ u.scalarHeap=s.scalarHeap ∧ u.natReg 651=Shape p := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by have :=layout.2.2.2.2.2.2;omega)
  have size:=cross_size p layout.1.widthA layout.1.widthE
  have typedArgs:UniformDAGDepthMachine.Header p.e
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size p.tape p.depth e:=by
    refine ⟨args.inputs,?_,args.tape,args.bank⟩
    simpa only [size,e,setPC] using args.gates
  obtain ⟨v,t,run,tc,vp,vargs,bank,height,vtape,outside,fr⟩:=UniformDAGDepthMachine.cross_execution
    p.K p.a p.e layout.1.widthA layout.1.widthE p.tape p.depth B n x e typedArgs rfl tape
    (by simpa only [size] using layout.2.2.2.2.1)
    (by simpa only [size,Nat.add_assoc] using layout.2.2.2.2.2.1)
    (by have :=layout.2.2.2.2.2.2;omega) eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed depth_code
    (by rw [UniformDAGDepthMachine.program_length];have :=layout.2.2.2.2.2.2;omega)
    (by have :=layout.2.2.2.2.2.2;omega) run
  have pe:placed 686 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 721
  have wh:ReadyHeader p u:=((header.withPC 0).transport (depth_working fr)).withPC 721
  have gates:u.natReg 651=Shape p:=by simpa only [size,u,setPC] using vargs.gates
  refine ⟨u,t,placedRun,?_,rfl,wh,?_,?_,vtape,?_,fr.1,gates⟩
  · simpa only [size] using tc
  · exact bank
  · exact height
  · apply depth_frame (p:=p) fr
    intro q hq
    exact outside q (by simpa only [size] using hq)

theorem whole_execution_enriched (p : Parameters) (B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (header:Header p s) (layout:Layout p B)
    (bh:UniformRankKernelMachine.Bank p.H p.hSize h s)
    (bg:UniformRankKernelMachine.Bank p.G p.gSize g s)
    (master:s.scalarHeap 0=some (prepared (zeta p.D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget p ∧ u.pc=721 ∧ ReadyHeader p u ∧
    UniformKernelSpectrumMachine.Result p.K p.C (kernelValues p h g) u ∧
    u.scalarHeap (p.C+7*width p.K)=some (prepared (zeta (width p.K))) ∧
    UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape u ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),
      u.natHeap (p.depth+i.val)=some (UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i)) ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),
      UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i ≤ 8*p.K+6) ∧
    UniformRankKernelMachine.Bank p.H p.hSize h u ∧ UniformRankKernelMachine.Bank p.G p.gSize g u ∧
    Frame p s u ∧ u.scalarHeap 0=s.scalarHeap 0 ∧ u.natReg 651=Shape p := by
  have codeB:=layout.2.2.2.2.2.2
  obtain ⟨v,start,vp,vh,vf⟩:=sizing_call p B n x s header hp hs layout
  have hgv:UniformRankKernelMachine.Bank p.H p.hSize h v:=by
    exact vf.source layout bh layout.1.hFresh
  have ggv:UniformRankKernelMachine.Bank p.G p.gSize g v:=by
    exact vf.source layout bg layout.1.gFresh
  obtain ⟨w,rank,wp,wh,kernels,_,_,wf⟩:=rank_call p B n h g x v vh layout hgv ggv vp start.final_bound
  have beforeSpec:Frame p s w:=vf.trans wf
  have wm:w.scalarHeap 0=some (prepared (zeta p.D)):=(beforeSpec.master layout).trans master
  obtain ⟨z,ts,spectrum,tsB,zp,zh,bank,root,zf⟩:=spectrum_call p B n h g x w wh layout kernels wm wp rank.final_bound
  have safe:=crossSetup_safe zh spectrum.final_bound
  have crossStart:=block_runs crossSetup program 399 n B x z crossSetup_at zp spectrum.final_bound
    (by rw [crossSetup_length];omega) safe.1 safe.2
  let q:=applyBlock crossSetup z
  have qc:=crossSetup_spec zh
  have qp:q.pc=402:=by rw [UniformTensorMonomialMachine.applyBlock_pc,zp,crossSetup_length]
  obtain ⟨r,tc,cross,tcB,rp,rh,tape,rf,rs⟩:=cross_call p B n x q qc.1 layout qc.2 qp crossStart.final_bound
  have dsafe:=depthSetup_safe rh layout
  have depthStart:=block_runs depthSetup program 673 n B x r depthSetup_at rp cross.final_bound
    (by rw [depthSetup_length];omega) dsafe.1 dsafe.2
  let a:=applyBlock depthSetup r
  have ac:=depthSetup_spec rh
  have ap:a.pc=686:=by rw [UniformTensorMonomialMachine.applyBlock_pc,rp,depthSetup_length]
  have atape:UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape a:=tape
  obtain ⟨u,td,depth,tdB,up,uh,labels,height,utape,uf,us,ugates⟩:=depth_call_enriched p B n x a ac.1 layout ac.2 atape ap depthStart.final_bound
  have fullFrame:Frame p s u:=beforeSpec.trans (zf.trans ((caller_frame p crossSetup z (Or.inl rfl)).trans
    (rf.trans ((caller_frame p depthSetup r (Or.inr rfl)).trans uf))))
  have scalarEq:u.scalarHeap=z.scalarHeap:=us.trans rs
  have ubank:UniformKernelSpectrumMachine.Result p.K p.C (kernelValues p h g) u:=by
    intro j;rw [scalarEq];exact bank j
  have uroot:u.scalarHeap (p.C+7*width p.K)=some (prepared (zeta (width p.K))):=by rw [scalarEq];exact root
  have stop:BoundedExecution program n x B u 1 u:=.halt depth.final_bound (by simp only [step,up,final_halt])
  refine ⟨u,4*p.K+9+UniformRankKernelMachine.runtime p.rank+ts+3+tc+13+td+1,?_,?_,up,uh,ubank,uroot,
    utape,labels,height,fullFrame.source layout bh layout.1.hFresh,fullFrame.source layout bg layout.1.gFresh,
    fullFrame,fullFrame.master layout,ugates⟩
  · convert start.executes (rank.executes (spectrum.executes (crossStart.executes
      (cross.executes (depthStart.executes (depth.executes stop)))))) using 1
    simp only [crossSetup_length,depthSetup_length]
    omega
  · unfold runtimeBudget
    omega


end

/-- Caller inputs950..953 are addresses only. Every intermediate header is
installed by the literal programs below. -/
structure ReplayParameters where
 base : UniformRankCrossPreparationMachine.Parameters
 order : ℕ
 directory : ℕ
 negative : ℕ
 constants : ℕ

def bucketSetup : List Op := [.add 700 651 670,.add 701 675 485,
 .literal 954 1,.add 701 701 954,.add 702 950 670,.add 703 951 670]
def coefficientSetup : List Op := [.add 760 525 670,.add 761 529 670,
 .add 762 952 670,.add 763 953 670]
def beforeBucket : Program := UniformRankCrossPreparationMachine.program.map (relocate 0 722) ++ bucketSetup.map Op.code
def beforeCoefficient : Program := beforeBucket ++
 UniformDAGBucketMachine.program.map (relocate 728 752) ++ coefficientSetup.map Op.code
def program : Program := beforeCoefficient ++
 UniformReplayCoefficientMachine.program.map (relocate 756 798) ++ [.halt]
theorem bucketSetup_length : bucketSetup.length=6 := rfl
theorem coefficientSetup_length : coefficientSetup.length=4 := rfl
theorem beforeBucket_length : beforeBucket.length=728 := by
 simp [beforeBucket,bucketSetup_length,UniformRankCrossPreparationMachine.program_length]
theorem beforeCoefficient_length : beforeCoefficient.length=756 := by
 simp [beforeCoefficient,beforeBucket_length,UniformDAGBucketMachine.program_length,coefficientSetup_length]
theorem program_length : program.length=799 := by
 simp [program,beforeCoefficient_length,UniformReplayCoefficientMachine.program_length]
theorem whole_code : CodeAt UniformRankCrossPreparationMachine.program program 0 722 := by
 let after:=bucketSetup.map Op.code ++ UniformDAGBucketMachine.program.map (relocate 728 752) ++
  coefficientSetup.map Op.code ++ UniformReplayCoefficientMachine.program.map (relocate 756 798) ++ [.halt]
 have he:program=[] ++ UniformRankCrossPreparationMachine.program.map (relocate 0 722) ++ after:=by
  simp [program,beforeCoefficient,beforeBucket,after,List.append_assoc]
 rw [he]
 exact segment_code [] after UniformRankCrossPreparationMachine.program 0 722 rfl

theorem bucket_code : CodeAt UniformDAGBucketMachine.program program 728 752 := by
 let after:=coefficientSetup.map Op.code ++ UniformReplayCoefficientMachine.program.map (relocate 756 798) ++ [.halt]
 have he:program=beforeBucket ++ UniformDAGBucketMachine.program.map (relocate 728 752) ++ after:=by
  simp [program,beforeCoefficient,after,List.append_assoc]
 rw [he]
 exact segment_code beforeBucket after UniformDAGBucketMachine.program 728 752 beforeBucket_length

theorem coefficient_code : CodeAt UniformReplayCoefficientMachine.program program 756 798 :=
 segment_code beforeCoefficient [.halt] UniformReplayCoefficientMachine.program 756 798 beforeCoefficient_length

theorem bucketSetup_at : BlockAt bucketSetup program 722 := by
 intro i hi
 have len:=UniformRankCrossPreparationMachine.program_length
 have he:program=(UniformRankCrossPreparationMachine.program.map (relocate 0 722) ++ bucketSetup.map Op.code) ++
  (UniformDAGBucketMachine.program.map (relocate 728 752) ++ coefficientSetup.map Op.code ++
   UniformReplayCoefficientMachine.program.map (relocate 756 798) ++ [.halt]):=by
  simp [program,beforeCoefficient,beforeBucket,List.append_assoc]
 have hi' : i < 6 := by simpa only [bucketSetup_length] using hi
 rw [he,List.getElem?_append_left (by simp only [List.length_append,List.length_map,len,bucketSetup_length];omega),
  List.getElem?_append_right (by simp [len])]
 simp only [List.length_map,len,show 722+i-722=i by omega,List.getElem?_map]
 simp [hi]

theorem coefficientSetup_at : BlockAt coefficientSetup program 752 := by
 intro i hi
 have he:program=((beforeBucket ++ UniformDAGBucketMachine.program.map (relocate 728 752)) ++ coefficientSetup.map Op.code) ++
  (UniformReplayCoefficientMachine.program.map (relocate 756 798) ++ [.halt]):=by
  simp [program,beforeCoefficient,List.append_assoc]
 have len:(beforeBucket ++ UniformDAGBucketMachine.program.map (relocate 728 752)).length=752:=by
  simp [beforeBucket_length,UniformDAGBucketMachine.program_length]
 have hi' : i < 4 := by simpa only [coefficientSetup_length] using hi
 rw [he,List.getElem?_append_left (by simp only [List.length_append,List.length_map,beforeBucket_length,UniformDAGBucketMachine.program_length,coefficientSetup_length];omega),
  List.getElem?_append_right (by rw [len];omega)]
 simp only [len,show 752+i-752=i by omega,List.getElem?_map]
 simp [hi]

theorem final_halt : program[798]?=some .halt := by
 rw [program,List.getElem?_append_right (by simp [beforeCoefficient_length,UniformReplayCoefficientMachine.program_length])]
 simp [beforeCoefficient_length,UniformReplayCoefficientMachine.program_length]

structure ExtraHeader (p : ReplayParameters) (s : State) : Prop where
 order : s.natReg 950=p.order
 directory : s.natReg 951=p.directory
 negative : s.natReg 952=p.negative
 constants : s.natReg 953=p.constants

structure ReplayLayout (p : ReplayParameters) (B : ℕ) : Prop where
 original : UniformRankCrossPreparationMachine.Layout p.base B
 fftFresh : p.base.d+3*count p.base.K ≤ p.order
 depthFresh : p.base.depth+p.base.e+1+Shape p.base ≤ p.order
 directoryFresh : p.order+Shape p.base*(Shape p.base+1) ≤ p.directory
 directoryBound : p.directory+Shape p.base+2 ≤ B
 negativeFresh : p.base.C+7*width p.base.K+1 ≤ p.negative
 constantsFresh : p.negative+7*width p.base.K ≤ p.constants
 constantsBound : p.constants+6 ≤ B
 codeBound : 799 ≤ B

/-- The post722 helpers write700..711,760..772 and caller scratch954. -/
def TailPreserved (r : ℕ) : Prop := (r < 700 ∨ 712 ≤ r) ∧ (r < 760 ∨ 773 ≤ r) ∧ r ≠ 954

def TailFrame (p : ReplayParameters) (s u : State) : Prop :=
 (∀q,(q < p.order ∨ p.order+Shape p.base*(Shape p.base+1) ≤ q) →
  (q < p.directory ∨ p.directory+Shape p.base+2 ≤ q) → u.natHeap q=s.natHeap q) ∧
 (∀q,(q < p.negative ∨ p.negative+7*width p.base.K ≤ q) →
  (q < p.constants ∨ p.constants+6 ≤ q) → u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,TailPreserved r → u.natReg r=s.natReg r)

noncomputable section

theorem TailFrame.refl (p : ReplayParameters) (s : State) : TailFrame p s s :=
 ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,fun _ _=>rfl⟩
theorem TailFrame.trans {p : ReplayParameters} {s u v : State}
 (h:TailFrame p s u) (h':TailFrame p u v) : TailFrame p s v :=
 ⟨fun q a b=>(h'.1 q a b).trans (h.1 q a b),
 fun q a b=>(h'.2.1 q a b).trans (h.2.1 q a b),
 h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
 fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
theorem TailFrame.withPC {p : ReplayParameters} {s u : State}
 (h:TailFrame p s u) (pc : ℕ) : TailFrame p s (setPC u pc) := h

theorem header_range {r : ℕ} (hr:r ∈ headerRegisters) : TailPreserved r := by
 simp only [headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
 unfold TailPreserved
 omega

theorem TailFrame.ready {p : ReplayParameters} {s u : State} (f:TailFrame p s u)
 (h:ReadyHeader p.base s) : ReadyHeader p.base u := by
 refine ⟨?_,?_,?_,?_⟩
 · intro r hr;exact (f.2.2.2.2 r (header_range hr)).trans (h.1 r hr)
 · exact (f.2.2.2.2 489 (by unfold TailPreserved;decide)).trans h.2.1
 · exact (f.2.2.2.2 526 (by unfold TailPreserved;decide)).trans h.2.2.1
 · exact (f.2.2.2.2 670 (by unfold TailPreserved;decide)).trans h.2.2.2

theorem TailFrame.extra {p : ReplayParameters} {s u : State} (f:TailFrame p s u)
 (h:ExtraHeader p s) : ExtraHeader p u :=
 ⟨(f.2.2.2.2 950 (by unfold TailPreserved;decide)).trans h.order,(f.2.2.2.2 951 (by unfold TailPreserved;decide)).trans h.directory,
 (f.2.2.2.2 952 (by unfold TailPreserved;decide)).trans h.negative,(f.2.2.2.2 953 (by unfold TailPreserved;decide)).trans h.constants⟩

theorem caller_frame (p : ReplayParameters) (b : List Op) (s : State)
 (hb:b=bucketSetup ∨ b=coefficientSetup) : TailFrame p s (applyBlock b s) := by
 rcases hb with rfl|rfl
 all_goals refine ⟨fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,?_⟩
 all_goals intro r hr
 all_goals unfold TailPreserved at hr
 all_goals simp (disch:=omega) [bucketSetup,coefficientSetup,applyBlock,Op.apply,writeNat,next]

theorem bucketSetup_spec {p : ReplayParameters} {s : State}
 (ready:ReadyHeader p.base s) (extra:ExtraHeader p s) (shape:s.natReg 651=Shape p.base) :
 UniformDAGBucketMachine.Header (Shape p.base) (p.base.depth+p.base.e+1) p.order p.directory
  (applyBlock bucketSetup s) := by
 have hd:=ready.1 675 (by decide)
 have he:=ready.1 485 (by decide)
 constructor
 all_goals simp [bucketSetup,applyBlock,Op.apply,writeNat,next,ready.2.2.2,shape,
  extra.order,extra.directory,hd,he,UniformRankCrossPreparationMachine.Parameters.register]

theorem bucketSetup_safe {p : ReplayParameters} {s : State} {B : ℕ}
 (ready:ReadyHeader p.base s) (layout:ReplayLayout p B) (extra:ExtraHeader p s)
 (shape:s.natReg 651=Shape p.base) : readable bucketSetup s ∧ peak bucketSetup s ≤ B := by
 have sd:=layout.depthFresh
 have dB:=layout.directoryBound
 have qR:=layout.directoryFresh
 have z:=ready.2.2.2
 have hd:=ready.1 675 (by decide)
 have he:=ready.1 485 (by decide)
 simp [readable,peak,bucketSetup,Op.readable,Op.peak,Op.apply,writeNat,next,z,shape,
  extra.order,extra.directory,hd,he,UniformRankCrossPreparationMachine.Parameters.register]
 omega

theorem coefficientSetup_spec {p : ReplayParameters} {s : State}
 (ready:ReadyHeader p.base s) (extra:ExtraHeader p s) :
 UniformReplayCoefficientMachine.Header p.base.K p.base.C p.negative p.constants
  (applyBlock coefficientSetup s) := by
 have hk:=ready.1 525 (by decide)
 have hc:=ready.1 529 (by decide)
 constructor
 all_goals simp [coefficientSetup,applyBlock,Op.apply,writeNat,next,ready.2.2.2,
  extra.negative,extra.constants,hk,hc,UniformRankCrossPreparationMachine.Parameters.register]

theorem coefficientSetup_safe {p : ReplayParameters} {s : State} {B : ℕ}
 (ready:ReadyHeader p.base s) (_extra:ExtraHeader p s) (hs:WordBound B s) :
 readable coefficientSetup s ∧ peak coefficientSetup s ≤ B := by
 have hk:=hs.2.1 525
 have hc:=hs.2.1 529
 have ht:=hs.2.1 952
 have hp:=hs.2.1 953
 simpa [readable,peak,coefficientSetup,Op.readable,Op.peak,Op.apply,writeNat,next,ready.2.2.2]
  using And.intro hk (And.intro hc (And.intro ht hp))


def cross (p : ReplayParameters) {B : ℕ} (layout:ReplayLayout p B) :=
 UniformToeplitzCrossDAG.crossDAG p.base.K p.base.a p.base.e layout.original.1.widthA layout.original.1.widthE

theorem cross_shape (p : ReplayParameters) {B : ℕ} (layout:ReplayLayout p B) :
 (cross p layout).size=Shape p.base := cross_size p.base _ _

def bankValues (p : ReplayParameters) (h g : ℕ → ℂ) (j : ℕ) : ℂ :=
 if hj:j < UniformToeplitzCrossDAG.bankSize p.base.K then
  UniformToeplitzCrossDAG.sharedBank p.base.K (kernelValues p.base h g) ⟨j,hj⟩ else 0

theorem bank_source {p : ReplayParameters} {h g : ℕ → ℂ} {s : State}
 (bank:UniformKernelSpectrumMachine.Result p.base.K p.base.C (kernelValues p.base h g) s) :
 UniformReplayCoefficientMachine.Source p.base.C (7*width p.base.K) (bankValues p h g) s := by
 intro j hj
 have hj':j < UniformToeplitzCrossDAG.bankSize p.base.K:=by
  unfold UniformToeplitzCrossDAG.bankSize;omega
 simpa only [bankValues,dite_eq_left hj'] using bank ⟨j,hj'⟩

structure BasePost (p : ReplayParameters) (B : ℕ) (layout:ReplayLayout p B)
 (h g : ℕ → ℂ) (s : State) : Prop where
 ready : ReadyHeader p.base s
 extra : ExtraHeader p s
 shape : s.natReg 651=Shape p.base
 positive : UniformKernelSpectrumMachine.Result p.base.K p.base.C (kernelValues p.base h g) s
 root : s.scalarHeap (p.base.C+7*width p.base.K)=some (prepared (zeta (width p.base.K)))
 tape : UniformDAGDepthMachine.EncodedTape (cross p layout).program p.base.tape s
 depths : ∀i : Fin (p.base.e+1+(cross p layout).size),s.natHeap (p.base.depth+i.val)=
  some (UniformToeplitzCrossDAG.runDepth (cross p layout).program (fun _=>0) i)
 height : ∀i : Fin (p.base.e+1+(cross p layout).size),
  UniformToeplitzCrossDAG.runDepth (cross p layout).program (fun _=>0) i ≤ 8*p.base.K+6
 sourceH : UniformRankKernelMachine.Bank p.base.H p.base.hSize h s
 sourceG : UniformRankKernelMachine.Bank p.base.G p.base.gSize g s
 master : s.scalarHeap 0=some (prepared (zeta p.base.D))

theorem ExtraHeader.withPC {p : ReplayParameters} {s : State}
 (h:ExtraHeader p s) (pc : ℕ) : ExtraHeader p (setPC s pc) :=
 ⟨h.order,h.directory,h.negative,h.constants⟩

theorem BasePost.withPC {p : ReplayParameters} {B : ℕ} {layout:ReplayLayout p B}
 {h g : ℕ → ℂ} {s : State} (post:BasePost p B layout h g s) (pc : ℕ) :
 BasePost p B layout h g (setPC s pc) :=
 ⟨post.ready.withPC pc,post.extra.withPC pc,post.shape,post.positive,post.root,post.tape,
 post.depths,post.height,post.sourceH,post.sourceG,post.master⟩

theorem TailFrame.nat_before {p : ReplayParameters} {B : ℕ} {s u : State}
 (f:TailFrame p s u) (layout:ReplayLayout p B) (q : ℕ) (hq:q < p.order) :
 u.natHeap q=s.natHeap q := by
 have qr: p.order ≤ p.directory:=by have :=layout.directoryFresh;omega
 exact f.1 q (Or.inl hq) (Or.inl (by omega))

theorem TailFrame.scalar_before {p : ReplayParameters} {B : ℕ} {s u : State}
 (f:TailFrame p s u) (layout:ReplayLayout p B) (q : ℕ) (hq:q < p.negative) :
 u.scalarHeap q=s.scalarHeap q := by
 have tp:p.negative ≤ p.constants:=by have :=layout.constantsFresh;omega
 exact f.2.1 q (Or.inl hq) (Or.inl (by omega))

theorem TailFrame.post {p : ReplayParameters} {B : ℕ} {layout:ReplayLayout p B}
 {h g : ℕ → ℂ} {s u : State} (f:TailFrame p s u) (post:BasePost p B layout h g s) :
 BasePost p B layout h g u := by
 have cs:p.base.S ≤ p.base.C:=by
  have :=layout.original.2.1.sourceEnd.trans layout.original.2.1.arena_le_bank
  omega
 have cn:p.base.C < p.negative:=by have :=layout.negativeFresh;omega
 have shapeEq:=cross_shape p layout
 have dirF:=layout.directoryFresh
 have tapeEnd:p.base.tape+5*(cross p layout).size ≤ p.order:=by
  rw [shapeEq]
  have :=layout.original.2.2.2.2.1
  have :=layout.depthFresh
  omega
 refine ⟨f.ready post.ready,f.extra post.extra,
  (f.2.2.2.2 651 (by unfold TailPreserved;decide)).trans post.shape,?_,?_,?_,?_,post.height,?_,?_,?_⟩
 · intro j
   have hj:=j.isLt
   unfold UniformToeplitzCrossDAG.bankSize at hj
   have eqn:=f.scalar_before layout (p.base.C+j.val) (by have :=layout.negativeFresh;omega)
   exact eqn.trans (post.positive j)
 · exact (f.scalar_before layout _ (by have :=layout.negativeFresh;omega)).trans post.root
 · apply post.tape.outside (P:=p.order) (size:=p.directory+Shape p.base+2) tapeEnd
   intro q hq
   rcases hq with hq|hq
   · exact f.nat_before layout q hq
   · apply f.1 q <;> right <;> omega
 · intro i
   have hi : i.val < p.base.e+1+Shape p.base := by simpa only [shapeEq] using i.isLt
   have hd:=layout.depthFresh
   exact (f.nat_before layout _ (by omega)).trans (post.depths i)
 · intro i hi
   have fresh:=layout.original.1.hFresh
   simp only [UniformRankCrossPreparationMachine.Parameters.rank] at fresh
   exact (f.scalar_before layout _ (by omega)).trans (post.sourceH i hi)
 · intro i hi
   have fresh:=layout.original.1.gFresh
   simp only [UniformRankCrossPreparationMachine.Parameters.rank] at fresh
   exact (f.scalar_before layout _ (by omega)).trans (post.sourceG i hi)
 · exact (f.scalar_before layout 0 (by omega)).trans post.master

def gateDepth (p : ReplayParameters) {B : ℕ} (layout:ReplayLayout p B) :=
 UniformDAGBucketMachine.typedDepth (cross p layout).program

structure BucketPost (p : ReplayParameters) (B : ℕ) (layout:ReplayLayout p B) (s : State) : Prop where
 bank : UniformDAGBucketMachine.Bank p.order
  (UniformDAGBucketMachine.order (cross p layout).size (gateDepth p layout)) s
 directory : UniformDAGBucketMachine.Directory p.directory (cross p layout).size
  ((cross p layout).size+2) (gateDepth p layout) s
 permutation : (UniformDAGBucketMachine.order (cross p layout).size (gateDepth p layout)).Perm
  (List.range (cross p layout).size)
 length : (UniformDAGBucketMachine.order (cross p layout).size (gateDepth p layout)).length=(cross p layout).size
 stable : (UniformDAGBucketMachine.order (cross p layout).size (gateDepth p layout)).Pairwise
  (fun a b=>gateDepth p layout a < gateDepth p layout b ∨ (gateDepth p layout a=gateDepth p layout b ∧ a < b))

theorem BucketPost.withPC {p : ReplayParameters} {B : ℕ} {layout:ReplayLayout p B} {s : State}
 (post:BucketPost p B layout s) (pc : ℕ) : BucketPost p B layout (setPC s pc) :=
 ⟨post.bank,post.directory,post.permutation,post.length,post.stable⟩

theorem BucketPost.heap {p : ReplayParameters} {B : ℕ} {layout:ReplayLayout p B} {s u : State}
 (post:BucketPost p B layout s) (eqn:u.natHeap=s.natHeap) : BucketPost p B layout u := by
 refine ⟨?_,?_,post.permutation,post.length,post.stable⟩
 · intro j hj;rw [eqn];exact post.bank j hj
 · intro j hj;rw [eqn];exact post.directory j hj

theorem whole_call (p : ReplayParameters) (B n : ℕ) (layout:ReplayLayout p B)
 (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
 (header:UniformRankCrossPreparationMachine.Header p.base s) (extra:ExtraHeader p s)
 (bh:UniformRankKernelMachine.Bank p.base.H p.base.hSize h s)
 (bg:UniformRankKernelMachine.Bank p.base.G p.base.gSize g s)
 (master:s.scalarHeap 0=some (prepared (zeta p.base.D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedRuns program n x B s t u ∧ t ≤ UniformRankCrossPreparationMachine.runtimeBudget p.base ∧
 u.pc=722 ∧ BasePost p B layout h g u ∧ UniformRankCrossPreparationMachine.Frame p.base s u := by
 obtain ⟨v,t,run,cost,pc,ready,bank,root,tape,labels,height,vh,vg,frame,vm,gates⟩:=
  whole_execution_enriched p.base B n h g x s header layout.original bh bg master hp hs
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed whole_code
  (by rw [UniformRankCrossPreparationMachine.program_length];have :=layout.codeBound;omega)
  (by have :=layout.codeBound;omega) run
 have pe:placed 0 s=s:=by cases s;simp [placed]
 rw [pe] at placedRun
 let u:=setPC v 722
 have ex:ExtraHeader p v:=by
  refine ⟨?_,?_,?_,?_⟩
  all_goals first
   | exact (frame.2.2.2.2 _ (Or.inr (Or.inr (by omega)))).trans extra.order
   | exact (frame.2.2.2.2 _ (Or.inr (Or.inr (by omega)))).trans extra.directory
   | exact (frame.2.2.2.2 _ (Or.inr (Or.inr (by omega)))).trans extra.negative
   | exact (frame.2.2.2.2 _ (Or.inr (Or.inr (by omega)))).trans extra.constants
 have post:BasePost p B layout h g v:=⟨ready,ex,gates,bank,root,tape,labels,height,vh,vg,vm.trans master⟩
 exact ⟨u,t,placedRun,cost,rfl,post.withPC 722,frame.withPC 722⟩

theorem bucket_frame {p : ReplayParameters} {s u : State}
 (outside:UniformDAGBucketMachine.Outside p.order (Shape p.base*(Shape p.base+1))
  p.directory (Shape p.base+2) s u) (fr:UniformDAGBucketMachine.Frame s u) : TailFrame p s u := by
 refine ⟨outside,fun q _ _=>congrFun fr.1 q,fr.2.2.1,fr.2.2.2.1,?_⟩
 intro r hr
 exact fr.2.2.2.2 r (by unfold TailPreserved at hr;omega)

theorem bucket_call (p : ReplayParameters) (B n : ℕ) (layout:ReplayLayout p B)
 (x : Fin n → ℂ) (s : State) (h g : ℕ → ℂ) (post:BasePost p B layout h g s)
 (args:UniformDAGBucketMachine.Header (Shape p.base) (p.base.depth+p.base.e+1) p.order p.directory s)
 (hp:s.pc=728) (hs:WordBound B s) : ∃u t,
 BoundedRuns program n x B s t u ∧ t ≤ UniformDAGBucketMachine.runtimeBudget (Shape p.base) ∧
 u.pc=752 ∧ BucketPost p B layout u ∧ TailFrame p s u := by
 let entry:=setPC s 0
 have eb:=changePC_bound B s 0 hs (by have :=layout.codeBound;omega)
 have shapeEq:=cross_shape p layout
 have args':UniformDAGBucketMachine.Header (cross p layout).size (p.base.depth+p.base.e+1)
  p.order p.directory entry:=by
   refine ⟨?_,args.source,args.output,args.directory⟩
   change s.natReg 700=(cross p layout).size
   simpa only [shapeEq] using args.count
 obtain ⟨v,t,run,cost,pc,_,bank,dir,_,perm,len,stable,outside,fr⟩:=
  UniformDAGBucketMachine.typed_execution (cross p layout).program p.base.depth p.order p.directory B n x entry
   args' rfl post.depths (by simpa only [shapeEq] using layout.depthFresh)
   (by simpa only [shapeEq] using layout.directoryFresh)
   (by simpa only [shapeEq] using layout.directoryBound) (by have :=layout.codeBound;omega) eb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed bucket_code
  (by rw [UniformDAGBucketMachine.program_length];have :=layout.codeBound;omega)
  (by have :=layout.codeBound;omega) run
 have pe:placed 728 entry=s:=by cases s;simp_all [placed,entry,setPC]
 rw [pe] at placedRun
 let u:=setPC v 752
 have bp:BucketPost p B layout v:=⟨bank,dir,perm,len,stable⟩
 have tf:TailFrame p s v:=bucket_frame (by simpa only [UniformDAGBucketMachine.Outside,shapeEq,entry,setPC] using outside) fr
 exact ⟨u,t,placedRun,by simpa only [shapeEq] using cost,rfl,bp.withPC 752,tf.withPC 752⟩

theorem coefficient_frame {p : ReplayParameters} {s u : State}
 (outside:∀j,(j < p.negative ∨ p.negative+7*width p.base.K ≤ j) →
  (j < p.constants ∨ p.constants+6 ≤ j) → u.scalarHeap j=s.scalarHeap j)
 (fr:UniformReplayCoefficientMachine.Frame s u) : TailFrame p s u := by
 refine ⟨fun q _ _=>congrFun fr.1 q,outside,fr.2.1,fr.2.2.1,?_⟩
 intro r hr
 exact fr.2.2.2.1 r (by unfold TailPreserved at hr;omega)

theorem coefficient_call (p : ReplayParameters) (B n : ℕ) (layout:ReplayLayout p B)
 (x : Fin n → ℂ) (s : State) (h g : ℕ → ℂ) (post:BasePost p B layout h g s)
 (args:UniformReplayCoefficientMachine.Header p.base.K p.base.C p.negative p.constants s)
 (hp:s.pc=756) (hs:WordBound B s) : ∃u,
 BoundedRuns program n x B s (UniformReplayCoefficientMachine.runtime p.base.K) u ∧
 u.pc=798 ∧ UniformReplayCoefficientMachine.NegativeBank p.negative (7*width p.base.K) (bankValues p h g) u ∧
 UniformReplayCoefficientMachine.Constants p.base.K p.constants u ∧ TailFrame p s u ∧ u.natHeap=s.natHeap := by
 let entry:=setPC s 0
 have eb:=changePC_bound B s 0 hs (by have :=layout.codeBound;omega)
 have args':UniformReplayCoefficientMachine.Header p.base.K p.base.C p.negative p.constants entry:=
  ⟨args.height,args.source,args.target,args.constants⟩
 obtain ⟨v,run,pc,_,_,negative,constants,outside,fr⟩:=UniformReplayCoefficientMachine.execution
  p.base.K p.base.C p.negative p.constants B n x entry (bankValues p h g) args' rfl
  (bank_source post.positive) (by have :=layout.codeBound;omega)
  (by have :=layout.negativeFresh;omega) layout.constantsFresh layout.constantsBound eb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed coefficient_code
  (by rw [UniformReplayCoefficientMachine.program_length];have :=layout.codeBound;omega)
  (by have :=layout.codeBound;omega) run
 have pe:placed 756 entry=s:=by cases s;simp_all [placed,entry,setPC]
 rw [pe] at placedRun
 let u:=setPC v 798
 have tf:TailFrame p s v:=coefficient_frame outside fr
 exact ⟨u,placedRun,rfl,negative,constants,tf.withPC 798,fr.1⟩


/-- All semantic fields refer to the actual shared cross DAG and retained
original H/G. No ordering, signed bank or constants are entry certificates. -/
structure PreparedReplay (p : ReplayParameters) (B : ℕ) (layout:ReplayLayout p B)
 (h g : ℕ → ℂ) (s : State) : Prop extends BasePost p B layout h g s where
 buckets : BucketPost p B layout s
 negative : UniformReplayCoefficientMachine.NegativeBank p.negative (7*width p.base.K) (bankValues p h g) s
 constants : UniformReplayCoefficientMachine.Constants p.base.K p.constants s

/-- This factors the precise external frame through the actually reached
post722 state. The projection lemmas below expose all written regions. -/
def ExternalFrame (p : ReplayParameters) (s u : State) : Prop :=
 ∃v,UniformRankCrossPreparationMachine.Frame p.base s v ∧ TailFrame p v u

theorem ExternalFrame.nat {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u) (q : ℕ)
 (hfft:q < p.base.d ∨ p.base.d+3*count p.base.K ≤ q)
 (hconv:q < p.base.conv ∨ p.base.conv+5*UniformToeplitzCrossTopologyMachine.G p.base.K ≤ q)
 (htape:q < p.base.tape ∨ p.base.tape+5*Shape p.base ≤ q)
 (hdepth:q < p.base.depth ∨ p.base.depth+p.base.e+1+Shape p.base ≤ q)
 (horder:q < p.order ∨ p.order+Shape p.base*(Shape p.base+1) ≤ q)
 (hdir:q < p.directory ∨ p.directory+Shape p.base+2 ≤ q) : u.natHeap q=s.natHeap q := by
 obtain ⟨v,old,tail⟩:=f
 exact (tail.1 q horder hdir).trans (old.1 q hfft hconv htape hdepth)

theorem ExternalFrame.scalar {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u) (q : ℕ)
 (hrank:q < p.base.S ∨ p.base.S+6*width p.base.K ≤ q)
 (hfft:q < p.base.A ∨ UniformPreparedFFTMachine.rootAddress p.base.K p.base.A+1 ≤ q)
 (hbank:q < p.base.C ∨ p.base.C+7*width p.base.K+1 ≤ q)
 (hnegative:q < p.negative ∨ p.negative+7*width p.base.K ≤ q)
 (hconstants:q < p.constants ∨ p.constants+6 ≤ q) : u.scalarHeap q=s.scalarHeap q := by
 obtain ⟨v,old,tail⟩:=f
 exact (tail.2.1 q hnegative hconstants).trans (old.2.1 q hrank hfft hbank)

theorem ExternalFrame.headers {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u) (r : ℕ)
 (old:UniformRankCrossPreparationMachine.Preserved r) (tail:TailPreserved r) : u.natReg r=s.natReg r := by
 obtain ⟨v,fo,ft⟩:=f
 exact (ft.2.2.2.2 r tail).trans (fo.2.2.2.2 r old)

theorem ExternalFrame.saved {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u)
 (r : ℕ) (hr:100 ≤ r ∧ r ≤ 106) : u.natReg r=s.natReg r :=
 f.headers r (Or.inl hr) (by unfold TailPreserved;omega)

theorem ExternalFrame.outputs {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u) : u.outputs=s.outputs := by
 obtain ⟨v,old,tail⟩:=f
 exact tail.2.2.1.trans old.2.2.1

theorem ExternalFrame.roots {p : ReplayParameters} {s u : State} (f:ExternalFrame p s u) : u.rootOrders=s.rootOrders := by
 obtain ⟨v,old,tail⟩:=f
 exact tail.2.2.2.1.trans old.2.2.2.1

def runtimeBudget (p : ReplayParameters) := UniformRankCrossPreparationMachine.runtimeBudget p.base+6+
 UniformDAGBucketMachine.runtimeBudget (Shape p.base)+4+UniformReplayCoefficientMachine.runtime p.base.K+1

/-- One continuous charged execution: original physical H/G/master only,
followed by physical stable bucketing and signed coefficient preparation. -/
theorem execution (p : ReplayParameters) (B n : ℕ) (layout:ReplayLayout p B)
 (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
 (header:UniformRankCrossPreparationMachine.Header p.base s) (extra:ExtraHeader p s)
 (bh:UniformRankKernelMachine.Bank p.base.H p.base.hSize h s)
 (bg:UniformRankKernelMachine.Bank p.base.G p.base.gSize g s)
 (master:s.scalarHeap 0=some (prepared (zeta p.base.D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget p ∧ u.pc=798 ∧
 PreparedReplay p B layout h g u ∧ ExternalFrame p s u := by
 obtain ⟨v,tv,whole,tvB,vp,vpost,vframe⟩:=whole_call p B n layout h g x s header extra bh bg master hp hs
 have bsafe:=bucketSetup_safe vpost.ready layout vpost.extra vpost.shape
 have br:=block_runs bucketSetup program 722 n B x v bucketSetup_at vp whole.final_bound
  (by rw [bucketSetup_length];have :=layout.codeBound;omega) bsafe.1 bsafe.2
 let b:=applyBlock bucketSetup v
 have bf:=caller_frame p bucketSetup v (Or.inl rfl)
 have bp:BasePost p B layout h g b:=bf.post vpost
 have bargs:=bucketSetup_spec vpost.ready vpost.extra vpost.shape
 have bpc:b.pc=728:=by rw [UniformTensorMonomialMachine.applyBlock_pc,vp,bucketSetup_length]
 obtain ⟨w,tw,bucket,twB,wp,wbuckets,wframe⟩:=bucket_call p B n layout x b h g bp bargs bpc br.final_bound
 have wpost:=wframe.post bp
 have csafe:=coefficientSetup_safe wpost.ready wpost.extra bucket.final_bound
 have cr:=block_runs coefficientSetup program 752 n B x w coefficientSetup_at wp bucket.final_bound
  (by rw [coefficientSetup_length];have :=layout.codeBound;omega) csafe.1 csafe.2
 let c:=applyBlock coefficientSetup w
 have cf:=caller_frame p coefficientSetup w (Or.inr rfl)
 have cp:BasePost p B layout h g c:=cf.post wpost
 have cargs:=coefficientSetup_spec wpost.ready wpost.extra
 have cpc:c.pc=756:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp,coefficientSetup_length]
 obtain ⟨u,coeff,up,negative,constants,uframe,nateq⟩:=coefficient_call p B n layout x c h g cp cargs cpc cr.final_bound
 have upost:=uframe.post cp
 have buckets:BucketPost p B layout u:=wbuckets.heap nateq
 have frame:ExternalFrame p s u:=⟨v,vframe,bf.trans (wframe.trans (cf.trans uframe))⟩
 have stop:BoundedExecution program n x B u 1 u:=.halt coeff.final_bound (by simp only [step,up,final_halt])
 refine ⟨u,tv+6+tw+4+UniformReplayCoefficientMachine.runtime p.base.K+1,?_,?_,up,
  ⟨upost,buckets,negative,constants⟩,frame⟩
 · convert whole.executes (br.executes (bucket.executes (cr.executes (coeff.executes stop)))) using 1
   simp only [bucketSetup_length,coefficientSetup_length]
   omega
 · unfold runtimeBudget
   omega

/-- Both signs are actual prepared cells, including coefficients equal to zero. -/
theorem PreparedReplay.signed {p : ReplayParameters} {B : ℕ} {layout:ReplayLayout p B}
 {h g : ℕ → ℂ} {s : State} (post:PreparedReplay p B layout h g s)
 (sign : Bool) (j : ℕ) (hj:j < 7*width p.base.K) :
 s.scalarHeap (UniformReplayCoefficientMachine.signedAddress p.base.C p.negative sign j)=
 some (prepared (UniformReplayCoefficientMachine.signedValue sign (bankValues p h g j))) :=
 UniformReplayCoefficientMachine.signed_ready (bank_source post.positive) post.negative sign j hj

end
end ExactFourierCircuits.UniformRankCrossReplayPreparationMachine
