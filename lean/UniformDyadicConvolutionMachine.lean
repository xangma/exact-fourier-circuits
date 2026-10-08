import UniformFFTInputMachine
import UniformChirpPointwiseMachine
import UniformNormalizationMachine
import UniformConvolutionDAG
import UniformChirpOutputMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDyadicConvolutionMachine
open UniformMachine UniformAssembly UniformRadixTwoDAG OAI.ExactFourier
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
noncomputable section

/-- Numeric values and the actual evaluated dependency flag of the printed FFT. -/
def transform (K : ℕ) (v : Fin (width K) → Scalar) : Fin (width K) → Scalar :=
  fun i=>⟨(fourierMatrix (width K)).mulVec (fun j=>(v j).value) i,
    UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun j=>(v j).dependent) (count K+i.val)⟩
def fixed (K : ℕ) (v : Fin (width K) → ℂ) : Fin (width K) → Scalar := fun i=>⟨v i,false⟩
def product (K : ℕ) (v : Fin (width K) → Scalar) (k : Fin (width K) → ℂ) : Fin (width K) → Scalar :=
  fun i=>UniformChirpPointwiseMachine.productScalar (transform K v i) (transform K (fixed K k) i).value

def normalized (K : ℕ) (v : Fin (width K) → Scalar) (i : Fin (width K)) : Scalar :=
  ⟨(width K:ℂ)⁻¹*(v (UniformConvolutionDAG.reverseIndex K i)).value,
    (v (UniformConvolutionDAG.reverseIndex K i)).dependent⟩
def convolution (K : ℕ) (v : Fin (width K) → Scalar) (k : Fin (width K) → ℂ) : Fin (width K) → Scalar :=
  normalized K (transform K (product K v k))

theorem transform_prepared (K : ℕ) (v : Fin (width K) → Scalar) (h:∀i,(v i).dependent=false) :
    ∀i,(transform K v i).dependent=false := by
  intro i;exact UniformOffsetLinearMachine.TaggedFFT.dependencyValue_prepared K _ h _
theorem fixed_transform_prepared (K : ℕ) (k : Fin (width K) → ℂ) :
    ∀i,(transform K (fixed K k) i).dependent=false := transform_prepared K _ (fun _=>rfl)
theorem convolution_prepared (K : ℕ) (v : Fin (width K) → Scalar) (k : Fin (width K) → ℂ)
    (h:∀i,(v i).dependent=false) : ∀i,(convolution K v k i).dependent=false := by
  intro i
  exact transform_prepared K _ (transform_prepared K v h) _

theorem padded_full (K : ℕ) (v : Fin (width K) → Scalar) :
    UniformFFTInputMachine.padded K (width K) v=v := by
  funext i;simp [UniformFFTInputMachine.padded,UniformFFTInputMachine.paddedAt,i.isLt]

theorem transform_toZMod (K : ℕ) (v : Fin (width K) → Scalar) :
    UniformCyclic.toZMod (fun i=>(transform K v i).value)=
      UniformCyclic.positiveDFT (UniformCyclic.toZMod (fun i=>(v i).value)) := by
  funext z
  simpa [UniformCyclic.toZMod,transform] using
    (UniformCyclic.positiveDFT_fin (fun i=>(v i).value) ((FourierCRT.finZMod (width K)).symm z)).symm

/-- Three actual positive transforms, with index reversal and 1/N, give the
standard cyclic convolution. No transform action certificate is an input. -/
theorem convolution_value (K : ℕ) (v : Fin (width K) → Scalar) (k : Fin (width K) → ℂ)
    (i : Fin (width K)) : (convolution K v k i).value=
    UniformCyclic.convolution (UniformCyclic.toZMod (fun i=>(v i).value))
      (UniformCyclic.toZMod k) (FourierCRT.finZMod (width K) i) := by
  have hi:FourierCRT.finZMod (width K) (UniformConvolutionDAG.reverseIndex K i)=
      -(FourierCRT.finZMod (width K) i):=by
    change ((width K-i.val)%width K:ZMod (width K))= -(i.val:ZMod (width K))
    exact UniformChirpOutputMachine.negativeIndex_ZMod i.val (Nat.le_of_lt i.isLt)
  have hp:UniformCyclic.toZMod (fun i=>(product K v k i).value)=
      fun z=>UniformCyclic.positiveDFT (UniformCyclic.toZMod (fun i=>(v i).value)) z *
        UniformCyclic.positiveDFT (UniformCyclic.toZMod k) z:=by
    funext z
    change UniformCyclic.toZMod (fun i=>(transform K v i).value) z *
      UniformCyclic.toZMod (fun i=>(transform K (fixed K k) i).value) z=_
    rw [transform_toZMod,transform_toZMod]
    rfl
  change (width K:ℂ)⁻¹*(fourierMatrix (width K)).mulVec (fun i=>(product K v k i).value)
    (UniformConvolutionDAG.reverseIndex K i)=_
  rw [←UniformCyclic.positiveDFT_fin,hi,←UniformCyclic.inversePositiveDFT_apply,hp,
    UniformCyclic.convolution_via_fourier]

/-- Fresh output heap: Nat203=N,208=normalization cell,209=destination,
212=third spectrum. Only Nat220..223 and Scalar0..1 are overwritten. -/
def outputBody : List Op := [.add 222 212 222,.getScalar 1 222,.field .mul 1 0 1,
  .add 223 209 221,.putScalar 223 1,.add 221 221 220]
def outputProgram : Program := [.natLiteral 220 1,.natLiteral 221 0,.loadScalar 0 208,
  .branchLT 221 203 4 13,.natBinary .sub 222 203 221,.natBinary .mod 222 222 203]++
  outputBody.map Op.code++[.jump 3,.halt]
theorem outputProgram_length : outputProgram.length=14 := rfl
theorem outputBody_code : BlockAt outputBody outputProgram 6 := by
  intro i hi;change i < 6 at hi;interval_cases i <;> rfl

def Values (K a : ℕ) (v : Fin (width K) → Scalar) (s : State) : Prop :=
  ∀i,s.scalarHeap (a+i.val)=some (v i)
def OutputOutside (a N : ℕ) (s u : State) : Prop :=
  ∀i,(i < a ∨ a+N ≤ i) → u.scalarHeap i=s.scalarHeap i
structure OutputGeometry (K a c out j : ℕ) (s : State) : Prop where
  pc:s.pc=3
  size:s.natReg 203=width K
  source:s.natReg 212=a
  norm:s.natReg 208=c
  dest:s.natReg 209=out
  one:s.natReg 220=1
  index:s.natReg 221=j
  coefficient:s.scalarReg 0=⟨(width K:ℂ)⁻¹,false⟩
def outputEntered (s : State) : State:={s with pc:=4}
def outputDifference (K j : ℕ) (s : State) : State:=writeNat (outputEntered s) 222 (width K-j)
def outputResidue (K j : ℕ) (s : State) : State:=writeNat (outputDifference K j s) 222 ((width K-j)%width K)
def outputEnd (K j : ℕ) (s : State) : State:={applyBlock outputBody (outputResidue K j s) with pc:=3}

theorem output_row {n : ℕ} (x : Fin n → ℂ) (K a c out j B : ℕ)
    (v : Fin (width K) → Scalar) (s : State) (h:OutputGeometry K a c out j s)
    (hj:j < width K) (hv:Values K a v s) (ha:a+width K ≤ B) (ho:out+width K ≤ B)
    (hc:224 ≤ B) (hs:WordBound B s) : BoundedRuns outputProgram n x B s 10 (outputEnd K j s) := by
  have hN:=width_pos K
  have he:=changePC_bound B s 4 hs (by omega)
  have hd:=writeNat_bound B (outputEntered s) 222 (width K-j) he (by change 4+1 ≤ B;omega)
    (by
      have hn:width K ≤ B:=by rw [←h.size];exact hs.2.1 203
      omega)
  have hm:=writeNat_bound B (outputDifference K j s) 222 ((width K-j)%width K) hd
    (by change 5+1 ≤ B;omega) ((Nat.le_of_lt (Nat.mod_lt _ hN)).trans (by omega))
  have first:BoundedRuns outputProgram n x B s 3 (outputResidue K j s):=by
    refine .next hs ?_ (.next he ?_ (.next hd ?_ (.refl hm)))
    all_goals simp [step,outputProgram,outputBody,outputResidue,outputDifference,outputEntered,
      writeNat,next,h.pc,h.size,h.index,hj,evalNat,show width K≠0 by omega]
  have hb:=hv (UniformConvolutionDAG.reverseIndex K ⟨j,hj⟩)
  have read:readable outputBody (outputResidue K j s):=by
    simp [readable,outputBody,Op.readable,Op.apply,outputResidue,outputDifference,outputEntered,
      writeNat,writeScalar,next,h.source,h.coefficient,evalField,
      UniformConvolutionDAG.reverseIndex] at hb ⊢
    simp [hb]
  have pk:peak outputBody (outputResidue K j s) ≤ B:=by
    simp [peak,outputBody,Op.peak,Op.apply,outputResidue,outputDifference,outputEntered,
      writeNat,writeScalar,next,h.source,h.dest,h.index,h.one]
    have hm':(width K-j)%width K < width K:=Nat.mod_lt _ hN
    omega
  have body:=block_runs outputBody outputProgram 6 n B x (outputResidue K j s) outputBody_code rfl hm
    (by change 6+6 ≤ B;omega) read pk
  have endpc:(applyBlock outputBody (outputResidue K j s)).pc=12:=by
    rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have final:=changePC_bound B _ 3 body.final_bound (by omega)
  have jump:BoundedRuns outputProgram n x B (applyBlock outputBody (outputResidue K j s)) 1 (outputEnd K j s):=by
    refine .next body.final_bound ?_ (.refl final)
    simp only [step,endpc];rfl
  convert (first.trans body).trans jump using 1
  rfl

theorem output_geometry (K a c out j : ℕ) (s : State) (h:OutputGeometry K a c out j s) :
    OutputGeometry K a c out (j+1) (outputEnd K j s) := by
  constructor <;> simp [outputEnd,outputBody,applyBlock,Op.apply,outputResidue,outputDifference,outputEntered,
    writeNat,writeScalar,next,h.size,h.source,h.norm,h.dest,h.one,h.index,h.coefficient]

theorem output_heap (K a c out j : ℕ) (v : Fin (width K) → Scalar) (s : State)
    (h:OutputGeometry K a c out j s) (hj:j < width K) (hv:Values K a v s) :
    (outputEnd K j s).scalarHeap=Function.update s.scalarHeap (out+j) (some (normalized K v ⟨j,hj⟩)) := by
  have hb:=hv (UniformConvolutionDAG.reverseIndex K ⟨j,hj⟩)
  simp [outputEnd,outputBody,applyBlock,Op.apply,outputResidue,outputDifference,outputEntered,
    writeNat,writeScalar,next,h.source,h.dest,h.index,h.coefficient,evalField,
    normalized,UniformConvolutionDAG.reverseIndex] at hb ⊢
  rw [hb]
  rfl

def OutputFrame (a N : ℕ) (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  OutputOutside a N s u ∧ (∀r,(r < 220 ∨ 223 < r) → u.natReg r=s.natReg r)
theorem OutputFrame.refl (a N : ℕ) (s : State) : OutputFrame a N s s:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem OutputFrame.trans {a N : ℕ} {s u v : State} (h:OutputFrame a N s u) (h':OutputFrame a N u v) : OutputFrame a N s v:=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun i hi=>(h'.2.2.2.1 i hi).trans (h.2.2.2.1 i hi),fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
theorem output_frame (K a c out j : ℕ) (v : Fin (width K) → Scalar) (s : State)
    (h:OutputGeometry K a c out j s) (hj:j < width K) (hv:Values K a v s) : OutputFrame out (width K) s (outputEnd K j s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro i hi;rw [output_heap K a c out j v s h hj hv,Function.update_of_ne (by omega)]
  · intro r hr;simp [outputEnd,outputBody,applyBlock,Op.apply,outputResidue,outputDifference,outputEntered,
      writeNat,writeScalar,next,show r≠221 by omega,show r≠222 by omega,show r≠223 by omega]

theorem output_loop {n : ℕ} (x : Fin n → ℂ) (K a c out j fuel B : ℕ) (v : Fin (width K) → Scalar) (s : State)
    (h:OutputGeometry K a c out j s) (hf:j+fuel=width K) (hv:Values K a v s)
    (hsep:a+width K ≤ out) (ha:a+width K ≤ B) (ho:out+width K ≤ B) (hc:224 ≤ B)
    (hw:∀i:Fin (width K),i.val < j → s.scalarHeap (out+i.val)=some (normalized K v i)) (hs:WordBound B s) : ∃u,
    BoundedExecution outputProgram n x B s (10*fuel+2) u ∧ Values K out (normalized K v) u ∧
    OutputFrame out (width K) s u ∧ u.pc=13 := by
  induction fuel generalizing j s with
  | zero=>
    have he:j=width K:=by omega
    let u:State:={s with pc:=13}
    have hu:=changePC_bound B s 13 hs (by omega)
    refine ⟨u,.next hs ?_ (.halt hu ?_),fun i=>hw i (by have:=i.isLt;omega),OutputFrame.refl out (width K) s,rfl⟩
    · simp [step,outputProgram,outputBody,h.pc,h.index,h.size,he,u]
    · simp only [step];rfl
  | succ fuel ih=>
    have hj:j < width K:=by omega
    have row:=output_row x K a c out j B v s h hj hv ha ho hc hs
    have frame:=output_frame K a c out j v s h hj hv
    have next:Values K a v (outputEnd K j s):=by
      intro i;exact (frame.2.2.2.1 (a+i.val) (Or.inl (by have:=i.isLt;omega))).trans (hv i)
    have written:∀i:Fin (width K),i.val < j+1 → (outputEnd K j s).scalarHeap (out+i.val)=some (normalized K v i):=by
      intro i hi
      rw [output_heap K a c out j v s h hj hv]
      by_cases he:i.val=j
      · have ei:i=⟨j,hj⟩:=Fin.ext he;subst i;simp
      · rw [Function.update_of_ne (by omega)];exact hw i (by omega)
    obtain ⟨u,hu,hou,hfu,hup⟩:=ih (j+1) (outputEnd K j s) (output_geometry K a c out j s h) (by omega)
      next written row.final_bound
    exact ⟨u,by convert row.executes hu using 1;omega,hou,frame.trans hfu,hup⟩

def outputStart (s : State) : State:=writeScalar (writeNat (writeNat s 220 1) 221 0) 0
  ((s.scalarHeap (s.natReg 208)).getD Scalar.zero)
theorem output_execution {n : ℕ} (x : Fin n → ℂ) (K a c out B : ℕ) (v : Fin (width K) → Scalar) (s : State)
    (hp:s.pc=0) (h203:s.natReg 203=width K) (h212:s.natReg 212=a) (h208:s.natReg 208=c)
    (h209:s.natReg 209=out) (hv:Values K a v s) (hn:s.scalarHeap c=some ⟨(width K:ℂ)⁻¹,false⟩)
    (hsep:a+width K ≤ out) (ha:a+width K ≤ B) (ho:out+width K ≤ B) (hc:224 ≤ B)
    (hs:WordBound B s) : ∃u,BoundedExecution outputProgram n x B s (10*width K+5) u ∧
    Values K out (normalized K v) u ∧ OutputFrame out (width K) s u ∧ u.pc=13 := by
  have h1:=writeNat_bound B s 220 1 hs (by omega) (by omega)
  have h2:=writeNat_bound B (writeNat s 220 1) 221 0 h1 (by simp [writeNat,next,hp];omega) (by omega)
  have h3:=writeScalar_bound B (writeNat (writeNat s 220 1) 221 0) 0
    ((s.scalarHeap c).getD Scalar.zero) h2 (by simp [writeNat,next,hp];omega)
  have start:BoundedRuns outputProgram n x B s 3 (outputStart s):=by
    refine .next hs ?_ (.next h1 ?_ (.next h2 ?_ (.refl h3)))
    all_goals simp [step,outputProgram,outputBody,outputStart,writeNat,writeScalar,next,hp,h208,hn]
  have geom:OutputGeometry K a c out 0 (outputStart s):=by
    constructor <;> simp [outputStart,writeNat,writeScalar,next,hp,h203,h212,h208,h209,hn]
  have frame:OutputFrame out (width K) s (outputStart s):=by
    refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
    intro r hr;simp [outputStart,writeNat,writeScalar,next,show r≠220 by omega,show r≠221 by omega]
  obtain ⟨u,hu,hou,hfu,hup⟩:=output_loop x K a c out 0 (width K) B v (outputStart s) geom (by omega) hv hsep ha ho hc
    (by intro i hi;omega) start.final_bound
  exact ⟨u,by convert start.executes hu using 1;omega,hou,frame.trans hfu,hup⟩


def span (K : ℕ) : ℕ := count K+6*width K+5
def dataArena (K A : ℕ) := A+span K
def thirdArena (K A : ℕ) := A+2*span K
def normCell (K A : ℕ) := A+3*span K
def outputBase (K A : ℕ) := normCell K A+1
def endAddress (K A : ℕ) := outputBase K A+width K

def Persistent (r : ℕ) : Prop := r=70 ∨ r=107 ∨ (100 ≤ r ∧ r ≤ 106) ∨
  (160 ≤ r ∧ r < 174) ∨ (184 ≤ r ∧ r ≤ 202) ∨ 224 ≤ r
structure Frame (K A d : ℕ) (s u : State) : Prop where
  nats:UniformRadixRowTableMachine.Outside d (3*count K) s.natHeap u
  scalars:∀i,(i < A ∨ endAddress K A ≤ i)→u.scalarHeap i=s.scalarHeap i
  outputs:u.outputs=s.outputs
  roots:u.rootOrders=s.rootOrders
  regs:∀r,Persistent r→u.natReg r=s.natReg r

theorem Frame.refl (K A d : ℕ) (s : State) : Frame K A d s s:=⟨fun _ _=>rfl,fun _ _=>rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {K A d : ℕ} {s u v : State} (h:Frame K A d s u) (h':Frame K A d u v) : Frame K A d s v:=
  ⟨fun i hi=>(h'.nats i hi).trans (h.nats i hi),fun i hi=>(h'.scalars i hi).trans (h.scalars i hi),
    h'.outputs.trans h.outputs,h'.roots.trans h.roots,fun r hr=>(h'.regs r hr).trans (h.regs r hr)⟩

def sizeSetup : List Op := [.literal 203 1,.literal 218 0,.literal 214 1,.literal 215 2]
def sizeGrow : List Op := [.mul 203 203 215,.add 218 218 214]
def sizeProgram : Program := sizeSetup.map Op.code++[.branchLT 218 70 5 8]++sizeGrow.map Op.code++[.jump 4,.halt]
theorem sizeProgram_length : sizeProgram.length=9:=rfl
theorem sizeSetup_code : BlockAt sizeSetup sizeProgram 0:=by intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem sizeGrow_code : BlockAt sizeGrow sizeProgram 5:=by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
structure Sizing (K t : ℕ) (s : State) : Prop where
  height:s.natReg 70=K
  size:s.natReg 203=width t
  index:s.natReg 218=t
  one:s.natReg 214=1
  two:s.natReg 215=2

theorem Sizing.withPC {K t pc : ℕ} {s : State} (h:Sizing K t s) : Sizing K t {s with pc:=pc}:=by cases h;constructor <;> assumption

def SizeFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ∀r,(r < 203 ∨ 218 < r)→u.natReg r=s.natReg r

theorem size_block_frame (s : State) : SizeFrame s (applyBlock sizeSetup s) ∧ SizeFrame s (applyBlock sizeGrow s):=by
  constructor <;> refine ⟨rfl,rfl,rfl,rfl,?_⟩ <;> intro r hr <;>
    simp (disch:=omega) [sizeSetup,sizeGrow,applyBlock,Op.apply,writeNat,next]
theorem sizeFrame_trans {s u v : State} (h:SizeFrame s u) (h':SizeFrame u v) : SizeFrame s v:=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem size_loop {n : ℕ} (x : Fin n→ℂ) (K t f B : ℕ) (s : State) (h:Sizing K t s)
    (hf:t+f=K) (hp:s.pc=4) (hN:width K ≤ B) (hK:K ≤ B) (hc:224 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns sizeProgram n x B s (4*f+1) u ∧ Sizing K K u ∧ u.pc=8 ∧ SizeFrame s u:=by
  induction f generalizing t s with
  | zero=>
    have he:t=K:=by omega
    subst t
    let u:State:={s with pc:=8}
    have hu:=changePC_bound B s 8 hs (by omega)
    refine ⟨u,.next hs ?_ (.refl hu),h.withPC,rfl,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
    simp [step,sizeProgram,sizeSetup,sizeGrow,Op.code,hp,h.index,h.height,u]
  | succ f ih=>
    have hlt:t < K:=by omega
    let e:State:={s with pc:=5}
    have he:=changePC_bound B s 5 hs (by omega)
    have first:BoundedRuns sizeProgram n x B s 1 e:=by
      refine .next hs ?_ (.refl he)
      simp [step,sizeProgram,sizeSetup,sizeGrow,Op.code,hp,h.index,h.height,hlt,e]
    have hn:width (t+1) ≤ width K:=UniformRadixInstructionMachine.width_mono (by omega)
    have pk:peak sizeGrow e ≤ B:=by
      simp [peak,sizeGrow,Op.peak,Op.apply,writeNat,next,e,h.size,h.index,h.one,h.two]
      constructor
      · simpa only [width,Nat.mul_comm,Nat.two_mul] using hn.trans hN
      · omega
    have body:=block_runs sizeGrow sizeProgram 5 n B x e sizeGrow_code rfl he
      (by change 5+2 ≤ B;omega) (by simp [readable,sizeGrow,Op.readable]) pk
    let z:State:={applyBlock sizeGrow e with pc:=4}
    have hz:=changePC_bound B _ 4 body.final_bound (by omega)
    have zp:(applyBlock sizeGrow e).pc=7:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
    have jump:BoundedRuns sizeProgram n x B (applyBlock sizeGrow e) 1 z:=by
      refine .next body.final_bound ?_ (.refl hz)
      simp only [step,zp];rfl
    have zh:Sizing K (t+1) z:=by
      constructor <;> simp [z,sizeGrow,applyBlock,Op.apply,writeNat,next,e,h.height,h.size,h.index,h.one,h.two,width,Nat.two_mul,Nat.mul_comm]
    obtain ⟨u,hu,hui,hup,hfu⟩:=ih (t+1) z zh (by omega) rfl hz
    refine ⟨u,?_,hui,hup,sizeFrame_trans (size_block_frame e).2 hfu⟩
    convert ((first.trans body).trans jump).trans hu using 1
    simp only [show sizeGrow.length=2 by rfl];omega

theorem size_execution {n : ℕ} (x : Fin n→ℂ) (K B : ℕ) (s : State)
    (hp:s.pc=0) (h70:s.natReg 70=K) (hN:width K ≤ B) (hc:224 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution sizeProgram n x B s (4*K+6) u ∧ Sizing K K u ∧ SizeFrame s u ∧ u.pc=8:=by
  have head:=block_runs sizeSetup sizeProgram 0 n B x s sizeSetup_code hp hs (by change 4 ≤ B;omega)
    (by simp [readable,sizeSetup,Op.readable]) (by simp [peak,sizeSetup,Op.peak];omega)
  have geom:Sizing K 0 (applyBlock sizeSetup s):=by
    constructor <;> simp [sizeSetup,applyBlock,Op.apply,writeNat,next,h70,width]
  have p:(applyBlock sizeSetup s).pc=4:=by rw [UniformReciprocalMachine.applyBlock_pc,hp];rfl
  obtain ⟨u,hu,hui,hup,hfu⟩:=size_loop x K 0 K B (applyBlock sizeSetup s) geom (by omega) p hN
    (by rw [←h70];exact hs.2.1 70) hc head.final_bound
  have halt:BoundedExecution sizeProgram n x B u 1 u:=.halt hu.final_bound (by simp only [step,hup];rfl)
  refine ⟨u,?_,hui,sizeFrame_trans (size_block_frame s).1 hfu,hup⟩
  convert head.executes (hu.executes halt) using 1
  simp only [show sizeSetup.length=4 by rfl];omega

def layoutHead : List Op := [.literal 213 0,.literal 216 3,.mul 204 70 203,.mul 204 204 216]
def layoutTail : List Op := [.literal 217 6,.mul 205 203 217,.add 205 205 204,.literal 219 5,
  .add 205 205 219,.add 206 202 205,.add 207 206 205,.add 208 207 205,.add 209 208 214,
  .add 210 202 204,.add 211 206 204,.add 212 207 204]
def kernelSetup : List Op := [.add 174 203 213,.add 175 201 213,.literal 176 1,.add 122 202 213]
def dataSetup : List Op := [.add 174 203 213,.add 175 200 213,.literal 176 1,.add 122 206 213]
def pointSetup : List Op := [.add 17 203 213,.add 26 211 213,.add 28 210 213]
def thirdSetup : List Op := [.add 174 203 213,.add 175 211 213,.literal 176 1,.add 122 207 213]
def normSetup : List Op := [.add 17 203 213,.add 27 208 213]

def program : Program := sizeProgram.map (relocate 0 9)++layoutHead.map Op.code++[.natBinary .div 204 204 215]++
  layoutTail.map Op.code++kernelSetup.map Op.code++UniformFFTInputMachine.combinedProgram.map (relocate 30 251)++
  dataSetup.map Op.code++UniformFFTInputMachine.combinedProgram.map (relocate 255 476)++pointSetup.map Op.code++
  UniformChirpPointwiseMachine.program.map (relocate 479 491)++thirdSetup.map Op.code++
  UniformFFTInputMachine.combinedProgram.map (relocate 495 716)++normSetup.map Op.code++
  UniformNormalizationMachine.program.map (relocate 718 754)++outputProgram.map (relocate 754 768)++[.halt]

theorem layoutHead_length : layoutHead.length=4:=rfl
theorem layoutTail_length : layoutTail.length=12:=rfl
theorem kernelSetup_length : kernelSetup.length=4:=rfl
theorem dataSetup_length : dataSetup.length=4:=rfl
theorem pointSetup_length : pointSetup.length=3:=rfl
theorem thirdSetup_length : thirdSetup.length=4:=rfl
theorem normSetup_length : normSetup.length=2:=rfl
theorem program_length : program.length=769:=by
  simp [program,sizeProgram_length,layoutHead_length,layoutTail_length,kernelSetup_length,dataSetup_length,
    pointSetup_length,thirdSetup_length,normSetup_length,UniformFFTInputMachine.combinedProgram_length,
    UniformChirpPointwiseMachine.program_length,UniformNormalizationMachine.program_length,outputProgram_length]

attribute [local simp] sizeProgram_length layoutHead_length layoutTail_length kernelSetup_length dataSetup_length pointSetup_length thirdSetup_length normSetup_length UniformFFTInputMachine.combinedProgram_length UniformChirpPointwiseMachine.program_length UniformNormalizationMachine.program_length outputProgram_length

theorem block_segment_code (a b : Program) (o : List Op) : BlockAt o (a++o.map Op.code++b) a.length:=by
  intro i hi
  rw [List.getElem?_append_left (by simp;omega),List.getElem?_append_right (by omega)]
  simp only [List.getElem?_map,Nat.add_sub_cancel_left,List.getElem?_eq_getElem hi,Option.map_some]

theorem size_code : CodeAt sizeProgram program 0 9:=by
  let before : Program := []
  let after : Program := layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=0:=by simp [before]
  have hp:program=before++sizeProgram.map (relocate 0 9)++after:=by
    simp only [program,before,after,List.append_assoc,List.nil_append]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after sizeProgram 9

theorem kernel_code : CodeAt UniformFFTInputMachine.combinedProgram program 30 251:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code
  let after : Program := dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=30:=by simp [before]
  have hp:program=before++UniformFFTInputMachine.combinedProgram.map (relocate 30 251)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after UniformFFTInputMachine.combinedProgram 251

theorem data_code : CodeAt UniformFFTInputMachine.combinedProgram program 255 476:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code
  let after : Program := pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=255:=by simp [before]
  have hp:program=before++UniformFFTInputMachine.combinedProgram.map (relocate 255 476)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after UniformFFTInputMachine.combinedProgram 476

theorem point_code : CodeAt UniformChirpPointwiseMachine.program program 479 491:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code
  let after : Program := thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=479:=by simp [before]
  have hp:program=before++UniformChirpPointwiseMachine.program.map (relocate 479 491)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after UniformChirpPointwiseMachine.program 491

theorem third_code : CodeAt UniformFFTInputMachine.combinedProgram program 495 716:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code
  let after : Program := normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=495:=by simp [before]
  have hp:program=before++UniformFFTInputMachine.combinedProgram.map (relocate 495 716)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after UniformFFTInputMachine.combinedProgram 716

theorem norm_code : CodeAt UniformNormalizationMachine.program program 718 754:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code
  let after : Program := outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=718:=by simp [before]
  have hp:program=before++UniformNormalizationMachine.program.map (relocate 718 754)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after UniformNormalizationMachine.program 754

theorem output_code : CodeAt outputProgram program 754 768:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754)
  let after : Program := [.halt]
  have hl:before.length=754:=by simp [before]
  have hp:program=before++outputProgram.map (relocate 754 768)++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using UniformPreparedFFTMachine.segment_code before after outputProgram 768

theorem layoutHead_code : BlockAt layoutHead program 9:=by
  let before : Program := sizeProgram.map (relocate 0 9)
  let after : Program := [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=9:=by simp [before]
  have hp:program=before++layoutHead.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after layoutHead

theorem layoutTail_code : BlockAt layoutTail program 14:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215]
  let after : Program := kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=14:=by simp [before]
  have hp:program=before++layoutTail.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after layoutTail

theorem kernelSetup_code : BlockAt kernelSetup program 26:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code
  let after : Program := UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=26:=by simp [before]
  have hp:program=before++kernelSetup.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after kernelSetup

theorem dataSetup_code : BlockAt dataSetup program 251:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251)
  let after : Program := UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=251:=by simp [before]
  have hp:program=before++dataSetup.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after dataSetup

theorem pointSetup_code : BlockAt pointSetup program 476:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476)
  let after : Program := UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=476:=by simp [before]
  have hp:program=before++pointSetup.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after pointSetup

theorem thirdSetup_code : BlockAt thirdSetup program 491:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491)
  let after : Program := UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=491:=by simp [before]
  have hp:program=before++thirdSetup.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after thirdSetup

theorem normSetup_code : BlockAt normSetup program 716:=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716)
  let after : Program := UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=716:=by simp [before]
  have hp:program=before++normSetup.map Op.code++after:=by
    simp only [program,before,after,List.append_assoc]
  simpa only [hl,←hp] using block_segment_code before after normSetup

theorem layoutDivide_code : program[13]?=some (.natBinary .div 204 204 215):=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code
  let after : Program := layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768) ++ [.halt]
  have hl:before.length=13:=by simp [before]
  have hp:program=before++[.natBinary .div 204 204 215]++after:=by simp only [program,before,after,List.append_assoc]
  rw [hp,List.getElem?_append_left (by simp;omega),List.getElem?_append_right (by omega)]
  simp [hl]

theorem halt_code : program[768]?=some (.halt):=by
  let before : Program := sizeProgram.map (relocate 0 9) ++ layoutHead.map Op.code ++ [.natBinary .div 204 204 215] ++ layoutTail.map Op.code ++ kernelSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 30 251) ++ dataSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 255 476) ++ pointSetup.map Op.code ++ UniformChirpPointwiseMachine.program.map (relocate 479 491) ++ thirdSetup.map Op.code ++ UniformFFTInputMachine.combinedProgram.map (relocate 495 716) ++ normSetup.map Op.code ++ UniformNormalizationMachine.program.map (relocate 718 754) ++ outputProgram.map (relocate 754 768)
  let after : Program := []
  have hl:before.length=768:=by simp [before]
  have hp:program=before++[.halt]++after:=by simp only [program,before,after,List.append_assoc,List.append_nil]
  rw [hp,List.getElem?_append_left (by simp;omega),List.getElem?_append_right (by omega)]
  simp [hl]


structure Layout (K S T A d D : ℕ) (s : State) : Prop where
  height:s.natReg 70=K
  source:s.natReg 200=S
  kernel:s.natReg 201=T
  arena:s.natReg 202=A
  table:s.natReg 107=d
  order:s.natReg 104=D
  size:s.natReg 203=width K
  gates:s.natReg 204=count K
  capacity:s.natReg 205=span K
  data:s.natReg 206=dataArena K A
  third:s.natReg 207=thirdArena K A
  norm:s.natReg 208=normCell K A
  output:s.natReg 209=outputBase K A
  kernelSpectrum:s.natReg 210=A+count K
  dataSpectrum:s.natReg 211=dataArena K A+count K
  thirdSpectrum:s.natReg 212=thirdArena K A+count K
  zero:s.natReg 213=0
  one:s.natReg 214=1
  two:s.natReg 215=2

def LayoutRegister (r : ℕ) : Prop := r=70 ∨ r=200 ∨ r=201 ∨ r=202 ∨ r=107 ∨ r=104 ∨ (203 ≤ r ∧ r ≤ 215)
theorem Layout.transport {K S T A d D : ℕ} {s u : State} (h:Layout K S T A d D s)
    (hr:∀r,LayoutRegister r→u.natReg r=s.natReg r) : Layout K S T A d D u:=by
  cases h
  constructor
  all_goals rwa [hr _ (by simp [LayoutRegister])]

theorem Layout.withPC {K S T A d D pc : ℕ} {s : State} (h:Layout K S T A d D s) : Layout K S T A d D {s with pc:=pc}:=by
  cases h;constructor <;> assumption

def Op.natOnly : Op→Prop
  | .literal _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _=>True
  | _=>False
def Op.destination : Op→ℕ
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _=>d
  | _=>0

theorem plain_block_heaps (b : List Op) (s : State) (h:∀o∈b,Op.natOnly o) :
    (applyBlock b s).scalarHeap=s.scalarHeap ∧ (applyBlock b s).natHeap=s.natHeap ∧
    (applyBlock b s).outputs=s.outputs ∧ (applyBlock b s).rootOrders=s.rootOrders:=by
  induction b generalizing s with
  | nil=>exact ⟨rfl,rfl,rfl,rfl⟩
  | cons o b ih=>
    have ho:=h o (by simp)
    have hb:=ih (o.apply s) (by intro a ha;exact h a (by simp [ha]))
    cases o <;> simp_all [Op.natOnly,Op.apply,applyBlock,writeNat,next]

theorem plain_block_register (b : List Op) (s : State) (r : ℕ)
    (h:∀o∈b,Op.natOnly o ∧ Op.destination o≠r) : (applyBlock b s).natReg r=s.natReg r:=by
  induction b generalizing s with
  | nil=>rfl
  | cons o b ih=>
    have ho:=h o (by simp)
    have hb:=ih (o.apply s) (by intro a ha;exact h a (by simp [ha]))
    rw [applyBlock,hb]
    cases o <;> simp_all [Op.natOnly,Op.destination,Op.apply,writeNat,next]
    all_goals rw [Function.update_of_ne (by omega)]

theorem plain_frame (b : List Op) (K A d : ℕ) (s : State) (h:∀o∈b,Op.natOnly o)
    (hr:∀r,Persistent r→∀o∈b,Op.destination o≠r) : Frame K A d s (applyBlock b s):=by
  obtain ⟨hscalar,hnat,hout,hroot⟩:=plain_block_heaps b s h
  refine ⟨fun i _=>congrFun hnat i,fun i _=>congrFun hscalar i,hout,hroot,?_⟩
  intro r hp;exact plain_block_register b s r (by intro o ho;exact ⟨h o ho,hr r hp o ho⟩)

theorem setup_layout {K S T A d D : ℕ} {s : State} (h:Layout K S T A d D s)
    (b : List Op) (hr:∀r,LayoutRegister r→∀o∈b,Op.natOnly o ∧ Op.destination o≠r) : Layout K S T A d D (applyBlock b s):=
  h.transport (fun r hp=>plain_block_register b s r (hr r hp))

def layoutDivided (s : State) : State:=writeNat (applyBlock layoutHead s) 204
  ((applyBlock layoutHead s).natReg 204/(applyBlock layoutHead s).natReg 215)
def layoutFinal (s : State) : State:=applyBlock layoutTail (layoutDivided s)

theorem layout_execution {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ) (s : State)
    (hp:s.pc=9) (h:Sizing K K s) (h200:s.natReg 200=S) (h201:s.natReg 201=T)
    (h202:s.natReg 202=A) (h107:s.natReg 107=d) (h104:s.natReg 104=D)
    (hcode:769 ≤ B) (hraw:3*K*width K ≤ B) (hend:endAddress K A ≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 17 (layoutFinal s) ∧ Layout K S T A d D (layoutFinal s) ∧
    Frame K A d s (layoutFinal s) ∧ (layoutFinal s).pc=26:=by
  have hN:=width_pos K
  have raw:(applyBlock layoutHead s).natReg 204=3*K*width K:=by
    simp [layoutHead,applyBlock,Op.apply,writeNat,next,h.height,h.size];ring
  have two:(applyBlock layoutHead s).natReg 215=2:=by
    simpa [layoutHead,applyBlock,Op.apply,writeNat,next] using h.two
  have hgates:(layoutDivided s).natReg 204=count K:=by
    simp only [layoutDivided,writeNat,next,Function.update_self]
    rw [raw,two,UniformRadixInstructionMachine.count_div]
  have hcalc:K*width K*3/2=count K:=by
    rw [show K*width K*3=3*K*width K by ring,UniformRadixInstructionMachine.count_div]
  have hkn:K*width K ≤ B:=by
    have he:3*K*width K=3*(K*width K):=by ring
    rw [he] at hraw;omega
  have pk:peak layoutHead s ≤ B:=by
    simp [peak,layoutHead,Op.peak,Op.apply,writeNat,next,h.height,h.size]
    rw [show K*width K*3=3*K*width K by ring]
    omega
  have head:=block_runs layoutHead program 9 n B x s layoutHead_code hp hs
    (by rw [layoutHead_length];omega) (by simp [readable,layoutHead,Op.readable]) pk
  have headpc:(applyBlock layoutHead s).pc=13:=by rw [UniformReciprocalMachine.applyBlock_pc,hp,layoutHead_length]
  have dw:=writeNat_bound B (applyBlock layoutHead s) 204
    ((applyBlock layoutHead s).natReg 204/(applyBlock layoutHead s).natReg 215) head.final_bound (by rw [headpc];omega)
    (by rw [raw,two];omega)
  have div:BoundedRuns program n x B (applyBlock layoutHead s) 1 (layoutDivided s):=by
    refine .next head.final_bound ?_ (.refl dw)
    simp [step,headpc,layoutDivide_code,evalNat,two,layoutDivided]
  have tailpeak:peak layoutTail (layoutDivided s) ≤ B:=by
    simp [peak,layoutTail,Op.peak,Op.apply,layoutDivided,layoutHead,applyBlock,writeNat,next,
      h.size,h.height,h202,h.one,h.two,hcalc]
    unfold endAddress outputBase normCell span at hend
    omega
  have divpc:(layoutDivided s).pc=14:=by simp [layoutDivided,writeNat,next,headpc]
  have tail:=block_runs layoutTail program 14 n B x (layoutDivided s) layoutTail_code divpc dw
    (by rw [layoutTail_length];omega) (by simp [readable,layoutTail,Op.readable]) tailpeak
  have shape:Layout K S T A d D (layoutFinal s):=by
    constructor <;> simp [layoutFinal,layoutTail,layoutDivided,layoutHead,applyBlock,Op.apply,writeNat,next,
      h.height,h.size,h.one,h.two,h200,h201,h202,h107,h104,hcalc,
      span,dataArena,thirdArena,normCell,outputBase]
    all_goals omega
  have fp:=plain_frame layoutHead K A d s (by simp [layoutHead,Op.natOnly]) (by
    intro r hr o ho;simp [layoutHead] at ho
    rcases ho with rfl|rfl|rfl|rfl <;> simp only [Op.destination] <;> unfold Persistent at hr <;> omega)
  have fd:Frame K A d (applyBlock layoutHead s) (layoutDivided s):=by
    refine ⟨fun _ _=>rfl,fun _ _=>rfl,rfl,rfl,?_⟩
    intro r hr;simp [layoutDivided,writeNat,next,show r≠204 by unfold Persistent at hr;omega]
  have ft:=plain_frame layoutTail K A d (layoutDivided s) (by simp [layoutTail,Op.natOnly]) (by
    intro r hr o ho;simp [layoutTail] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Op.destination] <;> unfold Persistent at hr <;> omega)
  exact ⟨by convert (head.trans div).trans tail using 1 <;> first | (rw [layoutHead_length,layoutTail_length]) | rfl,shape,
    fp.trans (fd.trans ft),by rw [layoutFinal,UniformReciprocalMachine.applyBlock_pc,divpc,layoutTail_length]⟩


def phaseSetup (p : Fin 3) : List Op:=match p.val with | 0 =>kernelSetup | 1 =>dataSetup | _ =>thirdSetup
def phaseBase (p : Fin 3) : ℕ:=match p.val with | 0 =>26 | 1 =>251 | _ =>491
def phaseFFTBase (p : Fin 3) : ℕ:=match p.val with | 0 =>30 | 1 =>255 | _ =>495
def phaseReturn (p : Fin 3) : ℕ:=match p.val with | 0 =>251 | 1 =>476 | _ =>716
def phaseArena (K A : ℕ) (p : Fin 3) : ℕ:=match p.val with | 0 =>A | 1 =>dataArena K A | _ =>thirdArena K A
def phaseSource (K S T A : ℕ) (p : Fin 3) : ℕ:=match p.val with | 0 =>T | 1 =>S | _ =>dataArena K A+count K

theorem phaseSetup_length (p : Fin 3) : (phaseSetup p).length=4:=by
  fin_cases p <;> simp [phaseSetup]
theorem phase_setup_code (p : Fin 3) : BlockAt (phaseSetup p) program (phaseBase p):=by
  fin_cases p
  · exact kernelSetup_code
  · exact dataSetup_code
  · exact thirdSetup_code
theorem phase_fft_code (p : Fin 3) : CodeAt UniformFFTInputMachine.combinedProgram program (phaseFFTBase p) (phaseReturn p):=by
  fin_cases p
  · exact kernel_code
  · exact data_code
  · exact third_code

def wordBudget (K A d : ℕ) : ℕ:=max 769 (max (3*K*width K)
  (max (UniformPreparedFFTMachine.wordBudget K (thirdArena K A) d) (endAddress K A)))

theorem wordBudget_bounds (K A d B : ℕ) (h:wordBudget K A d ≤ B) :
    769 ≤ B ∧ 3*K*width K ≤ B ∧ endAddress K A ≤ B ∧
    (∀p:Fin 3,UniformPreparedFFTMachine.wordBudget K (phaseArena K A p) d ≤ B):=by
  have hb:UniformPreparedFFTMachine.wordBudget K (thirdArena K A) d ≤ B:=by unfold wordBudget at h;omega
  refine ⟨by unfold wordBudget at h;omega,by unfold wordBudget at h;omega,by unfold wordBudget at h;omega,?_⟩
  intro p
  fin_cases p <;> simp only [phaseArena]
  · unfold UniformPreparedFFTMachine.wordBudget UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at hb ⊢
    unfold thirdArena at hb
    omega
  · unfold UniformPreparedFFTMachine.wordBudget UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at hb ⊢
    simp only [dataArena,thirdArena] at hb ⊢
    omega
  · exact hb

theorem phase_run {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ) (p : Fin 3)
    (v : Fin (width K)→Scalar) (s : State) (hl:Layout K S T A d D s) (hp:s.pc=phaseBase p)
    (hv:Values K (phaseSource K S T A p) v s) (hsep:phaseSource K S T A p+width K ≤ phaseArena K A p)
    (hA:0 < A) (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hD:0 < D) (hdiv:width K∣D)
    (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 4*K+10*width K+13+UniformPreparedFFTMachine.runtime D K ∧
    Values K (phaseArena K A p+count K) (transform K v) u ∧ Layout K S T A d D u ∧ Frame K A d s u ∧
    (∀i,(i < phaseArena K A p ∨ phaseArena K A p+span K ≤ i)→u.scalarHeap i=s.scalarHeap i) ∧ u.pc=phaseReturn p:=by
  obtain ⟨hc,_,hend,hbud⟩:=wordBudget_bounds K A d B hb
  have hN:=width_pos K
  have parena:A ≤ phaseArena K A p ∧ phaseArena K A p+span K ≤ endAddress K A:=by
    fin_cases p <;> simp [phaseArena,dataArena,thirdArena,endAddress,outputBase,normCell] <;> omega
  have args:(applyBlock (phaseSetup p) s).natReg 174=width K ∧
      (applyBlock (phaseSetup p) s).natReg 175=phaseSource K S T A p ∧
      (applyBlock (phaseSetup p) s).natReg 176=1 ∧
      (applyBlock (phaseSetup p) s).natReg 122=phaseArena K A p:=by
    fin_cases p <;> simp [phaseSetup,phaseSource,phaseArena,kernelSetup,dataSetup,thirdSetup,
      applyBlock,Op.apply,writeNat,next,hl.size,hl.source,hl.kernel,hl.arena,hl.data,hl.third,hl.dataSpectrum,hl.zero]
  have nat:∀o∈phaseSetup p,Op.natOnly o:=by fin_cases p <;> simp [phaseSetup,kernelSetup,dataSetup,thirdSetup,Op.natOnly]
  have regs:∀r,LayoutRegister r→∀o∈phaseSetup p,Op.destination o≠r:=by
    intro r hr o ho
    fin_cases p <;> simp [phaseSetup,kernelSetup,dataSetup,thirdSetup] at ho
    all_goals rcases ho with rfl|rfl|rfl|rfl <;> simp only [Op.destination] <;> unfold LayoutRegister at hr <;> omega
  have plain:Frame K A d s (applyBlock (phaseSetup p) s):=plain_frame _ K A d s nat (by
    intro r hr o ho
    fin_cases p <;> simp [phaseSetup,kernelSetup,dataSetup,thirdSetup] at ho
    all_goals rcases ho with rfl|rfl|rfl|rfl <;> simp only [Op.destination] <;> unfold Persistent at hr <;> omega)
  have geom:Layout K S T A d D (applyBlock (phaseSetup p) s):=setup_layout hl _ (by
    intro r hr o ho;exact ⟨nat o ho,regs r hr o ho⟩)
  have pk:peak (phaseSetup p) s ≤ B:=by
    have ha:phaseArena K A p ≤ B:=by omega
    have hsr:phaseSource K S T A p ≤ B:=by omega
    fin_cases p <;> simp [phaseSetup,phaseArena,phaseSource,kernelSetup,dataSetup,thirdSetup,peak,Op.peak,Op.apply,
      writeNat,next,hl.size,hl.source,hl.kernel,hl.arena,hl.data,hl.third,hl.dataSpectrum,hl.zero] at ha hsr ⊢ <;> omega
  have codeB:phaseBase p+(phaseSetup p).length ≤ B:=by
    rw [phaseSetup_length];fin_cases p <;> simp [phaseBase] <;> omega
  have setup:=block_runs (phaseSetup p) program (phaseBase p) n B x s (phase_setup_code p) hp hs codeB
    (by fin_cases p <;> simp [phaseSetup,kernelSetup,dataSetup,thirdSetup,readable,Op.readable]) pk
  let a:=applyBlock (phaseSetup p) s
  let e:State:={a with pc:=0}
  have ep:WordBound B e:=changePC_bound B _ 0 setup.final_bound (by omega)
  have eb:Values K (phaseSource K S T A p) v e:=by
    intro i;rw [(plain_block_heaps _ s nat).1];exact hv i
  have eroot:e.scalarHeap 0=some ⟨zeta D,false⟩:=by rw [(plain_block_heaps _ s nat).1];exact hroot
  obtain ⟨u,t,hu,ht,hout,_,hNat,hScalar,hOut,hRoots,hRegs,hpc⟩:=UniformFFTInputMachine.combined_execution n K (width K)
    (phaseSource K S T A p) 1 (phaseArena K A p) d D B x v e (by intro i;simpa using eb i) le_rfl (by simpa using hsep)
    (by omega) (by omega) rfl geom.height args.1 args.2.1 args.2.2.1 args.2.2.2 geom.table geom.order eroot hD hdiv (hbud p) ep
  have run:=UniformBoundedAssembly.boundedExecution_placed (phase_fft_code p)
    (by rw [UniformFFTInputMachine.combinedProgram_length];fin_cases p <;> simp [phaseFFTBase] <;> omega)
    (by fin_cases p <;> simp [phaseReturn] <;> omega) hu
  have ap:a.pc=phaseFFTBase p:=by
    rw [UniformReciprocalMachine.applyBlock_pc,hp,phaseSetup_length]
    fin_cases p <;> rfl
  have place:placed (phaseFFTBase p) e=a:=UniformPreparedFFTMachine.reset_placed a _ ap
  rw [place] at run
  let z:State:={u with pc:=phaseReturn p}
  have uz:Layout K S T A d D z:=geom.transport (by
    intro r hr;exact hRegs r (by unfold UniformFFTInputMachine.CombinedPersistent UniformPreparedFFTMachine.Persistent;unfold LayoutRegister at hr;omega))
  have rootEnd:UniformPreparedFFTMachine.rootAddress K (phaseArena K A p)+1=phaseArena K A p+span K:=by
    unfold UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase span;omega
  have outside:∀i,(i < phaseArena K A p ∨ phaseArena K A p+span K ≤ i)→z.scalarHeap i=s.scalarHeap i:=by
    intro i hi
    exact (hScalar i (by rw [rootEnd];exact hi)).trans (congrFun (plain_block_heaps _ s nat).1 i)
  have frame:Frame K A d a z:=by
    refine ⟨hNat,?_,hOut,hRoots,?_⟩
    · intro i hi;exact hScalar i (by rw [rootEnd];omega)
    · intro r hr;exact hRegs r (by unfold UniformFFTInputMachine.CombinedPersistent UniformPreparedFFTMachine.Persistent;unfold Persistent at hr;omega)
  refine ⟨z,_,setup.trans run,by rw [phaseSetup_length];omega,?_,uz,plain.trans frame,outside,rfl⟩
  simpa only [Values,z,padded_full,transform] using hout


def extendScalar (K : ℕ) (v : Fin (width K)→Scalar) (j : ℕ) : Scalar:=if h:j < width K then v ⟨j,h⟩ else Scalar.zero
def extendComplex (K : ℕ) (v : Fin (width K)→ℂ) (j : ℕ) : ℂ:=if h:j < width K then v ⟨j,h⟩ else 0

theorem point_run {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ)
    (v : Fin (width K)→Scalar) (k : Fin (width K)→ℂ) (s : State) (hl:Layout K S T A d D s)
    (hp:s.pc=476) (hv:Values K (dataArena K A+count K) (transform K v) s)
    (hk:Values K (A+count K) (transform K (fixed K k)) s) (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (9*width K+7) u ∧ Values K (dataArena K A+count K) (product K v k) u ∧
    Layout K S T A d D u ∧ Frame K A d s u ∧ u.pc=491:=by
  obtain ⟨hc,_,hend,_⟩:=wordBudget_bounds K A d B hb
  have hN:=width_pos K
  have nat:∀o∈pointSetup,Op.natOnly o:=by simp [pointSetup,Op.natOnly]
  have plain:=plain_frame pointSetup K A d s nat (by
    intro r hr o ho;simp [pointSetup] at ho
    rcases ho with rfl|rfl|rfl <;> simp only [Op.destination] <;> unfold Persistent at hr <;> omega)
  have geom:=setup_layout hl pointSetup (by
    intro r hr o ho
    refine ⟨nat o ho,?_⟩
    simp [pointSetup] at ho
    rcases ho with rfl|rfl|rfl <;> simp only [Op.destination] <;> unfold LayoutRegister at hr <;> omega)
  have pk:peak pointSetup s ≤ B:=by
    simp [peak,pointSetup,Op.peak,Op.apply,writeNat,next,hl.size,hl.dataSpectrum,hl.kernelSpectrum,hl.zero]
    simp only [endAddress,outputBase,normCell,dataArena,span] at hend ⊢
    omega
  have setup:=block_runs pointSetup program 476 n B x s pointSetup_code hp hs
    (by rw [pointSetup_length];omega) (by simp [readable,pointSetup,Op.readable]) pk
  let a:=applyBlock pointSetup s
  let e:State:={a with pc:=0}
  have he:=changePC_bound B a 0 setup.final_bound (by omega)
  have hae:a.pc=479:=by rw [UniformReciprocalMachine.applyBlock_pc,hp,pointSetup_length]
  have bank:UniformChirpPointwiseMachine.Bank (dataArena K A+count K) (width K) 0
      (extendScalar K (transform K v)) (extendComplex K (fun i=>(transform K (fixed K k) i).value)) e:=by
    intro j hj
    rw [(plain_block_heaps pointSetup s nat).1]
    simpa [UniformChirpPointwiseMachine.adjusted,extendScalar,hj] using hv ⟨j,hj⟩
  have kernels:UniformChirpPointwiseMachine.Kernels (A+count K) (width K)
      (extendComplex K (fun i=>(transform K (fixed K k) i).value)) e:=by
    intro j hj
    rw [(plain_block_heaps pointSetup s nat).1]
    have dep:=fixed_transform_prepared K k ⟨j,hj⟩
    have hi:=hk ⟨j,hj⟩
    cases heq:transform K (fixed K k) ⟨j,hj⟩ with | mk val flag=>
      simp only [heq] at dep hi
      simpa [extendComplex,hj,UniformPairMachine.prepared,←dep,heq] using hi
  have args:a.natReg 17=width K ∧ a.natReg 26=dataArena K A+count K ∧ a.natReg 28=A+count K:=by
    simp [a,pointSetup,applyBlock,Op.apply,writeNat,next,hl.size,hl.dataSpectrum,hl.kernelSpectrum,hl.zero]
  obtain ⟨u,hu,hprod,_,hframe,hpc⟩:=UniformChirpPointwiseMachine.pointwise_execution x (dataArena K A+count K)
    (A+count K) (width K) B (extendScalar K (transform K v))
    (extendComplex K (fun i=>(transform K (fixed K k) i).value)) e rfl args.1 args.2.1 args.2.2 bank kernels
    (Or.inr (by unfold dataArena span;omega)) (by omega)
    (by simp only [dataArena,endAddress,outputBase,normCell,span] at hend ⊢;omega)
    (by unfold endAddress outputBase normCell span at hend;omega) he
  have run:=UniformBoundedAssembly.boundedExecution_placed point_code (by rw [UniformChirpPointwiseMachine.program_length];omega) (by omega) hu
  rw [UniformPreparedFFTMachine.reset_placed a 479 hae] at run
  let z:State:={u with pc:=491}
  have lz:Layout K S T A d D z:=geom.transport (by
    intro r hr;exact hframe.2.2.2.2.1 r (Or.inr (by unfold LayoutRegister at hr;omega)))
  have fz:Frame K A d a z:=by
    refine ⟨fun i _=>congrFun hframe.1 i,?_,hframe.2.1,hframe.2.2.1,?_⟩
    · intro i hi;exact hframe.2.2.2.1 i (by simp only [dataArena,endAddress,outputBase,normCell,span] at hi ⊢;omega)
    · intro r hr;exact hframe.2.2.2.2.1 r (Or.inr (by unfold Persistent at hr;omega))
  refine ⟨z,?_,?_,lz,plain.trans fz,rfl⟩
  · convert setup.trans run using 1;rw [pointSetup_length];omega
  · intro i
    simpa [Values,z,extendScalar,extendComplex,i.isLt,product] using hprod i.val i.isLt

theorem norm_run {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ)
    (v : Fin (width K)→Scalar) (s : State) (hl:Layout K S T A d D s) (hp:s.pc=716)
    (hv:Values K (thirdArena K A+count K) v s) (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (2+UniformNormalizationMachine.runtime (width K)) u ∧
    Values K (thirdArena K A+count K) v u ∧
    u.scalarHeap (normCell K A)=some ⟨(width K:ℂ)⁻¹,false⟩ ∧ Layout K S T A d D u ∧ Frame K A d s u ∧ u.pc=754:=by
  obtain ⟨hc,_,hend,_⟩:=wordBudget_bounds K A d B hb
  have hN:=width_pos K
  have nat:∀o∈normSetup,Op.natOnly o:=by simp [normSetup,Op.natOnly]
  have plain:=plain_frame normSetup K A d s nat (by
    intro r hr o ho;simp [normSetup] at ho
    rcases ho with rfl|rfl <;> simp only [Op.destination] <;> unfold Persistent at hr <;> omega)
  have geom:=setup_layout hl normSetup (by
    intro r hr o ho;refine ⟨nat o ho,?_⟩
    simp [normSetup] at ho;rcases ho with rfl|rfl <;> simp only [Op.destination] <;> unfold LayoutRegister at hr <;> omega)
  have pk:peak normSetup s ≤ B:=by
    simp [peak,normSetup,Op.peak,Op.apply,writeNat,next,hl.size,hl.norm,hl.zero]
    unfold endAddress outputBase at hend;omega
  have setup:=block_runs normSetup program 716 n B x s normSetup_code hp hs
    (by rw [normSetup_length];omega) (by simp [readable,normSetup,Op.readable]) pk
  let a:=applyBlock normSetup s
  let e:State:={a with pc:=0}
  have he:=changePC_bound B a 0 setup.final_bound (by omega)
  have hae:a.pc=718:=by rw [UniformReciprocalMachine.applyBlock_pc,hp,normSetup_length]
  have args:a.natReg 17=width K ∧ a.natReg 27=normCell K A:=by
    simp [a,normSetup,applyBlock,Op.apply,writeNat,next,hl.size,hl.norm,hl.zero]
  obtain ⟨u,hu,hval,hframe,hpc⟩:=UniformNormalizationMachine.normalization_execution x B (width K) (normCell K A)
    e rfl args.1 args.2 hN (by omega) he
  have run:=UniformBoundedAssembly.boundedExecution_placed norm_code
    (by rw [UniformNormalizationMachine.program_length];omega) (by omega) hu
  rw [UniformPreparedFFTMachine.reset_placed a 718 hae] at run
  let z:State:={u with pc:=754}
  have lz:Layout K S T A d D z:=geom.transport (by
    intro r hr;exact hframe.2.2.2.2.2.1 r (by unfold LayoutRegister at hr;omega) (by unfold LayoutRegister at hr;omega) (by unfold LayoutRegister at hr;omega))
  have fz:Frame K A d a z:=by
    refine ⟨fun i _=>congrFun hframe.1 i,?_,hframe.2.1,hframe.2.2.1,?_⟩
    · intro i hi;exact hframe.2.2.2.1 i (by simp only [endAddress,outputBase,normCell] at hi ⊢;omega)
    · intro r hr;exact hframe.2.2.2.2.2.1 r (by unfold Persistent at hr;omega) (by unfold Persistent at hr;omega) (by unfold Persistent at hr;omega)
  refine ⟨z,?_,?_,hval,lz,plain.trans fz,rfl⟩
  · convert setup.trans run using 1;rw [normSetup_length]
  · intro i
    exact (hframe.2.2.2.1 (thirdArena K A+count K+i.val) (by unfold thirdArena normCell span;have:=i.isLt;omega)).trans
      ((congrFun (plain_block_heaps normSetup s nat).1 _).trans (hv i))

theorem output_run {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ)
    (v : Fin (width K)→Scalar) (s : State) (hl:Layout K S T A d D s) (hp:s.pc=754)
    (hv:Values K (thirdArena K A+count K) v s) (hn:s.scalarHeap (normCell K A)=some ⟨(width K:ℂ)⁻¹,false⟩)
    (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (10*width K+5) u ∧ Values K (outputBase K A) (normalized K v) u ∧
    Frame K A d s u ∧ u.pc=768:=by
  obtain ⟨hc,_,hend,_⟩:=wordBudget_bounds K A d B hb
  have hN:=width_pos K
  let e:State:={s with pc:=0}
  have he:=changePC_bound B s 0 hs (by omega)
  obtain ⟨u,hu,hval,hframe,hpc⟩:=output_execution x K (thirdArena K A+count K) (normCell K A) (outputBase K A) B v e
    rfl hl.size hl.thirdSpectrum hl.norm hl.output hv hn
    (by unfold thirdArena outputBase normCell span;omega)
    (by simp only [endAddress,outputBase,normCell,thirdArena,span] at hend ⊢;omega)
    (by exact hend) (by omega) he
  have run:=UniformBoundedAssembly.boundedExecution_placed output_code (by rw [outputProgram_length];omega) (by omega) hu
  rw [UniformPreparedFFTMachine.reset_placed s 754 hp] at run
  let z:State:={u with pc:=768}
  have fz:Frame K A d s z:=by
    refine ⟨fun i _=>congrFun hframe.1 i,?_,hframe.2.1,hframe.2.2.1,?_⟩
    · intro i hi;exact hframe.2.2.2.1 i (by simp only [endAddress,outputBase,normCell] at hi ⊢;omega)
    · intro r hr;exact hframe.2.2.2.2 r (by unfold Persistent at hr;omega)
  exact ⟨z,run,hval,fz,rfl⟩


def runtime (D K : ℕ) : ℕ:=16*K+49*width K+77+3*UniformPreparedFFTMachine.runtime D K+
  UniformNormalizationMachine.runtime (width K)

theorem initialization_run {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ) (s : State)
    (hp:s.pc=0) (h70:s.natReg 70=K) (h200:s.natReg 200=S) (h201:s.natReg 201=T)
    (h202:s.natReg 202=A) (h107:s.natReg 107=d) (h104:s.natReg 104=D)
    (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (4*K+23) u ∧ Layout K S T A d D u ∧ Frame K A d s u ∧ u.pc=26:=by
  obtain ⟨hc,hraw,hend,_⟩:=wordBudget_bounds K A d B hb
  have hN:width K ≤ B:=by unfold endAddress at hend;omega
  obtain ⟨v,hv,hvi,hvf,hvp⟩:=size_execution x K B s hp h70 hN (by omega) hs
  have first:=UniformBoundedAssembly.boundedExecution_placed size_code
    (by rw [sizeProgram_length];omega) (by omega) hv
  have he:placed 0 s=s:=by cases s;simp [placed]
  rw [he] at first
  let z:State:={v with pc:=9}
  have fz:Frame K A d s z:=by
    refine ⟨fun i _=>congrFun hvf.1 i,fun i _=>congrFun hvf.2.1 i,hvf.2.2.1,hvf.2.2.2.1,?_⟩
    intro r hr;exact hvf.2.2.2.2 r (by unfold Persistent at hr;omega)
  obtain ⟨tail,hl,hf,hpc⟩:=layout_execution x K S T A d D B z rfl hvi.withPC
    ((hvf.2.2.2.2 200 (Or.inl (by decide))).trans h200)
    ((hvf.2.2.2.2 201 (Or.inl (by decide))).trans h201)
    ((hvf.2.2.2.2 202 (Or.inl (by decide))).trans h202)
    ((hvf.2.2.2.2 107 (Or.inl (by decide))).trans h107)
    ((hvf.2.2.2.2 104 (Or.inl (by decide))).trans h104)
    hc hraw hend first.final_bound
  exact ⟨layoutFinal z,by convert first.trans tail using 1,hl,fz.trans hf,hpc⟩

theorem Values.transport_below {K a limit : ℕ} {v : Fin (width K)→Scalar} {s u : State}
    (h:Values K a v s) (ha:a+width K ≤ limit) (hf:∀i,i < limit→u.scalarHeap i=s.scalarHeap i) : Values K a v u:=by
  intro i;exact (hf (a+i.val) (by have:=i.isLt;omega)).trans (h i)

/-- One fixed three-transform program. Only the original physical data/kernel
banks and existing master root enter; every later bank is produced internally. -/
theorem execution {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ)
    (v : Fin (width K)→Scalar) (k : Fin (width K)→ℂ) (s : State)
    (hv:Values K S v s) (hk:Values K T (fixed K k) s) (hS:S+width K ≤ A) (hT:T+width K ≤ A) (hA:0 < A)
    (hp:s.pc=0) (h70:s.natReg 70=K) (h200:s.natReg 200=S) (h201:s.natReg 201=T)
    (h202:s.natReg 202=A) (h107:s.natReg 107=d) (h104:s.natReg 104=D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hD:0 < D) (hdiv:width K∣D)
    (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtime D K ∧
    Values K (outputBase K A) (convolution K v k) u ∧ Values K S v u ∧ Values K T (fixed K k) u ∧
    Frame K A d s u ∧ u.pc=768:=by
  obtain ⟨hc,_,_,_⟩:=wordBudget_bounds K A d B hb
  have hN:=width_pos K
  obtain ⟨z,hz,hlz,hfz,hzp⟩:=initialization_run x K S T A d D B s hp h70 h200 h201 h202 h107 h104 hb hs
  have vz:Values K S v z:=hv.transport_below hS (fun i hi=>hfz.scalars i (Or.inl hi))
  have kz:Values K T (fixed K k) z:=hk.transport_below hT (fun i hi=>hfz.scalars i (Or.inl hi))
  obtain ⟨u0,t0,hu0,ht0,hkernel,hl0,hf0,_,hp0⟩:=phase_run x K S T A d D B 0 (fixed K k) z hlz hzp kz hT hA
    ((hfz.scalars 0 (Or.inl hA)).trans hroot) hD hdiv hb hz.final_bound
  have vs0:Values K S v u0:=vz.transport_below hS (fun i hi=>hf0.scalars i (Or.inl hi))
  have sep1:phaseSource K S T A 1+width K ≤ phaseArena K A 1:=by simp [phaseSource,phaseArena,dataArena];omega
  obtain ⟨u1,t1,hu1,ht1,hdata,hl1,hf1,outside1,hp1⟩:=phase_run x K S T A d D B 1 v u0 hl0 hp0 vs0 sep1 hA
    ((hf0.scalars 0 (Or.inl hA)).trans ((hfz.scalars 0 (Or.inl hA)).trans hroot)) hD hdiv hb hu0.final_bound
  have kernel1:Values K (A+count K) (transform K (fixed K k)) u1:=hkernel.transport_below
    (show A+count K+width K ≤ phaseArena K A 1 by simp [phaseArena,dataArena,span];omega)
    (fun i hi=>outside1 i (Or.inl hi))
  obtain ⟨u2,hu2,hproduct,hl2,hf2,hp2⟩:=point_run x K S T A d D B v k u1 hl1 hp1 hdata kernel1 hb hu1.final_bound
  have sep2:phaseSource K S T A 2+width K ≤ phaseArena K A 2:=by simp [phaseSource,phaseArena,dataArena,thirdArena,span];omega
  obtain ⟨u3,t3,hu3,ht3,hthird,hl3,hf3,_,hp3⟩:=phase_run x K S T A d D B 2 (product K v k) u2 hl2 hp2 hproduct sep2 hA
    ((hf2.scalars 0 (Or.inl hA)).trans ((hf1.scalars 0 (Or.inl hA)).trans ((hf0.scalars 0 (Or.inl hA)).trans
      ((hfz.scalars 0 (Or.inl hA)).trans hroot)))) hD hdiv hb hu2.final_bound
  obtain ⟨u4,hu4,hthird4,hnorm,hl4,hf4,hp4⟩:=norm_run x K S T A d D B (transform K (product K v k)) u3 hl3 hp3 hthird hb hu3.final_bound
  obtain ⟨u5,hu5,hout,hf5,hp5⟩:=output_run x K S T A d D B (transform K (product K v k)) u4 hl4 hp4 hthird4 hnorm hb hu4.final_bound
  have halt:BoundedExecution program n x B u5 1 u5:=.halt hu5.final_bound (by simp [step,hp5,halt_code])
  have all:=hz.executes (hu0.executes (hu1.executes (hu2.executes (hu3.executes (hu4.executes (hu5.executes halt))))))
  have frame:=hfz.trans (hf0.trans (hf1.trans (hf2.trans (hf3.trans (hf4.trans hf5)))))
  refine ⟨u5,_,all,by unfold runtime;omega,hout,?_,?_,frame,hp5⟩
  · exact hv.transport_below hS (fun i hi=>frame.scalars i (Or.inl hi))
  · exact hk.transport_below hT (fun i hi=>frame.scalars i (Or.inl hi))

/-- Numeric cyclic convolution and actual tags are both retained by the literal
word: the flag is the evaluated three-FFT recurrence, never inferred from zero. -/
theorem execution_cyclic {n : ℕ} (x : Fin n→ℂ) (K S T A d D B : ℕ)
    (v : Fin (width K)→Scalar) (k : Fin (width K)→ℂ) (s : State)
    (hv:Values K S v s) (hk:Values K T (fixed K k) s) (hS:S+width K ≤ A) (hT:T+width K ≤ A) (hA:0 < A)
    (hp:s.pc=0) (h70:s.natReg 70=K) (h200:s.natReg 200=S) (h201:s.natReg 201=T)
    (h202:s.natReg 202=A) (h107:s.natReg 107=d) (h104:s.natReg 104=D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hD:0 < D) (hdiv:width K∣D)
    (hb:wordBudget K A d ≤ B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtime D K ∧
    (∀i,u.scalarHeap (outputBase K A+i.val)=some ⟨UniformCyclic.convolution
      (UniformCyclic.toZMod (fun i=>(v i).value)) (UniformCyclic.toZMod k) (FourierCRT.finZMod (width K) i),
      (convolution K v k i).dependent⟩) ∧ Frame K A d s u ∧ u.pc=768:=by
  obtain ⟨u,t,hu,ht,hout,_,_,hf,hp⟩:=execution x K S T A d D B v k s hv hk hS hT hA hp h70 h200 h201 h202 h107 h104 hroot hD hdiv hb hs
  refine ⟨u,t,hu,ht,?_,hf,hp⟩
  intro i
  rw [hout i]
  have value:=convolution_value K v k i
  cases hcv:convolution K v k i with | mk val dep=>
    simp only [hcv] at value ⊢
    rw [value]


/-- Startup metadata closes the master root and dyadic divisor. Placement and
original physical operands remain honest allocation/source obligations. -/
theorem selected_execution {n : ℕ} (hn:0 < n) (x : Fin n→ℂ) (r K S T A d : ℕ)
    (v : Fin (width K)→Scalar) (k : Fin (width K)→ℂ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hr:r ≤ UniformWorkingLength.workingLength n) (hsize:2^K ≤ 8*r)
    (hv:Values K S v s) (hk:Values K T (fixed K k) s) (hS:S+width K ≤ A) (hT:T+width K ≤ A)
    (hp:s.pc=0) (h70:s.natReg 70=K) (h200:s.natReg 200=S) (h201:s.natReg 201=T)
    (h202:s.natReg 202=A) (h107:s.natReg 107=d)
    (hA:UniformGlobalLocalPreparation.globalEnd n ≤ A)
    (hd:UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n ≤ d)
    (hb:wordBudget K A d ≤ (n+2)^19) (hs:WordBound ((n+2)^19) s) : ∃u t,
    BoundedExecution program n x ((n+2)^19) s t u ∧ t ≤ runtime (UniformMasterRootMachine.order n) K ∧
    Values K (outputBase K A) (convolution K v k) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    Values K S v u ∧ Values K T (fixed K k) u ∧ Frame K A d s u ∧ u.pc=768:=by
  have hroot:s.scalarHeap 0=some ⟨zeta (UniformMasterRootMachine.order n),false⟩:=by
    simpa [UniformCConstantsMachine.bank,UniformPairMachine.prepared] using ho.constants 0
  have hdiv:width K∣UniformMasterRootMachine.order n:=by
    simpa only [width_eq] using UniformMasterRootMachine.localPowerOrder_dvd hr hsize
  have hpositive:0 < A:=by have hg:=UniformGlobalLocalPreparation.globalEnd_formula n;omega
  obtain ⟨u,t,hu,ht,hout,hvs,hks,hf,hpc⟩:=execution x K S T A d (UniformMasterRootMachine.order n) ((n+2)^19)
    v k s hv hk hS hT hpositive hp h70 h200 h201 h202 h107 hm.saved.masterRoot hroot
    (UniformMasterRootMachine.order_bounds hn).1 hdiv hb hs
  have hsaved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
      (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) u:=by
    constructor
    · exact (hf.regs 100 (by simp [Persistent])).trans hm.saved.nextPrime
    · exact (hf.regs 101 (by simp [Persistent])).trans hm.saved.inputLength
    · exact (hf.regs 102 (by simp [Persistent])).trans hm.saved.count
    · exact (hf.regs 103 (by simp [Persistent])).trans hm.saved.workingLength
    · exact (hf.regs 104 (by simp [Persistent])).trans hm.saved.masterRoot
    · exact (hf.regs 105 (by simp [Persistent])).trans hm.saved.copyAddress
    · exact (hf.regs 106 (by simp [Persistent])).trans hm.saved.copyLength
  have metadata:=hm.transport_saved hsaved (by
    intro i hi;exact hf.nats (UniformInitialPreparation.copyBase n+i) (Or.inl (by unfold UniformPermutationInversePreparation.inverseBase at hd;omega)))
  have operands:=UniformGlobalLocalPreparation.operands_transport_below ho (by
    intro i hi;exact hf.scalars i (Or.inl (by omega)))
  exact ⟨u,t,hu,ht,hout,metadata,operands,hvs,hks,hf,hpc⟩

theorem runtime_log_bound (D K : ℕ) : runtime D K ≤
    3*((19*K+85)*count K+4*K+8*width K+7*(Nat.log2 (D+1)+1)+53)+
      16*K+49*width K+7*(Nat.log2 (width K+1)+1)+117:=by
  have hf:=UniformPreparedFFTMachine.runtime_log_bound D K
  have hn:=UniformNormalizationMachine.runtime_log_bound (width K)
  unfold runtime;omega

theorem wordBudget_power (K A d : ℕ) : wordBudget K A d ≤
    4*A+2*d+9*span K+width K+3*K*width K+2^(4*K+15)+770:=by
  have hf:=UniformPreparedFFTMachine.wordBudget_power K (thirdArena K A) d
  simp only [wordBudget,thirdArena,endAddress,outputBase,normCell] at hf ⊢
  omega

end
end ExactFourierCircuits.UniformDyadicConvolutionMachine
