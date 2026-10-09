import UniformHeapDirectBatch
import UniformAllTensorFibersCopyMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSmallAxisFourierMachine
open UniformMachine UniformAssembly UniformPairMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
open UniformSelectedAxisFiberPreparation (radices)
namespace Copy
abbrev Args := UniformAllTensorFibersCopyMachine.Args
end Copy
noncomputable section
/-- Raw4970=axis,4971=array,4972=gather bank,4973=Fourier bank,4975=root.
The fixed caller reads the actual retained CRT radix and divides the working
length; no fiber-count or transform action is a header. -/
def boot : List Op := [.literal 4974 0,.add 1910 4970 4974,
 .add 1912 4971 4974,.add 1913 4972 4974]
def read : List Op := [.literal 4976 4,.add 4977 105 102,.mul 4978 4970 4976,
 .add 4978 4977 4978,.getNat 4950 4978]
def setup : List Op := [.add 4952 4972 4974,.add 4953 4973 4974,.add 4954 4975 4974]
def scatterSetup : List Op := [.add 1910 4970 4974,.add 1912 4971 4974,.add 1913 4973 4974]
def program : Program := boot.map Op.code++
 (UniformAllTensorFibersCopyMachine.program false).map (relocate 4 59)++read.map Op.code++
 [.natBinary .div 4951 103 4950]++setup.map Op.code++
 UniformHeapDirectBatch.program.map (relocate 68 102)++scatterSetup.map Op.code++
 (UniformAllTensorFibersCopyMachine.program true).map (relocate 105 160)++[.halt]
theorem program_length : program.length=161 := by
 simp only [program,List.length_append,List.length_map,boot,read,setup,scatterSetup,
  UniformAllTensorFibersCopyMachine.program_length,UniformHeapDirectBatch.program_length]
 rfl
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem gather_code : CodeAt (UniformAllTensorFibersCopyMachine.program false) program 4 59 := by
 intro i hi;rw [UniformAllTensorFibersCopyMachine.program_length] at hi
 interval_cases i <;> rfl
theorem read_code : BlockAt read program 59 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem div_code : program[64]?=some (.natBinary .div 4951 103 4950) := rfl
theorem setup_code : BlockAt setup program 65 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem batch_code : CodeAt UniformHeapDirectBatch.program program 68 102 := by
 intro i hi;rw [UniformHeapDirectBatch.program_length] at hi
 interval_cases i <;> rfl
theorem scatterSetup_code : BlockAt scatterSetup program 102 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem scatter_code : CodeAt (UniformAllTensorFibersCopyMachine.program true) program 105 160 := by
 intro i hi;rw [UniformAllTensorFibersCopyMachine.program_length] at hi
 interval_cases i <;> rfl
theorem halt_code : program[160]?=some .halt := rfl
structure Args (axis A D E root : ℕ) (s : State) : Prop where
 axis : s.natReg 4970=axis
 array : s.natReg 4971=A
 gather : s.natReg 4972=D
 transformed : s.natReg 4973=E
 root : s.natReg 4975=root

def Changed (q:ℕ) : Prop := q=1910 ∨ q=1912 ∨ q=1913 ∨ q=4974 ∨
 q=4976 ∨ q=4977 ∨ q=4978 ∨ (4950≤q ∧ q≤4954)
def SetupFrame (s u:State) : Prop := u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,¬Changed q→u.natReg q=s.natReg q)
theorem writeNat_frame (s:State) (d v:ℕ) (hd:Changed d) : SetupFrame s (writeNat s d v) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq
 have ne:q≠d:=by intro eq;subst q;exact hq hd
 simp [writeNat,next,ne]
theorem setup_frame (os:List Op) (s:State)
 (h:∀o∈os,match o with
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _=>Changed d
  | _=>False) : SetupFrame s (applyBlock os s) := by
 induction os generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | cons o os ih=>
   have ho:=h o (by simp)
   have rest:=ih (o.apply s) (by intro q hq;exact h q (by simp [hq]))
   have fr:SetupFrame s (o.apply s):=by
    cases o <;> simp only at ho <;> try contradiction
    all_goals exact writeNat_frame s _ _ ho
   exact ⟨rest.1.trans fr.1,rest.2.1.trans fr.2.1,rest.2.2.1.trans fr.2.2.1,
    rest.2.2.2.1.trans fr.2.2.2.1,rest.2.2.2.2.1.trans fr.2.2.2.2.1,
    fun q hq=>(rest.2.2.2.2.2 q hq).trans (fr.2.2.2.2.2 q hq)⟩
theorem boot_frame (s:State) : SetupFrame s (applyBlock boot s) := by
 apply setup_frame;intro o ho;simp [boot] at ho
 rcases ho with rfl|rfl|rfl|rfl <;> simp [Changed]
theorem read_frame (s:State) : SetupFrame s (applyBlock read s) := by
 apply setup_frame;intro o ho;simp [read] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp [Changed]
theorem finalSetup_frame (s:State) : SetupFrame s (applyBlock setup s) := by
 apply setup_frame;intro o ho;simp [setup] at ho
 rcases ho with rfl|rfl|rfl <;> simp [Changed]
theorem scatterSetup_frame (s:State) : SetupFrame s (applyBlock scatterSetup s) := by
 apply setup_frame;intro o ho;simp [scatterSetup] at ho
 rcases ho with rfl|rfl|rfl <;> simp [Changed]
theorem SetupFrame.metadata {n:ℕ} {s u:State} (f:SetupFrame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · constructor
   all_goals exact (f.2.2.2.2.2 _ (by unfold Changed;omega)).trans (by first
    |exact h.saved.nextPrime|exact h.saved.inputLength|exact h.saved.count
    |exact h.saved.workingLength|exact h.saved.masterRoot|exact h.saved.copyAddress|exact h.saved.copyLength)
 · intro a _;exact congrFun f.1 _

theorem boot_args {axis A D E root : ℕ} {s:State} (h:Args axis A D E root s) :
 Copy.Args axis A D (applyBlock boot s) := by
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.axis,h.array,h.gather]
theorem boot_raw {axis A D E root : ℕ} {s:State} (h:Args axis A D E root s) :
 Args axis A D E root (applyBlock boot s) := by
 constructor
 all_goals exact (boot_frame s).2.2.2.2.2 _ (by unfold Changed;omega) |>.trans (by first
  |exact h.axis|exact h.array|exact h.gather|exact h.transformed|exact h.root)

theorem read_values {n:ℕ} (i:Fin (ell n+1)) (s:State) (h:Metadata n s)
 (axis:s.natReg 4970=i.val) :
 (applyBlock read s).natReg 4950=radices n i ∧
 (applyBlock read s).natReg 4978=copyBase n+ell n+4*i.val := by
 have cell:=UniformSelectedAxisFiberPreparation.crt_cell i s h
 have cp:s.natReg 105=copyBase n:=h.saved.copyAddress
 simp [read,applyBlock,Op.apply,writeNat,next,cp,h.saved.count,axis,Nat.mul_comm]
 rw [Nat.mul_comm i.val 4,cell]
 rfl

theorem read_runs {n B:ℕ} (i:Fin (ell n+1)) (x:Fin n→ℂ) (s:State) (h:Metadata n s)
 (axis:s.natReg 4970=i.val) (code:161≤B) (pc:s.pc=59)
 (bound:WordBound B s) :
 BoundedRuns program n x B s 5 (applyBlock read s) := by
 have cell:=UniformSelectedAxisFiberPreparation.crt_cell i s h
 have cp:s.natReg 105=copyBase n:=h.saved.copyAddress
 have address:copyBase n+ell n+4*i.val≤B:=(bound.2.2.1 _ _ cell).1
 have rp:radices n i≤B:=(bound.2.2.1 _ _ cell).2
 have start:copyBase n+ell n≤B:=by omega
 have off:4*i.val≤B:=by omega
 have normalized:s.natHeap (copyBase n+ell n+i.val*4)=some (radices n i):=by
  simpa only [Nat.mul_comm] using cell
 exact block_runs read program 59 n B x s read_code pc bound (by change 59+5≤B;omega)
  (by simp [read,readable,Op.readable,Op.apply,writeNat,next,cp,h.saved.count,axis,normalized])
  (by simp [read,peak,Op.peak,Op.apply,writeNat,next,cp,h.saved.count,axis,normalized]
      omega)

theorem div_runs {n B:ℕ} (i:Fin (ell n+1)) (x:Fin n→ℂ) (s:State) (h:Metadata n s)
 (width:s.natReg 4950=radices n i) (code:161≤B) (pc:s.pc=64) (bound:WordBound B s) :
 BoundedRuns program n x B s 1 (writeNat s 4951 (len n/radices n i)) := by
 have pos:0<radices n i:=(UniformSelectedAxisFiberPreparation.selected_positive n i).2.1
 have wb:len n/radices n i≤B:=(Nat.div_le_self _ _).trans
  (by rw [←h.saved.workingLength];exact bound.2.1 103)
 refine .next bound ?_ (.refl (writeNat_bound B s 4951 _ bound (by simp [pc];omega) wb))
 simp [step,pc,div_code,width,h.saved.workingLength,evalNat,Nat.ne_of_gt pos]

theorem selected_count (n:ℕ) (i:Fin (ell n+1)) : len n/radices n i=UniformAllTensorFibersCopyMachine.fibers n i := by
 rw [←UniformAllTensorFibersCopyMachine.fibers_product n i]
 exact Nat.mul_div_cancel _ (UniformSelectedAxisFiberPreparation.selected_positive n i).2.1

theorem Args.copy_frame {axis A D E root:ℕ} {s u:State}
 (f:UniformAllTensorFibersCopyMachine.Frame s u) (h:Args axis A D E root s) : Args axis A D E root u := by
 constructor
 all_goals exact (f.natReg _ (by decide)).trans (by first
  |exact h.axis|exact h.array|exact h.gather|exact h.transformed|exact h.root)

theorem boot_runs {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=0) (code:161≤B) (bound:WordBound B s) :
 BoundedRuns program n x B s 4 (applyBlock boot s) := by
 exact block_runs boot program 0 n B x s boot_code pc bound (by change 0+4≤B;omega)
  (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next]
      exact ⟨bound.2.1 4970,bound.2.1 4971,bound.2.1 4972⟩)

theorem gather_execution {n B:ℕ} (hn:0<n) (i:Fin (ell n+1)) (A D E root:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val A D E root s)
 (source:UniformAllTensorFibersCopyMachine.FullSource false n A D s.scalarHeap)
 (sep:A+len n≤D) (aBound:A+2*len n≤B) (dBound:D+len n≤B)
 (code:161≤B) (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (4+UniformAllTensorFibersCopyMachine.runtime n i) u ∧
 u.pc=59 ∧ Metadata n u ∧ Args i.val A D E root u ∧ u.natReg 4974=0 ∧
 (∀j,j<UniformAllTensorFibersCopyMachine.fibers n i→∀t,t<radices n i→
  u.scalarHeap (D+UniformAllTensorFibersCopyMachine.packed n i j t)=
  s.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j t)) ∧
 (∀z,z<D∨D+len n≤z→u.scalarHeap z=s.scalarHeap z) ∧
 u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 have first:=boot_runs x s pc code bound
 let e:=setPC (applyBlock boot s) 0
 have eb:=changePC_bound B _ 0 first.final_bound (by omega)
 have ef:=UniformAllTensorFibersCopyMachine.Frame.pc (applyBlock boot s) 0
 have md:Metadata n e:=ef.metadata ((boot_frame s).metadata metadata)
 have ea:Copy.Args i.val A D e:=
  ⟨(boot_args args).axis,(boot_args args).array,(boot_args args).bank⟩
 obtain ⟨v,run,_,action,outside,frame,mv⟩:=UniformAllTensorFibersCopyMachine.execution hn false i A D B
  x e md ea source sep aBound dBound (by omega) rfl eb
 have placed:=UniformBoundedAssembly.boundedExecution_placed gather_code
  (by rw [UniformAllTensorFibersCopyMachine.program_length];omega) (by omega :59≤B) run
 have eq:UniformAssembly.placed 4 e=applyBlock boot s:=by
  change setPC (applyBlock boot s) 4=applyBlock boot s
  have pe:(applyBlock boot s).pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
  unfold setPC;rw [←pe]
 rw [eq] at placed
 have fr:=ef.trans (frame.trans (UniformAllTensorFibersCopyMachine.Frame.pc v 59))
 refine ⟨setPC v 59,first.trans placed,rfl,(UniformAllTensorFibersCopyMachine.Frame.pc v 59).metadata mv,Args.copy_frame fr (boot_raw args),?_,action,outside,?_,?_,?_⟩
 · exact (frame.natReg 4974 (by decide)).trans (by simp [e,setPC,boot,applyBlock,Op.apply,writeNat,next])
 · exact frame.natHeap
 · exact frame.outputs
 · exact frame.roots

/-- The actual read/divide/setup prefix supplies raw batch headers. -/
theorem batchSetup_execution {n B:ℕ} (i:Fin (ell n+1)) (A D E root:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val A D E root s)
 (zero:s.natReg 4974=0) (code:161≤B) (pc:s.pc=59) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s 9 u ∧ u.pc=68 ∧ Metadata n u ∧
 Args i.val A D E root u ∧u.natReg 4974=0 ∧
 u.natReg 4950=radices n i ∧u.natReg 4951=UniformAllTensorFibersCopyMachine.fibers n i ∧
 u.natReg 4952=D ∧u.natReg 4953=E ∧u.natReg 4954=root ∧
 SetupFrame s u := by
 have readRun:=read_runs i x s metadata args.axis code pc bound
 let v:=applyBlock read s
 have vp:v.pc=64:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have vm:Metadata n v:=(read_frame s).metadata metadata
 have width:v.natReg 4950=radices n i:=(read_values i s metadata args.axis).1
 have divide:=div_runs i x v vm width code vp readRun.final_bound
 let w:=writeNat v 4951 (len n/radices n i)
 have wp:w.pc=65:=by simp [w,writeNat,next,vp]
 have divFrame:SetupFrame v w:=writeNat_frame v 4951 _ (by simp [Changed])
 have kept(q:ℕ)(hq:q=4970∨q=4971∨q=4972∨q=4973∨q=4974∨q=4975):w.natReg q=s.natReg q:=by
  simp [w,v,read,applyBlock,Op.apply,writeNat,next]
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
 have last:=block_runs setup program 65 n B x w setup_code wp divide.final_bound
  (by change 65+3≤B;omega) (by simp [setup,readable,Op.readable])
  (by simp [setup,peak,Op.peak,Op.apply,writeNat,next,kept 4974 (by simp),zero,
        kept 4972 (by simp),kept 4973 (by simp),kept 4975 (by simp)]
      exact ⟨bound.2.1 4972,bound.2.1 4973,bound.2.1 4975⟩)
 let u:=applyBlock setup w
 have fr:SetupFrame s u:=by
  have rf:=read_frame s
  have ff:=finalSetup_frame w
  exact ⟨rfl,rfl,rfl,rfl,rfl,fun q hq=>(ff.2.2.2.2.2 q hq).trans
    ((divFrame.2.2.2.2.2 q hq).trans (rf.2.2.2.2.2 q hq))⟩
 refine ⟨u,by convert (readRun.trans divide).trans last using 1; rfl,?_,fr.metadata metadata,?_,?_,?_,?_,?_,?_,?_,fr⟩
 · rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
 · constructor
   all_goals simp [u,setup,applyBlock,Op.apply,writeNat,next,kept, args.axis,args.array,args.gather,args.transformed,args.root]
 · simp [u,setup,applyBlock,Op.apply,writeNat,next,kept 4974 (by simp),zero]
 · simpa [u,setup,applyBlock,Op.apply,writeNat,next,w] using width
 · simp [u,setup,applyBlock,Op.apply,writeNat,next,w,selected_count]
 · simp [u,setup,applyBlock,Op.apply,writeNat,next,kept 4972 (by simp),kept 4974 (by simp),zero,args.gather]
 · simp [u,setup,applyBlock,Op.apply,writeNat,next,kept 4973 (by simp),kept 4974 (by simp),zero,args.transformed]
 · simp [u,setup,applyBlock,Op.apply,writeNat,next,kept 4975 (by simp),kept 4974 (by simp),zero,args.root]

theorem Args.batch_frame {n axis A D E root:ℕ} {s u:State}
 (f:UniformHeapDirectBatch.Frame E (len n) s u) (h:Args axis A D E root s) : Args axis A D E root u := by
 constructor
 all_goals exact (f.natReg _ (by unfold UniformHeapDirectBatch.Changed;omega)).trans (by first
  |exact h.axis|exact h.array|exact h.gather|exact h.transformed|exact h.root)

theorem batch_metadata {n E volume:ℕ} {s u:State} (f:UniformHeapDirectBatch.Frame E volume s u)
 (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · constructor
   all_goals exact (f.natReg _ (by unfold UniformHeapDirectBatch.Changed;omega)).trans (by first
    |exact h.saved.nextPrime|exact h.saved.inputLength|exact h.saved.count
    |exact h.saved.workingLength|exact h.saved.masterRoot|exact h.saved.copyAddress|exact h.saved.copyLength)
 · intro a _;exact congrFun f.natHeap _

theorem scatterSetup_runs {n B axis A D E root:ℕ} (x:Fin n→ℂ) (s:State)
 (_h:Args axis A D E root s) (zero:s.natReg 4974=0)
 (code:161≤B) (pc:s.pc=102) (bound:WordBound B s) :
 BoundedRuns program n x B s 3 (applyBlock scatterSetup s) := by
 exact block_runs scatterSetup program 102 n B x s scatterSetup_code pc bound
  (by change 102+3≤B;omega) (by simp [scatterSetup,readable,Op.readable])
  (by simp [scatterSetup,peak,Op.peak,Op.apply,writeNat,next,zero]
      exact ⟨bound.2.1 4970,bound.2.1 4971,bound.2.1 4973⟩)

theorem scatterSetup_args {axis A D E root:ℕ} {s:State}
 (h:Args axis A D E root s) (zero:s.natReg 4974=0) :
 Copy.Args axis A E (applyBlock scatterSetup s) := by
 constructor <;> simp [scatterSetup,applyBlock,Op.apply,writeNat,next,zero,h.axis,h.array,h.transformed]

/-- Gather every actual fiber, run the22-instruction direct Fourier kernel on
all contiguous fibers, and scatter every full tagged Scalar back. -/
theorem execution {n B:ℕ} (hn:0<n) (i:Fin (ell n+1)) (A D E root:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val A D E root s)
 (eta:ℂ) (v:Fin (len n)→Scalar)
 (source:∀z:Fin (len n),s.scalarHeap (A+z.val)=some (v z))
 (rootVal:s.scalarHeap root=some (prepared eta))
 (rootD:root<D∨D+len n≤root) (rootE:root<E∨E+len n≤root)
 (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B)
 (code:161≤B) (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s
  (2*UniformAllTensorFibersCopyMachine.runtime n i+
   UniformAllTensorFibersCopyMachine.fibers n i*UniformHeapDirectBatch.arrayCost (radices n i)+22) u ∧
 (∀j:Fin (UniformAllTensorFibersCopyMachine.fibers n i),∀k:Fin (radices n i),∃a,
   u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=some a ∧
   a.value=∑t:Fin (radices n i),eta^(k.val*t.val)*
    (v (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))).value) ∧
 Metadata n u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 have fs:UniformAllTensorFibersCopyMachine.FullSource false n A D s.scalarHeap:=by
  intro z hz;exact ⟨v ⟨z,hz⟩,source ⟨z,hz⟩⟩
 obtain ⟨g,gr,pg,mg,ag,zg,ga,go,ng,og,rg⟩:=gather_execution hn i A D E root x s metadata args fs
  sepAD (by omega) (by omega) code pc bound
 obtain ⟨b,br,pb,mb,ab,zb,width,count,bsource,bdest,broot,bf⟩:=batchSetup_execution i A D E root
  x g mg ag zg code pg gr.final_bound
 let bank:Fin (UniformAllTensorFibersCopyMachine.fibers n i)→Fin (radices n i)→Scalar:=
  fun j t=>v (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))
 have bs:UniformHeapDirectBatch.Source (radices n i) D bank b:=by
  intro j t
  rw [bf.2.1]
  have eq:=ga j.val j.isLt t.val t.isLt
  change g.scalarHeap (D+(j.val*radices n i+t.val))=s.scalarHeap
   (A+UniformAllTensorFibersCopyMachine.native n i j.val t.val) at eq
  rw [show UniformHeapDirectBatch.arrayBase D (radices n i) j.val+t.val=
    D+(j.val*radices n i+t.val) by simp [UniformHeapDirectBatch.arrayBase,Nat.add_assoc],eq]
  exact source (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))
 have rb:b.scalarHeap root=some (prepared eta):=by rw [bf.2.1,go root rootD,rootVal]
 let be:=setPC b 0
 obtain ⟨c,cr,ca,_,cf,_,_⟩:=UniformHeapDirectBatch.execution n B (radices n i)
  (UniformAllTensorFibersCopyMachine.fibers n i) D E root x be eta bank rfl width count bsource bdest broot
  rb bs (by simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using rootE)
  (Or.inl (by simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using sepDE))
  (by omega) (by rw [UniformAllTensorFibersCopyMachine.fibers_product];omega)
  (by rw [UniformAllTensorFibersCopyMachine.fibers_product];exact eBound)
  (changePC_bound B b 0 br.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed batch_code
  (by rw [UniformHeapDirectBatch.program_length];omega) (by omega :102≤B) cr
 have bpeq:UniformAssembly.placed 68 be=b:=by change setPC b 68=b;unfold setPC;rw [←pb]
 rw [bpeq] at moved
 let m:=setPC c 102
 have fm:UniformHeapDirectBatch.Frame E (len n) b m:=by
  have ff:=(UniformHeapDirectBatch.Frame.pc E _ b 0).trans
    (cf.trans (UniformHeapDirectBatch.Frame.pc E _ c 102))
  simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using ff
 have mm:Metadata n m:=batch_metadata fm mb
 have am:Args i.val A D E root m:=Args.batch_frame fm ab
 have zm:m.natReg 4974=0:=(fm.natReg 4974 (by unfold UniformHeapDirectBatch.Changed;omega)).trans zb
 have sr:=scatterSetup_runs x m am zm code rfl moved.final_bound
 let ss:=applyBlock scatterSetup m
 have sp:ss.pc=105:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have sm:Metadata n ss:=(scatterSetup_frame m).metadata mm
 let se:=setPC ss 0
 have ep:=UniformAllTensorFibersCopyMachine.Frame.pc ss 0
 have seMeta:Metadata n se:=ep.metadata sm
 have seArgs:Copy.Args i.val A E se:=⟨(scatterSetup_args am zm).axis,
  (scatterSetup_args am zm).array,(scatterSetup_args am zm).bank⟩
 have fse:UniformAllTensorFibersCopyMachine.FullSource true n A E se.scalarHeap:=by
  intro z hz
  let p:Fin (UniformAllTensorFibersCopyMachine.fibers n i)×Fin (radices n i):=
    (UniformAllTensorFibersCopyMachine.packedEquiv n i).symm ⟨z,hz⟩
  have pe:UniformAllTensorFibersCopyMachine.packedEquiv n i p=⟨z,hz⟩:=
   (UniformAllTensorFibersCopyMachine.packedEquiv n i).apply_symm_apply ⟨z,hz⟩
  have pv:=congrArg Fin.val pe
  rw [UniformAllTensorFibersCopyMachine.packedEquiv_val] at pv
  change p.1.val*radices n i+p.2.val=z at pv
  obtain ⟨a,ha,_⟩:=ca p.1 p.2
  refine ⟨a,?_⟩
  change c.scalarHeap (E+z)=some a
  simpa only [UniformHeapDirectBatch.arrayBase,Nat.add_assoc,pv] using ha
 obtain ⟨u,ur,_,ua,_,uf,um⟩:=UniformAllTensorFibersCopyMachine.execution hn true i A E B x se seMeta
  seArgs fse (by omega) aBound eBound (by omega) rfl
  (changePC_bound B ss 0 sr.final_bound (by omega))
 have smoved:=UniformBoundedAssembly.boundedExecution_placed scatter_code
  (by rw [UniformAllTensorFibersCopyMachine.program_length];omega) (by omega :160≤B) ur
 have seq:UniformAssembly.placed 105 se=ss:=by change setPC ss 105=ss;unfold setPC;rw [←sp]
 rw [seq] at smoved
 let final:=setPC u 160
 have halt:BoundedExecution program n x B final 1 final:=.halt smoved.final_bound
  (by simp [step,final,setPC,halt_code])
 refine ⟨final,?_,?_,(UniformAllTensorFibersCopyMachine.Frame.pc u 160).metadata um,?_,?_,?_⟩
 · convert (((gr.trans br).trans moved).trans sr).trans smoved |>.executes halt using 1
   ring
 · intro j k
   obtain ⟨a,ha,hv⟩:=ca j k
   refine ⟨a,?_,hv⟩
   have copy:=ua j.val j.isLt k.val k.isLt
   change u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=
    c.scalarHeap (E+UniformAllTensorFibersCopyMachine.packed n i j.val k.val) at copy
   change u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=some a
   rw [copy]
   simpa only [UniformHeapDirectBatch.arrayBase,UniformAllTensorFibersCopyMachine.packed,Nat.add_assoc] using ha
 · exact uf.natHeap.trans (fm.natHeap.trans (bf.1.trans ng))
 · exact uf.outputs.trans (fm.outputs.trans (bf.2.2.2.1.trans og))
 · exact uf.roots.trans (fm.roots.trans (bf.2.2.2.2.1.trans rg))

def runtime (n:ℕ) (i:Fin (ell n+1)) :=
 2*UniformAllTensorFibersCopyMachine.runtime n i+
 UniformAllTensorFibersCopyMachine.fibers n i*UniformHeapDirectBatch.arrayCost (radices n i)+22

theorem small_cost_bound {n threshold:ℕ} (i:Fin (ell n+1)) (hsmall:radices n i<threshold) :
 runtime n i≤(8*threshold+96)*len n+14*i.val+50 := by
 have copy:=UniformAllTensorFibersCopyMachine.runtime_bound n i
 have small:=UniformHeapDirectBatch.small_cost_bound
  (UniformSelectedAxisFiberPreparation.selected_positive n i).2.1 hsmall
  (UniformAllTensorFibersCopyMachine.fibers n i)
 rw [UniformAllTensorFibersCopyMachine.fibers_product] at small
 unfold runtime
 nlinarith
end
end ExactFourierCircuits.UniformSmallAxisFourierMachine
