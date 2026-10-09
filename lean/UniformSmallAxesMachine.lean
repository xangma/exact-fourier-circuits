import UniformSmallAxisFourierPreservation
import UniformSmallAxesBudget
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSmallAxesMachine
open UniformMachine UniformAssembly
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
open UniformSelectedAxisFiberPreparation (radices)
noncomputable section
/-- One fixed outer loop:5102=array,5103=gather bank,5104=Fourier bank.
All selected roots come from the actual retained bank6+i. -/
def boot (T:ℕ) : List Op := [.literal 5105 0,.literal 5106 0,.literal 5107 1,.literal 5108 4,
 .literal 5110 6,.add 5111 105 102,.add 5112 102 5107,.literal 5114 T]
def read : List Op := [.mul 5109 5105 5108,.add 5109 5111 5109,.getNat 5113 5109]
def setup : List Op := [.add 4970 5105 5106,.add 4971 5102 5106,.add 4972 5103 5106,
 .add 4973 5104 5106,.add 4975 5110 5105]
def post : List Op := [.add 5105 5105 5107]
def head (T:ℕ) : Program := (boot T).map Op.code++[.branchLT 5105 5112 9 181]++
 read.map Op.code++[.branchLT 5113 5114 13 179]++setup.map Op.code
def program (T:ℕ) : Program := head T++UniformSmallAxisFourierMachine.program.map (relocate 18 179)++
 post.map Op.code++[.jump 8,.halt]
theorem head_length (T:ℕ) : (head T).length=18 := rfl
theorem program_length (T:ℕ) : (program T).length=182 := by
 simp only [program,List.length_append,List.length_map,head_length,UniformSmallAxisFourierMachine.program_length]
 rfl
theorem boot_code (T:ℕ) : BlockAt (boot T) (program T) 0 := by
 intro i hi;change i<8 at hi;interval_cases i <;> rfl
theorem read_code (T:ℕ) : BlockAt read (program T) 9 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem setup_code (T:ℕ) : BlockAt setup (program T) 13 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem child_code (T:ℕ) : CodeAt UniformSmallAxisFourierMachine.program (program T) 18 179 := by
 intro i hi
 simp only [program,List.append_assoc]
 rw [List.getElem?_append_right (by rw [head_length];omega)]
 simp only [head_length,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
theorem post_code (T:ℕ) : BlockAt post (program T) 179 := by
 intro i hi;change i<1 at hi;interval_cases i;rfl
theorem branch_code (T:ℕ) : (program T)[8]?=some (.branchLT 5105 5112 9 181) := rfl
theorem active_code (T:ℕ) : (program T)[12]?=some (.branchLT 5113 5114 13 179) := rfl
theorem jump_code (T:ℕ) : (program T)[180]?=some (.jump 8) := rfl
theorem halt_code (T:ℕ) : (program T)[181]?=some .halt := rfl
structure Header (n T A D E i:ℕ) (s:State) : Prop where
 array : s.natReg 5102=A
 gather : s.natReg 5103=D
 transformed : s.natReg 5104=E
 index : s.natReg 5105=i
 zero : s.natReg 5106=0
 one : s.natReg 5107=1
 four : s.natReg 5108=4
 rootBase : s.natReg 5110=6
 table : s.natReg 5111=copyBase n+ell n
 count : s.natReg 5112=ell n+1
 threshold : s.natReg 5114=T

def Changed (q:ℕ) : Prop := (4970≤q ∧q≤4975)∨(5105≤q ∧q≤5114)
def Frame (s u:State) : Prop := u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,¬Changed q→u.natReg q=s.natReg q)
theorem Frame.pc (s:State) (pc:ℕ) : Frame s (setPC s pc) := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v:State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
 g.2.2.2.1.trans f.2.2.2.1,g.2.2.2.2.1.trans f.2.2.2.2.1,
 fun q h=>(g.2.2.2.2.2 q h).trans (f.2.2.2.2.2 q h)⟩
theorem writeNat_frame (s:State) (d v:ℕ) (hd:Changed d) : Frame s (writeNat s d v) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq
 have ne:q≠d:=by intro eq;subst q;exact hq hd
 simp [writeNat,next,ne]
theorem block_frame (os:List Op) (s:State)
 (h:∀o∈os,match o with
 |.literal d _|.add d _ _|.sub d _ _|.mul d _ _|.getNat d _=>Changed d
 |_=>False) : Frame s (applyBlock os s) := by
 induction os generalizing s with
 |nil=>exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 |cons o os ih=>
  have ho:=h o (by simp)
  have rest:=ih (o.apply s) (by intro q hq;exact h q (by simp [hq]))
  have fr:Frame s (o.apply s):=by
   cases o <;> simp only at ho <;> try contradiction
   all_goals exact writeNat_frame s _ _ ho
  exact fr.trans rest
theorem boot_frame (T:ℕ) (s:State) : Frame s (applyBlock (boot T) s) := by
 apply block_frame;intro o ho;simp [boot] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Changed]
theorem read_frame (s:State) : Frame s (applyBlock read s) := by
 apply block_frame;intro o ho;simp [read] at ho
 rcases ho with rfl|rfl|rfl <;> simp [Changed]
theorem setup_frame (s:State) : Frame s (applyBlock setup s) := by
 apply block_frame;intro o ho;simp [setup] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp [Changed]
theorem post_frame (s:State) : Frame s (applyBlock post s) := by
 apply block_frame;intro o ho;simp [post] at ho;subst o;simp [Changed]
theorem Frame.metadata {n:ℕ} {s u:State} (f:Frame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · constructor
   all_goals exact (f.2.2.2.2.2 _ (by unfold Changed;omega)).trans (by first
    |exact h.saved.nextPrime|exact h.saved.inputLength|exact h.saved.count
    |exact h.saved.workingLength|exact h.saved.masterRoot|exact h.saved.copyAddress|exact h.saved.copyLength)
 · intro a _;exact congrFun f.1 _

def RootBank (n:ℕ) (s:State) : Prop :=∀i:Fin (ell n+1),s.scalarHeap (6+i.val)=some (prepared (OAI.ExactFourier.zeta (radices n i)))
theorem Frame.roots {n:ℕ} {s u:State} (f:Frame s u) (h:RootBank n s) : RootBank n u := by
 intro i;rw [f.2.1];exact h i

theorem boot_header {n T A D E:ℕ} {s:State} (md:Metadata n s) (pc:s.pc=0)
 (a:s.natReg 5102=A) (d:s.natReg 5103=D) (e:s.natReg 5104=E) : Header n T A D E 0 (applyBlock (boot T) s) := by
 have cp:s.natReg 105=copyBase n:=md.saved.copyAddress
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,pc,a,d,e,cp,md.saved.count]
theorem boot_runs {n B:ℕ} (T:ℕ) (x:Fin n→ℂ) (s:State) (md:Metadata n s)
 (tb:T≤B) (pc:s.pc=0) (code:182≤B) (bound:WordBound B s) :
 BoundedRuns (program T) n x B s 8 (applyBlock (boot T) s) := by
 have cell:=UniformSelectedAxisFiberPreparation.crt_cell (⟨0,by omega⟩:Fin (ell n+1)) s md
 have ab:copyBase n+ell n≤B:=by have:=(bound.2.2.1 _ _ cell).1;simpa using this
 have cb:ell n+1≤B:=by
  change UniformGlobalNatPreparation.amount (ell n) (len n)+24*len n+9+ell n≤B at ab
  omega
 have cp:s.natReg 105=copyBase n:=md.saved.copyAddress
 exact block_runs (boot T) (program T) 0 n B x s (boot_code T) pc bound
  (by change 0+8≤B;omega) (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next,cp,md.saved.count]
      exact ⟨by omega,ab,cb,tb⟩)

theorem read_values {n T A D E i:ℕ} {s:State} (h:Header n T A D E i s)
 (hi:i<ell n+1) (md:Metadata n s) :
 (applyBlock read (setPC s 9)).natReg 5113=radices n ⟨i,hi⟩ := by
 have cell:=UniformSelectedAxisFiberPreparation.crt_cell (⟨i,hi⟩:Fin (ell n+1)) s md
 have norm:s.natHeap (copyBase n+ell n+i*4)=some (radices n ⟨i,hi⟩):=by simpa only [Nat.mul_comm] using cell
 simp [read,applyBlock,Op.apply,writeNat,next,setPC,h.index,h.four,h.table,norm]

theorem read_runs {n T A D E i B:ℕ} (x:Fin n→ℂ) (s:State) (h:Header n T A D E i s)
 (hi:i<ell n+1) (md:Metadata n s) (code:182≤B) (pc:s.pc=8) (bound:WordBound B s) :
 BoundedRuns (program T) n x B s 4 (applyBlock read (setPC s 9)) := by
 have cell:=UniformSelectedAxisFiberPreparation.crt_cell (⟨i,hi⟩:Fin (ell n+1)) s md
 have ab:copyBase n+ell n+i*4≤B:=by simpa only [Nat.mul_comm] using (bound.2.2.1 _ _ cell).1
 have rb:radices n ⟨i,hi⟩≤B:=(bound.2.2.1 _ _ cell).2
 have norm:s.natHeap (copyBase n+ell n+i*4)=some (radices n ⟨i,hi⟩):=by simpa only [Nat.mul_comm] using cell
 let e:=setPC s 9
 have eb:=changePC_bound B s 9 bound (by omega)
 have branch:BoundedRuns (program T) n x B s 1 e:=.next bound
  (by simp [step,pc,branch_code,h.index,h.count,hi,e,setPC]) (.refl eb)
 have block:=block_runs read (program T) 9 n B x e (read_code T) rfl eb
  (by change 9+3≤B;omega)
  (by simp [read,readable,Op.readable,Op.apply,writeNat,next,e,setPC,h.index,h.four,h.table,norm])
  (by simp [read,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.index,h.four,h.table,norm]
      omega)
 exact branch.trans block
theorem Header.keep {n T A D E i:ℕ} {s u:State} (h:Header n T A D E i s)
 (keep:∀q,5000≤q→u.natReg q=s.natReg q) : Header n T A D E i u := by
 constructor
 all_goals first |rfl|exact (keep _ (by omega)).trans (by first
  |exact h.array|exact h.gather|exact h.transformed|exact h.index|exact h.zero|exact h.one
  |exact h.four|exact h.rootBase|exact h.table|exact h.count|exact h.threshold)

theorem read_header {n T A D E i:ℕ} {s:State} (h:Header n T A D E i s) :
 Header n T A D E i (applyBlock read (setPC s 9)) := by
 constructor <;> simp [read,applyBlock,Op.apply,writeNat,next,setPC,h.array,h.gather,h.transformed,
  h.index,h.zero,h.one,h.four,h.rootBase,h.table,h.count,h.threshold]
theorem setup_header {n T A D E i:ℕ} {s:State} (h:Header n T A D E i s) :
 Header n T A D E i (applyBlock setup s) := by
 constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next]
 all_goals first |exact h.array|exact h.gather|exact h.transformed|exact h.index|exact h.zero|exact h.one|exact h.four|exact h.rootBase|exact h.table|exact h.count|exact h.threshold

def after (s:State) : State :=setPC (applyBlock post (setPC s 179)) 8
theorem after_frame (s:State) : Frame s (after s) :=
 (Frame.pc s 179).trans ((post_frame (setPC s 179)).trans (Frame.pc _ 8))
theorem after_header {n T A D E i:ℕ} {s:State} (h:Header n T A D E i s) :
 Header n T A D E (i+1) (after s) := by
 constructor <;> simp [after,post,applyBlock,Op.apply,writeNat,next,setPC]
 all_goals first |exact h.array|exact h.gather|exact h.transformed|exact h.zero|exact h.one|exact h.four|exact h.rootBase|exact h.table|exact h.count|exact h.threshold|skip
 rw [h.index,h.one]

theorem post_runs {n T A D E i B:ℕ} (x:Fin n→ℂ) (s:State)
 (h:Header n T A D E i s) (hi:i<ell n+1) (code:182≤B)
 (pc:s.pc=179) (bound:WordBound B s) :
 BoundedRuns (program T) n x B s 2 (after s) := by
 have ib:i+1≤B:=by have hb:=bound.2.1 5112;rw [h.count] at hb;omega
 have block:=block_runs post (program T) 179 n B x s (post_code T) pc bound
  (by change 179+1≤B;omega) (by simp [post,readable,Op.readable])
  (by simp [post,peak,Op.peak];rw [h.index,h.one];exact ib)
 have zp:(applyBlock post s).pc=180:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have eq:setPC s 179=s:=by unfold setPC;rw [←pc]
 have ae:after s=setPC (applyBlock post s) 8:=by unfold after;rw [eq]
 have jump:BoundedRuns (program T) n x B (applyBlock post s) 1 (after s):=by
  rw [ae]
  exact .next block.final_bound
   (by simp only [step,zp,jump_code,setPC])
   (.refl (changePC_bound B (applyBlock post s) 8 block.final_bound (by omega)))
 exact block.trans jump

def Values {n:ℕ} (A:ℕ) (X:Fin (len n)→ℂ) (s:State) : Prop :=
 ∀z,∃v,s.scalarHeap (A+z.val)=some v ∧v.value=X z

def axisTransform {n:ℕ} (i:Fin (ell n+1)) (X:Fin (len n)→ℂ) (z:Fin (len n)) : ℂ :=
 let p:Fin (UniformAllTensorFibersCopyMachine.fibers n i)×Fin (radices n i):=
  (UniformAllTensorFibersCopyMachine.nativeEquiv n i).symm z
 ∑t:Fin (radices n i),OAI.ExactFourier.zeta (radices n i)^(p.2.val*t.val)*
  X (UniformAllTensorFibersCopyMachine.nativeEquiv n i (p.1,t))

theorem Values.frame {n A:ℕ} {X:Fin (len n)→ℂ} {s u:State} (f:Frame s u)
 (h:Values A X s) : Values A X u := by intro z;rw [f.2.1];exact h z

theorem setup_args {n T A D E i:ℕ} {s:State} (h:Header n T A D E i s) :
 UniformSmallAxisFourierMachine.Args i A D E (6+i) (applyBlock setup s) := by
 constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h.array,h.gather,h.transformed,h.index,h.zero,h.rootBase]

theorem setup_runs {n T A D E i B:ℕ} (x:Fin n→ℂ) (s:State)
 (h:Header n T A D E i s) (hi:i<ell n+1) (roots:RootBank n s)
 (code:182≤B) (pc:s.pc=13) (bound:WordBound B s) :
 BoundedRuns (program T) n x B s 5 (applyBlock setup s) := by
 have rootB:6+i≤B:=bound.2.2.2.1 _ _ (roots ⟨i,hi⟩)
 exact block_runs setup (program T) 13 n B x s (setup_code T) pc bound
  (by change 13+5≤B;omega) (by simp [setup,readable,Op.readable])
  (by simp [setup,peak,Op.peak,Op.apply,writeNat,next,h.index,h.zero,h.rootBase]
      exact ⟨bound.2.1 5102,bound.2.1 5103,bound.2.1 5104,rootB⟩)

theorem child_values {n B T A D E i:ℕ} (hn:0<n) (hi:i<ell n+1) (x:Fin n→ℂ)
 (s:State) (metadata:Metadata n s) (h:Header n T A D E i s)
 (args:UniformSmallAxisFourierMachine.Args i A D E (6+i) s)
 (roots:RootBank n s) (X:Fin (len n)→ℂ) (values:Values A X s)
 (rootBefore:6+ell n<A) (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B)
 (code:182≤B) (pc:s.pc=18) (bound:WordBound B s) : ∃u,
 BoundedRuns (program T) n x B s (UniformSmallAxisFourierMachine.runtime n ⟨i,hi⟩) u ∧
 u.pc=179 ∧Metadata n u ∧Header n T A D E i u ∧RootBank n u ∧
 Values A (axisTransform ⟨i,hi⟩ X) u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 let v:Fin (len n)→Scalar:=fun z=>Classical.choose (values z)
 have src:∀z,s.scalarHeap (A+z.val)=some (v z):=by intro z;exact (Classical.choose_spec (values z)).1
 have val:∀z,(v z).value=X z:=by intro z;exact (Classical.choose_spec (values z)).2
 let e:=setPC s 0
 have ep:=UniformAllTensorFibersCopyMachine.Frame.pc s 0
 have ea:UniformSmallAxisFourierMachine.Args i A D E (6+i) e:=
  ⟨args.axis,args.array,args.gather,args.transformed,args.root⟩
 obtain ⟨u,run,answer,md,nh,out,orders,outside⟩:=UniformSmallAxisFourierPreservation.execution hn ⟨i,hi⟩
  A D E (6+i) x e (ep.metadata metadata) ea (OAI.ExactFourier.zeta (radices n ⟨i,hi⟩)) v src (roots ⟨i,hi⟩)
  (Or.inl (by omega)) (Or.inl (by omega)) sepAD sepDE aBound eBound (by omega) rfl
  (changePC_bound B s 0 bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (child_code T)
  (by rw [UniformSmallAxisFourierMachine.program_length];omega) (by omega :179≤B) run
 have entry:UniformAssembly.placed 18 e=s:=by change setPC s 18=s;unfold setPC;rw [←pc]
 rw [entry] at moved
 have natKeep:∀q,5000≤q→(setPC u 179).natReg q=s.natReg q:=by
  intro q hq
  have keep:u.natReg q=e.natReg q:=UniformSmallAxisFourierPreservation.execution_nat run hq
  exact keep
 have finalMD:Metadata n (setPC u 179):=(UniformAllTensorFibersCopyMachine.Frame.pc u 179).metadata md
 refine ⟨setPC u 179,?_,rfl,finalMD,h.keep natKeep,?_,?_,nh,out,orders⟩
 · simpa only [UniformSmallAxisFourierMachine.runtime,setPC] using moved
 · intro j
   change u.scalarHeap (6+j.val)=some (prepared (OAI.ExactFourier.zeta (radices n j)))
   rw [outside (6+j.val) (Or.inl (by have:=j.isLt;omega))
    (Or.inl (by have:=j.isLt;omega)) (Or.inl (by have:=j.isLt;omega))]
   exact roots j
 · intro z
   let p:Fin (UniformAllTensorFibersCopyMachine.fibers n ⟨i,hi⟩)×Fin (radices n ⟨i,hi⟩):=
    (UniformAllTensorFibersCopyMachine.nativeEquiv n ⟨i,hi⟩).symm z
   have pe:UniformAllTensorFibersCopyMachine.nativeEquiv n ⟨i,hi⟩ p=z:=
    (UniformAllTensorFibersCopyMachine.nativeEquiv n ⟨i,hi⟩).apply_symm_apply z
   have pv:=congrArg Fin.val pe
   rw [UniformAllTensorFibersCopyMachine.nativeEquiv_val] at pv
   obtain ⟨a,ha,hv⟩:=answer p.1 p.2
   refine ⟨a,?_,?_⟩
   · change u.scalarHeap (A+z.val)=some a
     rw [←pv];exact ha
   · simpa only [axisTransform,p,val] using hv

def axisAt (n i:ℕ) : Fin (ell n+1) :=⟨i % (ell n+1),Nat.mod_lt _ (by omega)⟩
theorem axisAt_eq {n i:ℕ} (hi:i<ell n+1) : axisAt n i=⟨i,hi⟩ := by
 apply Fin.ext;exact Nat.mod_eq_of_lt hi

def oneValue {n:ℕ} (T i:ℕ) (X:Fin (len n)→ℂ) : Fin (len n)→ℂ :=
 if radices n (axisAt n i)<T then axisTransform (axisAt n i) X else X

def oneCost (n T i:ℕ) : ℕ :=7+if radices n (axisAt n i)<T then
 5+UniformSmallAxisFourierMachine.runtime n (axisAt n i) else 0

theorem iteration {n B T A D E i:ℕ} (hn:0<n) (hi:i<ell n+1) (x:Fin n→ℂ)
 (s:State) (md:Metadata n s) (h:Header n T A D E i s)
 (roots:RootBank n s) (X:Fin (len n)→ℂ) (values:Values A X s)
 (rootBefore:6+ell n<A) (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B)
 (code:182≤B) (pc:s.pc=8) (bound:WordBound B s) : ∃u,
 BoundedRuns (program T) n x B s (oneCost n T i) u ∧
 u.pc=8 ∧Metadata n u ∧Header n T A D E (i+1) u ∧RootBank n u ∧
 Values A (oneValue T i X) u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 let v:=applyBlock read (setPC s 9)
 have fr:Frame s v:=(Frame.pc s 9).trans (read_frame (setPC s 9))
 have first:=read_runs x s h hi md code pc bound
 have vh:Header n T A D E i v:=read_header h
 have vm:Metadata n v:=fr.metadata md
 have vr:RootBank n v:=fr.roots roots
 have vv:Values A X v:=values.frame fr
 have vp:v.pc=12:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have radix:v.natReg 5113=radices n ⟨i,hi⟩:=read_values h hi md
 by_cases small:radices n ⟨i,hi⟩<T
 · let w:=setPC v 13
   have wb:=changePC_bound B v 13 first.final_bound (by omega)
   have branch:BoundedRuns (program T) n x B v 1 w:=.next first.final_bound
    (by simp [step,vp,active_code,radix,vh.threshold,small,w,setPC]) (.refl wb)
   have wh:Header n T A D E i w:=vh.keep (by intros;rfl)
   have wf:=Frame.pc v 13
   have setupRun:=setup_runs x w wh hi (wf.roots vr) code rfl wb
   let e:=applyBlock setup w
   have ef:=setup_frame w
   have eh:Header n T A D E i e:=setup_header wh
   have ep:e.pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
   obtain ⟨u,run,up,um,uh,ur,uv,un,uo,ut⟩:=child_values hn hi x e
    (ef.metadata (wf.metadata vm)) eh (setup_args wh) (ef.roots (wf.roots vr)) X
    ((vv.frame wf).frame ef) rootBefore sepAD sepDE aBound eBound code ep setupRun.final_bound
   have last:=post_runs x u uh hi code up run.final_bound
   have pf:=after_frame u
   refine ⟨after u,?_,rfl,pf.metadata um,after_header uh,pf.roots ur,?_,?_,?_,?_⟩
   · convert ((first.trans branch).trans setupRun).trans (run.trans last) using 1
     simp only [oneCost,axisAt_eq hi,small,ite_true]
     omega
   · simpa only [oneValue,axisAt_eq hi,small,ite_true] using uv.frame pf
   · exact pf.1.trans (un.trans (ef.1.trans (wf.1.trans fr.1)))
   · exact pf.2.2.2.1.trans (uo.trans (ef.2.2.2.1.trans (wf.2.2.2.1.trans fr.2.2.2.1)))
   · exact pf.2.2.2.2.1.trans (ut.trans (ef.2.2.2.2.1.trans (wf.2.2.2.2.1.trans fr.2.2.2.2.1)))
 · let w:=setPC v 179
   have wb:=changePC_bound B v 179 first.final_bound (by omega)
   have branch:BoundedRuns (program T) n x B v 1 w:=.next first.final_bound
    (by simp [step,vp,active_code,radix,vh.threshold,small,w,setPC]) (.refl wb)
   have wh:Header n T A D E i w:=vh.keep (by intros;rfl)
   have wf:=Frame.pc v 179
   have last:=post_runs x w wh hi code rfl wb
   have pf:Frame s (after w):=fr.trans (wf.trans (after_frame w))
   refine ⟨after w,?_,rfl,pf.metadata md,after_header wh,pf.roots roots,?_,pf.1,pf.2.2.2.1,pf.2.2.2.2.1⟩
   · convert (first.trans branch).trans last using 1
     simp only [oneCost,axisAt_eq hi,small,ite_false,Nat.add_zero]
   · simpa only [oneValue,axisAt_eq hi,small,ite_false] using values.frame pf

def axisPrefix {n:ℕ} (T:ℕ) (X:Fin (len n)→ℂ) : ℕ→(Fin (len n)→ℂ)
 | 0 =>X
 | i+1 =>oneValue T i (axisPrefix T X i)

def remainingCost (n T i:ℕ) : ℕ→ℕ
 | 0 =>2
 | r+1 =>oneCost n T i+remainingCost n T (i+1) r

theorem loop_execution {n B T A D E:ℕ} (hn:0<n) (x:Fin n→ℂ)
 (rootBefore:6+ell n<A) (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B) (code:182≤B)
 (X:Fin (len n)→ℂ) (remaining:ℕ) : ∀i s,i+remaining=ell n+1→
 Metadata n s→Header n T A D E i s→RootBank n s→Values A (axisPrefix T X i) s→
 s.pc=8→WordBound B s→∃u,
 BoundedExecution (program T) n x B s (remainingCost n T i remaining) u ∧
 u.pc=181 ∧Metadata n u ∧Header n T A D E (ell n+1) u ∧RootBank n u ∧
 Values A (axisPrefix T X (ell n+1)) u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 induction remaining with
 |zero=>
  intro i s eq md h roots values pc bound
  have ie:i=ell n+1:=by omega
  let u:=setPC s 181
  have ub:=changePC_bound B s 181 bound (by omega)
  have pf:=Frame.pc s 181
  refine ⟨u,?_,rfl,pf.metadata md,?_,pf.roots roots,?_,rfl,rfl,rfl⟩
  · exact .next bound
     (by simp [step,pc,branch_code,h.index,h.count,ie,u,setPC])
     (.halt ub (by simp [step,halt_code,u,setPC]))
  · rw [←ie];exact h.keep (by intros;rfl)
  · rw [←ie];exact values.frame pf
 |succ remaining ih=>
  intro i s eq md h roots values pc bound
  obtain ⟨v,first,vp,vm,vh,vr,vv,vn,vo,vt⟩:=iteration hn (by omega) x s md h roots
   (axisPrefix T X i) values rootBefore sepAD sepDE aBound eBound code pc bound
  obtain ⟨u,last,up,um,uh,ur,uv,un,uo,ut⟩:=ih (i+1) v (by omega) vm vh vr vv vp first.final_bound
  refine ⟨u,first.executes last,up,um,uh,ur,uv,un.trans vn,uo.trans vo,ut.trans vt⟩

def runtime (n T:ℕ) : ℕ :=8+remainingCost n T 0 (ell n+1)

/-- The182-instruction outer program visits every real CRT axis and executes
its actual161 Fourier child exactly when the physically read radix is small. -/
theorem execution {n B T A D E:ℕ} (hn:0<n) (x:Fin n→ℂ) (s:State)
 (md:Metadata n s) (roots:RootBank n s) (X:Fin (len n)→ℂ) (values:Values A X s)
 (rootBefore:6+ell n<A) (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B) (code:182≤B) (tb:T≤B)
 (pc:s.pc=0) (a:s.natReg 5102=A) (d:s.natReg 5103=D) (e:s.natReg 5104=E)
 (bound:WordBound B s) : ∃u,
 BoundedExecution (program T) n x B s (runtime n T) u ∧
 u.pc=181 ∧Metadata n u ∧Header n T A D E (ell n+1) u ∧RootBank n u ∧
 Values A (axisPrefix T X (ell n+1)) u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 let v:=applyBlock (boot T) s
 have first:=boot_runs T x s md tb pc code bound
 have bf:=boot_frame T s
 have vp:v.pc=8:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 obtain ⟨u,last,up,um,uh,ur,uv,un,uo,ut⟩:=loop_execution hn x rootBefore sepAD sepDE
  aBound eBound code X (ell n+1) 0 v (by omega) (bf.metadata md) (boot_header md pc a d e)
  (bf.roots roots) (values.frame bf) vp first.final_bound
 exact ⟨u,first.executes last,up,um,uh,ur,uv,un.trans bf.1,uo.trans bf.2.2.2.1,ut.trans bf.2.2.2.2.1⟩

open scoped BigOperators

theorem remainingCost_sum (n T remaining:ℕ) : ∀i,
 remainingCost n T i remaining=2+∑j∈Finset.range remaining,oneCost n T (i+j) := by
 induction remaining with
 |zero=>intro i;simp [remainingCost]
 |succ r ih=>
  intro i
  rw [remainingCost,ih,Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have eq:(∑j∈Finset.range r,oneCost n T (i+(j+1)))=
   ∑j∈Finset.range r,oneCost n T (i+1+j):=by
   apply Finset.sum_congr rfl;intro j _;congr 1;omega
  rw [eq];omega

theorem runtime_sum (n T:ℕ) : runtime n T=10+∑i:Fin (ell n+1),oneCost n T i.val := by
 rw [runtime,remainingCost_sum]
 simp only [Nat.zero_add,Finset.sum_range]
 omega

theorem runtime_bound (n T:ℕ) :
 runtime n T≤10+7*(ell n+1)+(T+1)*((8*T+96)*len n+14*ell n+55) := by
 rw [runtime_sum]
 have sumEq:(∑i:Fin (ell n+1),oneCost n T i.val)=7*(ell n+1)+
   ∑i∈UniformSmallAxesBudget.small n T,(5+UniformSmallAxisFourierMachine.runtime n i):=by
  have axes:∀i:Fin (ell n+1),axisAt n i.val=i:=by intro i;exact axisAt_eq i.isLt
  have active:(∑i:Fin (ell n+1),if radices n i<T then
   5+UniformSmallAxisFourierMachine.runtime n i else 0)=
   ∑i∈UniformSmallAxesBudget.small n T,(5+UniformSmallAxisFourierMachine.runtime n i):=by
   rw [UniformSmallAxesBudget.small,Finset.sum_filter]
  simp only [oneCost,axes]
  rw [Finset.sum_add_distrib,active]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring
 rw [sumEq]
 have smallCost:=UniformSmallAxesBudget.actual_small_axes_cost n T
 have card:=UniformSmallAxesBudget.small_card n T
 have five:5*(UniformSmallAxesBudget.small n T).card≤5*(T+1):=Nat.mul_le_mul_left 5 card
 simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at ⊢
 nlinarith

theorem RootBank.fromOperands {n:ℕ} (x:Fin n→ℂ) {s:State}
 (ops:UniformInitialPreparation.Operands n x s) : RootBank n s := ops.roots

end
end ExactFourierCircuits.UniformSmallAxesMachine
