import UniformDFSProgram
import UniformPermutationInversePreparation
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSelectedDFSMachine
open UniformMachine UniformAssembly
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
open UniformInitialPreparation (ell len copyBase protectedView)

/-- Copy the protected CRT radix field with literal strided loads, then enter
    the frozen DFS. Low Nat heap is scratch; protected metadata is above it. -/
def setup : List Op := [.literal 61 0,.literal 62 1,.literal 63 4,
  .add 60 102 62,.add 64 105 102]
def headers : List Op := [.literal 0 0,.add 1 60 0,.literal 2 0,.literal 5 0,
  .add 6 60 0,.literal 66 3,.mul 7 60 66,.literal 8 0,.literal 9 1,
  .literal 10 2,.literal 13 0]
def head : Program := setup.map Op.code ++ [
  .branchLT 61 60 6 11,.loadNat 65 64,.storeNat 61 65,
  .natBinary .add 61 61 62,.natBinary .add 64 64 63,.jump 5] ++ headers.map Op.code
def program : Program := embed head UniformDFSProgram.program [.halt] 52

theorem setup_length : setup.length=5 := rfl
theorem headers_length : headers.length=11 := rfl
theorem head_length : head.length=22 := rfl
theorem program_length : program.length=53 := rfl
theorem setup_code : BlockAt setup program 0 := by
  intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem headers_code : BlockAt headers program 11 := by
  intro i hi;change i<11 at hi;interval_cases i <;> rfl
theorem dfs_code : CodeAt UniformDFSProgram.program program 22 52 := by
  simpa only [program,head_length] using embed_code head UniformDFSProgram.program [.halt] 52
theorem halt_at : program[52]?=some .halt := rfl

def selectedRadices (n : ℕ) : List ℕ := List.ofFn (UniformSelectedCRT.radices n)
theorem selectedRadices_length (n : ℕ) : (selectedRadices n).length=ell n+1 := by
  simp [selectedRadices]
theorem selectedRadices_product (n : ℕ) : (selectedRadices n).prod=len n := by
  rw [selectedRadices,List.prod_ofFn,UniformSelectedCRT.radices_product]
theorem selectedRadices_positive (n : ℕ) : UniformDFSProgram.Positive (selectedRadices n) := by
  intro r hr
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp hr
  subst r
  exact UniformSelectedCRT.radix_pos n i

/-- One positive, possibly unit, radix is retained after the prime axes. -/
theorem nodeCount_append_one (rs : List ℕ) (b : ℕ) (hb:0<b)
    (hr:∀r∈rs,2≤r) : UniformTraversal.nodeCount (rs++[b])+1≤3*(rs.prod*b) := by
  induction rs with
  | nil => simp [UniformTraversal.nodeCount];omega
  | cons r rs ih =>
    have htwo:2≤r:=hr r (by simp)
    have ht:=ih (by intro q hq;exact hr q (by simp [hq]))
    simp only [List.cons_append,List.prod_cons,UniformTraversal.nodeCount]
    calc
      1+r*UniformTraversal.nodeCount (rs++[b])+1
          ≤r*(UniformTraversal.nodeCount (rs++[b])+1) := by nlinarith
      _≤r*(3*(rs.prod*b)):=Nat.mul_le_mul_left r ht
      _=3*(r*rs.prod*b):=by ring

theorem selectedRadices_nodes (n : ℕ) : UniformTraversal.nodeCount (selectedRadices n)≤3*len n := by
  have he:selectedRadices n=List.ofFn (fun i:Fin (ell n)=>UniformWorkingLength.oddPrime i.val) ++
      [UniformWorkingLength.binaryFactor n] := by
    rw [selectedRadices,List.ofFn_succ']
    simp [UniformSelectedCRT.radices,List.concat_eq_append]
  have ht:=nodeCount_append_one (List.ofFn (fun i:Fin (ell n)=>UniformWorkingLength.oddPrime i.val))
    (UniformWorkingLength.binaryFactor n) (by simp [UniformWorkingLength.binaryFactor]) (by
      intro r hr
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hr
      subst r
      have hp:=UniformWorkingLength.oddPrime_lower i.val
      omega)
  have heprod:(List.ofFn (fun i:Fin (ell n)=>UniformWorkingLength.oddPrime i.val)).prod*
      UniformWorkingLength.binaryFactor n=len n:=by
    have hp:=selectedRadices_product n
    rw [he] at hp
    simpa using hp
  rw [←he,heprod] at ht
  omega

noncomputable section

/-- The original DFS's ambient theorem, with no smaller initial bound. -/
theorem dfs_ambient (rs : List ℕ) (n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hh:UniformDFSProgram.headers rs.length s)
    (hd:s.natReg 0=0) (hA:s.natReg 2=0) (hc:s.natReg 8=0)
    (ht:UniformDFSProgram.radicesAt rs 0 s) (hp:UniformDFSProgram.Positive rs)
    (hB:30+3*rs.length+rs.prod≤B) (hs:WordBound B s) :
    BoundedExecution UniformDFSProgram.program n x B s (UniformDFSProgram.treeCost rs+2)
      (UniformDFSProgram.setPC (UniformDFSProgram.tree rs s) 29) := by
  have h:=UniformDFSProgram.tree_bounded rs n x rs.length 0 0 0 rs.prod B s
    hpc hh hd hA hc (by omega) ht hp (by simp) (by simp) hB hs
  obtain ⟨_,e⟩:=UniformDFSProgram.tree_spec rs n x rs.length 0 0 0 s
    hpc hh hd hA hc (by omega) ht
  exact h.finish (UniformDFSProgram.halt_bounded n x B _ (by omega) h.final_bound
    e.pc e.header.2.2.2.2 e.depth)

/-- All high Nat registers are untouched by the actual DFS state recursion. -/
theorem dfs_children_nat (v : State→State) (hv:∀s r,14≤r→(v s).natReg r=s.natReg r)
    (k : ℕ) (s : State) (r : ℕ) (hr:14≤r) :
    (UniformDFSProgram.children v k s).natReg r=s.natReg r := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [UniformDFSProgram.children,ih]
    simp (disch:=omega) [UniformDFSProgram.pop,UniformDFSProgram.pop1,UniformDFSProgram.pop2,
      UniformDFSProgram.pop3,UniformDFSProgram.pop4,UniformDFSProgram.pop5,
      UniformDFSProgram.pop6,UniformDFSProgram.pop7,UniformDFSProgram.pop8,
      UniformDFSProgram.setPC,writeNat,next,hv _ r hr,UniformDFSProgram.child,
      UniformDFSProgram.child1,UniformDFSProgram.child2,UniformDFSProgram.child3,
      UniformDFSProgram.child4,UniformDFSProgram.child5,UniformDFSProgram.child6,
      UniformDFSProgram.child7,UniformDFSProgram.child8,UniformDFSProgram.child9,
      UniformDFSProgram.store]

theorem dfs_tree_nat (rs : List ℕ) (s : State) (r : ℕ) (hr:14≤r) :
    (UniformDFSProgram.tree rs s).natReg r=s.natReg r := by
  induction rs generalizing s r with
  | nil =>
    simp (disch:=omega) [UniformDFSProgram.tree,UniformDFSProgram.emit,UniformDFSProgram.emit1,
      UniformDFSProgram.emit2,UniformDFSProgram.emit3,UniformDFSProgram.store,
      UniformDFSProgram.setPC,writeNat,next]
  | cons q qs ih =>
    rw [UniformDFSProgram.tree,dfs_children_nat _ (fun s r hr=>ih s r hr) q _ r hr]
    simp (disch:=omega) [UniformDFSProgram.enter,UniformDFSProgram.setPC,writeNat,next]

/-- Heap frame strengthened beyond the DFS's low-prefix and old-output frames. -/
def HighTree (rs : List ℕ) : Prop :=
  ∀(n : ℕ)(_x : Fin n→ℂ)(ell d A c R : ℕ)(s : State),
  s.pc=0→UniformDFSProgram.headers ell s→s.natReg 0=d→s.natReg 2=A→s.natReg 8=c→
  d+rs.length=ell→UniformDFSProgram.radicesAt rs d s→c+rs.prod≤R→
  ∀a,3*ell+R≤a→(UniformDFSProgram.tree rs s).natHeap a=s.natHeap a

theorem dfs_children_high (rs : List ℕ) (hv:HighTree rs)
    (n : ℕ) (x : Fin n→ℂ) (ell d A c r i k R : ℕ) (s : State)
    (hpc:s.pc=4) (hh:UniformDFSProgram.headers ell s) (hd:s.natReg 0=d)
    (hA:s.natReg 2=A) (hc:s.natReg 8=c) (hi:s.natReg 3=i) (hr:s.natReg 4=r)
    (hdl:d+(r::rs).length=ell) (hik:i+k=r)
    (ht:UniformDFSProgram.radicesAt (r::rs) d s) (hb:c+k*rs.prod≤R) :
    ∀a,3*ell+R≤a→(UniformDFSProgram.children (UniformDFSProgram.tree rs) k s).natHeap a=s.natHeap a := by
  have hlen:d+(rs.length+1)=ell:=by simpa using hdl
  induction k generalizing s c i with
  | zero => intro a _;rfl
  | succ k ih =>
    have hde:d<ell:=by simp only [List.length_cons] at hdl;omega
    have cp:=UniformDFSProgram.child_properties ell s hh
    have cd:(UniformDFSProgram.child s).natReg 0=d+1:=by rw [cp.2.2.1,hd]
    have ca:(UniformDFSProgram.child s).natReg 2=A*r+i:=by rw [cp.2.2.2.1,hA,hr,hi]
    have cc:(UniformDFSProgram.child s).natReg 8=c:=cp.2.2.2.2.1.trans hc
    have ct:UniformDFSProgram.radicesAt rs (d+1) (UniformDFSProgram.child s):=by
      intro j
      have hj:=j.isLt
      have htab:=ht ⟨j.val+1,by simp only [List.length_cons];omega⟩
      rw [show d+1+j.val=d+(j.val+1) by omega,
        UniformDFSProgram.child_low ell d s hh hd _ (by omega)]
      simpa [List.get_eq_getElem] using htab
    obtain ⟨_,e⟩:=UniformDFSProgram.tree_spec rs n x ell (d+1) (A*r+i) c
      (UniformDFSProgram.child s) cp.1 cp.2.1 cd ca cc
      (by simp only [List.length_cons] at hdl;omega) ct
    have table:UniformDFSProgram.radicesAt (r::rs) d
        (UniformDFSProgram.tree rs (UniformDFSProgram.child s)):=by
      intro j
      rw [e.low _ (by omega),UniformDFSProgram.child_low ell d s hh hd _ (by omega)]
      exact ht j
    let t:=UniformDFSProgram.pop (UniformDFSProgram.tree rs (UniformDFSProgram.child s)) A (i+1) r
    have pp:=UniformDFSProgram.pop_properties ell
      (UniformDFSProgram.tree rs (UniformDFSProgram.child s)) A (i+1) r e.header
    have td:t.natReg 0=d:=by simpa [t,e.depth] using pp.2.2.1
    have tc:t.natReg 8=c+rs.prod:=pp.2.2.2.2.2.2.1.trans e.count
    have tt:UniformDFSProgram.radicesAt (r::rs) d t:=by
      intro j
      rw [show t.natHeap=(UniformDFSProgram.tree rs (UniformDFSProgram.child s)).natHeap from pp.2.2.2.2.2.2.2]
      exact table j
    have hc2:c+rs.prod+k*rs.prod≤R:=by
      simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
    have hc1:c+rs.prod≤R:=by omega
    have rest:=ih (c+rs.prod) (i+1) t pp.1 pp.2.1 td pp.2.2.2.1 tc
      pp.2.2.2.2.1 pp.2.2.2.2.2.1 (by omega) tt hc2
    intro a ha
    have heq:UniformDFSProgram.children (UniformDFSProgram.tree rs) (k+1) s=
      UniformDFSProgram.children (UniformDFSProgram.tree rs) k t:=by
      simp only [UniformDFSProgram.children,t,hA,hi,hr]
    rw [heq,rest a ha,
      show t.natHeap=(UniformDFSProgram.tree rs (UniformDFSProgram.child s)).natHeap from pp.2.2.2.2.2.2.2,
      hv n x ell (d+1) (A*r+i) c R (UniformDFSProgram.child s) cp.1 cp.2.1 cd ca cc
        (by simp only [List.length_cons] at hdl;omega) ct hc1 a ha,
      cp.2.2.2.2.2,hd]
    simp [Function.update_of_ne (show a≠ell+d*2+1 by omega),
      Function.update_of_ne (show a≠ell+d*2 by omega)]

theorem dfs_tree_high (rs : List ℕ) : HighTree rs := by
  induction rs with
  | nil =>
    intro n x ell d A c R s hpc hh hd hA hc hdl ht hb a ha
    simp only [List.prod_nil] at hb
    simp [UniformDFSProgram.tree,UniformDFSProgram.emit,UniformDFSProgram.emit1,
      UniformDFSProgram.emit2,UniformDFSProgram.emit3,UniformDFSProgram.store,
      UniformDFSProgram.setPC,writeNat,next,hh.2.2.2.1,hc,
      Function.update_of_ne (show a≠3*ell+c by omega)]
  | cons r rs ih =>
    intro n x ell d A c R s hpc hh hd hA hc hdl ht hb a ha
    have ep:=UniformDFSProgram.enter_properties ell s r hh
    have table:UniformDFSProgram.radicesAt (r::rs) d (UniformDFSProgram.enter s r):=by
      intro j;rw [ep.2.2.2.2.2.2.2];exact ht j
    exact (dfs_children_high rs ih n x ell d A c r 0 r R (UniformDFSProgram.enter s r)
      ep.1 ep.2.1 (ep.2.2.1.trans hd) (ep.2.2.2.1.trans hA)
      (ep.2.2.2.2.2.2.1.trans hc) ep.2.2.2.2.1 ep.2.2.2.2.2.1 hdl
      (by omega) table (by simpa using hb) a ha).trans (congrFun ep.2.2.2.2.2.2.2 a)

def Frame (s u : State) : Prop := UniformNatCopyMachine.Frame s u
def NatFrame (s u : State) : Prop := ∀r,100≤r→u.natReg r=s.natReg r

structure CopyInvariant (m a k : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop where
  length : s.natReg 60=m
  index : s.natReg 61=k
  one : s.natReg 62=1
  stride : s.natReg 63=4
  pointer : s.natReg 64=a+4*k
  copied : ∀j,j<k→s.natHeap j=heap (a+4*j)
  outside : ∀j,m≤j→s.natHeap j=heap j

theorem CopyInvariant.withPC {m a k pc : ℕ} {heap : ℕ→Option ℕ} {s : State}
    (h:CopyInvariant m a k heap s) : CopyInvariant m a k heap {s with pc:=pc} := by
  cases h;constructor <;> assumption

def loaded (s : State) (v : ℕ) : State := writeNat {s with pc:=6} 65 v
def stored (s : State) (v : ℕ) : State :=
  {next (loaded s v) with natHeap:=Function.update s.natHeap (s.natReg 61) (some v)}
def advanced (s : State) (v : ℕ) : State := writeNat (stored s v) 61 (s.natReg 61+1)
def advancedPointer (s : State) (v : ℕ) : State := writeNat (advanced s v) 64 (s.natReg 64+4)
def iterationEnd (s : State) (v : ℕ) : State := {advancedPointer s v with pc:=5}

theorem iteration_frame (s : State) (v : ℕ) : Frame s (iterationEnd s v) := ⟨rfl,rfl,rfl,rfl⟩
theorem iteration_nat (s : State) (v : ℕ) : NatFrame s (iterationEnd s v) := by
  intro r hr
  simp (disch:=omega) [iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next]

theorem iteration_invariant (m a k : ℕ) (heap : ℕ→Option ℕ) (s : State) (v : ℕ)
    (hi:CopyInvariant m a k heap s) (hk:k< m) (hv:heap (a+4*k)=some v) :
    CopyInvariant m a (k+1) heap (iterationEnd s v) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next] using hi.length
  · simp [iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next,hi.index]
  · simpa [iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next] using hi.one
  · simpa [iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next] using hi.stride
  · simp [iterationEnd,advancedPointer,writeNat,next,hi.pointer,
      Nat.mul_add,Nat.add_comm,Nat.add_left_comm]
  · intro j hj
    change Function.update s.natHeap (s.natReg 61) (some v) j=heap (a+4*j)
    rw [hi.index]
    by_cases he:j=k
    · subst j;simp [hv]
    · rw [Function.update_of_ne he];exact hi.copied j (by omega)
  · intro j hj
    change Function.update s.natHeap (s.natReg 61) (some v) j=heap j
    rw [hi.index,Function.update_of_ne (by omega)];exact hi.outside j hj

theorem iteration (n : ℕ) (x : Fin n→ℂ) (m a k B : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (hi:CopyInvariant m a k heap s)
    (hsrc:∀j,j< m→∃v,heap (a+4*j)=some v)
    (hk:k< m) (hd:m≤a) (hB:a+4*m≤B) (hcode:53≤B)
    (hpc:s.pc=5) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 6 u ∧ CopyInvariant m a (k+1) heap u ∧
    u.pc=5 ∧ Frame s u ∧ NatFrame s u := by
  obtain ⟨v,hv⟩:=hsrc k hk
  have hload:s.natHeap (a+4*k)=some v:=(hi.outside _ (by omega)).trans hv
  have hvB:v≤B:=(hs.2.2.1 _ _ hload).2
  have he:WordBound B {s with pc:=6}:=changePC_bound B s 6 hs (by omega)
  have h1:WordBound B (loaded s v):=writeNat_bound B _ _ _ he (by change 6+1≤B;omega) hvB
  have h2:WordBound B (stored s v):=UniformNatCopyMachine.store_bound B _ _ _ h1
    (by change 7+1≤B;omega) (by rw [hi.index];omega) hvB
  have h3:WordBound B (advanced s v):=writeNat_bound B _ _ _ h2
    (by change 8+1≤B;omega) (by rw [hi.index];omega)
  have h4:WordBound B (advancedPointer s v):=writeNat_bound B _ _ _ h3
    (by change 9+1≤B;omega) (by rw [hi.pointer];omega)
  have h5:WordBound B (iterationEnd s v):=changePC_bound B _ 5 h4 (by omega)
  have t0:step program n x s=.running {s with pc:=6}:=by
    simp [step,program,embed,head,setup,Op.code,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=6}=.running (loaded s v):=by
    simp [step,program,embed,head,setup,Op.code,loaded,hi.pointer,hload]
  have t2:step program n x (loaded s v)=.running (stored s v):=by
    simp [step,program,embed,head,setup,Op.code,stored,loaded,writeNat,next]
  have t3:step program n x (stored s v)=.running (advanced s v):=by
    simp [step,program,embed,head,setup,Op.code,advanced,stored,loaded,writeNat,next,hi.one,evalNat]
  have t4:step program n x (advanced s v)=.running (advancedPointer s v):=by
    simp [step,program,embed,head,setup,Op.code,advancedPointer,advanced,stored,loaded,
      writeNat,next,hi.stride,evalNat]
  have t5:step program n x (advancedPointer s v)=.running (iterationEnd s v):=by
    simp [step,program,embed,head,setup,Op.code,iterationEnd,advancedPointer,advanced,stored,loaded,writeNat,next]
  exact ⟨iterationEnd s v,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.refl h5)))))),iteration_invariant m a k heap s v hi hk hv,
    rfl,iteration_frame s v,iteration_nat s v⟩

theorem copy_loop (n : ℕ) (x : Fin n→ℂ) (m a k fuel B : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (hi:CopyInvariant m a k heap s)
    (hsrc:∀j,j< m→∃v,heap (a+4*j)=some v)
    (hk:k+fuel=m) (hd:m≤a) (hB:a+4*m≤B) (hcode:53≤B)
    (hpc:s.pc=5) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (6*fuel) u ∧ CopyInvariant m a m heap u ∧
    u.pc=5 ∧ Frame s u ∧ NatFrame s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k;exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,rfl⟩,fun _ _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=iteration n x m a k B heap s hi hsrc (by omega)
      hd hB hcode hpc hs
    obtain ⟨w,hw,hiw,hpw,hfw,hnw⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hiw,hpw,hfu.trans hfw,fun r hr=>(hnw r hr).trans (hnu r hr)⟩
    convert hu.trans hw using 1;omega

theorem setup_invariant (m a : ℕ) (s : State) (h102:s.natReg 102+1=m)
    (h105:s.natReg 105+s.natReg 102=a) : CopyInvariant m a 0 s.natHeap (applyBlock setup s) := by
  constructor <;> simp [applyBlock,setup,Op.apply,writeNat,next,h102,h105]

theorem setup_frame (s : State) : Frame s (applyBlock setup s) := ⟨rfl,rfl,rfl,rfl⟩
theorem setup_nat (s : State) : NatFrame s (applyBlock setup s) := by
  intro r hr;simp (disch:=omega) [applyBlock,setup,Op.apply,writeNat,next]
theorem setup_peak (m a B : ℕ) (s : State) (h102:s.natReg 102+1=m)
    (h105:s.natReg 105+s.natReg 102=a) (hm:m≤B) (ha:a≤B) (hB:4≤B) : peak setup s≤B := by
  simp [peak,setup,Op.peak,Op.apply,writeNat,next,h102,h105];omega

theorem headers_values (m : ℕ) (s : State) (hm:s.natReg 60=m) :
    UniformDFSProgram.headers m (applyBlock headers s) ∧
    (applyBlock headers s).natReg 0=0 ∧ (applyBlock headers s).natReg 2=0 ∧
    (applyBlock headers s).natReg 8=0 := by
  simp [applyBlock,headers,Op.apply,writeNat,next,hm,UniformDFSProgram.headers,
    UniformDFSProgram.constants,Nat.mul_comm]
theorem headers_heap (s : State) : (applyBlock headers s).natHeap=s.natHeap := rfl
theorem headers_frame (s : State) : Frame s (applyBlock headers s) := ⟨rfl,rfl,rfl,rfl⟩
theorem headers_nat (s : State) : NatFrame s (applyBlock headers s) := by
  intro r hr;simp (disch:=omega) [applyBlock,headers,Op.apply,writeNat,next]
theorem headers_peak (m B : ℕ) (s : State) (hm:s.natReg 60=m)
    (hB:3*m+3≤B) : peak headers s≤B := by
  simp [peak,headers,Op.peak,Op.apply,writeNat,next,hm];omega

/-- One fixed program prints all mixed-radix addresses into the low output
    region. Table reads, copy indexing, DFS initialization and continuation
    jumps are included in the exact count. -/
theorem execution (rs : List ℕ) (n a B : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (h102:s.natReg 102+1=rs.length)
    (h105:s.natReg 105+s.natReg 102=a)
    (hsrc:∀j:Fin rs.length,s.natHeap (a+4*j.val)=some (rs.get j))
    (hp:UniformDFSProgram.Positive rs) (hd:rs.length≤a)
    (hsource:a+4*rs.length≤B) (hcode:53≤B)
    (hsize:30+3*rs.length+rs.prod≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (6*rs.length+UniformDFSProgram.treeCost rs+20) u ∧
    u.pc=52 ∧ u.natReg 8=rs.prod ∧
    (∀j,j<rs.prod→u.natHeap (3*rs.length+j)=some j) ∧
    (∀a,3*rs.length+rs.prod≤a→u.natHeap a=s.natHeap a) ∧
    Frame s u ∧ NatFrame s u := by
  have boot:=block_runs setup program 0 n B x s setup_code hpc hs (by rw [setup_length];omega)
    (by simp [readable,setup,Op.readable])
    (setup_peak rs.length a B s h102 h105 (by omega) (by omega) (by omega))
  have bi:=setup_invariant rs.length a s h102 h105
  have bp:(applyBlock setup s).pc=5:=by rw [UniformReciprocalMachine.applyBlock_pc,hpc,setup_length]
  obtain ⟨c,cb,ci,cp,cf,cn⟩:=copy_loop n x rs.length a 0 rs.length B s.natHeap
    (applyBlock setup s) bi (by
      intro j hj;exact ⟨rs.get ⟨j,hj⟩,hsrc ⟨j,hj⟩⟩) (by omega) hd hsource hcode bp boot.final_bound
  let e:State:={c with pc:=11}
  have eb:WordBound B e:=changePC_bound B c 11 cb.final_bound (by omega)
  have exit:BoundedRuns program n x B c 1 e:=.next cb.final_bound (by
    simp [step,program,embed,head,setup,Op.code,cp,ci.index,ci.length,e]) (.refl eb)
  have hb:=block_runs headers program 11 n B x e headers_code rfl eb
    (by rw [headers_length];omega) (by simp [readable,headers,Op.readable])
    (headers_peak rs.length B e ci.length (by omega))
  let w:=applyBlock headers e
  have wp:w.pc=22:=by simp [w,UniformReciprocalMachine.applyBlock_pc,e,headers_length]
  have wh:=headers_values rs.length e ci.length
  have wt:UniformDFSProgram.radicesAt rs 0 {w with pc:=0}:=by
    intro j
    change w.natHeap (0+j.val)=some (rs.get j)
    rw [show w.natHeap=c.natHeap from headers_heap e,zero_add,ci.copied j.val j.isLt]
    exact hsrc j
  have wb:WordBound B {w with pc:=0}:=changePC_bound B w 0 hb.final_bound (by omega)
  have dfs:=dfs_ambient rs n B x {w with pc:=0} rfl wh.1 wh.2.1 wh.2.2.1 wh.2.2.2 wt hp hsize wb
  have placed:=UniformBoundedAssembly.boundedExecution_placed dfs_code
    (show 22+UniformDFSProgram.program.length≤B by change 22+30≤B;omega) (show 52≤B by omega) dfs
  have entry:UniformAssembly.placed 22 {w with pc:=0}=w:=by
    change {w with pc:=22}=w
    rw [←wp]
  rw [entry] at placed
  let u:State:={UniformDFSProgram.setPC (UniformDFSProgram.tree rs {w with pc:=0}) 29 with pc:=52}
  have hu:WordBound B u:=placed.final_bound
  have halt:BoundedExecution program n x B u 1 u:=.halt hu (by simp [step,u,UniformDFSProgram.setPC,halt_at])
  obtain ⟨_,dc,dout⟩:=UniformDFSProgram.complete_execution rs n x {w with pc:=0} rfl
    wh.1 wh.2.1 wh.2.2.1 wh.2.2.2 wt
  refine ⟨u,?_,rfl,dc,dout,?_,?_,?_⟩
  · convert boot.executes (cb.executes (exit.executes (hb.executes (placed.executes halt)))) using 1
    rw [setup_length,headers_length];omega
  · intro address ha
    have ht:=dfs_tree_high rs n x rs.length 0 0 0 rs.prod {w with pc:=0}
      rfl wh.1 wh.2.1 wh.2.2.1 wh.2.2.2 (by omega) wt (by simp) address ha
    exact ht.trans (ci.outside address (by omega))
  · have da:=UniformDFSProgram.final_auxiliary rs {w with pc:=0}
    have df:Frame w u:=by
      exact ⟨congrArg (fun a=>a.2.1) da,congrArg (fun a=>a.1) da,
        congrArg (fun a=>a.2.2.1) da,congrArg (fun a=>a.2.2.2) da⟩
    exact (setup_frame s).trans (cf.trans ((headers_frame e).trans df))
  · intro r hr
    have dr:=dfs_tree_nat rs {w with pc:=0} r (by omega)
    exact dr.trans ((headers_nat e r hr).trans ((cn r hr).trans (setup_nat s r hr)))

/-- Original protected metadata starts strictly above all DFS scratch/output. -/
theorem workspace_before_protected (n : ℕ) : 3*(ell n+1)+len n≤copyBase n := by
  unfold copyBase UniformGlobalNatPreparation.destination UniformGlobalNatPreparation.amount;omega

theorem selected_word_setup {n : ℕ} (hn:0<n) :
    53≤(n+2)^19 ∧ copyBase n+ell n+4*(ell n+1)≤(n+2)^19 ∧
    30+3*(ell n+1)+len n≤(n+2)^19 := by
  have h:=UniformInitialPreparation.word_setup hn
  unfold copyBase UniformGlobalNatPreparation.destination UniformGlobalNatPreparation.amount
    UniformGlobalNatPreparation.wordBudget at *
  omega

/-- Selected axes are the actual protected CRT table, including the possibly
    unit binary axis. No radix-table preparation hypothesis is left here. -/
theorem selected_execution (n : ℕ) (hn:0<n) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s
      (6*(ell n+1)+UniformDFSProgram.treeCost (selectedRadices n)+20) u ∧
    u.pc=52 ∧ u.natReg 8=len n ∧
    (∀j,j<len n→u.natHeap (3*(ell n+1)+j)=some j) ∧
    (∀a,3*(ell n+1)+len n≤a→u.natHeap a=s.natHeap a) ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    Frame s u ∧ NatFrame s u := by
  have hsrc:∀j:Fin (selectedRadices n).length,
      s.natHeap (copyBase n+ell n+4*j.val)=some ((selectedRadices n).get j):=by
    intro j
    have jj:j.val<ell n+1:=by simpa only [selectedRadices_length] using j.isLt
    have hc:=(hm.crt ⟨j.val,jj⟩).1
    have hg:((selectedRadices n).get j)=UniformSelectedCRT.radices n ⟨j.val,jj⟩:=by
      exact List.get_ofFn (UniformSelectedCRT.radices n)
        ⟨j.val,by simpa only [List.length_ofFn] using jj⟩
    rw [hg]
    simpa [protectedView,UniformCRTHeaderMachine.tableAddress,ell,Nat.add_assoc] using hc
  have hb:=selected_word_setup hn
  obtain ⟨u,hu,hpu,hcu,hout,hhigh,hframe,hnat⟩:=execution (selectedRadices n) n
    (copyBase n+ell n) ((n+2)^19) x s hpc
    (by rw [hm.saved.count,selectedRadices_length])
    (by rw [hm.saved.copyAddress,hm.saved.count]) hsrc (selectedRadices_positive n)
    (by rw [selectedRadices_length];have h:=workspace_before_protected n;omega)
    (by simpa only [selectedRadices_length] using hb.2.1) hb.1
    (by simpa only [selectedRadices_length,selectedRadices_product] using hb.2.2) hs
  simp only [selectedRadices_length,selectedRadices_product] at hu hcu hout hhigh
  have hmeta:=hm.transport hnat (by
    intro a _;exact hhigh (copyBase n+a) (by have h:=workspace_before_protected n;omega))
  exact ⟨u,hu,hpu,hcu,hout,hhigh,hmeta,ho.transport hframe.1,hframe,hnat⟩

/-- Linear charged work follows from the actual DFS tree, not an assumed
    per-axis scan. The sole binary axis is permitted to have radix one. -/
theorem selected_runtime_linear (n : ℕ) :
    6*(ell n+1)+UniformDFSProgram.treeCost (selectedRadices n)+20≤84*len n+6 := by
  have he:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:2*n≤len n:=UniformWorkingLength.workingLength_lower n
  have hc:=UniformDFSProgram.treeCost_balance (selectedRadices n)
  have ht:=selectedRadices_nodes n
  omega

/-- Any inverse permutation bank above protected metadata is retained. -/
theorem betaInverse_retained {n : ℕ} {s u : State}
    (hh:∀a,3*(ell n+1)+len n≤a→u.natHeap a=s.natHeap a) :
    ∀j,u.natHeap (UniformPermutationInversePreparation.inverseBase n+j)=
      s.natHeap (UniformPermutationInversePreparation.inverseBase n+j) := by
  intro j
  exact hh _ (by
    have h:=workspace_before_protected n
    unfold UniformPermutationInversePreparation.inverseBase;omega)

theorem betaInverse_bank_retained {n : ℕ} {s u : State}
    (hh:∀a,3*(ell n+1)+len n≤a→u.natHeap a=s.natHeap a)
    (hb:UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm) :
    UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm := by
  intro j
  exact (betaInverse_retained hh j.val).trans (hb j)

theorem program_integer_only : ∀i∈program,UniformDFSProgram.integerInstruction i=true := by
  simp [program,embed,head,setup,headers,Op.code,UniformDFSProgram.program,
    relocate,UniformDFSProgram.integerInstruction]

theorem program_natStep_correct (n : ℕ) (x : Fin n→ℂ) (s : State) :
    UniformDFSProgram.natResult (step program n x s)=
      UniformDFSProgram.natStep program n (UniformDFSProgram.natView s) :=
  UniformDFSProgram.natStep_correct program program_integer_only n x s

end
end ExactFourierCircuits.UniformSelectedDFSMachine
