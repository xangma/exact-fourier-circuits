import UniformFixedNetworkOpcodeMachine
import UniformInPlaceMachine
import RoleWords

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkShearChildMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Runtime Fin5 code comes from the actual printed scalar macro field2858.
Only these five rational literals occur; there is no root or scalar branch. -/
def rational (k:Fin 5) : ℚ := if k.val=0 then -1 else if k.val=1 then -1/2 else
 if k.val=2 then 0 else if k.val=3 then 1/2 else 1
def decodeBoot : List Op := [.literal 2911 1,.literal 2912 2,.literal 2913 3,
 .literal 2914 4,.literal 2915 5,.literal 2916 0]
def decodeProgram : Program := decodeBoot.map Op.code++
 [ .branchLT 2858 2911 12 7,.branchLT 2858 2912 14 8,
 .branchLT 2858 2913 16 9,.branchLT 2858 2914 18 10,
 .branchLT 2858 2915 20 11,.natBinary .div 2916 2916 2916,
 .scalarLiteral 104 (-1),.jump 22,.scalarLiteral 104 (-1/2),.jump 22,
 .scalarLiteral 104 0,.jump 22,.scalarLiteral 104 (1/2),.jump 22,
 .scalarLiteral 104 1,.jump 22,.halt]
lemma decodeProgram_length : decodeProgram.length=23 := rfl
lemma decodeBoot_code : BlockAt decodeBoot decodeProgram 0 := by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
lemma branch_code (j:ℕ) (hj:j < 5) : decodeProgram[6+j]?=some (.branchLT 2858 (2911+j) (12+2*j) (7+j)) := by
 interval_cases j <;> rfl
lemma literal_code (k:Fin 5) : decodeProgram[12+2*k.val]?=some (.scalarLiteral 104 (rational k)) := by
 fin_cases k <;> rfl
lemma jump_code (k:Fin 5) : decodeProgram[13+2*k.val]?=some (.jump 22) := by
 fin_cases k <;> rfl
lemma decode_halt : decodeProgram[22]?=some .halt := rfl

noncomputable section
lemma rational_decode (k:Fin 5) : (rational k:ℂ)=UniformFixedCoefficientCodec.decode k := by
 fin_cases k <;> norm_num [rational,UniformFixedCoefficientCodec.decode]
structure DecodedFields (k:Fin 5) (s:State) : Prop where
 code:s.natReg 2858=k.val
 threshold:∀j:Fin 5,s.natReg (2911+j.val)=j.val+1
 zero:s.natReg 2916=0
lemma decodeBoot_fields (k:Fin 5) (s:State) (code:s.natReg 2858=k.val) :
 DecodedFields k (applyBlock decodeBoot s) := by
 refine ⟨?_,?_,?_⟩
 · simp [decodeBoot,applyBlock,Op.apply,writeNat,next,code]
 · intro j;fin_cases j <;> simp [decodeBoot,applyBlock,Op.apply,writeNat,next]
 · simp [decodeBoot,applyBlock,Op.apply,writeNat,next]
lemma DecodedFields.pc {k:Fin 5} {s:State} (h:DecodedFields k s) (c:ℕ) : DecodedFields k (setPC s c) :=
 ⟨h.code,h.threshold,h.zero⟩
lemma decode_seek (B n:ℕ) (x:Fin n→ℂ) (k:Fin 5) (c:ℕ) (hc:c≤k.val) (s:State)
 (fields:DecodedFields k s) (pc:s.pc=6+(k.val-c)) (hs:WordBound B s) (bound:23≤B) :
 BoundedRuns decodeProgram n x B s (c+1) (setPC s (12+2*k.val)) := by
 induction c generalizing s with
 | zero=>
   have p:s.pc=6+k.val:=by simpa using pc
   have ins:decodeProgram[s.pc]?=some (.branchLT 2858 (2911+k.val) (12+2*k.val) (7+k.val)):=by rw [p];exact branch_code _ k.isLt
   exact .next hs (by simp [step,ins,fields.code,fields.threshold k,setPC])
     (.refl (changePC_bound B _ _ hs (by have h:=k.isLt;omega)))
 | succ c ih=>
   have idx:k.val-(c+1) < 5:=by have h:=k.isLt;omega
   have ins:decodeProgram[s.pc]?=some (.branchLT 2858 (2911+(k.val-(c+1))) (12+2*(k.val-(c+1))) (7+(k.val-(c+1)))):=by rw [pc];exact branch_code _ idx
   have th:=fields.threshold ⟨_,idx⟩
   let t:=setPC s (7+(k.val-(c+1)))
   have run:step decodeProgram n x s=.running t:=by simp [step,ins,fields.code,th,t,setPC,show ¬k.val < k.val-(c+1)+1 by omega]
   have bt:WordBound B t:=changePC_bound B _ _ hs (by have h:=k.isLt;omega)
   have rest:=ih (by omega) t (fields.pc _) (by dsimp [t,setPC];omega) bt
   have out:setPC t (12+2*k.val)=setPC s (12+2*k.val):=rfl
   rw [out] at rest
   simpa only [Nat.add_assoc] using BoundedRuns.next hs run rest

structure DecodeFrame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j < 2911∨2917≤j→u.natReg j=s.natReg j
 scalarReg:∀j,j≠104→u.scalarReg j=s.scalarReg j
lemma decodeFrame_boot (s:State) : DecodeFrame s (applyBlock decodeBoot s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro j h;simp (disch:=omega) [decodeBoot,applyBlock,Op.apply,writeNat,next]
lemma DecodeFrame.pc {s u:State} (h:DecodeFrame s u) (c:ℕ) : DecodeFrame s (setPC u c) :=
 ⟨h.natHeap,h.scalarHeap,h.outputs,h.roots,h.natReg,h.scalarReg⟩
lemma DecodeFrame.scalar {s u:State} (h:DecodeFrame s u) (c:Scalar) : DecodeFrame s (writeScalar u 104 c) := by
 refine ⟨h.natHeap,h.scalarHeap,h.outputs,h.roots,h.natReg,?_⟩
 intro j hj;simp only [writeScalar,next];rw [Function.update_of_ne hj];exact h.scalarReg j hj

/-- Exact prepared coefficient production, including code2=zero. -/
theorem decode_execution (B n:ℕ) (x:Fin n→ℂ) (k:Fin 5) (s:State)
 (code:s.natReg 2858=k.val) (pc:s.pc=0) (hs:WordBound B s) (bound:23≤B) : ∃u,
 BoundedExecution decodeProgram n x B s (k.val+10) u ∧
 u.scalarReg 104=UniformInPlaceMachine.prepared (UniformFixedCoefficientCodec.decode k) ∧ DecodeFrame s u := by
 have safe:readable decodeBoot s ∧ peak decodeBoot s≤B:=by
   simp [decodeBoot,readable,peak,Op.readable,Op.peak];omega
 have boot:=block_runs decodeBoot decodeProgram 0 n B x s decodeBoot_code pc hs (by change 0+6≤B;omega) safe.1 safe.2
 let ready:=applyBlock decodeBoot s
 have fields:=decodeBoot_fields k s code
 have p:ready.pc=6:=by simp [ready,UniformTensorMonomialMachine.applyBlock_pc,pc,decodeBoot]
 have seek:=decode_seek B n x k k.val (by omega) ready fields (by simpa using p) boot.final_bound bound
 let chosen:=setPC ready (12+2*k.val)
 let mid:=writeScalar chosen 104 (UniformInPlaceMachine.prepared (rational k))
 have bm:WordBound B mid:=writeScalar_bound B _ _ _ seek.final_bound (by change 12+2*k.val+1≤B;have h:=k.isLt;omega)
 have lit:step decodeProgram n x chosen=.running mid:=by simp [step,chosen,setPC,literal_code,mid,UniformInPlaceMachine.prepared]
 let done:=setPC mid 22
 have bd:=changePC_bound B mid 22 bm (by omega)
 have jump:step decodeProgram n x mid=.running done:=by
   have pm:mid.pc=13+2*k.val:=by simp [mid,writeScalar,next,chosen,setPC];omega
   simp [step,pm,jump_code,done,setPC]
 have last:BoundedExecution decodeProgram n x B chosen 3 done:=
   .next seek.final_bound lit (.next bm jump (.halt bd (by simp [step,done,setPC,decode_halt])))
 refine ⟨done,?_,?_,?_⟩
 · convert boot.executes (seek.executes last) using 1
   change k.val+10=6+(k.val+1+3);omega
 · simp [done,mid,writeScalar,next,setPC,rational_decode]
 · exact ((decodeFrame_boot s).pc _ |>.scalar _).pc _

/-- Actual role-major offsets use the ordinary physical base2900 and volume
2901, and fields2854/2855 read by the frozen header decoder. -/
def offsetSetup : List Op := [.mul 2905 2901 2854,.add 2905 2900 2905,
 .mul 2906 2901 2855,.add 2906 2900 2906,.literal 2907 0,.literal 2908 1]
def program : Program := UniformAssembly.embed [] decodeProgram
 (offsetSetup.map Op.code++[.branchLT 2907 2901 30 39,
 .natBinary .add 2909 2905 2907,.natBinary .add 2910 2906 2907,
 .loadScalar 100 2909,.loadScalar 101 2910,
 .fieldBinary .mul 102 104 101,.fieldBinary .add 100 100 102,
 .storeScalar 2909 100,.natBinary .add 2907 2907 2908,.jump 29,.halt]) 23
lemma program_length : program.length=40 := rfl
lemma decoder_code : UniformAssembly.CodeAt decodeProgram program 0 23 := UniformAssembly.embed_code [] _ _ _
lemma offsetSetup_code : BlockAt offsetSetup program 23 := by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
lemma loop_code (i:ℕ) (hi:i < 11) :
 program[29+i]?=([.branchLT 2907 2901 30 39,.natBinary .add 2909 2905 2907,
 .natBinary .add 2910 2906 2907,.loadScalar 100 2909,.loadScalar 101 2910,
 .fieldBinary .mul 102 104 101,.fieldBinary .add 100 100 102,.storeScalar 2909 100,
 .natBinary .add 2907 2907 2908,.jump 29,.halt]:Program)[i]? := by
 interval_cases i <;> rfl

structure Header (D S V i:ℕ) (c:ℂ) (s:State) : Prop where
 pc:s.pc=29
 dst:s.natReg 2905=D
 src:s.natReg 2906=S
 size:s.natReg 2901=V
 index:s.natReg 2907=i
 one:s.natReg 2908=1
 coefficient:s.scalarReg 104=UniformInPlaceMachine.prepared c

def value (c:ℂ) (a b:Scalar) : Scalar := UniformInPlaceMachine.result a b (UniformInPlaceMachine.prepared c)
def PairPresent (D S V i:ℕ) (c:ℂ) (a b:Fin V→Scalar) (s:State) : Prop :=
 (∀j,s.scalarHeap (D+j.val)=some (if j.val < i then value c (a j) (b j) else a j)) ∧
 (∀j,s.scalarHeap (S+j.val)=some (b j))
def entered (s:State) := setPC s 30
def dstAddress (D i:ℕ) (s:State) := writeNat (entered s) 2909 (D+i)
def srcAddress (D S i:ℕ) (s:State) := writeNat (dstAddress D i s) 2910 (S+i)
def dstLoaded (D S i:ℕ) (a:Scalar) (s:State) := writeScalar (srcAddress D S i s) 100 a
def srcLoaded (D S i:ℕ) (a b:Scalar) (s:State) := writeScalar (dstLoaded D S i a s) 101 b
def multiplied (D S i:ℕ) (c:ℂ) (a b:Scalar) (s:State) :=
 writeScalar (srcLoaded D S i a b s) 102 (UniformInPlaceMachine.product (UniformInPlaceMachine.prepared c) b)
def added (D S i:ℕ) (c:ℂ) (a b:Scalar) (s:State) :=
 writeScalar (multiplied D S i c a b s) 100 (value c a b)
def stored (D S i:ℕ) (c:ℂ) (a b:Scalar) (s:State) : State :=
 {next (added D S i c a b s) with scalarHeap:=Function.update s.scalarHeap (D+i) (some (value c a b))}
def advanced (D S i:ℕ) (c:ℂ) (a b:Scalar) (s:State) := writeNat (stored D S i c a b s) 2907 (i+1)
def rowEnd (D S i:ℕ) (c:ℂ) (a b:Scalar) (s:State) := setPC (advanced D S i c a b s) 29

structure Frame (D V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j < 2905∨2917≤j→u.natReg j=s.natReg j
 scalarReg:∀j,j≠100→j≠101→j≠102→j≠104→u.scalarReg j=s.scalarReg j
 scalarHeap:∀z,z < D∨D+V≤z→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (D V:ℕ) (s:State) : Frame D V s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.pc (D V:ℕ) (s:State) (c:ℕ) : Frame D V s (setPC s c) := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {D V:ℕ} {s u t:State} (a:Frame D V s u) (b:Frame D V u t) : Frame D V s t :=
 ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,
 fun j hj=>(b.natReg j hj).trans (a.natReg j hj),
 fun j h1 h2 h3 h4=>(b.scalarReg j h1 h2 h3 h4).trans (a.scalarReg j h1 h2 h3 h4),
 fun z hz=>(b.scalarHeap z hz).trans (a.scalarHeap z hz)⟩
lemma rowEnd_frame (D S V i:ℕ) (c:ℂ) (a b:Scalar) (s:State) (hi:i < V) : Frame D V s (rowEnd D S i c a b s) := by
 refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
 · intro j hj;simp (disch:=omega) [rowEnd,advanced,stored,added,multiplied,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next]
 · intro j h1 h2 h3 h4;simp [rowEnd,advanced,stored,added,multiplied,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next,h1,h2,h3]
 · intro z hz;change (Function.update s.scalarHeap (D+i) (some (value c a b))) z=s.scalarHeap z
   exact Function.update_of_ne (by omega) _ _
lemma rowEnd_header (D S V i:ℕ) (c:ℂ) (a b:Scalar) (s:State) (h:Header D S V i c s) :
 Header D S V (i+1) c (rowEnd D S i c a b s) := by
 rcases h with ⟨pc,dst,src,size,index,one,coefficient⟩
 constructor <;> simp [rowEnd,advanced,stored,added,multiplied,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next,dst,src,size,one,coefficient]

/-- Actual one-cell read/multiply/add/store, including its branch and return. -/
lemma row_bounded (B n D S V i:ℕ) (x:Fin n→ℂ) (c:ℂ) (a b:Scalar) (s:State)
 (h:Header D S V i c s) (hi:i < V) (ha:s.scalarHeap (D+i)=some a) (hb:s.scalarHeap (S+i)=some b)
 (bound:WordBound B s) (code:40≤B) (dst:D+V≤B) (src:S+V≤B) (vol:V≤B) :
 BoundedRuns program n x B s 10 (rowEnd D S i c a b s) := by
 have b0:WordBound B (entered s):=changePC_bound B s 30 bound (by omega)
 have b1:WordBound B (dstAddress D i s):=writeNat_bound B _ _ _ b0 (by change 31≤B;omega) (by omega)
 have b2:WordBound B (srcAddress D S i s):=writeNat_bound B _ _ _ b1 (by change 32≤B;omega) (by omega)
 have b3:WordBound B (dstLoaded D S i a s):=writeScalar_bound B _ _ _ b2 (by change 33≤B;omega)
 have b4:WordBound B (srcLoaded D S i a b s):=writeScalar_bound B _ _ _ b3 (by change 34≤B;omega)
 have b5:WordBound B (multiplied D S i c a b s):=writeScalar_bound B _ _ _ b4 (by change 35≤B;omega)
 have b6:WordBound B (added D S i c a b s):=writeScalar_bound B _ _ _ b5 (by change 36≤B;omega)
 have b7:WordBound B (stored D S i c a b s):=UniformInPlaceMachine.storeScalar_bound B _ _ _ b6 (by change 37≤B;omega) (by omega)
 have b8:WordBound B (advanced D S i c a b s):=writeNat_bound B _ _ _ b7 (by change 38≤B;omega) (by omega)
 have b9:WordBound B (rowEnd D S i c a b s):=changePC_bound B _ 29 b8 (by omega)
 rcases h with ⟨pc,dd,ss,vv,idx,one,coefficient⟩
 refine .next bound ?_ (.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.next b3 ?_ (.next b4 ?_
 (.next b5 ?_ (.next b6 ?_ (.next b7 ?_ (.next b8 ?_ (.refl b9))))))))))
 all_goals simp [step,program,UniformAssembly.embed,UniformAssembly.relocate,decodeProgram,decodeBoot,
 offsetSetup,rowEnd,advanced,stored,added,multiplied,srcLoaded,dstLoaded,srcAddress,dstAddress,
 entered,setPC,writeNat,writeScalar,next,evalNat,pc,dd,ss,vv,idx,one,ha,hb,
 show i < V from hi,coefficient,evalField,UniformInPlaceMachine.prepared,UniformInPlaceMachine.product,UniformInPlaceMachine.result,value]

/-- A real stored result advances the physical invariant; sources are untouched
because the source and destination intervals are disjoint. -/
lemma rowEnd_pair (D S V i:ℕ) (c:ℂ) (a b:Fin V→Scalar) (s:State) (hi:i < V)
 (pair:PairPresent D S V i c a b s)
 (disjoint:∀j l:Fin V,D+j.val≠S+l.val) :
 PairPresent D S V (i+1) c a b (rowEnd D S i c (a ⟨i,hi⟩) (b ⟨i,hi⟩) s) := by
 constructor
 · intro j
   change (Function.update s.scalarHeap (D+i) (some (value c (a ⟨i,hi⟩) (b ⟨i,hi⟩)))) (D+j.val)=_
   by_cases hj:j.val=i
   · have eq:j=(⟨i,hi⟩:Fin V):=Fin.ext hj
     subst j
     simp [show i < i+1 by omega]
   · rw [Function.update_of_ne (by omega),pair.1 j]
     have eq:(j.val < i)↔j.val < i+1:=by omega
     simp only [eq]
 · intro j
   change (Function.update s.scalarHeap (D+i) (some (value c (a ⟨i,hi⟩) (b ⟨i,hi⟩)))) (S+j.val)=_
   rw [Function.update_of_ne (disjoint ⟨i,hi⟩ j).symm]
   exact pair.2 j


/-- Whole-array execution from actual present source/destination cells, with
no Ready state or resulting action supplied. -/
theorem loop_execution (B n D S V count:ℕ) (x:Fin n→ℂ) (c:ℂ) (a b:Fin V→Scalar)
 (code:40≤B) (dst:D+V≤B) (src:S+V≤B) (vol:V≤B)
 (disjoint:∀j l:Fin V,D+j.val≠S+l.val) :
 ∀i s,i+count=V→Header D S V i c s→PairPresent D S V i c a b s→WordBound B s→∃u,
 BoundedExecution program n x B s (10*count+2) u ∧
 PairPresent D S V V c a b u ∧ Frame D V s u := by
 induction count with
 | zero=>
   intro i s eq h pair bound
   have stop:¬s.natReg 2907 < s.natReg 2901:=by rw [h.index,h.size];omega
   let u:=setPC s 39
   have bu:=changePC_bound B s 39 bound (by omega)
   refine ⟨u,?_,?_,Frame.pc D V s 39⟩
   · exact .next bound (by simp [step,h.pc,program,UniformAssembly.embed,decodeProgram,decodeBoot,offsetSetup,stop,u,setPC])
       (.halt bu (by simp [step,u,setPC,program,UniformAssembly.embed,decodeProgram,decodeBoot,offsetSetup]))
   · have vi:i=V:=by omega
     subst i;exact pair
 | succ count ih=>
   intro i s eq h pair bound
   have hi:i < V:=by omega
   let j:Fin V:=⟨i,hi⟩
   have ha:s.scalarHeap (D+i)=some (a j):=by simpa [j,show ¬i < i by omega] using pair.1 j
   have hb:s.scalarHeap (S+i)=some (b j):=pair.2 j
   let t:=rowEnd D S i c (a j) (b j) s
   have run:=row_bounded B n D S V i x c (a j) (b j) s h hi ha hb bound code dst src vol
   obtain ⟨u,tail,output,frame⟩:=ih (i+1) t (by omega) (rowEnd_header D S V i c (a j) (b j) s h)
     (rowEnd_pair D S V i c a b s hi pair disjoint) run.final_bound
   refine ⟨u,?_,output,(rowEnd_frame D S V i c (a j) (b j) s hi).trans frame⟩
   convert run.executes tail using 1
   ring

/-- Ordinary role-major physical array, including all dependency flags. -/
def Present (A R V:ℕ) (f:Fin R→Fin V→Scalar) (s:State) : Prop :=
 ∀r j,s.scalarHeap (A+r.val*V+j.val)=some (f r j)
def roleBase (A V:ℕ) (r:ℕ) : ℕ := A+r*V
lemma role_bound {R:ℕ} (A V:ℕ) (r:Fin R) : roleBase A V r.val+V≤A+R*V := by
 have h:=Nat.mul_le_mul_right V (show r.val+1≤R by have h:=r.isLt;omega)
 rw [Nat.add_mul,Nat.one_mul] at h
 unfold roleBase;omega
lemma role_outside {R V:ℕ} (A:ℕ) (d r:Fin R) (ne:r≠d) (j:Fin V) :
 A+r.val*V+j.val < roleBase A V d.val ∨ roleBase A V d.val+V≤A+r.val*V+j.val := by
 have hne:r.val≠d.val:=by intro h;exact ne (Fin.ext h)
 by_cases h:r.val < d.val
 · have b:=Nat.mul_le_mul_right V (show r.val+1≤d.val by omega)
   rw [Nat.add_mul,Nat.one_mul] at b
   left;unfold roleBase;have hj:=j.isLt;omega
 · have b:=Nat.mul_le_mul_right V (show d.val+1≤r.val by omega)
   rw [Nat.add_mul,Nat.one_mul] at b
   right;unfold roleBase;omega

lemma role_disjoint {R V:ℕ} (A:ℕ) (d r:Fin R) (ne:d≠r) :
 ∀j l:Fin V,roleBase A V d.val+j.val≠roleBase A V r.val+l.val := by
 intro j l
 have out:=role_outside A d r ne.symm l
 have hj:=j.isLt
 unfold roleBase at *;omega

def shearValues {R V:ℕ} (d source:Fin R) (c:ℂ) (f:Fin R→Fin V→Scalar) : Fin R→Fin V→Scalar :=
 fun r j=>if r=d then value c (f d j) (f source j) else f r j
lemma offsetSetup_frame (D V:ℕ) (s:State) : Frame D V s (applyBlock offsetSetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
 intro j hj;simp (disch:=omega) [offsetSetup,applyBlock,Op.apply,writeNat,next]
lemma Frame.of_decode (D V:ℕ) {s u:State} (h:DecodeFrame s u) : Frame D V s u :=
 ⟨h.natHeap,h.outputs,h.roots,fun j hj=>h.natReg j (by omega),
 fun j _ _ _ h4=>h.scalarReg j h4,fun z _=>congrFun h.scalarHeap z⟩
lemma offsetSetup_header (A V d source:ℕ) (c:ℂ) (s:State)
 (pc:s.pc=23) (base:s.natReg 2900=A) (size:s.natReg 2901=V)
 (dest:s.natReg 2854=d) (src:s.natReg 2855=source)
 (coef:s.scalarReg 104=UniformInPlaceMachine.prepared c) :
 Header (roleBase A V d) (roleBase A V source) V 0 c (applyBlock offsetSetup s) := by
 constructor <;> simp [offsetSetup,applyBlock,Op.apply,writeNat,next,pc,base,size,dest,src,coef,roleBase,Nat.mul_comm]
lemma offsetSetup_safe (A V d source B:ℕ) (s:State) (base:s.natReg 2900=A)
 (size:s.natReg 2901=V) (dest:s.natReg 2854=d) (src:s.natReg 2855=source)
 (db:roleBase A V d≤B) (sb:roleBase A V source≤B) (code:40≤B) :
 readable offsetSetup s ∧ peak offsetSetup s≤B := by
 unfold roleBase at db sb
 have db' : A+V*d≤B := by simpa only [Nat.mul_comm] using db
 have sb' : A+V*source≤B := by simpa only [Nat.mul_comm] using sb
 simp [offsetSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,base,size,dest,src]
 omega

/-- No coefficient bank or ready row is supplied: the literal decoder makes
its prepared scalar, and the physical loop derives every cell load internally. -/
theorem execution {R V:ℕ} (A B n:ℕ) (x:Fin n→ℂ) (d source:Fin R) (ne:d≠source)
 (k:Fin 5) (f:Fin R→Fin V→Scalar) (s:State)
 (pc:s.pc=0) (base:s.natReg 2900=A) (size:s.natReg 2901=V)
 (dest:s.natReg 2854=d.val) (src:s.natReg 2855=source.val) (scalar:s.natReg 2858=k.val)
 (data:Present A R V f s) (bound:WordBound B s) (code:40≤B) (extent:A+R*V≤B) : ∃u,
 BoundedExecution program n x B s (10*V+k.val+18) u ∧
 Present A R V (shearValues d source (UniformFixedCoefficientCodec.decode k) f) u ∧
 Frame (roleBase A V d.val) V s u := by
 let D:=roleBase A V d.val
 let S:=roleBase A V source.val
 have dst:D+V≤B:=(role_bound A V d).trans extent
 have sourceEnd:S+V≤B:=(role_bound A V source).trans extent
 have vol:V≤B:=by rw [←size];exact bound.2.1 2901
 obtain ⟨decoded,run,coefficient,frame⟩:=decode_execution B n x k s scalar pc bound (by omega)
 have placed:=UniformBoundedAssembly.boundedExecution_placed decoder_code (by rw [decodeProgram_length];omega) (by omega) run
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at placed
 let t:=setPC decoded 23
 have tb:t.natReg 2900=A:=by change decoded.natReg 2900=A;rw [frame.natReg 2900 (by omega)];exact base
 have tv:t.natReg 2901=V:=by change decoded.natReg 2901=V;rw [frame.natReg 2901 (by omega)];exact size
 have td:t.natReg 2854=d.val:=by change decoded.natReg 2854=d.val;rw [frame.natReg 2854 (by omega)];exact dest
 have ts:t.natReg 2855=source.val:=by change decoded.natReg 2855=source.val;rw [frame.natReg 2855 (by omega)];exact src
 have safe:=offsetSetup_safe A V d.val source.val B t tb tv td ts (by omega) (by omega) code
 have start:=block_runs offsetSetup program 23 n B x t offsetSetup_code rfl placed.final_bound (by change 23+6≤B;omega) safe.1 safe.2
 let ready:=applyBlock offsetSetup t
 have rh:Header D S V 0 (UniformFixedCoefficientCodec.decode k) ready:=offsetSetup_header A V d.val source.val _ t rfl tb tv td ts coefficient

 have present:PairPresent D S V 0 (UniformFixedCoefficientCodec.decode k) (f d) (f source) ready:=by
   constructor
   · intro j;change decoded.scalarHeap (D+j.val)=_
     rw [frame.scalarHeap]
     simpa [D,roleBase,show ¬ j.val < 0 by omega] using data d j
   · intro j;change decoded.scalarHeap (S+j.val)=_
     rw [frame.scalarHeap];exact data source j
 obtain ⟨u,last,output,lf⟩:=loop_execution B n D S V V x (UniformFixedCoefficientCodec.decode k)
   (f d) (f source) code dst sourceEnd vol (role_disjoint A d source ne) 0 ready (by omega) rh present start.final_bound
 have total:Frame D V s u:=((Frame.of_decode D V (frame.pc 23)).trans (offsetSetup_frame D V t)).trans lf

 refine ⟨u,?_,?_,total⟩
 · convert placed.executes (start.executes last) using 1
   change 10*V+k.val+18=(k.val+10)+(6+(10*V+2));omega
 · intro r j
   by_cases eq:r=d
   · subst r
     have h:=output.1 j
     simpa [Present,shearValues,D,roleBase,show j.val < V from j.isLt] using h
   · rw [total.scalarHeap _ (role_outside A d r eq j)]
     simpa [shearValues,eq] using data r j

/-- Values agree with the literal three-C pointwise shear word; dependency flags
are the conservative machine flags proved separately by `execution`. -/
theorem shearValues_pointwise {R:ℕ} (m:ℕ) (d source:Fin R) (ne:d≠source)
 (c:ℂ) (hc:c≠0) (f:Fin R→Fin (2^m)→Scalar) (r:Fin R) (j:Fin (2^m)) :
 (shearValues d source c f r j).value=
 (OAI.ExactFourier.wordMatrix (RoleWords.pointwiseShearWord m d source ne c hc)).mulVec
   (RoleWords.arrayValues m (fun i a=>(f i a).value)) (RoleWords.roleAddresses R m (r,j)) := by
 rw [RoleWords.pointwiseShearWord_apply]
 by_cases eq:r=d
 · subst r;simp [shearValues,value,UniformInPlaceMachine.result,
     UniformInPlaceMachine.prepared]
 · simp [shearValues,eq]

/-- The scalar macro's actual printed fields feed the executable child. This
is a component bridge after the earlier physical header reader, not a joined
opcode-dispatch execution theorem. -/
theorem macro_execution {r R w:ℕ} (q A T B n:ℕ) (x:Fin n→ℂ)
 (embedding:Fin r↪Fin R) (d source:Fin r) (ne:d≠source)
 (k:Fin 5) (hk:UniformFixedCoefficientCodec.decode k≠0)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State)
 (fields:UniformFixedNetworkOpcodeMachine.Fields T
   (UniformFixedNetworkScheduleMachine.macroRecord (n:=w) q embedding
     (UniformFixedCoefficientCodec.EncodedMacro.shear d source ne k hk)) s)
 (pc:s.pc=0) (base:s.natReg 2900=A) (size:s.natReg 2901=2^(q*w))
 (data:Present A R (2^(q*w)) f s) (bound:WordBound B s) (code:40≤B)
 (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedExecution program n x B s (10*2^(q*w)+k.val+18) u ∧
 Present A R (2^(q*w))
   (shearValues (embedding d) (embedding source) (UniformFixedCoefficientCodec.decode k) f) u ∧
 Frame (roleBase A (2^(q*w)) (embedding d).val) (2^(q*w)) s u := by
 apply execution A B n x (embedding d) (embedding source) (fun h=>ne (embedding.injective h)) k f s pc base size
 · simpa [UniformFixedNetworkScheduleMachine.macroRecord] using fields.dest
 · simpa [UniformFixedNetworkScheduleMachine.macroRecord] using fields.source
 · simpa [UniformFixedNetworkScheduleMachine.macroRecord] using fields.scalar
 · exact data
 · exact bound
 · exact code
 · exact extent

end
end ExactFourierCircuits.UniformFixedNetworkShearChildMachine
