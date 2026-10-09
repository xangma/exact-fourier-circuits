import UniformJointAllocation
import UniformTensorMonomialMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointAllocationMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace A
export UniformJointAllocation (Constants fixed slab envelope allocate)
end A
noncomputable section

def powerOps (t:ℕ):List Op:=List.replicate t (.mul 6002 6002 6000)
lemma power_succ (t:ℕ):powerOps (t+1)=.mul 6002 6002 6000::powerOps t:=by simp [powerOps,List.replicate_succ]
lemma power_length (t:ℕ):(powerOps t).length=t:=by simp [powerOps]
lemma power_value (t z v:ℕ)(s:State)(base:s.natReg 6000=z)(value:s.natReg 6002=v):
 (applyBlock (powerOps t) s).natReg 6002=v*z^t:=by
 induction t generalizing s v with
 | zero=>simpa [powerOps,applyBlock] using value
 | succ t ih=>
  rw [power_succ,applyBlock]
  have zb:(Op.apply (.mul 6002 6002 6000) s).natReg 6000=z:=by
   simp [Op.apply,writeNat,next,base]
  have vb:(Op.apply (.mul 6002 6002 6000) s).natReg 6002=v*z:=by
   simp [Op.apply,writeNat,next,base,value]
  rw [ih (v*z) _ zb vb,Nat.pow_succ];ring
lemma power_safe (t z v:ℕ)(s:State)(positive:1≤ z)(base:s.natReg 6000=z)(value:s.natReg 6002=v):
 readable (powerOps t) s ∧ peak (powerOps t) s≤ v*z^t:=by
 induction t generalizing s v with
 | zero=>simp [powerOps,readable,peak]
 | succ t ih=>
  have zb:(Op.apply (.mul 6002 6002 6000) s).natReg 6000=z:=by simp [Op.apply,writeNat,next,base]
  have vb:(Op.apply (.mul 6002 6002 6000) s).natReg 6002=v*z:=by simp [Op.apply,writeNat,next,base,value]
  have tail:=ih (v*z) _ zb vb
  have first:v*z≤ v*z^(t+1):=Nat.mul_le_mul_left v (by
   simpa using Nat.pow_le_pow_right positive (by omega : 1≤ t+1))
  have pe:v*z*z^t=v*z^(t+1):=by rw [Nat.pow_succ];ring
  have tb:peak (powerOps t) (Op.apply (.mul 6002 6002 6000) s)≤ v*z^(t+1):=by simpa only [pe] using tail.2
  simpa only [power_succ,readable,peak,Op.readable,Op.peak,value,base,true_and] using
   And.intro tail.1 (max_le first tb)
lemma power_natReg (t:ℕ)(s:State)(j:ℕ)(ne:j≠6002):
 (applyBlock (powerOps t) s).natReg j=s.natReg j:=by
 induction t generalizing s with
 | zero=>rfl
 | succ t ih=>rw [power_succ,applyBlock,ih];simp [Op.apply,writeNat,next,ne]
lemma power_frame (t:ℕ)(s:State):
 (applyBlock (powerOps t) s).natHeap=s.natHeap ∧
 (applyBlock (powerOps t) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (powerOps t) s).scalarReg=s.scalarReg ∧
 (applyBlock (powerOps t) s).outputs=s.outputs ∧
 (applyBlock (powerOps t) s).rootOrders=s.rootOrders:=by
 induction t generalizing s with
 | zero=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | succ t ih=>simpa [power_succ,applyBlock,Op.apply,writeNat,next] using ih (Op.apply (.mul 6002 6002 6000) s)

def factors:List ℕ:=[1,2,3,1,4,3,2,4,5,6,5,6,7,8,9,10,11,12]
def headerOps (r:ℕ)(fs:List ℕ):List Op:=match fs with
 | []=>[]
 | f::rest=>[.literal 6005 f,.mul r 6005 6004]++headerOps (r+1) rest
lemma headers_length (r:ℕ)(fs:List ℕ):(headerOps r fs).length=2*fs.length:=by
 induction fs generalizing r with
 | nil=>rfl
 | cons f fs ih=>simp [headerOps,ih];omega
lemma headers_slab (r u:ℕ)(fs:List ℕ)(s:State)(high:6005<r)(sl:s.natReg 6004=u):
 (applyBlock (headerOps r fs) s).natReg 6004=u:=by
 induction fs generalizing r s with
 | nil=>exact sl
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  apply ih (r+1) _ (by omega)
  simp (disch:=omega) [Op.apply,writeNat,next,sl]
lemma headers_natReg (r:ℕ)(fs:List ℕ)(s:State)(j:ℕ)(temp:j≠6005)(outside:j<r∨r+fs.length≤ j):
 (applyBlock (headerOps r fs) s).natReg j=s.natReg j:=by
 induction fs generalizing r s with
 | nil=>rfl
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  rw [ih (r+1) _ (by simp only [List.length_cons] at outside;omega)]
  have ne:j≠r:=by simp only [List.length_cons] at outside;omega
  simp [Op.apply,writeNat,next,temp,ne]
lemma headers_value (r u:ℕ)(fs:List ℕ)(s:State)(high:6005<r)(sl:s.natReg 6004=u)
 (i:ℕ)(hi:i<fs.length):
 (applyBlock (headerOps r fs) s).natReg (r+i)=fs[i]*u:=by
 induction fs generalizing r s i with
 | nil=>simp at hi
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  let t:=Op.apply (.mul r 6005 6004) (Op.apply (.literal 6005 f) s)
  have ts:t.natReg 6004=u:=by simp (disch:=omega) [t,Op.apply,writeNat,next,sl]
  cases i with
  | zero=>
   have keep:=headers_natReg (r+1) fs t r (by omega) (Or.inl (by omega))
   simp only [Nat.add_zero,List.getElem_cons_zero]
   change (applyBlock (headerOps (r+1) fs) t).natReg r=f*u
   rw [keep];simp [t,Op.apply,writeNat,next,sl]
  | succ i=>
   have h:=ih (r+1) t (by omega) ts i (by simp only [List.length_cons] at hi;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
lemma headers_safe (r u:ℕ)(fs:List ℕ)(s:State)(high:6005<r)(sl:s.natReg 6004=u)
 (positive:1≤ u)(small:∀f∈fs,f≤12):
 readable (headerOps r fs) s ∧ peak (headerOps r fs) s≤12*u:=by
 induction fs generalizing r s with
 | nil=>simp [headerOps,readable,peak]
 | cons f fs ih=>
  have fsmall:f≤12:=small f (by simp)
  let t:=Op.apply (.mul r 6005 6004) (Op.apply (.literal 6005 f) s)
  have ts:t.natReg 6004=u:=by simp (disch:=omega) [t,Op.apply,writeNat,next,sl]
  have tail:=ih (r+1) t (by omega) ts (by intro a ha;exact small a (by simp [ha]))
  have lit:f≤12*u:=(fsmall.trans (Nat.le_mul_of_pos_right _ positive))
  have prod:f*u≤12*u:=Nat.mul_le_mul_right u fsmall
  simpa (disch:=omega) [headerOps,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,sl,t] using
   And.intro tail.1 (max_le lit (max_le prod tail.2))
lemma headers_frame (r:ℕ)(fs:List ℕ)(s:State):
 (applyBlock (headerOps r fs) s).natHeap=s.natHeap ∧
 (applyBlock (headerOps r fs) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (headerOps r fs) s).scalarReg=s.scalarReg ∧
 (applyBlock (headerOps r fs) s).outputs=s.outputs ∧
 (applyBlock (headerOps r fs) s).rootOrders=s.rootOrders:=by
 induction fs generalizing r s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons f fs ih=>
  have h:=ih (r+1) (Op.apply (.mul r 6005 6004) (Op.apply (.literal 6005 f) s))
  simpa [headerOps,applyBlock,Op.apply,writeNat,next] using h

/-- Registers6020..6037 follow the actual Addresses field order. -/
def initOps:List Op:=[.literal 6001 2,.add 6000 6000 6001,.literal 6002 1]
def scale (c:A.Constants):ℕ:=100000*(A.fixed c+1)
def scaleOps (c:A.Constants):List Op:=[.literal 6003 (scale c),.mul 6004 6003 6002]
def initPrefix:Program:=[.length 6000]++initOps.map Op.code
def powerPrefix:Program:=initPrefix++(powerOps 19).map Op.code
def scalePrefix (c:A.Constants):Program:=powerPrefix++(scaleOps c).map Op.code
def program (c:A.Constants):Program:=scalePrefix c++(headerOps 6020 factors).map Op.code++[.halt]
lemma factors_length:factors.length=18:=rfl
lemma program_length (c:A.Constants):(program c).length=62:=by
 simp [program,scalePrefix,powerPrefix,initPrefix,initOps,scaleOps,power_length,headers_length,factors_length]
lemma segment_block (pre tail:Program)(ops:List Op)(loc:ℕ)(len:pre.length=loc):
 BlockAt ops (pre++ops.map Op.code++tail) loc:=by
 intro i hi
 rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,len];omega)]
 rw [List.getElem?_append_right (by omega)]
 simp only [len,show loc+i-loc=i by omega,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
lemma init_code (c:A.Constants):BlockAt initOps (program c) 1:=by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma power_code (c:A.Constants):BlockAt (powerOps 19) (program c) 4:=by
 intro i hi;rw [power_length] at hi;interval_cases i <;> rfl
lemma scale_code (c:A.Constants):BlockAt (scaleOps c) (program c) 23:=by
 simpa only [program,scalePrefix,List.append_assoc] using
  segment_block powerPrefix ((headerOps 6020 factors).map Op.code++[.halt]) (scaleOps c) 23 rfl
lemma headers_code (c:A.Constants):BlockAt (headerOps 6020 factors) (program c) 25:=
 segment_block (scalePrefix c) [.halt] (headerOps 6020 factors) 25 rfl
lemma length_code (c:A.Constants):(program c)[0]?=some (.length 6000):=rfl
lemma halt_code (c:A.Constants):(program c)[61]?=some .halt:=rfl

def boot (n:ℕ)(s:State):State:=writeNat s 6000 n
def initialized (n:ℕ)(s:State):State:=applyBlock initOps (boot n s)
def powered (n:ℕ)(s:State):State:=applyBlock (powerOps 19) (initialized n s)
def scaled (c:A.Constants)(n:ℕ)(s:State):State:=applyBlock (scaleOps c) (powered n s)
def result (c:A.Constants)(n:ℕ)(s:State):State:=applyBlock (headerOps 6020 factors) (scaled c n s)
lemma init_values (n:ℕ)(s:State):
 (initialized n s).natReg 6000=n+2 ∧ (initialized n s).natReg 6002=1:=by
 simp [initialized,initOps,applyBlock,boot,Op.apply,writeNat,next]
lemma pow_values (n:ℕ)(s:State):
 (powered n s).natReg 6000=n+2 ∧ (powered n s).natReg 6002=(n+2)^19:=by
 obtain ⟨z,v⟩:=init_values n s
 exact ⟨(power_natReg 19 (initialized n s) 6000 (by decide)).trans z,
  by simpa only [powered,Nat.one_mul] using power_value 19 (n+2) 1 (initialized n s) z v⟩
lemma scaled_value (c:A.Constants)(n:ℕ)(s:State):(scaled c n s).natReg 6004=A.slab c n:=by
 have v:=(pow_values n s).2
 simp [scaled,scaleOps,applyBlock,Op.apply,writeNat,next,v,scale,A.slab]
lemma arithmetic (c:A.Constants)(n:ℕ):
 62≤ A.envelope c n ∧ n+2≤ A.envelope c n ∧ 2≤ A.envelope c n ∧
 (n+2)^19≤ A.envelope c n ∧ scale c≤ A.envelope c n ∧ 12*A.slab c n≤ A.envelope c n:=by
 have zp:1≤ n+2:=by omega
 have pp:1≤(n+2)^19:=by
  have h:0<(n+2)^19:=by positivity
  omega
 have cp:1≤ scale c:=by unfold scale;omega
 have zp':n+2≤(n+2)^19:=by simpa only [Nat.pow_one] using Nat.pow_le_pow_right zp (by decide : 1≤19)
 have pu:(n+2)^19≤ A.slab c n:=by
  change (n+2)^19≤ scale c*(n+2)^19
  calc
   (n+2)^19=1*(n+2)^19:=(Nat.one_mul _).symm
   _≤ scale c*(n+2)^19:=Nat.mul_le_mul_right ((n+2)^19) cp
 have cu:scale c≤ A.slab c n:=by
  change scale c≤ scale c*(n+2)^19
  calc
   scale c=scale c*1:=(Nat.mul_one _).symm
   _≤ scale c*(n+2)^19:=Nat.mul_le_mul_left (scale c) pp
 have huge:100000≤ A.slab c n:=by
  have sc:100000≤ scale c:=by unfold scale;omega
  omega
 dsimp [A.envelope]
 omega

/-- Every emitted address is computed by actual arithmetic on n. The proof
neither changes heaps nor supplies any cache/transform output. -/
theorem execution (c:A.Constants)(n:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(bound:WordBound (A.envelope c n) s):
 BoundedExecution (program c) n x (A.envelope c n) s 62 (result c n s):=by
 obtain ⟨codeB,zB,twoB,powB,scaleB,headersB⟩:=arithmetic c n
 have b0:=writeNat_bound (A.envelope c n) s 6000 n bound (by omega) (by omega)
 have r0:BoundedRuns (program c) n x (A.envelope c n) s 1 (boot n s):=
  .next bound (by simp only [step,pc,length_code];rfl) (.refl b0)
 have ib:readable initOps (boot n s) ∧ peak initOps (boot n s)≤ A.envelope c n:=by
  simp [initOps,readable,peak,Op.readable,Op.peak,Op.apply,boot,writeNat,next];omega
 have ri:=block_runs initOps (program c) 1 n (A.envelope c n) x (boot n s) (init_code c)
  (by simp [boot,writeNat,next,pc]) b0 (by change 1+3≤ A.envelope c n;omega) ib.1 ib.2
 have ipc:(initialized n s).pc=4:=by rw [initialized,applyBlock_pc];simp [boot,initOps,writeNat,next,pc]
 obtain ⟨z,v⟩:=init_values n s
 have pb:=power_safe 19 (n+2) 1 (initialized n s) (by omega) z v
 have pbv:peak (powerOps 19) (initialized n s)≤ A.envelope c n:=by
  have h:peak (powerOps 19) (initialized n s)≤(n+2)^19:=by simpa only [Nat.one_mul] using pb.2
  exact h.trans powB
 have rp:=block_runs (powerOps 19) (program c) 4 n (A.envelope c n) x (initialized n s) (power_code c)
  ipc ri.final_bound (by rw [power_length];omega) pb.1 pbv
 have ppc:(powered n s).pc=23:=by rw [powered,applyBlock_pc,power_length,ipc]
 have pv:=(pow_values n s).2
 have sp:A.slab c n≤ A.envelope c n:=by omega
 have sb:readable (scaleOps c) (powered n s) ∧ peak (scaleOps c) (powered n s)≤ A.envelope c n:=by
  simp [scaleOps,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,pv]
  exact ⟨scaleB,by simpa only [A.slab,scale] using sp⟩
 have rs:=block_runs (scaleOps c) (program c) 23 n (A.envelope c n) x (powered n s) (scale_code c)
  ppc rp.final_bound (by change 23+2≤ A.envelope c n;omega) sb.1 sb.2
 have spc:(scaled c n s).pc=25:=by rw [scaled,applyBlock_pc,ppc];rfl
 have hb:=headers_safe 6020 (A.slab c n) factors (scaled c n s) (by decide) (scaled_value c n s)
  (by have h:=UniformJointAllocation.positive c n;omega) (by intro f hf;norm_num [factors] at hf;omega)
 have rh:=block_runs (headerOps 6020 factors) (program c) 25 n (A.envelope c n) x (scaled c n s)
  (headers_code c) spc rs.final_bound (by rw [headers_length,factors_length];omega) hb.1 (hb.2.trans headersB)
 have rpc:(result c n s).pc=61:=by rw [result,applyBlock_pc,spc,headers_length,factors_length]
 have rr:BoundedRuns (program c) n x (A.envelope c n) s 61 (result c n s):=by
  convert (((r0.trans ri).trans rp).trans rs).trans rh using 1 <;>
   simp [initOps,power_length,scaleOps,headers_length,factors_length,result]
 have done:BoundedExecution (program c) n x (A.envelope c n) (result c n s) 1 (result c n s):=
  .halt rh.final_bound (by simp only [step,rpc,halt_code])
 exact rr.executes done

lemma result_headers (c:A.Constants)(n:ℕ)(s:State)(i:ℕ)(hi:i<18):
 (result c n s).natReg (6020+i)=factors[i]*A.slab c n:=
 headers_value 6020 (A.slab c n) factors (scaled c n s) (by decide) (scaled_value c n s) i hi

attribute [irreducible] initialized powered scaled result

def Changed (j:ℕ):Prop:=j=6000∨j=6001∨j=6002∨j=6003∨j=6004∨j=6005∨(6020≤j∧j<6038)
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
lemma Frame.trans {s t u:State}(a:Frame s t)(b:Frame t u):Frame s u:=
 ⟨b.natHeap.trans a.natHeap,b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,
  b.outputs.trans a.outputs,b.roots.trans a.roots,fun j h=>(b.natReg j h).trans (a.natReg j h)⟩
lemma initialize_frame (n:ℕ)(s:State):Frame s (initialized n s):=by
 rw [initialized]
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj
 simp (disch:=omega) [initOps,applyBlock,Op.apply,boot,writeNat,next]
lemma power_Frame (t:ℕ)(s:State):Frame s (applyBlock (powerOps t) s):=by
 obtain ⟨hn,hs,hr,ho,hroot⟩:=power_frame t s
 exact ⟨hn,hs,hr,ho,hroot,fun j hj=>power_natReg t s j (by unfold Changed at hj;omega)⟩
lemma scale_Frame (c:A.Constants)(s:State):Frame s (applyBlock (scaleOps c) s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj
 simp (disch:=omega) [scaleOps,applyBlock,Op.apply,writeNat,next]
lemma headers_Frame (fs:List ℕ)(s:State)(len:fs.length≤18):Frame s (applyBlock (headerOps 6020 fs) s):=by
 obtain ⟨hn,hs,hr,ho,hroot⟩:=headers_frame 6020 fs s
 refine ⟨hn,hs,hr,ho,hroot,?_⟩
 intro j hj
 exact headers_natReg 6020 fs s j (by unfold Changed at hj;omega) (by unfold Changed at hj;omega)
lemma result_frame (c:A.Constants)(n:ℕ)(s:State):Frame s (result c n s):=by
 have p:Frame (initialized n s) (powered n s):=by simpa only [powered] using power_Frame 19 (initialized n s)
 have q:Frame (powered n s) (scaled c n s):=by simpa only [scaled] using scale_Frame c (powered n s)
 have h:Frame (scaled c n s) (result c n s):=by
  simpa only [result] using headers_Frame factors (scaled c n s) (by rw [factors_length])
 exact ((initialize_frame n s).trans p |>.trans q).trans h

/-- This is the actual bank read through the stable eighteen-register ABI. -/
def observed (s:State):UniformJointAllocation.Addresses:=
 ⟨s.natReg 6020,s.natReg 6021,s.natReg 6022,s.natReg 6023,s.natReg 6024,s.natReg 6025,
  s.natReg 6026,s.natReg 6027,s.natReg 6028,s.natReg 6029,s.natReg 6030,s.natReg 6031,
  s.natReg 6032,s.natReg 6033,s.natReg 6034,s.natReg 6035,s.natReg 6036,s.natReg 6037⟩
lemma observed_eq (s:State)(U:ℕ)(h:∀i,(hi:i<18)→s.natReg (6020+i)=factors[i]*U):
 observed s=⟨U,2*U,3*U,U,4*U,3*U,2*U,4*U,5*U,6*U,5*U,6*U,7*U,8*U,9*U,10*U,11*U,12*U⟩:=by
 have h0:=h 0 (by decide)
 have h1:=h 1 (by decide)
 have h2:=h 2 (by decide)
 have h3:=h 3 (by decide)
 have h4:=h 4 (by decide)
 have h5:=h 5 (by decide)
 have h6:=h 6 (by decide)
 have h7:=h 7 (by decide)
 have h8:=h 8 (by decide)
 have h9:=h 9 (by decide)
 have h10:=h 10 (by decide)
 have h11:=h 11 (by decide)
 have h12:=h 12 (by decide)
 have h13:=h 13 (by decide)
 have h14:=h 14 (by decide)
 have h15:=h 15 (by decide)
 have h16:=h 16 (by decide)
 have h17:=h 17 (by decide)
 norm_num [factors] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
 simp only [observed,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]
lemma output_addresses (c:A.Constants)(n:ℕ)(s:State):observed (result c n s)=A.allocate c n:=
 observed_eq (result c n s) (A.slab c n) (result_headers c n s)
lemma execution_bound_mono {p:Program}{n B C ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (h:BoundedExecution p n x B s ticks u)(bound:B≤C):BoundedExecution p n x C s ticks u:=by
 induction h with
 | halt hb hh=>exact .halt (wordBound_mono bound hb) hh
 | next hb hh tail ih=>exact .next (wordBound_mono bound hb) hh ih

/-- From the real empty state, install exactly the shared layout and stay
inside the single polynomial word envelope; charge the halt too. -/
theorem initial_execution (c:A.Constants)(n:ℕ)(positive:0<n)(x:Fin n→ℂ):∃u,
 BoundedExecution (program c) n x ((n+2)^(UniformJointAllocation.degree c)) initial 62 u ∧
 observed u=A.allocate c n ∧ Frame initial u:=by
 let u:=result c n initial
 have run:=execution c n x initial rfl (initial_wordBound _)
 refine ⟨u,?_,output_addresses c n initial,result_frame c n initial⟩
 exact execution_bound_mono run (UniformJointAllocation.polynomial c positive)

end
end ExactFourierCircuits.UniformJointAllocationMachine
