import UniformFixedNetworkShearChildMachine
import UniformBinaryTensorCMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkChildDispatchMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed)
/-- Charge q*width and every binary volume update from physical header fields. -/
def volumeBoot : List Op := [.mul 3302 2852 2853,.literal 3303 0,.literal 3304 1,.literal 3305 1,.literal 3306 2]
def volumeProgram : Program := volumeBoot.map Op.code++
 [.branchLT 3303 3302 6 9,.natBinary .mul 3304 3304 3306,.natBinary .add 3303 3303 3305,.jump 5,.halt]
lemma volumeProgram_length : volumeProgram.length=10 := rfl
lemma volumeBoot_code : BlockAt volumeBoot volumeProgram 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma volume_code (j:ℕ) (hj:j<5) : volumeProgram[5+j]?=
 ([.branchLT 3303 3302 6 9,.natBinary .mul 3304 3304 3306,.natBinary .add 3303 3303 3305,.jump 5,.halt]:Program)[j]? := by
 interval_cases j <;> rfl

def scalarSetup : List Op := [.add 2900 3300 2866,.add 2901 3304 2866]
def scalarReturn : List Op := [.add 2850 2865 2866]
def scalarProgram : Program := UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++
 volumeProgram.map (relocate 52 62)++scalarSetup.map Op.code++
 UniformFixedNetworkShearChildMachine.program.map (relocate 64 104)++scalarReturn.map Op.code++[.halt]
lemma scalarProgram_length : scalarProgram.length=106 := rfl
lemma reader_code : CodeAt UniformFixedNetworkOpcodeMachine.headProgram scalarProgram 0 52 := by
 intro i hi;change i<52 at hi;interval_cases i <;> rfl
lemma scalar_volume_code : CodeAt volumeProgram scalarProgram 52 62 := by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma scalarSetup_code : BlockAt scalarSetup scalarProgram 62 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma scalar_child_code : CodeAt UniformFixedNetworkShearChildMachine.program scalarProgram 64 104 := by
 intro i hi;change i<40 at hi;interval_cases i <;> rfl
lemma scalarReturn_code : BlockAt scalarReturn scalarProgram 104 := by
 intro i hi;change i<1 at hi;interval_cases i;rfl
lemma scalar_halt : scalarProgram[105]?=some .halt := rfl

def shearRecord {R:ℕ} (q w:ℕ) (d source:Fin R) (k:Fin 5) : Record := ⟨1,q,w,d.val,source.val,0,0,k.val,[]⟩
lemma shearRecord_good {R:ℕ} (q w:ℕ) (d source:Fin R) (k:Fin 5) :
 UniformFixedNetworkOpcodeMachine.WellFormed (shearRecord q w d source k) := by
 norm_num [shearRecord,UniformFixedNetworkOpcodeMachine.WellFormed,UniformFixedNetworkOpcodeMachine.bodyLength]
lemma shearRecord_length {R:ℕ} (q w:ℕ) (d source:Fin R) (k:Fin 5) : (shearRecord q w d source k).data.length=8 := rfl

noncomputable section
structure VolumeHeader (k i:ℕ) (s:State) : Prop where
 pc:s.pc=5
 bits:s.natReg 3302=k
 index:s.natReg 3303=i
 volume:s.natReg 3304=2^i
 one:s.natReg 3305=1
 two:s.natReg 3306=2
structure VolumeFrame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,r<3302∨3307≤r→u.natReg r=s.natReg r
lemma VolumeFrame.refl (s:State) : VolumeFrame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma VolumeFrame.pc {s u:State} (f:VolumeFrame s u) (p:ℕ) : VolumeFrame s (setPC u p) :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma VolumeFrame.trans {s u v:State} (f:VolumeFrame s u) (g:VolumeFrame u v) : VolumeFrame s v :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
 g.outputs.trans f.outputs,g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma volumeBoot_frame (s:State) : VolumeFrame s (applyBlock volumeBoot s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r hr;simp (disch:=omega) [volumeBoot,applyBlock,Op.apply,writeNat,next]
lemma volumeBoot_header (q w:ℕ) (s:State) (pc:s.pc=0) (hq:s.natReg 2852=q) (hw:s.natReg 2853=w) :
 VolumeHeader (q*w) 0 (applyBlock volumeBoot s) := by
 constructor <;> simp [volumeBoot,applyBlock,Op.apply,writeNat,next,pc,hq,hw]
def volumeAdvance (i:ℕ) (s:State) : State := setPC (writeNat (writeNat (setPC s 6) 3304 (2^(i+1))) 3303 (i+1)) 5
lemma volumeAdvance_frame (i:ℕ) (s:State) : VolumeFrame s (volumeAdvance i s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r hr;simp (disch:=omega) [volumeAdvance,setPC,writeNat,next]
lemma volumeAdvance_header (k i:ℕ) (s:State) (h:VolumeHeader k i s) : VolumeHeader k (i+1) (volumeAdvance i s) := by
 rcases h with ⟨pc,bits,index,volume,one,two⟩
 constructor <;> simp [volumeAdvance,setPC,writeNat,next,bits,one,two]
lemma volume_round (k i B n:ℕ) (x:Fin n→ℂ) (s:State) (h:VolumeHeader k i s)
 (hi:i<k) (hs:WordBound B s) (vbound:2^k≤B) (code:10≤B) : BoundedRuns volumeProgram n x B s 4 (volumeAdvance i s) := by
 have pbound:2^(i+1)≤B:=(pow_le_pow_right₀ (by decide:1≤(2:ℕ)) (by omega:i+1≤k)).trans vbound
 have ibound:i+1≤B:=(show i+1<2^(i+1) from Nat.lt_two_pow_self).le.trans pbound
 let e:=setPC s 6
 let v:=writeNat e 3304 (2^(i+1))
 let t:=writeNat v 3303 (i+1)
 have b0:=changePC_bound B s 6 hs (by omega)
 have b1:=writeNat_bound B e 3304 (2^(i+1)) b0 (by change 7≤B;omega) pbound
 have b2:=writeNat_bound B v 3303 (i+1) b1 (by change 8≤B;omega) ibound
 have b3:=changePC_bound B t 5 b2 (by omega)
 refine .next hs ?_ (.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.refl b3))))
 · simp [step,h.pc,volumeProgram,volumeBoot,h.index,h.bits,hi]
 · simp [step,e,setPC,volumeProgram,volumeBoot,evalNat,writeNat,next,h.volume,h.two,Nat.pow_succ]
 · simp [step,v,e,setPC,volumeProgram,volumeBoot,evalNat,writeNat,next,h.index,h.one]
 · simp [step,v,e,setPC,volumeProgram,volumeBoot,writeNat,next,volumeAdvance]
lemma volume_loop (k B n count:ℕ) (x:Fin n→ℂ) (vbound:2^k≤B) (code:10≤B) :
 ∀i s,i+count=k→VolumeHeader k i s→WordBound B s→∃u,
 BoundedExecution volumeProgram n x B s (4*count+2) u ∧ u.natReg 3302=k ∧ u.natReg 3304=2^k ∧ VolumeFrame s u ∧ u.natReg 3305=1 := by
 induction count with
 | zero=>
   intro i s eq h hs
   have ik:i=k:=by omega
   subst i
   let u:=setPC s 9
   have bu:=changePC_bound B s 9 hs (by omega)
   refine ⟨u,.next hs ?_ (.halt bu ?_),h.bits,h.volume,(VolumeFrame.refl s).pc 9,h.one⟩
   · simp [step,h.pc,volumeProgram,volumeBoot,h.index,h.bits,u,setPC]
   · simp [step,u,setPC,volumeProgram,volumeBoot]
 | succ count ih=>
   intro i s eq h hs
   have hi:i<k:=by omega
   have round:=volume_round k i B n x s h hi hs vbound code
   obtain ⟨u,tail,bits,vol,fr,one⟩:=ih (i+1) (volumeAdvance i s) (by omega) (volumeAdvance_header k i s h) round.final_bound
   refine ⟨u,?_,bits,vol,(volumeAdvance_frame i s).trans fr,one⟩
   convert round.executes tail using 1;ring
/-- Derive q*width and volume from actual loaded header registers. -/
theorem volume_execution (q w B n:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=0) (hq:s.natReg 2852=q) (hw:s.natReg 2853=w)
 (hs:WordBound B s) (vbound:2^(q*w)≤B) (code:10≤B) : ∃u,
 BoundedExecution volumeProgram n x B s (4*(q*w)+7) u ∧ u.natReg 3302=q*w ∧ u.natReg 3304=2^(q*w) ∧ VolumeFrame s u ∧ u.natReg 3305=1 := by
 have kbound:q*w≤B:=(show q*w<2^(q*w) from Nat.lt_two_pow_self).le.trans vbound
 have safe:readable volumeBoot s ∧ peak volumeBoot s≤B:=by
   simp [volumeBoot,readable,peak,Op.readable,Op.peak,hq,hw];omega
 have boot:=block_runs volumeBoot volumeProgram 0 n B x s volumeBoot_code pc hs (by change 5≤B;omega) safe.1 safe.2
 obtain ⟨u,tail,bits,vol,fr,one⟩:=volume_loop (q*w) B n (q*w) x vbound code 0
   (applyBlock volumeBoot s) (by omega) (volumeBoot_header q w s pc hq hw) boot.final_bound
 refine ⟨u,?_,bits,vol,(volumeBoot_frame s).trans fr,one⟩
 convert boot.executes tail using 1;change 4*(q*w)+7=5+(4*(q*w)+2);ring

/-- Only the actual interpreter/volume/child scratch registers may change. -/
def ScalarChanged (r:ℕ) : Prop := (2850≤r∧r<2877)∨(2900≤r∧r<2917)∨(3302≤r∧r<3307)
structure ScalarFrame (D V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬ScalarChanged r→u.natReg r=s.natReg r
 scalarReg:∀ r : ℕ, r ≠ 100 → r ≠ 101 → r ≠ 102 → r ≠ 104 → u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<D∨D+V≤z→u.scalarHeap z=s.scalarHeap z
lemma ScalarFrame.trans {D V:ℕ} {s u t:State} (f:ScalarFrame D V s u) (g:ScalarFrame D V u t) : ScalarFrame D V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),
 fun r a b c d=>(g.scalarReg r a b c d).trans (f.scalarReg r a b c d),
 fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma ScalarFrame.pc {D V:ℕ} {s u:State} (f:ScalarFrame D V s u) (p:ℕ) : ScalarFrame D V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma ScalarFrame.reader (D V:ℕ) {s u:State} (f:UniformFixedNetworkOpcodeMachine.Frame s u) : ScalarFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun _ _ _ _ _=>congrFun f.scalarReg _,fun _ _=>congrFun f.scalarHeap _⟩
 intro r h;apply f.natReg;unfold ScalarChanged at h;omega
lemma ScalarFrame.volume (D V:ℕ) {s u:State} (f:VolumeFrame s u) : ScalarFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun _ _ _ _ _=>congrFun f.scalarReg _,fun _ _=>congrFun f.scalarHeap _⟩
 intro r h;apply f.natReg;unfold ScalarChanged at h;omega
lemma ScalarFrame.child {D V:ℕ} {s u:State} (f:UniformFixedNetworkShearChildMachine.Frame D V s u) : ScalarFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,f.scalarHeap⟩
 intro r h;apply f.natReg;unfold ScalarChanged at h;omega
lemma scalarSetup_frame (D V:ℕ) (s:State) : ScalarFrame D V s (applyBlock scalarSetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold ScalarChanged at h;simp (disch:=omega) [scalarSetup,applyBlock,Op.apply,writeNat,next]
lemma scalarReturn_frame (D V:ℕ) (s:State) : ScalarFrame D V s (applyBlock scalarReturn s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold ScalarChanged at h;simp (disch:=omega) [scalarReturn,applyBlock,Op.apply,writeNat,next]

/-- Continuous printed scalar record → real header reads → charged binary
volume computation → coefficient decode and array update → cursor return.
There are no supplied Fields, volume headers, coefficient banks or actions. -/
theorem scalar_execution {R:ℕ} (q w A T B n:ℕ) (x:Fin n→ℂ)
 (d source:Fin R) (ne:d≠source) (k:Fin 5)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State)
 (pc:s.pc=0) (ptr:s.natReg 2850=T) (base:s.natReg 3300=A)
 (bank:Printed T (shearRecord q w d source k).data s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (hs:WordBound B s) (code:106≤B) (tableEnd:T+8≤B) (width:w+1≤B)
 (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedExecution scalarProgram n x B s (10*2^(q*w)+4*(q*w)+k.val+62) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w))
  (UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode k) f) u ∧
 u.natReg 2850=T+8 ∧
 ScalarFrame (UniformFixedNetworkShearChildMachine.roleBase A (2^(q*w)) d.val) (2^(q*w)) s u := by
 let V:=2^(q*w)
 let D:=UniformFixedNetworkShearChildMachine.roleBase A V d.val
 change A+R*V≤B at extent
 have vbound:V≤B:=by
   have h:=Nat.mul_le_mul_right V (show 1≤R by have h:=d.isLt;omega)
   simp only [Nat.one_mul] at h;omega
 obtain ⟨read,reader,fields,body,nextptr,rf⟩:=UniformFixedNetworkOpcodeMachine.head_execution T B n
   (shearRecord q w d source k) x s ptr pc hs bank (shearRecord_good q w d source k)
   (by simpa [shearRecord_length] using tableEnd) width (by omega)
 have rrun:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 52≤B;omega) (by omega) reader
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at rrun
 let ve:=setPC read 0
 have vbe:WordBound B ve:=changePC_bound B _ 0 reader.final_bound (by omega)
 obtain ⟨vol,vr,bits,volume,vf,_vone⟩:=volume_execution q w B n x ve rfl
   (by simpa [ve,setPC,shearRecord] using fields.columns)
   (by simpa [ve,setPC,shearRecord] using fields.width) vbe vbound (by omega)
 have vrun:=UniformBoundedAssembly.boundedExecution_placed scalar_volume_code (by change 62≤B;omega) (by omega) vr
 have entry:placed 52 ve=setPC read 52:=rfl
 rw [entry] at vrun
 let vs:=setPC vol 62
 have vb:vs.natReg 3300=A:=by
   change vol.natReg 3300=A
   rw [vf.natReg 3300 (by omega)]
   change read.natReg 3300=A
   rw [rf.natReg 3300 (by omega)];exact base
 have vz:vs.natReg 2866=0:=by
   change vol.natReg 2866=0
   rw [vf.natReg 2866 (by omega)]
   simpa [ve,setPC,shearRecord] using fields.zero
 have vv:vs.natReg 3304=V:=volume
 have setupSafe:readable scalarSetup vs ∧ peak scalarSetup vs≤B:=by
   simp [scalarSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,vb,vz,vv];omega
 have setup:=block_runs scalarSetup scalarProgram 62 n B x vs scalarSetup_code rfl vrun.final_bound
   (by change 64≤B;omega) setupSafe.1 setupSafe.2
 let ready:=applyBlock scalarSetup vs
 let ce:=setPC ready 0
 have cb:WordBound B ce:=changePC_bound B _ 0 setup.final_bound (by omega)
 have cd:ce.natReg 2854=d.val:=by
   simp only [ce,ready,scalarSetup,applyBlock,Op.apply,setPC,writeNat,next,Function.update_of_ne (by decide:2854≠2900),Function.update_of_ne (by decide:2854≠2901)]
   change vol.natReg 2854=d.val
   rw [vf.natReg 2854 (by omega)]
   simpa [ve,setPC,shearRecord] using fields.dest
 have cs:ce.natReg 2855=source.val:=by
   change vol.natReg 2855=source.val
   rw [vf.natReg 2855 (by omega)]
   simpa [ve,setPC,shearRecord] using fields.source
 have ck:ce.natReg 2858=k.val:=by
   change vol.natReg 2858=k.val
   rw [vf.natReg 2858 (by omega)]
   simpa [ve,setPC,shearRecord] using fields.scalar
 have present:UniformFixedNetworkShearChildMachine.Present A R V f ce:=by
   intro r j;change vol.scalarHeap (A+r.val*V+j.val)=_
   rw [vf.scalarHeap];change read.scalarHeap (A+r.val*V+j.val)=_
   rw [rf.scalarHeap];exact data r j
 obtain ⟨child,cr,output,cf⟩:=UniformFixedNetworkShearChildMachine.execution A B n x d source ne k f ce rfl
   (by simp [ce,ready,scalarSetup,applyBlock,Op.apply,setPC,writeNat,next,vb,vz])
   (by simp [ce,ready,scalarSetup,applyBlock,Op.apply,setPC,writeNat,next,vv,vz,V]) cd cs ck present cb (by omega) extent
 have crun:=UniformBoundedAssembly.boundedExecution_placed scalar_child_code (by change 104≤B;omega) (by omega) cr
 have centry:placed 64 ce=ready:=by
   simp [placed,ce,ready,scalarSetup,applyBlock,Op.apply,writeNat,next,vs,setPC]
 rw [centry] at crun
 let ret:=setPC child 104
 have rz:ret.natReg 2866=0:=by
   change child.natReg 2866=0;rw [cf.natReg 2866 (by omega)]
   change vol.natReg 2866=0;exact vz
 have rn:ret.natReg 2865=T+8:=by
   change child.natReg 2865=T+8;rw [cf.natReg 2865 (by omega)]
   change vol.natReg 2865=T+8;rw [vf.natReg 2865 (by omega)]
   simpa [ve,setPC,shearRecord_length] using nextptr
 have returnSafe:readable scalarReturn ret ∧ peak scalarReturn ret≤B:=by
   simp [scalarReturn,readable,peak,Op.readable,Op.peak,rn,rz];omega
 have tail:=block_runs scalarReturn scalarProgram 104 n B x ret scalarReturn_code rfl crun.final_bound
   (by change 105≤B;omega) returnSafe.1 returnSafe.2
 let u:=applyBlock scalarReturn ret
 have up:u.pc=105:=rfl
 have last:BoundedExecution scalarProgram n x B u 1 u:=.halt tail.final_bound (by simp [step,up,scalar_halt])
 have total:ScalarFrame D V s u:=
   (((ScalarFrame.reader D V rf).pc 0).trans (ScalarFrame.volume D V vf) |>.pc 62 |>.trans (scalarSetup_frame D V vs) |>.pc 0)
   |>.trans (ScalarFrame.child cf) |>.pc 104 |>.trans (scalarReturn_frame D V ret)
 refine ⟨u,?_,output,?_,total⟩
 · have all:=rrun.executes (vrun.executes (setup.executes (crun.executes (tail.executes last))))
   convert all using 1
   norm_num [UniformFixedNetworkOpcodeMachine.headCost,shearRecord,scalarSetup,scalarReturn]
   omega
 · simp [u,scalarReturn,applyBlock,Op.apply,writeNat,next,rn,rz]

end
end ExactFourierCircuits.UniformFixedNetworkChildDispatchMachine
