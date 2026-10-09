import UniformXorTranslationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualNativeTranslationMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformXorTableMachine (Entries)
export UniformXorTranslationMachine (program boot setup move copySetup boot_code setup_code xor_code move_code copySetup_code copy_code branch_at jump_at halt_at)
/- The same literal52 program now acts on a native k-bit prefix inside the
padded q*w-bit arithmetic envelope. There is no padding of the actual array. -/
noncomputable section

def volume (k : ℕ) := 2^k
def partner (_q _w k mask : ℕ) (j : Fin (volume k)) (hm : mask < volume k) : Fin (volume k) :=
 ⟨j.val^^^mask,Nat.xor_lt_two_pow j.isLt hm⟩
lemma partner_involution (q w k mask : ℕ) (hm : mask < volume k) (j : Fin (volume k)) :
 partner q w k mask (partner q w k mask j hm) hm=j := by
 apply Fin.ext
 simp [partner]

def translated (q w k mask : ℕ) (hm : mask < volume k) (f : Fin (volume k)→Scalar) :=
 fun j => f (partner q w k mask j hm)
structure Header (q w k mask A E : ℕ) (s : State) : Prop where
 data : s.natReg 3360=A
 width : s.natReg 3361=w
 volume : s.natReg 3362=volume k
 mask : s.natReg 3363=mask
 buffer : s.natReg 3364=E
 size : s.natReg 3353=2^q
 table : s.natReg 3354=s.natReg 3421
structure Control (q w k mask A E i : ℕ) (s : State) : Prop where
 header : Header q w k mask A E s
 pc : s.pc=2
 index : s.natReg 3365=i
 one : s.natReg 3366=1

def Changed (r : ℕ) := r=0 ∨ r=1 ∨ (1900≤r∧r<1909) ∨
 (3350≤r∧r<3353) ∨ (3355≤r∧r<3360) ∨ r=3365 ∨ r=3366 ∨ (3440≤r∧r<3447)
structure Frame (A E V : ℕ) (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r→ u.natReg r=s.natReg r
 scalarReg : ∀r,r≠100→ r≠114→ u.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,(z < A ∨ A+V≤z)→(z < E ∨ E+V≤z)→ u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (A E V : ℕ) (s : State) : Frame A E V s s :=
 ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.pc {A E V : ℕ} {s u : State} (f : Frame A E V s u) (p : ℕ) : Frame A E V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {A E V : ℕ} {s u t : State} (f : Frame A E V s u) (g : Frame A E V u t) : Frame A E V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h k=>(g.scalarReg r h k).trans (f.scalarReg r h k),
 fun z h k=>(g.scalarHeap z h k).trans (f.scalarHeap z h k)⟩
lemma frame_setup (A E V : ℕ) (s : State) : Frame A E V s (applyBlock setup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed at h
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma frame_xor {A E V : ℕ} {s u : State} (f : UniformBlockXorMachine.Frame s u) : Frame A E V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun r _ _=>congrFun f.scalarReg r,fun z _ _=>congrFun f.scalarHeap z⟩
 intro r h;apply f.natReg r
 unfold Changed UniformBlockXorMachine.Changed at *
 omega
lemma frame_boot (A E V : ℕ) (s : State) : Frame A E V s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed at h
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma header_frame {q w k mask A E : ℕ} {s u : State} (h : Header q w k mask A E s) (f : Frame A E (volume k) s u)
 (size : u.natReg 3353=s.natReg 3353) (table : u.natReg 3354=s.natReg 3354) : Header q w k mask A E u := by
 refine ⟨(f.natReg _ (by unfold Changed;omega)).trans h.data,
 (f.natReg _ (by unfold Changed;omega)).trans h.width,
 (f.natReg _ (by unfold Changed;omega)).trans h.volume,
 (f.natReg _ (by unfold Changed;omega)).trans h.mask,
 (f.natReg _ (by unfold Changed;omega)).trans h.buffer,size.trans h.size,?_⟩
 rw [table,h.table,f.natReg 3421 (by unfold Changed;omega)]

structure Bank (q w k mask A E i : ℕ) (hm : mask < volume k) (f : Fin (volume k)→Scalar) (heap : ℕ→Option Scalar) (s : State) : Prop where
 source : ∀j,s.scalarHeap (A+j.val)=some (f j)
 copied : ∀j,j.val < i→ s.scalarHeap (E+j.val)=some (translated q w k mask hm f j)
 outside : ∀z,(z < E ∨ E+volume k≤z)→ s.scalarHeap z=heap z

lemma iteration (q w k mask A E base i B n : ℕ) (hm : mask < volume k) (x : Fin n→ℂ)
 (f : Fin (volume k)→Scalar) (heap : ℕ→Option Scalar) (s : State)
 (c : Control q w k mask A E i s) (bank : Bank q w k mask A E i hm f heap s)
 (baseHeader : s.natReg 3421=base) (entries : Entries q base (2^q*2^q) s)
 (hi : i < volume k) (separate : A+volume k≤E ∨ E+volume k≤A)
 (hs : WordBound B s) (code : 52≤B) (tableEnd : base+2^q*2^q≤B)
 (extent : E+volume k≤B) (sourceBound:A+volume k≤B)
 (nativeWithin:k≤q*w) (paddedVolume:2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s (17*w+16) u ∧ Control q w k mask A E (i+1) u ∧
 Bank q w k mask A E (i+1) hm f heap u ∧ Frame A E (volume k) s u := by
 let entered:=setPC s 3
 have eb:=changePC_bound B s 3 hs (by omega)
 have br : BoundedRuns program n x B s 1 entered:=.next hs
  (by simp [step,c.pc,branch_at,c.index,c.header.volume,hi,entered,setPC]) (.refl eb)
 have safe : readable setup entered∧peak setup entered≤B := by
  have wb:=hs.2.1 3361
  simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,entered,setPC,c.index,c.header.mask,c.header.width,c.one]
  rw [c.header.width] at wb
  omega
 have prep:=block_runs setup program 3 n B x entered setup_code rfl eb (by change 6≤B;omega) safe.1 safe.2
 let ready:=applyBlock setup entered
 let caller:=UniformBlockXorMachine.setPC ready 0
 have cb:=changePC_bound B ready 0 prep.final_bound (by omega)
 have headers : caller.natReg 3350=i ∧ caller.natReg 3351=mask ∧ caller.natReg 3352=w ∧
 caller.natReg 3353=2^q ∧ caller.natReg 3354=base := by
  simp [caller,ready,setup,applyBlock,Op.apply,writeNat,next,entered,setPC,UniformBlockXorMachine.setPC,
   c.index,c.header.mask,c.header.width,c.one,c.header.size,c.header.table,baseHeader]
 obtain ⟨v,vr,pv,value,fv⟩:=UniformBlockXorMachine.execution q w base i mask B n x caller rfl
  headers.1 headers.2.1 headers.2.2.1 headers.2.2.2.1 headers.2.2.2.2
  (hi.trans_le (Nat.pow_le_pow_right (by omega) nativeWithin))
  (hm.trans_le (Nat.pow_le_pow_right (by omega) nativeWithin)) entries cb (by omega) tableEnd paddedVolume
 have placed:=UniformBoundedAssembly.boundedExecution_placed xor_code (by change 6+22≤B;omega) (by omega) vr
 have same : UniformAssembly.placed 6 caller=ready := by
  simp [UniformAssembly.placed,caller,ready,setup,applyBlock,Op.apply,writeNat,next,entered,setPC,UniformBlockXorMachine.setPC]
 rw [same] at placed
 let ret:=setPC v 28
 have fr : Frame A E (volume k) s ret:=((Frame.refl A E (volume k) s).pc 3 |>.trans (frame_setup A E (volume k) entered))
  |>.pc 0 |>.trans (frame_xor fv) |>.pc 28
 have keep (r : ℕ) (h : r < 3350 ∨ 3353≤r∧r<3355 ∨ 3360≤r∧r < 3440 ∨ 3447≤r) : ret.natReg r=s.natReg r := by
  have fvr:=fv.natReg r (by unfold UniformBlockXorMachine.Changed;omega)
  simp (disch:=omega) [ret,setPC,fvr,caller,ready,setup,applyBlock,Op.apply,writeNat,next,entered,UniformBlockXorMachine.setPC]
 have ax : ret.natReg 3357=i^^^mask:=value
 have da : ret.natReg 3360=A:=(keep _ (by omega)).trans c.header.data
 have bi : ret.natReg 3364=E:=(keep _ (by omega)).trans c.header.buffer
 have ix : ret.natReg 3365=i:=(keep _ (by omega)).trans c.index
 have one : ret.natReg 3366=1:=(keep _ (by omega)).trans c.one
 have pi : i^^^mask < volume k:=Nat.xor_lt_two_pow hi hm
 let j : Fin (volume k):=⟨i,hi⟩
 let other:=partner q w k mask j hm
 have rh : ret.scalarHeap=s.scalarHeap := fv.scalarHeap
 have load : ret.scalarHeap (A+(i^^^mask))=some (f other) := by
  rw [rh]
  exact bank.source other
 have moveSafe : readable move ret∧peak move ret≤B := by
  simp [move,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,writeScalar,next,da,bi,ix,one,ax,load]
  omega
 have moved:=block_runs move program 28 n B x ret move_code rfl placed.final_bound (by change 33≤B;omega) moveSafe.1 moveSafe.2
 let out:=applyBlock move ret
 let u:=setPC out 2
 have ub:=changePC_bound B out 2 moved.final_bound (by omega)
 have jumped : BoundedRuns program n x B out 1 u:=.next moved.final_bound
  (by simp [step,out,move,applyBlock,Op.apply,writeNat,writeScalar,next,ret,setPC,jump_at,u]) (.refl ub)
 have oldload : s.scalarHeap (A+(i^^^mask))=some (f other) := by rw [←rh];exact load
 have oh : u.scalarHeap=Function.update s.scalarHeap (E+i) (some (f other)) := by
  simp [u,setPC,out,move,applyBlock,Op.apply,writeNat,writeScalar,next,da,bi,ix,one,ax,rh,oldload]
 have fmove : Frame A E (volume k) ret u := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · intro r h;unfold Changed at h
    simp (disch:=omega) [u,setPC,out,move,applyBlock,Op.apply,writeNat,writeScalar,next]
  · intro r h k
    simp (disch:=omega) [u,setPC,out,move,applyBlock,Op.apply,writeNat,writeScalar,next]
  · intro z h k
    simp [u,setPC,out,move,applyBlock,Op.apply,writeNat,writeScalar,next,bi,ix,show z≠E+i by omega]
 have ctrl : Control q w k mask A E (i+1) u := by
  refine ⟨?_,rfl,?_,?_⟩
  · have ff:=fr.trans fmove
    exact header_frame c.header ff (ff.natReg _ (by unfold Changed;omega)) (ff.natReg _ (by unfold Changed;omega))
  · simp [u,setPC,out,move,applyBlock,Op.apply,writeNat,writeScalar,next,ix,one]
  · exact one
 have bout : Bank q w k mask A E (i+1) hm f heap u := by
  constructor
  · intro k
    rw [oh,Function.update_of_ne (by have hk:=k.isLt;omega)]
    exact bank.source k
  · intro k hk
    rw [oh]
    by_cases eq : k.val=i
    · have kj : k=j:=Fin.ext eq
      subst k
      simp [other,j,translated]
    · rw [Function.update_of_ne (by omega)]
      exact bank.copied k (by omega)
  · intro z hz
    rw [oh,Function.update_of_ne (by omega)]
    exact bank.outside z hz
 refine ⟨u,?_,ctrl,bout,fr.trans fmove⟩
 convert br.trans (prep.trans (placed.trans (moved.trans jumped))) using 1
 simp only [setup,move,List.length_cons,List.length_nil]
 omega
lemma fill_execution (q w k mask A E base i fuel B n : ℕ) (hm : mask < volume k) (x : Fin n→ℂ)
 (f : Fin (volume k)→Scalar) (heap : ℕ→Option Scalar) (s : State)
 (c : Control q w k mask A E i s) (bank : Bank q w k mask A E i hm f heap s)
 (baseHeader : s.natReg 3421=base) (entries : Entries q base (2^q*2^q) s)
 (total : i+fuel=volume k) (separate : A+volume k≤E ∨ E+volume k≤A)
 (hs : WordBound B s) (code : 52≤B) (tableEnd : base+2^q*2^q≤B)
 (extent : E+volume k≤B) (sourceBound:A+volume k≤B)
 (nativeWithin:k≤q*w) (paddedVolume:2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s ((17*w+16)*fuel+1) u ∧ u.pc=34 ∧
 Bank q w k mask A E (volume k) hm f heap u ∧ Frame A E (volume k) s u ∧
 Header q w k mask A E u ∧ u.natReg 3366=1 := by
 induction fuel generalizing i s with
 | zero =>
   have eq : i=volume k := by omega
   let u := setPC s 34
   have ub:=changePC_bound B s 34 hs (by omega)
   refine ⟨u,.next hs ?_ (.refl ub),rfl,?_,(Frame.refl A E (volume k) s).pc 34,⟨c.header.data,c.header.width,c.header.volume,c.header.mask,c.header.buffer,c.header.size,c.header.table⟩,c.one⟩
   · simp [step,c.pc,branch_at,c.index,c.header.volume,eq,u,setPC]
   · constructor
     · exact bank.source
     · intro j hj;exact bank.copied j (by omega)
     · exact bank.outside
 | succ fuel ih =>
   obtain ⟨v,rv,cv,bv,fv⟩:=iteration q w k mask A E base i B n hm x f heap s c bank baseHeader entries
    (by omega) separate hs code tableEnd extent sourceBound nativeWithin paddedVolume
   have bh : v.natReg 3421=base := (fv.natReg _ (by unfold Changed;omega)).trans baseHeader
   have ev : Entries q base (2^q*2^q) v := by simpa only [Entries,fv.natHeap] using entries
   obtain ⟨u,ru,pu,bu,fu,hu,one⟩:=ih (i+1) v cv bv bh ev (by omega) rv.final_bound
   refine ⟨u,?_,pu,bu,fv.trans fu,hu,one⟩
   convert rv.trans ru using 1
   ring

lemma frame_copySetup (A E V : ℕ) (s : State) : Frame A E V s (applyBlock copySetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed at h
 simp (disch:=omega) [copySetup,applyBlock,Op.apply,writeNat,next]

/-- A real physical array is translated in place. Every Scalar is copied
including its dependency flag; the buffer is ordinary fresh workspace. -/
theorem execution (q w k mask A E base B n : ℕ) (hm : mask < volume k) (x : Fin n→ℂ)
 (f : Fin (volume k)→Scalar) (s : State) (pc : s.pc=0)
 (h : Header q w k mask A E s) (data : ∀j,s.scalarHeap (A+j.val)=some (f j))
 (baseHeader : s.natReg 3421=base) (entries : Entries q base (2^q*2^q) s)
 (separate : A+volume k≤E ∨ E+volume k≤A) (hs : WordBound B s) (code : 52≤B)
 (tableEnd : base+2^q*2^q≤B) (extent : E+volume k≤B) (sourceBound:A+volume k≤B)
 (nativeWithin:k≤q*w) (paddedVolume:2^(q*w)≤B) : ∃u,
 BoundedExecution program n x B s ((17*w+25)*volume k+13) u ∧ u.pc=51 ∧
 (∀j,u.scalarHeap (A+j.val)=some (translated q w k mask hm f j)) ∧
 Frame A E (volume k) s u ∧ Header q w k mask A E u := by
 have start:=block_runs boot program 0 n B x s boot_code pc hs (by change 2≤B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let v:=applyBlock boot s
 have hv : Header q w k mask A E v := by
  cases h
  constructor <;> simp_all [v,boot,applyBlock,Op.apply,writeNat,next]
 have cv : Control q w k mask A E 0 v := by
  refine ⟨hv,?_,?_,?_⟩
  all_goals simp [v,boot,applyBlock,Op.apply,writeNat,next,pc]
 have bv : Bank q w k mask A E 0 hm f s.scalarHeap v :=
  ⟨data,fun _ hk=>by omega,fun _ _=>rfl⟩
 obtain ⟨t,fill,pt,bt,ft,ht,one⟩:=fill_execution q w k mask A E base 0 (volume k) B n hm x f s.scalarHeap v cv bv
  baseHeader entries (by omega) separate start.final_bound code tableEnd extent sourceBound nativeWithin paddedVolume
 have copySafe : readable copySetup t∧peak copySetup t≤B := by
  simp [copySetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,ht.data,ht.buffer,ht.volume,one]
  omega
 have prep:=block_runs copySetup program 34 n B x t copySetup_code pt fill.final_bound
  (by change 39≤B;omega) copySafe.1 copySafe.2
 let ready:=applyBlock copySetup t
 let caller:=setPC ready 0
 have cb:=changePC_bound B ready 0 prep.final_bound (by omega)
 have hdr : UniformTensorFiberCopyMachine.Header (volume k) E A 1 1 caller := by
  constructor <;> simp [caller,setPC,ready,copySetup,applyBlock,Op.apply,writeNat,next,ht.data,ht.buffer,ht.volume,one]
 have src : UniformTensorFiberCopyMachine.Source (volume k) E 1 caller.scalarHeap := by
  intro j hj
  refine ⟨translated q w k mask hm f ⟨j,hj⟩,?_⟩
  change t.scalarHeap (E+j*1)=some _
  simpa using bt.copied ⟨j,hj⟩ hj
 have sep : ∀i,i < volume k→∀j,j < volume k→E+i*1≠A+j*1 := by
  intro i hi j hj
  omega
 obtain ⟨u,copy,pu,values,outside,fu⟩:=UniformTensorFiberCopyMachine.execution n B (volume k) E A 1 1 x caller
  hdr (by omega) src sep (by simpa using extent) (by simpa using sourceBound)
  (by omega) rfl cb
 have placed:=UniformBoundedAssembly.boundedExecution_placed copy_code (by change 39+12≤B;omega) (by omega) copy
 have same : UniformAssembly.placed 39 caller=ready := by
  simp [UniformAssembly.placed,caller,setPC,ready,copySetup,applyBlock,Op.apply,writeNat,next,pt]
 rw [same] at placed
 let result:=setPC u 51
 have rb:=changePC_bound B u 51 copy.final_bound (by omega)
 have halt : BoundedExecution program n x B result 1 result:=.halt rb (by simp [step,result,setPC,halt_at])
 have fc : Frame A E (volume k) caller result := by
  refine ⟨fu.natHeap,fu.outputs,fu.roots,?_,?_,?_⟩
  · intro r hr
    exact fu.natReg r (by unfold Changed at hr;omega)
  · intro r h100 _
    exact fu.scalarReg r h100
  · intro z hA _
    exact outside z (by intro j hj;omega)
 have ff : Frame A E (volume k) s result :=
  (frame_boot A E (volume k) s).trans ft |>.trans (frame_copySetup A E (volume k) t) |>.pc 0 |>.trans fc
 have finalValues : ∀j,result.scalarHeap (A+j.val)=some (translated q w k mask hm f j) := by
  intro j
  have hv:=values j.val j.isLt
  rw [show caller.scalarHeap=t.scalarHeap by rfl] at hv
  simpa [result,setPC,bt.copied j j.isLt] using hv
 have finalHeader:=header_frame h ff (ff.natReg _ (by unfold Changed;omega)) (ff.natReg _ (by unfold Changed;omega))
 refine ⟨result,?_,rfl,finalValues,ff,finalHeader⟩
 convert start.trans (fill.trans (prep.trans placed)) |>.executes halt using 1
 simp only [boot,copySetup,List.length_cons,List.length_nil]
 ring
end
end ExactFourierCircuits.UniformResidualNativeTranslationMachine

