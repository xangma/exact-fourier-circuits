import UniformSelectedAxisFiberPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllTensorFibersCopyMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformInitialPreparation (ell len)
open UniformPermutationInversePreparation (Metadata)
namespace S
abbrev Parameters := UniformSelectedAxisFiberPreparation.Parameters
end S
open UniformSelectedAxisFiberPreparation (lower upper radices selected_positive selected_product)

/-- Initialize the fiber ordinal once. All other entries are ordinary axis/A/D arguments. -/
def tail : Program := [.natBinary .add 1911 1911 1915,.natBinary .add 1913 1913 1923,
 .natBinary .mul 1952 70 72,.branchLT 1911 1952 19 54,.halt]
def program (scatter:Bool) : Program := embed [.natLiteral 1911 0]
 (UniformSelectedAxisFiberPreparation.program scatter) tail 50

theorem program_length (scatter:Bool) : (program scatter).length=55 := by
 rw [program,embed_length,UniformSelectedAxisFiberPreparation.program_length];rfl
theorem selected_code (scatter:Bool) : CodeAt (UniformSelectedAxisFiberPreparation.program scatter)
 (program scatter) 1 50 := embed_code _ _ _ _
theorem decoder_code (scatter:Bool) : CodeAt UniformTensorAddressMachine.program (program scatter) 24 31 := by
 intro k hk;rw [UniformTensorAddressMachine.program_length] at hk
 interval_cases k <;> cases scatter <;> rfl
theorem copy_code (scatter:Bool) : CodeAt UniformTensorFiberCopyMachine.program (program scatter) 37 49 := by
 intro k hk;rw [UniformTensorFiberCopyMachine.program_length] at hk
 interval_cases k <;> cases scatter <;> rfl
theorem jump_at (scatter:Bool) : (program scatter)[49]?=some (.jump 50) := by cases scatter <;> rfl
theorem branch_at (scatter:Bool) : (program scatter)[53]?=some (.branchLT 1911 1952 19 54) := by cases scatter <;> rfl
theorem halt_at (scatter:Bool) : (program scatter)[54]?=some .halt := by cases scatter <;> rfl
noncomputable section

/-- Relocate nonhalting segments in the SAME ambient bound, including final PC. -/
theorem runs_placed_same {p q:Program} {base ret n B t:ℕ} {x:Fin n→ℂ}
 (code:CodeAt p q base ret) (hc:base+p.length≤B) {s u:State}
 (run:BoundedRuns p n x B s t u) (hu:base+u.pc≤B) :
 BoundedRuns q n x B (placed base s) t (placed base u) := by
 induction run with
 | refl hb => exact .refl (UniformBoundedAssembly.placed_bound _ _ _ hb hu)
 | next hb step _ ih =>
   exact .next (UniformBoundedAssembly.placed_bound _ _ _ hb (by have:=running_pc step;omega))
     (running_placed code step) (ih hu)

/-- Registers retained during each single-fiber body. -/
def Kept (z:ℕ) : Prop := (z<89∨100≤z) ∧ (z<1900∨1909≤z) ∧ z≠1929
instance (z:ℕ) : Decidable (Kept z) := by unfold Kept;infer_instance
structure LocalFrame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀z,Kept z→u.natReg z=s.natReg z
 scalarReg : ∀z,z≠100→u.scalarReg z=s.scalarReg z

theorem LocalFrame.pc (s:State) (pc:ℕ) : LocalFrame s {s with pc:=pc} := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem LocalFrame.trans {s u v:State} (f:LocalFrame s u) (g:LocalFrame u v) : LocalFrame s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun z hz=>(g.natReg z hz).trans (f.natReg z hz),fun z hz=>(g.scalarReg z hz).trans (f.scalarReg z hz)⟩
theorem LocalFrame.metadata {n:ℕ} {s u:State} (f:LocalFrame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · exact ⟨(f.natReg 100 (by decide)).trans h.saved.nextPrime,
   (f.natReg 101 (by decide)).trans h.saved.inputLength,(f.natReg 102 (by decide)).trans h.saved.count,
   (f.natReg 103 (by decide)).trans h.saved.workingLength,(f.natReg 104 (by decide)).trans h.saved.masterRoot,
   (f.natReg 105 (by decide)).trans h.saved.copyAddress,(f.natReg 106 (by decide)).trans h.saved.copyLength⟩
 · intro a _;exact congrFun f.natHeap _
theorem LocalFrame.parameters {n:ℕ} {i:Fin (ell n+1)} {j a d:ℕ} {s u:State}
 (f:LocalFrame s u) (h:S.Parameters n i j a d s) : S.Parameters n i j a d u := by
 refine ⟨⟨(f.natReg 1910 (by decide)).trans h.args.axis,(f.natReg 1911 (by decide)).trans h.args.fiber,
   (f.natReg 1912 (by decide)).trans h.args.array,(f.natReg 1913 (by decide)).trans h.args.bank⟩,
   f.metadata h.metadata,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals first | exact (f.natReg _ (by decide)).trans h.one | exact (f.natReg _ (by decide)).trans h.zero |
   exact (f.natReg _ (by decide)).trans h.product | exact (f.natReg _ (by decide)).trans h.radix |
   exact (f.natReg _ (by decide)).trans h.quotient | exact (f.natReg _ (by decide)).trans h.p |
   exact (f.natReg _ (by decide)).trans h.r | exact (f.natReg _ (by decide)).trans h.q |
   exact (f.natReg _ (by decide)).trans h.j | exact (f.natReg _ (by decide)).trans h.t

theorem decoder_frame {s u:State} (f:UniformTensorAddressMachine.Frame s u) : LocalFrame s u := by
 refine ⟨f.1,f.2.2.2.1,f.2.2.2.2.1,?_,fun z _=>congrFun f.2.2.1 z⟩
 intro z hz;apply f.2.2.2.2.2;unfold Kept at hz;omega

theorem copySetup_frame (scatter:Bool) (s:State) : LocalFrame s (applyBlock (UniformSelectedAxisFiberPreparation.copySetup scatter) s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro z hz
 simp (disch:=unfold Kept at hz;omega) [applyBlock,UniformSelectedAxisFiberPreparation.copySetup,Op.apply,writeNat,next]

theorem copy_frame {s u:State} (f:UniformTensorFiberCopyMachine.Frame s u) : LocalFrame s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg⟩
 intro z hz;apply f.natReg;unfold Kept at hz;omega

def fibers (n:ℕ) (i:Fin (ell n+1)) := lower n i*upper n i
def native (n:ℕ) (i:Fin (ell n+1)) (j t:ℕ) := UniformTensorAddressMachine.address (lower n i) (radices n i) j t
def packed (n:ℕ) (i:Fin (ell n+1)) (j t:ℕ) := j*radices n i+t

theorem fibers_positive (n:ℕ) (i:Fin (ell n+1)) : 0<fibers n i :=
 Nat.mul_pos (selected_positive n i).1 (selected_positive n i).2.2
theorem fibers_product (n:ℕ) (i:Fin (ell n+1)) : fibers n i*radices n i=len n := by
 unfold fibers;rw [←selected_product n i];ring

theorem coordinate_lt (n:ℕ) (i:Fin (ell n+1)) (j t:ℕ) (hj:j<fibers n i) (ht:t<radices n i) :
 native n i j t<len n ∧ packed n i j t<len n := by
 refine ⟨?_,?_⟩
 · rw [←selected_product n i];exact UniformTensorAddressMachine.address_lt _ _ _ j t hj ht
 · have h:= (finProdFinEquiv (⟨j,hj⟩,⟨t,ht⟩):Fin (fibers n i*radices n i)).isLt
   change t+radices n i*j<fibers n i*radices n i at h
   rw [fibers_product] at h;simpa only [packed,Nat.mul_comm,Nat.add_comm] using h

theorem native_injective (n:ℕ) (i:Fin (ell n+1)) (j t k v:ℕ)
 (hj:j<fibers n i) (ht:t<radices n i) (hk:k<fibers n i) (hv:v<radices n i)
 (eq:native n i j t=native n i k v) : j=k ∧ t=v := by
 have h:= (UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i)).injective
   (show UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i) (⟨j,hj⟩,⟨t,ht⟩)=
     UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i) (⟨k,hk⟩,⟨v,hv⟩) from Fin.ext eq)
 exact ⟨congrArg (fun q=>q.1.val) h,congrArg (fun q=>q.2.val) h⟩
theorem packed_injective (n:ℕ) (i:Fin (ell n+1)) (j t k v:ℕ)
 (hj:j<fibers n i) (ht:t<radices n i) (hk:k<fibers n i) (hv:v<radices n i)
 (eq:packed n i j t=packed n i k v) : j=k ∧ t=v := by
 have h:= (finProdFinEquiv:Fin (fibers n i)×Fin (radices n i)≃Fin (fibers n i*radices n i)).injective
   (show finProdFinEquiv (⟨j,hj⟩,⟨t,ht⟩)=finProdFinEquiv (⟨k,hk⟩,⟨v,hv⟩) from Fin.ext (by simpa [packed,Nat.add_comm,Nat.mul_comm] using eq))
 exact ⟨congrArg (fun q=>q.1.val) h,congrArg (fun q=>q.2.val) h⟩


/-- A single body uses only already computed P/r/Q, never scans the axes. -/
theorem fiber_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:S.Parameters n i j a d s) (hj:j<fibers n i)
 (src:UniformSelectedAxisFiberPreparation.PhysicalSource scatter n i a d s.scalarHeap)
 (sep:a+len n≤d) (ha:a+2*len n≤B) (hd:d+radices n i≤B)
 (hc:55≤B) (hp:s.pc=24) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s (9*radices n i+18) u ∧ u.pc=50 ∧
 (∀t,t<radices n i→u.scalarHeap (UniformSelectedAxisFiberPreparation.toAddress scatter n i j a d+
   t*UniformSelectedAxisFiberPreparation.toStride scatter n i)=s.scalarHeap
   (UniformSelectedAxisFiberPreparation.fromAddress scatter n i j a d+
   t*UniformSelectedAxisFiberPreparation.fromStride scatter n i)) ∧
 UniformTensorFiberCopyMachine.Outside (UniformSelectedAxisFiberPreparation.toAddress scatter n i j a d)
   (UniformSelectedAxisFiberPreparation.toStride scatter n i) (radices n i) s.scalarHeap u ∧
 LocalFrame s u ∧ S.Parameters n i j a d u := by
 let v:State:={s with pc:=0}
 have lb:len n≤B:=by rw [←h.metadata.saved.workingLength];exact hs.2.1 103
 obtain ⟨z,dec,offset,_rng,df,_pc⟩:=UniformTensorAddressMachine.execution n x (lower n i) (radices n i)
   (upper n i) j 0 B v (selected_positive n i).1 hj (selected_positive n i).2.1
   (by rw [selected_product];exact lb) (by omega) rfl h.p h.r h.q h.j h.t
   (changePC_bound B s 0 hs (by omega))
 have drun:=UniformBoundedAssembly.boundedExecution_placed (decoder_code scatter)
   (by rw [UniformTensorAddressMachine.program_length];omega) (by omega) dec
 have eq:placed 24 v=s:=by change {s with pc:=24}=s;rw [←hp]
 rw [eq] at drun
 let w:State:={z with pc:=31}
 have fw:LocalFrame s w:=(LocalFrame.pc s 0).trans ((decoder_frame df).trans (LocalFrame.pc z 31))
 have p31:w.pc=31:=rfl
 have carg:UniformSelectedAxisFiberPreparation.CopyArgs n i j a d w:=by
   have hw:=fw.parameters h
   exact ⟨hw.args,hw.metadata,hw.one,hw.zero,hw.product,hw.radix,offset⟩
 let w0:State:={w with pc:=30}
 have carg0:UniformSelectedAxisFiberPreparation.CopyArgs n i j a d w0:=
   ⟨(UniformSelectedAxisFiberPreparation.PureFrame.pc w 30).args carg.args,
    (UniformSelectedAxisFiberPreparation.PureFrame.pc w 30).metadata carg.metadata,
    carg.one,carg.zero,carg.product,carg.radix,carg.offset⟩
 have setup:=UniformSelectedAxisFiberPreparation.copySetup_execution scatter i j a d B x w0 carg0 hj
   ha hd (by omega) rfl (changePC_bound B w 30 drun.final_bound (by omega))
 have setupPlaced:=runs_placed_same (selected_code scatter) (by rw [UniformSelectedAxisFiberPreparation.program_length];omega)
   setup (by rw [UniformTensorMonomialMachine.applyBlock_pc];cases scatter <;> change 1+(30+6)≤B <;> omega)
 have weq:placed 1 w0=w:=by change {w with pc:=31}=w;rw [←p31]
 rw [weq] at setupPlaced
 let c:State:=placed 1 (applyBlock (UniformSelectedAxisFiberPreparation.copySetup scatter) w0)
 have cpc:c.pc=37:=by simp [c,placed,UniformTensorMonomialMachine.applyBlock_pc,w0,UniformSelectedAxisFiberPreparation.copySetup]
 have fc:LocalFrame s c:=fw.trans ((LocalFrame.pc w 30).trans
   ((copySetup_frame scatter w0).trans (LocalFrame.pc _ 37)))
 have heap:c.scalarHeap=s.scalarHeap:=by
   simpa [c,placed,w0,w,v,applyBlock,UniformSelectedAxisFiberPreparation.copySetup,Op.apply,writeNat,next] using df.2.1
 have header:=UniformSelectedAxisFiberPreparation.copySetup_header scatter i j a d w0 carg0
 have ss:UniformTensorFiberCopyMachine.Source (radices n i)
   (UniformSelectedAxisFiberPreparation.fromAddress scatter n i j a d)
   (UniformSelectedAxisFiberPreparation.fromStride scatter n i) c.scalarHeap:=by
   rw [heap];exact UniformSelectedAxisFiberPreparation.source_from_array scatter n i j a d _ hj src
 have st:=UniformSelectedAxisFiberPreparation.start_bounds n i j hj
 have hab:UniformSelectedAxisFiberPreparation.fromAddress scatter n i j a d+
   radices n i*UniformSelectedAxisFiberPreparation.fromStride scatter n i≤B:=by
   cases scatter <;> simp [UniformSelectedAxisFiberPreparation.fromAddress,UniformSelectedAxisFiberPreparation.fromStride] <;> omega
 have hdb:UniformSelectedAxisFiberPreparation.toAddress scatter n i j a d+
   radices n i*UniformSelectedAxisFiberPreparation.toStride scatter n i≤B:=by
   cases scatter <;> simp [UniformSelectedAxisFiberPreparation.toAddress,UniformSelectedAxisFiberPreparation.toStride] <;> omega
 let c0:State:={c with pc:=0}
 obtain ⟨u,copy,_up,action,outside,cf⟩:=UniformTensorFiberCopyMachine.execution n B (radices n i)
   (UniformSelectedAxisFiberPreparation.fromAddress scatter n i j a d)
   (UniformSelectedAxisFiberPreparation.toAddress scatter n i j a d)
   (UniformSelectedAxisFiberPreparation.fromStride scatter n i) (UniformSelectedAxisFiberPreparation.toStride scatter n i)
   x c0 header.withPC
   (by cases scatter <;> simp [UniformSelectedAxisFiberPreparation.toStride];exact (selected_positive n i).1)
   ss (UniformSelectedAxisFiberPreparation.copy_separate scatter n i j a d hj sep) hab hdb (by omega)
   rfl (changePC_bound B c 0 setupPlaced.final_bound (by omega))
 have copied:=UniformBoundedAssembly.boundedExecution_placed (copy_code scatter)
   (by rw [UniformTensorFiberCopyMachine.program_length];omega) (by omega) copy
 have ceq:placed 37 c0=c:=by change {c with pc:=37}=c;rw [←cpc]
 rw [ceq] at copied
 let u49:State:={u with pc:=49}
 let u50:State:={u with pc:=50}
 have jump:BoundedRuns (program scatter) n x B u49 1 u50:=.next copied.final_bound
   (by simp [step,u49,jump_at,u50]) (.refl (changePC_bound B u 50 copy.final_bound (by omega)))
 have frame:LocalFrame s u50:=fc.trans ((LocalFrame.pc c 0).trans
   ((copy_frame cf).trans (LocalFrame.pc u 50)))
 refine ⟨u50,?_,rfl,?_,?_,frame,frame.parameters h⟩
 · convert drun.trans (setupPlaced.trans (copied.trans jump)) using 1;omega
 · intro t ht;simpa only [u50,c0,heap] using action t ht
 · intro z hz;simpa only [u50,c0,heap] using outside z hz


def targetBase (scatter:Bool) (a d:ℕ) := if scatter then a else d
def sourceBase (scatter:Bool) (a d:ℕ) := if scatter then d else a
def target (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ) :=
 if scatter then a+native n i j t else d+packed n i j t
def source (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ) :=
 if scatter then d+packed n i j t else a+native n i j t

theorem target_row (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ) :
 UniformSelectedAxisFiberPreparation.toAddress scatter n i j a (d+j*radices n i)+
 t*UniformSelectedAxisFiberPreparation.toStride scatter n i=target scatter n i a d j t := by
 cases scatter <;> simp [UniformSelectedAxisFiberPreparation.toAddress,UniformSelectedAxisFiberPreparation.toStride,
 target,packed,native,UniformSelectedAxisFiberPreparation.start,UniformTensorAddressMachine.address] <;> ring
theorem source_row (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ) :
 UniformSelectedAxisFiberPreparation.fromAddress scatter n i j a (d+j*radices n i)+
 t*UniformSelectedAxisFiberPreparation.fromStride scatter n i=source scatter n i a d j t := by
 cases scatter <;> simp [UniformSelectedAxisFiberPreparation.fromAddress,UniformSelectedAxisFiberPreparation.fromStride,
 source,packed,native,UniformSelectedAxisFiberPreparation.start,UniformTensorAddressMachine.address] <;> ring

theorem target_range (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ)
 (hj:j<fibers n i) (ht:t<radices n i) :
 targetBase scatter a d≤target scatter n i a d j t ∧
 target scatter n i a d j t<targetBase scatter a d+len n := by
 have h:=coordinate_lt n i j t hj ht
 cases scatter <;> simp [targetBase,target] <;> omega

theorem target_injective (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t k v:ℕ)
 (hj:j<fibers n i) (ht:t<radices n i) (hk:k<fibers n i) (hv:v<radices n i)
 (eq:target scatter n i a d j t=target scatter n i a d k v) : j=k ∧ t=v := by
 cases scatter
 · apply packed_injective n i j t k v hj ht hk hv
   exact Nat.add_left_cancel eq
 · apply native_injective n i j t k v hj ht hk hv
   exact Nat.add_left_cancel eq

def FullSource (scatter:Bool) (n a d:ℕ) (heap:ℕ→Option Scalar) : Prop :=
 ∀z,z<len n→∃v,heap (sourceBase scatter a d+z)=some v
structure Partial (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j:ℕ)
 (heap:ℕ→Option Scalar) (s:State) : Prop where
 copied : ∀k,k<j→∀t,t<radices n i→s.scalarHeap (target scatter n i a d k t)=heap (source scatter n i a d k t)
 outside : ∀z,z<targetBase scatter a d∨targetBase scatter a d+len n≤z→s.scalarHeap z=heap z

theorem source_external (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d j t:ℕ)
 (hj:j<fibers n i) (ht:t<radices n i) (sep:a+len n≤d) :
 source scatter n i a d j t<targetBase scatter a d∨targetBase scatter a d+len n≤ source scatter n i a d j t := by
 have h:=coordinate_lt n i j t hj ht
 cases scatter <;> simp [source,targetBase] <;> omega

theorem Partial.physical_source {scatter:Bool} {n:ℕ} {i:Fin (ell n+1)} {a d j:ℕ} {heap:ℕ→Option Scalar} {s:State}
 (h:Partial scatter n i a d j heap s) (hj:j<fibers n i) (sep:a+len n≤d)
 (src:FullSource scatter n a d heap) : UniformSelectedAxisFiberPreparation.PhysicalSource scatter n i a (d+j*radices n i) s.scalarHeap := by
 cases scatter with
 | false =>
   intro z hz
   obtain ⟨v,hv⟩:=src z hz
   exact ⟨v,(h.outside (a+z) (by simp [targetBase];omega)).trans hv⟩
 | true =>
   intro t ht
   have range:packed n i j t<len n:=(coordinate_lt n i j t hj ht).2
   obtain ⟨v,hv⟩:=src _ range
   have ext:=h.outside (d+packed n i j t) (by simp [targetBase];omega)
   exact ⟨v,by simpa [packed,sourceBase,Nat.add_assoc] using ext.trans hv⟩

theorem Partial.after_fiber {scatter:Bool} {n:ℕ} {i:Fin (ell n+1)} {a d j:ℕ} {heap:ℕ→Option Scalar} {s u:State}
 (h:Partial scatter n i a d j heap s) (hj:j<fibers n i) (sep:a+len n≤d)
 (action:∀t,t<radices n i→u.scalarHeap (target scatter n i a d j t)=s.scalarHeap (source scatter n i a d j t))
 (outside:UniformTensorFiberCopyMachine.Outside
   (UniformSelectedAxisFiberPreparation.toAddress scatter n i j a (d+j*radices n i))
   (UniformSelectedAxisFiberPreparation.toStride scatter n i) (radices n i) s.scalarHeap u) :
 Partial scatter n i a d (j+1) heap u := by
 constructor
 · intro k hk t ht
   by_cases eq:k=j
   · subst k;rw [action t ht];exact h.outside _ (source_external scatter n i a d j t hj ht sep)
   · have nk:k<j:=by omega
     rw [outside _ (by
       intro v hv
       rw [target_row]
       intro e
       have inj:=target_injective scatter n i a d k t j v (by omega) ht hj hv e
       exact eq inj.1)]
     exact h.copied k nk t ht
 · intro z hz
   rw [outside z (by
     intro t ht;rw [target_row]
     have range:=target_range scatter n i a d j t hj ht
     omega)]
   exact h.outside z hz

/-- The three tail arithmetic operations advance the fiber and packed address. -/
def advance : List Op := [.add 1911 1911 1915,.add 1913 1913 1923,.mul 1952 70 72]
def advanced (s:State) := applyBlock advance s

theorem advance_code (scatter:Bool) : BlockAt advance (program scatter) 50 := by
 intro k hk;change k<3 at hk;interval_cases k <;> cases scatter <;> rfl

def FrameKept (z:ℕ) : Prop := UniformSelectedAxisFiberPreparation.Protected z ∧ z≠1911 ∧ z≠1913 ∧ z≠1952
instance (z:ℕ) : Decidable (FrameKept z) := by unfold FrameKept;infer_instance
structure Frame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀z,FrameKept z→u.natReg z=s.natReg z
 scalarReg : ∀z,z≠100→u.scalarReg z=s.scalarReg z

theorem Frame.pc (s:State) (pc:ℕ) : Frame s {s with pc:=pc} := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v:State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun z hz=>(g.natReg z hz).trans (f.natReg z hz),fun z hz=>(g.scalarReg z hz).trans (f.scalarReg z hz)⟩
theorem LocalFrame.frame {s u:State} (f:LocalFrame s u) : Frame s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg⟩
 intro z hz;apply f.natReg;unfold FrameKept UniformSelectedAxisFiberPreparation.Protected Kept at *;omega

theorem advance_frame (s:State) : Frame s (advanced s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro z hz
 simp (disch:=unfold FrameKept at hz;omega) [advanced,applyBlock,advance,Op.apply,writeNat,next]

theorem advance_parameters {n:ℕ} (i:Fin (ell n+1)) (j a d:ℕ) (s:State)
 (h:S.Parameters n i j a d s) :
 S.Parameters n i (j+1) a (d+radices n i) (applyBlock UniformSelectedAxisFiberPreparation.decodeSetup {advanced s with pc:=18}) := by
 let v:=applyBlock UniformSelectedAxisFiberPreparation.decodeSetup {advanced s with pc:=18}
 have saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n (ell n) (len n)
   (UniformMasterRootMachine.order n) v:=by
   constructor <;> simp [v,advanced,applyBlock,advance,UniformSelectedAxisFiberPreparation.decodeSetup,Op.apply,writeNat,next,
     h.metadata.saved.nextPrime,h.metadata.saved.inputLength,h.metadata.saved.count,h.metadata.saved.workingLength,
     h.metadata.saved.masterRoot,h.metadata.saved.copyAddress,h.metadata.saved.copyLength]
 have hm:Metadata n v:=h.metadata.transport_saved saved (fun _ _=>rfl)
 refine ⟨⟨?_,?_,?_,?_⟩,hm,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [advanced,applyBlock,advance,UniformSelectedAxisFiberPreparation.decodeSetup,Op.apply,writeNat,next,
   h.args.axis,h.args.fiber,h.args.array,h.args.bank,h.one,h.zero,h.product,h.radix,h.quotient,h.p,h.q]


theorem PureFrame_frame {s u:State} (f:UniformSelectedAxisFiberPreparation.PureFrame s u) : Frame s u :=
 ⟨f.natHeap,f.outputs,f.roots,fun z hz=>f.natReg z hz.1,fun z _=>congrFun f.scalarReg z⟩
theorem Partial.heap_transport {scatter:Bool} {n:ℕ} {i:Fin (ell n+1)} {a d j:ℕ} {heap:ℕ→Option Scalar} {s u:State}
 (h:Partial scatter n i a d j heap s) (he:u.scalarHeap=s.scalarHeap) : Partial scatter n i a d j heap u := by
 constructor
 · intro k hk t ht;rw [he];exact h.copied k hk t ht
 · intro z hz;rw [he];exact h.outside z hz

def continued (s:State) := applyBlock UniformSelectedAxisFiberPreparation.decodeSetup {advanced s with pc:=19}
def stopped (s:State) := {advanced s with pc:=54}

theorem decodeSetup_code (scatter:Bool) : BlockAt UniformSelectedAxisFiberPreparation.decodeSetup (program scatter) 19 := by
 intro k hk;change k<5 at hk;interval_cases k <;> cases scatter <;> rfl

theorem advance_runs {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:S.Parameters n i j a d s) (hj:j<fibers n i)
 (hd:d+radices n i≤B) (hc:55≤B) (hp:s.pc=50) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 3 (advanced s) := by
 have lb:len n≤B:=by rw [←h.metadata.saved.workingLength];exact hs.2.1 103
 have prod:=fibers_product n i
 have pos:1≤radices n i:=by have :=(selected_positive n i).2.1;omega
 have fb:fibers n i≤B:=by nlinarith
 apply block_runs advance (program scatter) 50 n B x s (advance_code scatter) hp hs
   (by change 50+3≤B;omega) (by simp [readable,advance,Op.readable])
 simp [peak,advance,Op.peak,Op.apply,writeNat,next,h.args.fiber,h.args.bank,h.one,h.radix,h.p,h.q]
 change j+1≤B ∧ d+radices n i≤B ∧ lower n i*upper n i≤B
 exact ⟨by omega,hd,fb⟩

theorem continue_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:S.Parameters n i j a d s) (hj:j+1<fibers n i)
 (hd:d+radices n i≤B) (hc:55≤B) (hp:s.pc=50) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 9 (continued s) ∧ (continued s).pc=24 ∧
 S.Parameters n i (j+1) a (d+radices n i) (continued s) ∧ Frame s (continued s) := by
 have arun:=advance_runs scatter i j a d B x s h (by omega) hd hc hp hs
 have ap:(advanced s).pc=53:=by unfold advanced;rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 let v:State:={advanced s with pc:=19}
 change j+1<lower n i*upper n i at hj
 have branch:BoundedRuns (program scatter) n x B (advanced s) 1 v:=.next arun.final_bound
   (by simp [step,hp,branch_at,v,advanced,applyBlock,advance,Op.apply,writeNat,next,h.args.fiber,h.one,h.p,h.q,hj])
   (.refl (changePC_bound B _ 19 arun.final_bound (by omega)))
 have drun:=block_runs UniformSelectedAxisFiberPreparation.decodeSetup (program scatter) 19 n B x v
   (decodeSetup_code scatter) rfl branch.final_bound (by change 19+5≤B;omega)
   (by simp [readable,UniformSelectedAxisFiberPreparation.decodeSetup,Op.readable])
   (by simp [peak,UniformSelectedAxisFiberPreparation.decodeSetup,Op.peak,Op.apply,writeNat,next]
       have hb:=branch.final_bound.2.1
       have z:v.natReg 1920=0:=by simp [v,advanced,applyBlock,advance,Op.apply,writeNat,next,h.zero]
       simp only [z,Nat.add_zero,max_le_iff];exact ⟨hb 1919,hb 1923,hb 1925,hb 1911,by omega⟩)
 have params:=advance_parameters i j a d s h
 have pc:(continued s).pc=24:=by unfold continued;rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have same:LocalFrame (applyBlock UniformSelectedAxisFiberPreparation.decodeSetup {advanced s with pc:=18}) (continued s):=
   ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 exact ⟨by convert arun.trans (branch.trans drun) using 1 <;> rfl,pc,same.parameters params,
   (advance_frame s).trans ((Frame.pc _ 19).trans (PureFrame_frame (UniformSelectedAxisFiberPreparation.decodeSetup_frame _)))⟩

theorem stop_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:S.Parameters n i j a d s) (hj:j+1=fibers n i)
 (hd:d+radices n i≤B) (hc:55≤B) (hp:s.pc=50) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 4 (stopped s) ∧ Frame s (stopped s) := by
 have arun:=advance_runs scatter i j a d B x s h (by omega) hd hc hp hs
 have ap:(advanced s).pc=53:=by unfold advanced;rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 change j+1=lower n i*upper n i at hj
 have branch:BoundedRuns (program scatter) n x B (advanced s) 1 (stopped s):=.next arun.final_bound
   (by simp [step,hp,branch_at,stopped,advanced,applyBlock,advance,Op.apply,writeNat,next,h.args.fiber,h.one,h.p,h.q] ;omega)
   (.refl (changePC_bound B _ 54 arun.final_bound (by omega)))
 exact ⟨by exact arun.trans branch,(advance_frame s).trans (Frame.pc _ 54)⟩

structure Args (axis a d:ℕ) (s:State) : Prop where
 axis : s.natReg 1910=axis
 array : s.natReg 1912=a
 bank : s.natReg 1913=d

theorem prologue_execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (hm:Metadata n s) (args:Args i.val a d s)
 (hc:55≤B) (hp:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s (7*i.val+18) u ∧ S.Parameters n i 0 a d u ∧
 u.pc=24 ∧ Frame s u ∧ u.scalarHeap=s.scalarHeap := by
 let init:=writeNat s 1911 0
 have ib:=writeNat_bound B s 1911 0 hs (by omega) (by omega)
 have ip:init.pc=1:=by simp [init,writeNat,next,hp]
 have first:BoundedRuns (program scatter) n x B s 1 init:=.next hs
   (by simp [step,program,embed,hp,init]) (.refl ib)
 have im:Metadata n init:=by
   apply hm.transport_saved
   · constructor <;> simp [init,writeNat,next,hm.saved.nextPrime,hm.saved.inputLength,hm.saved.count,
       hm.saved.workingLength,hm.saved.masterRoot,hm.saved.copyAddress,hm.saved.copyLength]
   · intro _ _;rfl
 let v:State:={init with pc:=0}
 have va:UniformSelectedAxisFiberPreparation.Args i.val 0 a d v:=by
   constructor <;> simp [v,init,writeNat,next,args.axis,args.array,args.bank]
 have vm:Metadata n v:=(UniformSelectedAxisFiberPreparation.PureFrame.pc init 0).metadata im
 obtain ⟨p,prun,cp,pp,fp⟩:=UniformSelectedAxisFiberPreparation.prefix_execution hn scatter i 0 a d B x v
   vm va (by omega) rfl (changePC_bound B _ 0 ib (by omega))
 have p2:=UniformSelectedAxisFiberPreparation.parameters_execution scatter i 0 a d B x p cp (by omega) pp prun.final_bound
 have pv:=UniformSelectedAxisFiberPreparation.parameters_values i 0 a d p cp
 have ppc:(UniformSelectedAxisFiberPreparation.parametersState p).pc=23:=by
   simp [UniformSelectedAxisFiberPreparation.parametersState,UniformTensorMonomialMachine.applyBlock_pc,
     UniformRadixInstructionMachine.block_pc,pp,UniformSelectedAxisFiberPreparation.decodeSetup,
     UniformSelectedAxisFiberPreparation.quotients,UniformSelectedAxisFiberPreparation.readRadix]
 have placed:=runs_placed_same (selected_code scatter) (by rw [UniformSelectedAxisFiberPreparation.program_length];omega)
   (prun.trans p2) (by rw [ppc];omega)
 have eq:UniformAssembly.placed 1 v=init:=by change {init with pc:=1}=init;rw [←ip]
 rw [eq] at placed
 let u:=UniformAssembly.placed 1 (UniformSelectedAxisFiberPreparation.parametersState p)
 have fi:Frame s init:=by
   refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
   intro z hz;simp [init,writeNat,next,hz.2.1]
 have fip:Frame init u:=(Frame.pc init 0).trans ((PureFrame_frame
   (fp.trans (UniformSelectedAxisFiberPreparation.parameters_frame p))).trans (Frame.pc _ _))
 have ue:u={UniformSelectedAxisFiberPreparation.parametersState p with pc:=24}:=by simp [u,UniformAssembly.placed,ppc]
 have pu:S.Parameters n i 0 a d u:=by rw [ue];exact (LocalFrame.pc _ 24).parameters pv
 refine ⟨u,?_,pu,by simp [u,UniformAssembly.placed,ppc],fi.trans fip,?_⟩
 · convert first.trans placed using 1;omega
 · exact (fp.trans (UniformSelectedAxisFiberPreparation.parameters_frame p)).scalarHeap


def loopCost (r fuel:ℕ) := fuel*(9*r+27)-5

theorem loopCost_one (r:ℕ) : loopCost r 1=9*r+22 := by unfold loopCost;omega
theorem loopCost_succ (r fuel:ℕ) (hf:0<fuel) : 9*r+18+9+loopCost r fuel=loopCost r (fuel+1) := by
 have hb:5≤fuel*(9*r+27):=by
   have h:=Nat.mul_le_mul_right (9*r+27) (show 1≤fuel by omega);simp only [Nat.one_mul] at h;omega
 unfold loopCost;rw [Nat.add_mul];omega

theorem loop {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (a d j fuel B:ℕ)
 (x:Fin n→ℂ) (heap:ℕ→Option Scalar) (s:State) (h:S.Parameters n i j a (d+j*radices n i) s)
 (part:Partial scatter n i a d j heap s) (src:FullSource scatter n a d heap)
 (count:j+fuel=fibers n i) (hf:0<fuel) (sep:a+len n≤d) (ha:a+2*len n≤B) (hd:d+len n≤B)
 (hc:55≤B) (hp:s.pc=24) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s (loopCost (radices n i) fuel) u ∧ u.pc=54 ∧
 Partial scatter n i a d (fibers n i) heap u ∧ Frame s u := by
 induction fuel generalizing j s with
 | zero => omega
 | succ fuel ih =>
   have hj:j<fibers n i:=by omega
   have dcur:d+j*radices n i+radices n i≤B:=by
     have mul:=Nat.mul_le_mul_right (radices n i) (show j+1≤fibers n i by omega)
     rw [Nat.add_mul,Nat.one_mul,fibers_product] at mul;omega
   obtain ⟨u,run,pu,action,outside,frame,params⟩:=fiber_execution scatter i j a (d+j*radices n i) B x s h hj
     (part.physical_source hj sep src) (by omega) ha dcur hc hp hs
   have copied:Partial scatter n i a d (j+1) heap u:=part.after_fiber hj sep
     (by intro t ht;rw [←target_row,action t ht,source_row]) outside
   by_cases last:fuel=0
   · subst fuel
     have endindex:j+1=fibers n i:=by omega
     obtain ⟨stop,stopframe⟩:=stop_execution scatter i j a (d+j*radices n i) B x u params endindex dcur hc pu run.final_bound
     refine ⟨stopped u,?_,rfl,?_,frame.frame.trans stopframe⟩
     · rw [loopCost_one];convert run.trans stop using 1
     · rw [←endindex];exact copied.heap_transport rfl
   · obtain ⟨next,np,nparams,nframe⟩:=continue_execution scatter i j a (d+j*radices n i) B x u params
       (by omega) dcur hc pu run.final_bound
     have eq:d+j*radices n i+radices n i=d+(j+1)*radices n i:=by ring
     rw [eq] at nparams
     obtain ⟨v,rest,pv,pfinal,ffinal⟩:=ih (j+1) (continued u) nparams (copied.heap_transport rfl)
       (by omega) (by omega) np next.final_bound
     refine ⟨v,?_,pv,pfinal,frame.frame.trans (nframe.trans ffinal)⟩
     rw [←loopCost_succ (radices n i) fuel (by omega)]
     convert run.trans (next.trans rest) using 1;omega

theorem Frame.metadata {n:ℕ} {s u:State} (f:Frame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · exact ⟨(f.natReg 100 (by decide)).trans h.saved.nextPrime,
   (f.natReg 101 (by decide)).trans h.saved.inputLength,(f.natReg 102 (by decide)).trans h.saved.count,
   (f.natReg 103 (by decide)).trans h.saved.workingLength,(f.natReg 104 (by decide)).trans h.saved.masterRoot,
   (f.natReg 105 (by decide)).trans h.saved.copyAddress,(f.natReg 106 (by decide)).trans h.saved.copyLength⟩
 · intro z _;exact congrFun f.natHeap _

def runtime (n:ℕ) (i:Fin (ell n+1)) := fibers n i*(9*radices n i+27)+7*i.val+14

/-- Actual complete physical permutation, both directions, with no output-bank,
address-table, axis-product or copy-header premise. -/
theorem execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (hm:Metadata n s) (args:Args i.val a d s)
 (src:FullSource scatter n a d s.scalarHeap) (sep:a+len n≤d)
 (ha:a+2*len n≤B) (hd:d+len n≤B) (hc:55≤B) (hp:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution (program scatter) n x B s (runtime n i) u ∧ u.pc=54 ∧
 (∀j,j<fibers n i→∀t,t<radices n i→u.scalarHeap (target scatter n i a d j t)=
   s.scalarHeap (source scatter n i a d j t)) ∧
 (∀z,z<targetBase scatter a d∨targetBase scatter a d+len n≤z→u.scalarHeap z=s.scalarHeap z) ∧
 Frame s u ∧ Metadata n u := by
 obtain ⟨p,prologue,params,pp,fp,heap⟩:=prologue_execution hn scatter i a d B x s hm args hc hp hs
 have initial:Partial scatter n i a d 0 s.scalarHeap p:=by
   constructor
   · intro j hj;omega
   · intro z _;exact congrFun heap z
 have params0:S.Parameters n i 0 a (d+0*radices n i) p:=by simpa using params
 obtain ⟨u,run,pu,part,fr⟩:=loop scatter i a d 0 (fibers n i) B x s.scalarHeap p params0 initial src
   (by omega) (fibers_positive n i) sep ha hd hc pp prologue.final_bound
 have stop:BoundedExecution (program scatter) n x B u 1 u:=.halt run.final_bound (by simp [step,pu,halt_at])
 have total:Frame s u:=fp.trans fr
 refine ⟨u,?_,pu,part.copied,part.outside,total,total.metadata hm⟩
 have hb:5≤fibers n i*(9*radices n i+27):=by
   have h:=Nat.mul_le_mul_right (9*radices n i+27) (show 1≤fibers n i by have:=fibers_positive n i;omega)
   simp only [Nat.one_mul] at h;omega
 convert prologue.executes (run.executes stop) using 1;unfold runtime loopCost;omega

/-- Fiber-major and native addresses are explicit finite equivalences. -/
def packedEquiv (n:ℕ) (i:Fin (ell n+1)) :
 (Fin (fibers n i)×Fin (radices n i))≃Fin (len n) :=
 finProdFinEquiv.trans (finCongr (fibers_product n i))
def nativeEquiv (n:ℕ) (i:Fin (ell n+1)) :
 (Fin (fibers n i)×Fin (radices n i))≃Fin (len n) :=
 (UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i)).trans
   (finCongr (selected_product n i))

/-- The actual full-array gather permutation; its inverse is the scatter. -/
def permutation (n:ℕ) (i:Fin (ell n+1)) : Fin (len n)≃Fin (len n) :=
 (packedEquiv n i).symm.trans (nativeEquiv n i)

theorem packedEquiv_val (n:ℕ) (i:Fin (ell n+1)) (p:Fin (fibers n i)×Fin (radices n i)) :
 (packedEquiv n i p).val=packed n i p.1.val p.2.val := by
 simp [packedEquiv,packed,Nat.mul_comm,Nat.add_comm]
theorem nativeEquiv_val (n:ℕ) (i:Fin (ell n+1)) (p:Fin (fibers n i)×Fin (radices n i)) :
 (nativeEquiv n i p).val=native n i p.1.val p.2.val := rfl
theorem permutation_packed (n:ℕ) (i:Fin (ell n+1)) (p:Fin (fibers n i)×Fin (radices n i)) :
 permutation n i (packedEquiv n i p)=nativeEquiv n i p := by simp [permutation]
theorem permutation_inverse_native (n:ℕ) (i:Fin (ell n+1)) (p:Fin (fibers n i)×Fin (radices n i)) :
 (permutation n i).symm (nativeEquiv n i p)=packedEquiv n i p := by simp [permutation]

/-- Every coordinate is copied, including its arbitrary dirty dependency tag. -/
theorem complete_action (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d:ℕ) (s u:State)
 (h:∀j,j<fibers n i→∀t,t<radices n i→u.scalarHeap (target scatter n i a d j t)=
   s.scalarHeap (source scatter n i a d j t)) :
 ∀z:Fin (len n),u.scalarHeap (targetBase scatter a d+z.val)=
   s.scalarHeap (sourceBase scatter a d+(if scatter then (permutation n i).symm z else permutation n i z).val) := by
 intro z
 cases scatter
 · let p:Fin (fibers n i)×Fin (radices n i):=(packedEquiv n i).symm z
   have zp:packedEquiv n i p=z:=(packedEquiv n i).apply_symm_apply z
   have v:=h p.1.val p.1.isLt p.2.val p.2.isLt
   change u.scalarHeap (d+packed n i p.1.val p.2.val)=s.scalarHeap (a+native n i p.1.val p.2.val) at v
   simp only [targetBase,sourceBase,Bool.false_eq_true,ite_false]
   rw [←zp,permutation_packed,packedEquiv_val,nativeEquiv_val];exact v
 · let p:Fin (fibers n i)×Fin (radices n i):=(nativeEquiv n i).symm z
   have zp:nativeEquiv n i p=z:=(nativeEquiv n i).apply_symm_apply z
   have v:=h p.1.val p.1.isLt p.2.val p.2.isLt
   change u.scalarHeap (a+native n i p.1.val p.2.val)=s.scalarHeap (d+packed n i p.1.val p.2.val) at v
   simp only [targetBase,sourceBase,ite_true]
   rw [←zp,permutation_inverse_native,packedEquiv_val,nativeEquiv_val];exact v

theorem runtime_bound (n:ℕ) (i:Fin (ell n+1)) : runtime n i≤36*len n+7*i.val+14 := by
 have fr:=fibers_product n i
 have rpos:1≤radices n i:=by have:=(selected_positive n i).2.1;omega
 have fl:fibers n i≤len n:=by nlinarith
 unfold runtime
 have eq:fibers n i*(9*radices n i+27)=9*(fibers n i*radices n i)+27*fibers n i:=by ring
 rw [eq,fr];omega

theorem canonical_code_bound {n:ℕ} (hn:0<n) : 55≤(n+2)^19 := by
 have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
 norm_num at h ⊢;omega

/-- Metadata supplies actual selected radices. The only scalar premise is the
ordinary present input array; every address/header and every fiber is charged. -/
theorem canonical_execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (a d:ℕ)
 (x:Fin n→ℂ) (s:State) (hm:Metadata n s) (args:Args i.val a d s)
 (src:FullSource scatter n a d s.scalarHeap) (sep:a+len n≤d)
 (ha:a+2*len n≤(n+2)^19) (hd:d+len n≤(n+2)^19)
 (hp:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
 BoundedExecution (program scatter) n x ((n+2)^19) s (runtime n i) u ∧
 (∀z:Fin (len n),u.scalarHeap (targetBase scatter a d+z.val)=
   s.scalarHeap (sourceBase scatter a d+(if scatter then (permutation n i).symm z else permutation n i z).val)) ∧
 (∀z,z<targetBase scatter a d∨targetBase scatter a d+len n≤z→u.scalarHeap z=s.scalarHeap z) ∧
 Frame s u ∧ Metadata n u := by
 obtain ⟨u,run,_pc,action,outside,frame,metadata⟩:=execution hn scatter i a d ((n+2)^19) x s hm args src sep ha hd
   (canonical_code_bound hn) hp hs
 exact ⟨u,run,complete_action scatter n i a d s u action,outside,frame,metadata⟩

/-- Join directly to actual initialized padded/chirped native operand cells.
Fresh destination placement retains all original operand/coefficient/root banks. -/
theorem native_gather_execution {n:ℕ} (hn:0<n) (i:Fin (ell n+1)) (d:ℕ)
 (x:Fin n→ℂ) (s:State) (hm:Metadata n s) (operands:UniformInitialPreparation.Operands n x s)
 (args:Args i.val (UniformPaddedInputPreparation.dataBase n) d s)
 (fresh:UniformNormalizationPreparation.normBase n<d)
 (ha:UniformPaddedInputPreparation.dataBase n+2*len n≤(n+2)^19)
 (hd:d+len n≤(n+2)^19) (hp:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
 BoundedExecution (program false) n x ((n+2)^19) s (runtime n i) u ∧
 (∀z:Fin (len n),u.scalarHeap (d+z.val)=some (UniformPaddedInputMachine.paddedScalar
   (OAI.ExactFourier.zeta (2*n)) x (permutation n i z).val)) ∧
 Frame s u ∧ Metadata n u ∧ UniformInitialPreparation.Operands n x u := by
 have sep:UniformPaddedInputPreparation.dataBase n+len n≤d:=by
   change UniformPaddedInputPreparation.dataBase n+len n+len n<d at fresh;omega
 have src:FullSource false n (UniformPaddedInputPreparation.dataBase n) d s.scalarHeap:=by
   intro z hz;exact ⟨_,operands.input z hz⟩
 obtain ⟨u,run,action,outside,frame,metadata⟩:=canonical_execution hn false i _ d x s hm args src sep ha hd hp hs
 refine ⟨u,run,?_,frame,metadata,UniformSelectedAxisFiberPreparation.operands_of_below d operands fresh ?_⟩
 · intro z
   have hz:=action z
   change u.scalarHeap (d+z.val)=s.scalarHeap (UniformPaddedInputPreparation.dataBase n+(permutation n i z).val) at hz
   exact hz.trans (operands.input _ (permutation n i z).isLt)
 · intro z hz;exact outside z (Or.inl hz)

end
end ExactFourierCircuits.UniformAllTensorFibersCopyMachine
