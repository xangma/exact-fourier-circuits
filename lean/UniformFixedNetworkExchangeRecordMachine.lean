import UniformFixedNetworkExchangeChildMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkExchangeRecordMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed)
namespace E
export UniformFixedNetworkExchangeChildMachine (program execution role_execution Frame values)
end E
namespace V
export UniformFixedNetworkChildDispatchMachine (volumeProgram volume_execution VolumeFrame)
end V
structure Pair (R:ℕ) where
 first:Fin R
 second:Fin R
 distinct:first≠second

def Pair.data {R:ℕ} (p:Pair R) : List ℕ := [p.first.val,p.second.val,4,0]
def body {R:ℕ} (pairs:List (Pair R)) : List ℕ := (pairs.map Pair.data).flatten
lemma body_length {R:ℕ} (pairs:List (Pair R)) : (body pairs).length=4*pairs.length := by
 induction pairs with
 | nil=>rfl
 | cons p ps ih=>
   simp only [body,List.map_cons,List.flatten_cons,List.length_append] at *
   change 4+(body ps).length=4*(ps.length+1)
   change (body ps).length=4*ps.length at ih
   rw [ih];omega

def record {R:ℕ} (q w:ℕ) (pairs:List (Pair R)) : Record := ⟨4,q,w,0,0,0,pairs.length,0,body pairs⟩
lemma record_good {R:ℕ} (q w:ℕ) (pairs:List (Pair R)) : UniformFixedNetworkOpcodeMachine.WellFormed (record q w pairs) := by
 constructor
 · norm_num [record]
 · simp [record,UniformFixedNetworkOpcodeMachine.bodyLength,body_length]
lemma record_length {R:ℕ} (q w:ℕ) (pairs:List (Pair R)) : (record q w pairs).data.length=8+4*pairs.length := by
 simp [record,Record.data_length,body_length]
def boot : List Op := [.add 3339 2850 2860,.literal 3340 0,.add 3341 2857 2866,.add 3322 3304 2866]
def pairSetup : List Op := [.add 3330 3339 2866,.getNat 3331 3330,.add 3330 3330 2859,
 .getNat 3332 3330,.add 3330 3330 2859,.getNat 3333 3330,.add 3330 3330 2859,
 .getNat 3334 3330,.mul 3320 3322 3331,.add 3320 3300 3320,
 .mul 3321 3322 3332,.add 3321 3300 3321]
def tail : List Op := [.add 3340 3340 2859,.add 3339 3339 2861]
def finish : List Op := [.add 2850 2865 2866]
def program : Program := UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++
 V.volumeProgram.map (relocate 52 62)++boot.map Op.code++
 [.branchLT 3340 3341 67 96]++pairSetup.map Op.code++E.program.map (relocate 79 93)++
 tail.map Op.code++[.jump 66]++finish.map Op.code++[.halt]
lemma program_length : program.length=98 := by
 simp only [program,List.length_append,List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length,
 UniformFixedNetworkChildDispatchMachine.volumeProgram_length,UniformFixedNetworkExchangeChildMachine.program_length]
 rfl
lemma reader_code : CodeAt UniformFixedNetworkOpcodeMachine.headProgram program 0 52 := by intro i hi;change i<52 at hi;interval_cases i <;> rfl
lemma volume_code : CodeAt V.volumeProgram program 52 62 := by intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma boot_code : BlockAt boot program 62 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma pair_code : BlockAt pairSetup program 67 := by intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma child_code : CodeAt E.program program 79 93 := by intro i hi;change i<14 at hi;interval_cases i <;> rfl
lemma tail_code : BlockAt tail program 93 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma finish_code : BlockAt finish program 96 := by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma branch_at : program[66]?=some (.branchLT 3340 3341 67 96) := rfl
lemma jump_at : program[95]?=some (.jump 66) := rfl
lemma halt_at : program[97]?=some .halt := rfl

noncomputable section
open UniformFixedNetworkShearChildMachine (Present roleBase role_bound)
def Changed (r:ℕ) : Prop := (3320≤r∧r<3342)
structure Frame (A W:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg:∀r,r<110∨114≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<A∨A+W≤z→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (A W:ℕ) (s:State) : Frame A W s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.pc {A W:ℕ} {s u:State} (f:Frame A W s u) (p:ℕ) : Frame A W s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {A W:ℕ} {s u t:State} (f:Frame A W s u) (g:Frame A W u t) : Frame A W s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun j h=>(g.natReg j h).trans (f.natReg j h),fun j h=>(g.scalarReg j h).trans (f.scalarReg j h),fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma frame_pair (A W:ℕ) (s:State) : Frame A W s (applyBlock pairSetup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [pairSetup,applyBlock,Op.apply,writeNat,next]
lemma frame_tail (A W:ℕ) (s:State) : Frame A W s (applyBlock tail s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [tail,applyBlock,Op.apply,writeNat,next]
lemma Frame.child {R V:ℕ} (A:ℕ) (d source:Fin R) {s u:State}
 (f:E.Frame (roleBase A V d.val) (roleBase A V source.val) V s u) : Frame A (R*V) s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;omega
 · intro z h
   have hd:=role_bound A V d;have hs:=role_bound A V source
   have ld:A≤roleBase A V d.val:=by unfold roleBase;omega
   have ls:A≤roleBase A V source.val:=by unfold roleBase;omega
   exact f.scalarHeap z (by omega) (by omega)
structure Header (A V cursor index count:ℕ) (s:State) : Prop where
 pc:s.pc=66
 base:s.natReg 3300=A
 volume:s.natReg 3322=V
 cursor:s.natReg 3339=cursor
 index:s.natReg 3340=index
 count:s.natReg 3341=count
 one:s.natReg 2859=1
 four:s.natReg 2861=4
 zero:s.natReg 2866=0

def actions {R V:ℕ} (pairs:List (Pair R)) (f:Fin R→Fin V→Scalar) := pairs.foldl (fun g p=>E.values p.first p.second g) f
lemma actions_cons {R V:ℕ} (p:Pair R) (ps:List (Pair R)) (f:Fin R→Fin V→Scalar) :
 actions (p::ps) f=actions ps (E.values p.first p.second f) := rfl
/-- Literal body rows contain exactly the two role coordinates and Fin5 +1 and −1
codes emitted by the existing terminal descriptor. Both code fields are read. -/
def PrintedPairs {R:ℕ} (cursor:ℕ) : List (Pair R)→State→Prop
 | [],_=>True
 | p::ps,s=>Printed cursor p.data s ∧ PrintedPairs (cursor+4) ps s
lemma printed_pairs {R:ℕ} (pairs:List (Pair R)) (T:ℕ) (s:State) (h:Printed T (body pairs) s) : PrintedPairs T pairs s := by
 induction pairs generalizing T with
 | nil=>trivial
 | cons p ps ih=>
   have split:=h.split
   exact ⟨split.1,ih (T+4) split.2⟩
lemma PrintedPairs.transport {R:ℕ} {pairs:List (Pair R)} {T:ℕ} {s u:State} (h:PrintedPairs T pairs s)
 (eq:u.natHeap=s.natHeap) : PrintedPairs T pairs u := by
 induction pairs generalizing T with
 | nil=>trivial
 | cons p ps ih=>
   exact ⟨fun j hj=>by rw [eq];exact h.1 j hj,ih h.2⟩

lemma round_execution {R V:ℕ} (A T i count B n:ℕ) (x:Fin n→ℂ) (p:Pair R) (f:Fin R→Fin V→Scalar)
 (s:State) (h:Header A V T i count s) (yes:i<count) (row:Printed T p.data s) (data:Present A R V f s)
 (hs:WordBound B s) (code:98≤B) (extent:A+R*V≤B) (tableEnd:T+4≤B) (_vol:V≤B) :∃u,
 BoundedRuns program n x B s (10*V+21) u ∧ Header A V (T+4) (i+1) count u ∧
 Present A R V (E.values p.first p.second f) u ∧ Frame A (R*V) s u := by
 let entry:=setPC s 67
 have eb:=changePC_bound B s 67 hs (by omega)
 have enter:BoundedRuns program n x B s 1 entry:=.next hs
   (by simp [step,h.pc,branch_at,h.index,h.count,yes,entry,setPC]) (.refl eb)
 have r0:s.natHeap T=some p.first.val:=by simpa [Pair.data] using row 0 (by simp [Pair.data])
 have r1:s.natHeap (T+1)=some p.second.val:=by simpa [Pair.data] using row 1 (by simp [Pair.data])
 have r2:s.natHeap (T+2)=some 4:=by simpa [Pair.data] using row 2 (by simp [Pair.data])
 have r3:s.natHeap (T+3)=some 0:=by simpa [Pair.data] using row 3 (by simp [Pair.data])
 have dd:=role_bound A V p.first
 have ss:=role_bound A V p.second
 have safe:readable pairSetup entry∧peak pairSetup entry≤B:=by
   simp [entry,setPC,pairSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.base,h.volume,h.cursor,h.one,h.zero,r0,r1,r2,r3]
   simp only [roleBase] at dd ss
   have db:A+V*p.first.val≤B:=by simpa [Nat.mul_comm] using (show A+p.first.val*V≤B by omega)
   have sb:A+V*p.second.val≤B:=by simpa [Nat.mul_comm] using (show A+p.second.val*V≤B by omega)
   have mx:A+V*max p.first.val p.second.val≤B:=by
     rcases le_total p.first.val p.second.val with le|le
     · simpa [max_eq_right le] using sb
     · simpa [max_eq_left le] using db
   have fb:=(hs.2.2.1 T _ r0).2
   have gb:=(hs.2.2.1 (T+1) _ r1).2
   omega
 have caller:=block_runs pairSetup program 67 n B x entry pair_code rfl eb (by change 79≤B;omega) safe.1 safe.2
 let ready:=applyBlock pairSetup entry
 let ce:=setPC ready 0
 have cb:=changePC_bound B ready 0 caller.final_bound (by omega)
 have dst:ce.natReg 3320=roleBase A V p.first.val:=by simp [ce,ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.base,h.volume,h.cursor,h.one,h.zero,r0,r1,r2,r3,roleBase,Nat.mul_comm]
 have src:ce.natReg 3321=roleBase A V p.second.val:=by simp [ce,ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.base,h.volume,h.cursor,h.one,h.zero,r0,r1,r2,r3,roleBase,Nat.mul_comm]
 have size:ce.natReg 3322=V:=by simp [ce,ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.volume]
 obtain ⟨child,cr,out,cf⟩:=E.role_execution A B n x p.first p.second p.distinct f ce rfl dst src size data cb (by omega) extent
 have placed:=UniformBoundedAssembly.boundedExecution_placed child_code (by change 93≤B;omega) (by omega) cr
 have same:UniformAssembly.placed 79 ce=ready:=by simp [UniformAssembly.placed,ce,ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next]
 rw [same] at placed
 let ret:=setPC child 93
 have keep (r:ℕ) (hr:r≠3323∧r≠3324∧r≠3325∧r≠3326) : ret.natReg r=ready.natReg r := by
   apply cf.natReg
   omega
 have idx:ret.natReg 3340=i:=(keep 3340 (by decide)).trans (by simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.index])
 have cur:ret.natReg 3339=T:=(keep 3339 (by decide)).trans (by simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.cursor])
 have one:ret.natReg 2859=1:=(keep 2859 (by decide)).trans (by simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.one])
 have four:ret.natReg 2861=4:=(keep 2861 (by decide)).trans (by simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.four])
 have ct:ret.natReg 3341=count:=(keep 3341 (by decide)).trans (by simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.count])
 have cbound:count≤B:=by have b:=hs.2.1 3341;rw [h.count] at b;exact b
 have safeTail:readable tail ret∧peak tail ret≤B:=by simp [tail,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,idx,cur,one,four];omega
 have tr:=block_runs tail program 93 n B x ret tail_code rfl placed.final_bound (by change 95≤B;omega) safeTail.1 safeTail.2
 let advanced:=applyBlock tail ret
 let u:=setPC advanced 66
 have ub:=changePC_bound B advanced 66 tr.final_bound (by omega)
 have jump:BoundedRuns program n x B advanced 1 u:=.next tr.final_bound (by simp [step,advanced,tail,applyBlock,Op.apply,writeNat,next,ret,setPC,jump_at,u]) (.refl ub)
 have full:Frame A (R*V) s u:=((Frame.refl A (R*V) s).pc 67 |>.trans (frame_pair A (R*V) entry) |>.pc 0)
   |>.trans (Frame.child A p.first p.second cf) |>.pc 93 |>.trans (frame_tail A (R*V) ret) |>.pc 66
 have head:Header A V (T+4) (i+1) count u:=by
   constructor
   · rfl
   · exact (full.natReg 3300 (by unfold Changed;omega)).trans h.base
   · change ret.natReg 3322=V
     rw [keep 3322 (by decide)];exact size
   · simp [u,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next,cur,four]
   · simp [u,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next,idx,one]
   · simpa [u,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next] using ct
   · simpa [u,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next] using one
   · simpa [u,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next] using four
   · change ret.natReg 2866=0
     rw [keep 2866 (by decide)]
     simp [ready,entry,setPC,pairSetup,applyBlock,Op.apply,writeNat,next,h.zero]
 refine ⟨u,?_,head,out,full⟩
 convert enter.trans (caller.trans (placed.trans (tr.trans jump))) using 1
 simp only [pairSetup,tail,List.length_cons,List.length_nil]
 omega

lemma loop_runs {R V:ℕ} (A count B n:ℕ) (x:Fin n→ℂ) (pairs:List (Pair R))
 (code:98≤B) (extent:A+R*V≤B) (vol:V≤B) :∀i T s (f:Fin R→Fin V→Scalar),
 i+pairs.length=count→Header A V T i count s→PrintedPairs T pairs s→Present A R V f s→WordBound B s→
 T+4*pairs.length≤B→∃u,
 BoundedRuns program n x B s ((10*V+21)*pairs.length+1) (setPC u 96) ∧
 Present A R V (actions pairs f) u ∧ Frame A (R*V) s u := by
 induction pairs with
 | nil=>
   intro i T s f eq h bank data hs endbound
   have stop:¬i<count:=by simp only [List.length_nil] at eq;omega
   refine ⟨s,?_,data,Frame.refl A (R*V) s⟩
   exact .next hs (by simp [step,h.pc,branch_at,h.index,h.count,stop,setPC])
     (.refl (changePC_bound B s 96 hs (by omega)))
 | cons p ps ih=>
   intro i T s f eq h bank data hs endbound
   have yes:i<count:=by simp only [List.length_cons] at eq;omega
   obtain ⟨mid,round,head,out,frame⟩:=round_execution A T i count B n x p f s h yes bank.1 data hs code extent
     (by simp only [List.length_cons] at endbound;omega) vol
   have bankTail:=PrintedPairs.transport bank.2 frame.natHeap
   obtain ⟨u,last,result,rest⟩:=ih (i+1) (T+4) mid (E.values p.first p.second f)
     (by simp only [List.length_cons] at eq;omega) head bankTail out round.final_bound
     (by simp only [List.length_cons] at endbound;omega)
   refine ⟨u,?_,result,frame.trans rest⟩
   convert round.trans last using 1
   simp only [List.length_cons]
   ring

def FullChanged (r:ℕ) : Prop := Changed r∨(2850≤r∧r<2877)∨(3302≤r∧r<3307)
structure FullFrame (A W:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬FullChanged r→u.natReg r=s.natReg r
 scalarReg:∀r,r<110∨114≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<A∨A+W≤z→u.scalarHeap z=s.scalarHeap z
lemma FullFrame.pc {A W:ℕ} {s u:State} (f:FullFrame A W s u) (p:ℕ) : FullFrame A W s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma FullFrame.trans {A W:ℕ} {s u t:State} (f:FullFrame A W s u) (g:FullFrame A W u t) : FullFrame A W s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun j h=>(g.natReg j h).trans (f.natReg j h),fun j h=>(g.scalarReg j h).trans (f.scalarReg j h),fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma FullFrame.reader (A W:ℕ) {s u:State} (f:UniformFixedNetworkOpcodeMachine.Frame s u) : FullFrame A W s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun r _=>congrFun f.scalarReg r,fun z _=>congrFun f.scalarHeap z⟩
 intro r h;apply f.natReg;unfold FullChanged Changed at h;omega
lemma FullFrame.volume (A W:ℕ) {s u:State} (f:V.VolumeFrame s u) : FullFrame A W s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun r _=>congrFun f.scalarReg r,fun z _=>congrFun f.scalarHeap z⟩
 intro r h;apply f.natReg;unfold FullChanged Changed at h;omega
lemma FullFrame.child {A W:ℕ} {s u:State} (f:Frame A W s u) : FullFrame A W s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,f.scalarHeap⟩
 intro r h;apply f.natReg;unfold FullChanged at h;tauto
lemma full_boot (A W:ℕ) (s:State) : FullFrame A W s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold FullChanged Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma full_finish (A W:ℕ) (s:State) : FullFrame A W s (applyBlock finish s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold FullChanged Changed at h;simp (disch:=omega) [finish,applyBlock,Op.apply,writeNat,next]

/-- Actual complete signed-exchange record: read its real header and every
four-word pair, compute volume, and run the literal swaps in chronological
order. Original bank presence/table geometry are the only semantic inputs. -/
theorem execution {R:ℕ} (q w A T B n:ℕ) (x:Fin n→ℂ) (pairs:List (Pair R))
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (pc:s.pc=0) (ptr:s.natReg 2850=T)
 (base:s.natReg 3300=A) (bank:Printed T (record q w pairs).data s)
 (data:Present A R (2^(q*w)) f s) (hr:0<R) (hs:WordBound B s) (code:98≤B)
 (extent:A+R*2^(q*w)≤B) (tableEnd:T+8+4*pairs.length≤B) (width:w+1≤B) :∃u,
 BoundedExecution program n x B s ((10*2^(q*w)+21)*pairs.length+4*(q*w)+50) u ∧
 Present A R (2^(q*w)) (actions pairs f) u ∧ u.natReg 2850=T+8+4*pairs.length ∧
 FullFrame A (R*2^(q*w)) s u := by
 let volume:=2^(q*w)
 change A+R*volume≤B at extent
 have vb:volume≤B:=by
   have b:=Nat.mul_le_mul_right volume (show 1≤R by omega)
   simp only [Nat.one_mul] at b
   omega
 obtain ⟨read,reader,fields,bodySize,nextptr,rf⟩:=UniformFixedNetworkOpcodeMachine.head_execution T B n (record q w pairs) x s ptr pc hs bank
   (record_good q w pairs) (by simpa [record_length,Nat.add_assoc] using tableEnd) width (by omega)
 have readerRun:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 52≤B;omega) (by omega) reader
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at readerRun
 let ve:=setPC read 0
 have vbe:=changePC_bound B read 0 reader.final_bound (by omega)
 obtain ⟨vol,vr,bits,volumeValue,vf,one⟩:=V.volume_execution q w B n x ve rfl
   (by simpa [ve,setPC,record] using fields.columns) (by simpa [ve,setPC,record] using fields.width) vbe vb (by omega)
 have volumeRun:=UniformBoundedAssembly.boundedExecution_placed volume_code (by change 62≤B;omega) (by omega) vr
 have ventry:placed 52 ve=setPC read 52:=rfl
 rw [ventry] at volumeRun
 let bs:=setPC vol 62
 have cb:bs.natReg 2850=T:=by change vol.natReg 2850=T;rw [vf.natReg 2850 (by omega)];exact fields.cursor
 have eight:bs.natReg 2860=8:=by change vol.natReg 2860=8;rw [vf.natReg 2860 (by omega)];exact fields.eight
 have zero:bs.natReg 2866=0:=by change vol.natReg 2866=0;rw [vf.natReg 2866 (by omega)];exact fields.zero
 have dim:bs.natReg 2857=pairs.length:=by change vol.natReg 2857=pairs.length;rw [vf.natReg 2857 (by omega)];exact fields.dimension
 have vval:bs.natReg 3304=volume:=volumeValue
 have rb:bs.natReg 3300=A:=by
   change vol.natReg 3300=A
   rw [vf.natReg 3300 (by omega)]
   change read.natReg 3300=A
   rw [rf.natReg 3300 (by omega)];exact base
 have db:pairs.length≤B:=by
   have b:bs.natReg 2857≤B:=volumeRun.final_bound.2.1 2857
   rw [dim] at b
   exact b
 have safe:readable boot bs∧peak boot bs≤B:=by simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,cb,eight,dim,zero,vval];omega
 have br:=block_runs boot program 62 n B x bs boot_code rfl volumeRun.final_bound (by change 66≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot bs
 have header:Header A volume (T+8) 0 pairs.length ready:=by
   constructor
   · rfl
   · simp [ready,boot,applyBlock,Op.apply,writeNat,next,rb]
   · simp [ready,boot,applyBlock,Op.apply,writeNat,next,vval,zero]
   · simp [ready,boot,applyBlock,Op.apply,writeNat,next,cb,eight]
   · simp [ready,boot,applyBlock,Op.apply,writeNat,next]
   · simp [ready,boot,applyBlock,Op.apply,writeNat,next,dim,zero]
   · change vol.natReg 2859=1
     rw [vf.natReg 2859 (by omega)];exact fields.one
   · change vol.natReg 2861=4
     rw [vf.natReg 2861 (by omega)];exact fields.four
   · exact zero
 have readyData:Present A R volume f ready:=by
   intro r j;change vol.scalarHeap (A+r.val*volume+j.val)=_
   rw [vf.scalarHeap];change read.scalarHeap (A+r.val*volume+j.val)=_
   rw [rf.scalarHeap];exact data r j
 have readyBody:PrintedPairs (T+8) pairs ready:=by
   have hbody:=bank.split.2
   have pp:=printed_pairs pairs (T+8) s hbody
   apply PrintedPairs.transport pp
   change vol.natHeap=s.natHeap
   exact vf.natHeap.trans rf.natHeap
 obtain ⟨child,loop,out,lf⟩:=loop_runs A pairs.length B n x pairs code extent vb 0 (T+8) ready f (by simp) header readyBody readyData br.final_bound tableEnd
 let ret:=setPC child 96
 have rz:ret.natReg 2866=0:=by
   change child.natReg 2866=0
   rw [lf.natReg 2866 (by unfold Changed;omega)]
   exact header.zero
 have rn:ret.natReg 2865=T+8+4*pairs.length:=by
   change child.natReg 2865=T+8+4*pairs.length
   rw [lf.natReg 2865 (by unfold Changed;omega)]
   change vol.natReg 2865=T+8+4*pairs.length
   rw [vf.natReg 2865 (by omega)]
   simpa [ve,setPC,record_length,Nat.add_assoc] using nextptr
 have tailSafe:readable finish ret∧peak finish ret≤B:=by simp [finish,readable,peak,Op.readable,Op.peak,rn,rz];omega
 have finalRun:=block_runs finish program 96 n B x ret finish_code rfl loop.final_bound (by change 97≤B;omega) tailSafe.1 tailSafe.2
 let u:=applyBlock finish ret
 have last:BoundedExecution program n x B u 1 u:=.halt finalRun.final_bound (by simp [step,u,finish,applyBlock,Op.apply,writeNat,next,ret,setPC,halt_at])
 have frame:FullFrame A (R*volume) s u:=
   ((FullFrame.reader A (R*volume) rf).pc 0 |>.trans (FullFrame.volume A (R*volume) vf) |>.pc 62 |>.trans (full_boot A (R*volume) bs))
   |>.trans (FullFrame.child lf) |>.pc 96 |>.trans (full_finish A (R*volume) ret)
 refine ⟨u,?_,out,?_,frame⟩
 · convert readerRun.executes (volumeRun.executes (br.executes (loop.executes (finalRun.executes last)))) using 1
   norm_num [UniformFixedNetworkOpcodeMachine.headCost,record,boot,finish,volume]
   omega
 · simp [u,finish,applyBlock,Op.apply,writeNat,next,rn,rz]

end
end ExactFourierCircuits.UniformFixedNetworkExchangeRecordMachine
