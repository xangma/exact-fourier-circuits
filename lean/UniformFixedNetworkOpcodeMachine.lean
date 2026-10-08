import UniformFixedNetworkLiteralDecoderMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkOpcodeMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords serialize)

/-- Header offsets0..7 are read from the physical table; q is never a code
literal. Nat2850=cursor;2851..2858=eight fields;2864=body;2865=next cursor.
The seven thresholds live in2870..2876. No scalar/data/root instruction occurs. -/
def readBlock : List Op :=
 [.literal 2859 1,.literal 2860 8,.literal 2861 4,.literal 2866 0,
  .add 2863 2850 2866,
  .getNat 2851 2863,.add 2863 2863 2859,
  .getNat 2852 2863,.add 2863 2863 2859,
  .getNat 2853 2863,.add 2863 2863 2859,
  .getNat 2854 2863,.add 2863 2863 2859,
  .getNat 2855 2863,.add 2863 2863 2859,
  .getNat 2856 2863,.add 2863 2863 2859,
  .getNat 2857 2863,.add 2863 2863 2859,
  .getNat 2858 2863,
  .literal 2871 2,.literal 2872 3,
  .literal 2873 4,.literal 2874 5,.literal 2875 6,.literal 2876 7]
def entry (k:ℕ) : ℕ := if k=0 then 34 else if k=1 then 36 else if k=2 then 38 else
 if k=3 then 40 else if k=4 then 43 else if k=5 then 45 else 47
def thresholdRegister (j:ℕ) : ℕ := if j=0 then 2859 else 2870+j
lemma entry_bound (k:ℕ) : entry k≤47 := by unfold entry;split_ifs <;> omega
def branches : Program := List.ofFn (fun j:Fin 7=>.branchLT 2851 (thresholdRegister j.val) (entry j.val) (27+j.val))
def finish : List Op := [.add 2865 2850 2860,.add 2865 2865 2864]
def headProgram : Program := readBlock.map Op.code++branches++
 [.natBinary .div 2864 2866 2866]++
 ([.mul 2864 2857 2853]:List Op).map Op.code++[.jump 49]++
 ([.literal 2864 0]:List Op).map Op.code++[.jump 49]++
 ([.add 2864 2855 2866]:List Op).map Op.code++[.jump 49]++
 ([.add 2864 2853 2859,.mul 2864 2857 2864]:List Op).map Op.code++[.jump 49]++
 ([.mul 2864 2857 2861]:List Op).map Op.code++[.jump 49]++
 ([.literal 2864 0]:List Op).map Op.code++[.jump 49]++
 ([.literal 2864 0]:List Op).map Op.code++[.jump 49]++finish.map Op.code++[.halt]
lemma readBlock_length : readBlock.length=26 := rfl
lemma headProgram_length : headProgram.length=52 := rfl
lemma read_code : BlockAt readBlock headProgram 0 := by
 intro i hi
 simp only [headProgram,Nat.zero_add]
 simp [List.getElem?_append_left,hi]
lemma branch_code (j:ℕ) (hj:j<7) : headProgram[26+j]?=some (.branchLT 2851 (thresholdRegister j) (entry j) (27+j)) := by
 interval_cases j <;> rfl
lemma finish_code : BlockAt finish headProgram 49 := by
 intro j hj
 have hj':j<2:=hj
 interval_cases j <;> rfl
lemma head_halt : headProgram[51]?=some .halt := rfl

/-- Only actual opcode/body geometry is required; no child action is encoded.
Zero-dimensional edges, zero width and empty terminal banks are retained. -/
def bodyLength (r:Record) : ℕ := if r.opcode=0 then r.dimension*r.width else
 if r.opcode=1 then 0 else if r.opcode=2 then r.source else
 if r.opcode=3 then r.dimension*(r.width+1) else if r.opcode=4 then 4*r.dimension else 0
def WellFormed (r:Record) : Prop := r.opcode<7 ∧ r.directions.length=bodyLength r
def headCost (r:Record) : ℕ := 32+r.opcode+(if r.opcode=3 then 1 else 0)
lemma headCost_bound (r:Record) (h:r.opcode<7) : headCost r≤38 := by
 unfold headCost;split <;> omega

noncomputable section
/-- Concrete prepared field state after the literal header loads. -/
structure Fields (A:ℕ) (r:Record) (s:State) : Prop where
 cursor:s.natReg 2850=A
 opcode:s.natReg 2851=r.opcode
 columns:s.natReg 2852=r.columns
 width:s.natReg 2853=r.width
 dest:s.natReg 2854=r.dest
 source:s.natReg 2855=r.source
 inverse:s.natReg 2856=r.inverse
 dimension:s.natReg 2857=r.dimension
 scalar:s.natReg 2858=r.scalar
 one:s.natReg 2859=1
 eight:s.natReg 2860=8
 four:s.natReg 2861=4
 zero:s.natReg 2866=0
 threshold:∀j:Fin 7,s.natReg (thresholdRegister j.val)=j.val+1
lemma read_fields (A:ℕ) (r:Record) (s:State) (ptr:s.natReg 2850=A) (h:Printed A r.data s) :
 Fields A r (applyBlock readBlock s) := by
 have h0:=h.header (0:Fin 8);have h1:=h.header (1:Fin 8)
 have h2:=h.header (2:Fin 8);have h3:=h.header (3:Fin 8)
 have h4:=h.header (4:Fin 8);have h5:=h.header (5:Fin 8)
 have h6:=h.header (6:Fin 8);have h7:=h.header (7:Fin 8)
 simp [Record.header] at h0 h1 h2 h3 h4 h5 h6 h7
 constructor
 all_goals first
  | intro j;fin_cases j <;> simp_all [thresholdRegister,readBlock,applyBlock,Op.apply,writeNat,next,Nat.add_assoc]
  | simp_all [readBlock,applyBlock,Op.apply,writeNat,next,Nat.add_assoc]

lemma read_safe (A B:ℕ) (r:Record) (s:State) (ptr:s.natReg 2850=A)
 (bank:Printed A r.data s) (hs:WordBound B s) (extent:A+8≤B) (code:52≤B) :
 readable readBlock s ∧ peak readBlock s≤B := by
 have h0:=bank.header (0:Fin 8);have h1:=bank.header (1:Fin 8)
 have h2:=bank.header (2:Fin 8);have h3:=bank.header (3:Fin 8)
 have h4:=bank.header (4:Fin 8);have h5:=bank.header (5:Fin 8)
 have h6:=bank.header (6:Fin 8);have h7:=bank.header (7:Fin 8)
 simp [Record.header] at h0 h1 h2 h3 h4 h5 h6 h7
 have b0:=(hs.2.2.1 A _ h0).2;have b1:=(hs.2.2.1 (A+1) _ h1).2
 have b2:=(hs.2.2.1 (A+2) _ h2).2;have b3:=(hs.2.2.1 (A+3) _ h3).2
 have b4:=(hs.2.2.1 (A+4) _ h4).2;have b5:=(hs.2.2.1 (A+5) _ h5).2
 have b6:=(hs.2.2.1 (A+6) _ h6).2;have b7:=(hs.2.2.1 (A+7) _ h7).2
 constructor
 · simp [readBlock,readable,Op.readable,Op.apply,writeNat,next,Nat.add_assoc,ptr,h0,h1,h2,h3,h4,h5,h6,h7]
 · simp [readBlock,peak,Op.peak,Op.apply,writeNat,next,Nat.add_assoc,ptr,h0,h1,h2,h3,h4,h5,h6,h7]
   omega

/-- All branch tests are Nat-only and charged. Every skipped threshold advances
one PC; the selected threshold jumps to the corresponding literal body block. -/
lemma branch_seek (A B n k c:ℕ) (r:Record) (x:Fin n→ℂ) (s:State)
 (hk:k<7) (hc:c≤k) (hr:r.opcode=k) (fields:Fields A r s)
 (pc:s.pc=26+(k-c)) (hs:WordBound B s) (code:52≤B) :
 BoundedRuns headProgram n x B s (c+1) {s with pc:=entry k} := by
 induction c generalizing s with
 | zero=>
   have hp:s.pc=26+k:=by simpa using pc
   have ins:headProgram[s.pc]?=some (.branchLT 2851 (thresholdRegister k) (entry k) (27+k)):=by rw [hp];exact branch_code k hk
   have op:s.natReg 2851=k:=fields.opcode.trans hr
   have th:s.natReg (thresholdRegister k)=k+1:=fields.threshold ⟨k,hk⟩
   exact .next hs (by simp [step,ins,op,th]) (.refl (changePC_bound B _ _ hs ((entry_bound k).trans (by omega))))
 | succ c ih=>
   have idx:k-(c+1)<7:=by omega
   have ins:headProgram[s.pc]?=some (.branchLT 2851 (thresholdRegister (k-(c+1))) (entry (k-(c+1))) (27+(k-(c+1)))):=by rw [pc];exact branch_code _ idx
   have op:s.natReg 2851=k:=fields.opcode.trans hr
   have th:s.natReg (thresholdRegister (k-(c+1)))=k-(c+1)+1:=fields.threshold ⟨_,idx⟩
   let t:State:={s with pc:=27+(k-(c+1))}
   have run:step headProgram n x s=.running t:=by simp [step,ins,op,th,t,show ¬k<k-(c+1)+1 by omega]
   have bt:WordBound B t:=changePC_bound B _ _ hs (by omega)
   have ft:Fields A r t:=by exact ⟨fields.cursor,fields.opcode,fields.columns,fields.width,fields.dest,fields.source,fields.inverse,fields.dimension,fields.scalar,fields.one,fields.eight,fields.four,fields.zero,fields.threshold⟩
   have next:=ih t (by omega) ft (by dsimp [t];omega) bt
   have out:{t with pc:=entry k}={s with pc:=entry k}:=rfl
   rw [out] at next
   simpa only [Nat.add_assoc] using BoundedRuns.next hs run next

def bodyOps (k:ℕ) : List Op := if k=0 then [.mul 2864 2857 2853] else
 if k=1 then [.literal 2864 0] else if k=2 then [.add 2864 2855 2866] else
 if k=3 then [.add 2864 2853 2859,.mul 2864 2857 2864] else
 if k=4 then [.mul 2864 2857 2861] else [.literal 2864 0]
lemma bodyOps_length (k:ℕ) : (bodyOps k).length=1+(if k=3 then 1 else 0) := by
 unfold bodyOps;split_ifs <;> simp_all
lemma body_code (k:ℕ) (hk:k<7) : BlockAt (bodyOps k) headProgram (entry k) := by
 intro j hj
 have size:(bodyOps k).length≤2:=by rw [bodyOps_length];split_ifs <;> omega
 have jh:j<2:=hj.trans_le size
 interval_cases j
 · interval_cases k <;> rfl
 · have k3:k=3:=by rw [bodyOps_length] at hj;split_ifs at hj <;> omega
   subst k;rfl
lemma body_jump (k:ℕ) (hk:k<7) :
 headProgram[entry k+(bodyOps k).length]?=some (.jump 49) := by interval_cases k <;> rfl

lemma body_fields (A k:ℕ) (r:Record) (s:State) (h:Fields A r s) : Fields A r (applyBlock (bodyOps k) s) := by
 rcases h with ⟨hc,ho,hq,hw,hd,hs,hi,hm,hv,h1,h8,h4,h0,ht⟩
 unfold bodyOps;split_ifs
 all_goals constructor
 all_goals first
 | (intro j
    have nz:thresholdRegister j.val≠2864:=by unfold thresholdRegister;split_ifs <;> omega
    simp_all [applyBlock,Op.apply,writeNat,next])
 | simp_all [applyBlock,Op.apply,writeNat,next]
lemma body_value (A k:ℕ) (r:Record) (s:State) (hk:k<7) (hr:r.opcode=k) (h:Fields A r s) :
 (applyBlock (bodyOps k) s).natReg 2864=bodyLength r := by
 rcases h with ⟨hc,ho,hq,hw,hd,hs,hi,hm,hv,h1,h8,h4,h0,ht⟩
 interval_cases k
 all_goals simp_all [bodyOps,bodyLength,applyBlock,Op.apply,writeNat,next,Nat.mul_comm]
lemma body_safe (A B k:ℕ) (r:Record) (s:State) (hk:k<7) (hr:r.opcode=k) (h:Fields A r s)
 (body:bodyLength r≤B) (width:r.width+1≤B) :
 readable (bodyOps k) s ∧ peak (bodyOps k) s≤B := by
 rcases h with ⟨hc,ho,hq,hw,hd,hs,hi,hm,hv,h1,h8,h4,h0,ht⟩
 interval_cases k
 all_goals simp_all [bodyOps,bodyLength,readable,peak,Op.peak,Op.readable,Op.apply,writeNat,next,Nat.mul_comm]

/-- The body operation and its continuation jump are actual machine steps. -/
lemma body_run (A B n k:ℕ) (r:Record) (x:Fin n→ℂ) (s:State)
 (hk:k<7) (hr:r.opcode=k) (h:Fields A r s) (pc:s.pc=entry k) (hs:WordBound B s)
 (body:bodyLength r≤B) (width:r.width+1≤B) (code:52≤B) :
 BoundedRuns headProgram n x B s ((bodyOps k).length+1) {applyBlock (bodyOps k) s with pc:=49} := by
 have safe:=body_safe A B k r s hk hr h body width
 have run:=block_runs (bodyOps k) headProgram (entry k) n B x s (body_code k hk) pc hs
   (by rw [bodyOps_length];have b:=entry_bound k;split_ifs <;> omega) safe.1 safe.2
 let t:=applyBlock (bodyOps k) s
 have tp:t.pc=entry k+(bodyOps k).length:=by simp [t,UniformTensorMonomialMachine.applyBlock_pc,pc]
 have jump:BoundedRuns headProgram n x B t 1 {t with pc:=49}:=
  .next run.final_bound (by simp [step,tp,body_jump k hk]) (.refl (changePC_bound B _ _ run.final_bound (by omega)))
 exact run.trans jump

lemma Fields.pc {A:ℕ} {r:Record} {s:State} (h:Fields A r s) (pc:ℕ) : Fields A r {s with pc:=pc} :=
 ⟨h.cursor,h.opcode,h.columns,h.width,h.dest,h.source,h.inverse,h.dimension,h.scalar,h.one,h.eight,h.four,h.zero,h.threshold⟩
lemma finish_fields (A:ℕ) (r:Record) (s:State) (h:Fields A r s) : Fields A r (applyBlock finish s) := by
 rcases h with ⟨hc,ho,hq,hw,hd,hs,hi,hm,hv,h1,h8,h4,h0,ht⟩
 constructor
 all_goals first
 | (intro j
    have nz:thresholdRegister j.val≠2865:=by unfold thresholdRegister;split_ifs <;> omega
    simp_all [finish,applyBlock,Op.apply,writeNat,next])
 | simp_all [finish,applyBlock,Op.apply,writeNat,next]

structure Frame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀(j:ℕ),j<2850∨2877≤j→u.natReg j=s.natReg j
lemma Frame.trans {s t u:State} (a:Frame s t) (b:Frame t u) : Frame s u :=
 ⟨b.natHeap.trans a.natHeap,b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,
 b.outputs.trans a.outputs,b.roots.trans a.roots,fun j hj=>(b.natReg j hj).trans (a.natReg j hj)⟩
lemma Frame.pc {s t:State} (h:Frame s t) (c:ℕ) : Frame s {t with pc:=c} :=
 ⟨h.natHeap,h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩
def NatRange : Op→Prop
 | .literal d _ | .add d _ _ | .mul d _ _ | .getNat d _=>2850≤d ∧ d<2877
 | _=>False
lemma op_frame (o:Op) (s:State) (ho:NatRange o) : Frame s (o.apply s) := by
 cases o <;> simp only [NatRange] at ho
 all_goals refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 all_goals intro j hj
 all_goals simp only [Op.apply,writeNat,next]
 all_goals apply Function.update_of_ne
 all_goals omega
lemma block_frame (b:List Op) (s:State) (h:∀o∈b,NatRange o) : Frame s (applyBlock b s) := by
 induction b generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | cons o b ih=>
   exact (op_frame o s (h o (by simp))).trans (ih _ (by intro u hu;exact h u (by simp [hu])))
lemma read_frame (s:State) : Frame s (applyBlock readBlock s) := by
 apply block_frame
 intro o ho;simp only [readBlock,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst o <;> norm_num [NatRange]
lemma body_frame (k:ℕ) (s:State) : Frame s (applyBlock (bodyOps k) s) := by
 apply block_frame
 intro o ho
 unfold bodyOps at ho;split_ifs at ho
 all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
 all_goals first | (subst o;norm_num [NatRange]) | (rcases ho with h|h <;> subst o <;> norm_num [NatRange])
lemma finish_frame (s:State) : Frame s (applyBlock finish s) := by
 apply block_frame
 intro o ho;simp only [finish,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with h|h <;> subst o <;> norm_num [NatRange]

/-- Every header is loaded from the printed bank and every opcode0..6 takes
its concrete branch/body path. No handler, child action or decoded fields are
entry premises. The body table and all heaps remain intact. -/
theorem head_execution (A B n:ℕ) (r:Record) (x:Fin n→ℂ) (s:State)
 (ptr:s.natReg 2850=A) (pc:s.pc=0) (hs:WordBound B s) (bank:Printed A r.data s)
 (good:WellFormed r) (extent:A+r.data.length≤B) (width:r.width+1≤B) (code:52≤B) : ∃u,
 BoundedExecution headProgram n x B s (headCost r) u ∧ Fields A r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=A+r.data.length ∧ Frame s u := by
 have safe:=read_safe A B r s ptr bank hs (by have l:=UniformFixedNetworkLiteralDecoderMachine.data_length_positive r;omega) code
 have readRun:=block_runs readBlock headProgram 0 n B x s read_code pc hs (by rw [readBlock_length];omega) safe.1 safe.2
 let ready:=applyBlock readBlock s
 have fr:Fields A r ready:=read_fields A r s ptr bank
 have rp:ready.pc=26:=by simp [ready,UniformTensorMonomialMachine.applyBlock_pc,pc,readBlock_length]
 have seek:=branch_seek A B n r.opcode r.opcode r x ready good.1 (by omega) rfl fr
   (by simpa using rp) readRun.final_bound code
 let selected:State:={ready with pc:=entry r.opcode}
 have fs:Fields A r selected:=fr.pc _
 have bb:bodyLength r≤B:=by rw [←good.2];rw [Record.data_length] at extent;omega
 have bodyRun:=body_run A B n r.opcode r x selected good.1 rfl fs rfl seek.final_bound bb width code
 let after:State:={applyBlock (bodyOps r.opcode) selected with pc:=49}
 have fa:Fields A r after:=(body_fields A r.opcode r selected fs).pc _
 have val:after.natReg 2864=bodyLength r:=body_value A r.opcode r selected good.1 rfl fs
 have finishRead:readable finish after:=by simp [finish,readable,Op.readable]
 have finishPeak:peak finish after≤B:=by
   simp [finish,peak,Op.peak,Op.apply,writeNat,next,fa.cursor,fa.eight,val]
   rw [Record.data_length,good.2] at extent
   omega
 have doneRun:=block_runs finish headProgram 49 n B x after finish_code rfl bodyRun.final_bound
   (by change 49+2≤B;omega) finishRead finishPeak
 let u:=applyBlock finish after
 have up:u.pc=51:=by simp [u,UniformTensorMonomialMachine.applyBlock_pc,after];rfl
 have halt:BoundedExecution headProgram n x B u 1 u:=.halt doneRun.final_bound (by simp [step,up,head_halt])
 refine ⟨u,?_,finish_fields A r after fa,?_,?_,?_⟩
 · convert readRun.executes (seek.executes (bodyRun.executes (doneRun.executes halt))) using 1
   rw [readBlock_length,bodyOps_length,show finish.length=2 from rfl];unfold headCost;omega
 · simpa [u,finish,applyBlock,Op.apply,writeNat,next,good.2] using val
 · simp [u,finish,applyBlock,Op.apply,writeNat,next,fa.cursor,fa.eight,val,Record.data_length,good.2,Nat.add_assoc]
 · exact (read_frame s).pc _ |>.trans ((body_frame r.opcode selected).pc _ |>.trans (finish_frame after))

/-- Actual header traversal: branch, load/dispatch header, copy the computed
next cursor, jump back. There is no callback instruction or child execution. -/
def loopProgram : Program := UniformAssembly.embed
 [.branchLT 2850 2880 1 55] headProgram
 [.natBinary .add 2850 2865 2866,.jump 0,.halt] 53
lemma loopProgram_length : loopProgram.length=56 := rfl
lemma loop_head_code : UniformAssembly.CodeAt headProgram loopProgram 1 53 :=
 UniformAssembly.embed_code _ _ _ _
lemma loop_branch : loopProgram[0]?=some (.branchLT 2850 2880 1 55) := rfl
lemma loop_advance : loopProgram[53]?=some (.natBinary .add 2850 2865 2866) := rfl
lemma loop_jump : loopProgram[54]?=some (.jump 0) := rfl
lemma loop_halt : loopProgram[55]?=some .halt := rfl
def loopCost : List Record→ℕ
 | []=>2
 | r::rs=>headCost r+3+loopCost rs
lemma loopCost_bound (rs:List Record) (good:∀r∈rs,WellFormed r) : loopCost rs≤41*rs.length+2 := by
 induction rs with
 | nil=>simp [loopCost]
 | cons r rs ih=>
   have a:=headCost_bound r (good r (by simp)).1
   have b:=ih (by intro t ht;exact good t (by simp [ht]))
   simp only [loopCost,List.length_cons];omega

/-- Every variable-length record is read exactly once. Physical body lengths
and finite marker tests determine every cursor advance. The code is one fixed
56-instruction program, independent of q, records and input length. -/
theorem loop_execution (rs:List Record) (A B n:ℕ) (x:Fin n→ℂ) (s:State)
 (ptr:s.natReg 2850=A) (endptr:s.natReg 2880=A+(serialize rs).length)
 (pc:s.pc=0) (hs:WordBound B s) (bank:PrintedRecords A rs s)
 (good:∀r∈rs,WellFormed r) (width:∀r∈rs,r.width+1≤B)
 (extent:A+(serialize rs).length≤B) (code:56≤B) : ∃u,
 BoundedExecution loopProgram n x B s (loopCost rs) u ∧
 u.natReg 2850=A+(serialize rs).length ∧ Frame s u := by
 induction rs generalizing A s with
 | nil=>
   let u:State:={s with pc:=55}
   have branch:step loopProgram n x s=.running u:=by simp [step,pc,loop_branch,u,ptr,endptr,serialize]
   have bu:WordBound B u:=changePC_bound B _ _ hs (by omega)
   refine ⟨u,?_,?_,?_⟩
   · exact .next hs branch (.halt bu (by simp [step,u,loop_halt]))
   · simpa [u,serialize] using ptr
   · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | cons r rs ih=>
   have len:=UniformFixedNetworkLiteralDecoderMachine.data_length_positive r
   have yes:s.natReg 2850<s.natReg 2880:=by rw [ptr,endptr,UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons];omega
   have first:BoundedRuns loopProgram n x B s 1 {s with pc:=1}:=
     .next hs (by simp [step,pc,loop_branch,yes]) (.refl (changePC_bound B _ _ hs (by omega)))
   obtain ⟨u,head,fields,body,nextval,frame⟩:=head_execution A B n r x s ptr pc hs bank.1
     (good r (by simp)) (by rw [UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons] at extent;omega)
     (width r (by simp)) (by omega)
   have call:=UniformBoundedAssembly.boundedExecution_placed loop_head_code
     (by rw [headProgram_length];omega) (by omega) head
   have start:UniformAssembly.placed 1 s={s with pc:=1}:=by unfold UniformAssembly.placed;rw [pc]
   rw [start] at call
   let t:State:={u with pc:=53}
   have ft:Fields A r t:=fields.pc _
   have tn:t.natReg 2865=A+r.data.length:=nextval
   let v:=writeNat t 2850 (A+r.data.length)
   have bv:WordBound B v:=writeNat_bound B t 2850 _ call.final_bound (by simp only [t];omega)
     (by rw [UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons] at extent;omega)
   have advance:step loopProgram n x t=.running v:=by
     simp only [step,show t.pc=53 from rfl,loop_advance]
     rw [tn,ft.zero]
     rfl
   let ready:State:={v with pc:=0}
   have br:WordBound B ready:=changePC_bound B _ _ bv (by omega)
   have jump:step loopProgram n x v=.running ready:=by
     simp only [step,show v.pc=54 from rfl,loop_jump]
     rfl
   have two:BoundedRuns loopProgram n x B t 2 ready:=.next call.final_bound advance (.next bv jump (.refl br))
   have tail:PrintedRecords (A+r.data.length) rs ready:=by
     apply UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport bank.2
     intro z _;change u.natHeap z=s.natHeap z;rw [frame.natHeap]
   have rp:ready.natReg 2850=A+r.data.length:=by simp [ready,v,writeNat]
   have re:ready.natReg 2880=(A+r.data.length)+(serialize rs).length:=by
     change (Function.update u.natReg 2850 (A+r.data.length)) 2880=_
     rw [Function.update_of_ne (by decide),frame.natReg 2880 (Or.inr (by omega)),endptr]
     rw [UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons];omega
   obtain ⟨w,run,wp,fw⟩:=ih (A+r.data.length) ready rp re rfl br tail
     (by intro z hz;exact good z (by simp [hz])) (by intro z hz;exact width z (by simp [hz]))
     (by rw [UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons] at extent;omega)
   have fv:Frame t v:=by
     have eq:v=(Op.add 2850 2865 2866).apply t:=by simp [v,Op.apply,tn,ft.zero]
     rw [eq];exact op_frame _ _ (by norm_num [NatRange])
   have total:Frame s w:=((frame.pc 53).trans (fv.pc 0)).trans fw
   refine ⟨w,?_,?_,total⟩
   · convert first.executes (call.executes (two.executes run)) using 1
     simp [loopCost];omega
   · rw [UniformFixedNetworkLiteralDecoderMachine.serialize_length_cons];simpa only [Nat.add_assoc] using wp


lemma flatten_map_length {α:Type*} (xs:List α) (f:α→List ℕ) (c:ℕ)
 (hf:∀a∈xs,(f a).length=c) : (xs.map f).flatten.length=xs.length*c := by
 induction xs with
 | nil=>simp
 | cons a xs ih=>
   simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons]
   rw [hf a (by simp),ih (by intro b hb;exact hf b (by simp [hb]))]
   rw [Nat.add_mul];omega

lemma macro_wellFormed {r R n:ℕ} (q:ℕ) (e:Fin r↪Fin R)
 (a:UniformFixedCoefficientCodec.EncodedMacro r n) : WellFormed (UniformFixedNetworkScheduleMachine.macroRecord q e a) := by
 cases a <;> simp [WellFormed,bodyLength,UniformFixedNetworkScheduleMachine.macroRecord,UniformFixedNetworkScheduleMachine.edgeBits_length]
lemma boundary_wellFormed (q:ℕ) (a:UniformFixedNetworkScheduleMachine.Invocation) : WellFormed (UniformFixedNetworkScheduleMachine.blockBoundary q a) := by
 simp [WellFormed,bodyLength,UniformFixedNetworkScheduleMachine.blockBoundary]
lemma withColumns_wellFormed (q:ℕ) (r:Record) (h:WellFormed r) : WellFormed (r.withColumns q) := by
 cases r;exact h
lemma block_wellFormed (q:ℕ) (a:UniformFixedNetworkScheduleMachine.Invocation) : ∀r∈UniformFixedNetworkScheduleMachine.blockRecords q a,WellFormed r := by
 intro r hr
 change r∈(UniformFixedNetworkScheduleMachine.encodedBlock a).map (UniformFixedNetworkScheduleMachine.macroRecord q _) at hr
 obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
 exact macro_wellFormed q _ m
lemma lineLength_symbolic (h:ℕ) (xs:List (TripleNetwork.Bank (Fin h))) :
 (xs.map (fun d=>(TripleSchedule.Global.coordinates h (.inl (1,d))).val::
   UniformFixedNetworkScheduleMachine.bitWords (TripleColumnAction.globalDirection 1 d))).flatten.length=
 xs.length*(h^3+1) := by
 apply flatten_map_length
 intro d _
 rw [List.length_cons,UniformFixedNetworkScheduleMachine.bitWords_length,Nat.one_mul]

def terminalTemplate (h roles padded:ℕ) (xs:List (TripleNetwork.Bank (Fin h))) : List Record :=
 let pairs:=xs.map (fun d=>((TripleSchedule.Global.coordinates h (.inl (0,d))).val,
                           (TripleSchedule.Global.coordinates h (.inl (1,d))).val))
 [⟨3,0,h^3,0,0,0,pairs.length,0,
   (xs.map (fun d=>(TripleSchedule.Global.coordinates h (.inl (1,d))).val::
     UniformFixedNetworkScheduleMachine.bitWords (TripleColumnAction.globalDirection 1 d))).flatten⟩,
  ⟨4,0,h^3,0,0,0,pairs.length,0,(pairs.map (fun p=>[p.1,p.2,4,0])).flatten⟩,
  ⟨5,0,h^3,roles,padded-roles,0,0,0,[]⟩]
lemma terminalTemplate_wellFormed (h roles padded:ℕ) (xs:List (TripleNetwork.Bank (Fin h))) :
 ∀r∈terminalTemplate h roles padded xs,WellFormed r := by
 let pairs:=xs.map (fun d=>((TripleSchedule.Global.coordinates h (.inl (0,d))).val,
                           (TripleSchedule.Global.coordinates h (.inl (1,d))).val))
 have pairsLen:pairs.length=xs.length:=by simp [pairs]
 have lineLen:=lineLength_symbolic h xs
 have exchangeLen:=flatten_map_length pairs (fun p=>[p.1,p.2,4,0]) 4 (by intro _ _;rfl)
 intro r hr
 simp only [terminalTemplate,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with rfl|rfl|rfl
 · constructor
   · change (3:ℕ)<7;omega
   · change _=pairs.length*(h^3+1)
     rw [pairsLen];exact lineLen
 · constructor
   · change (4:ℕ)<7;omega
   · change _=4*pairs.length
     rw [Nat.mul_comm];exact exchangeLen
 · exact ⟨by change (5:ℕ)<7;omega,rfl⟩
lemma rawTerminal_wellFormed : ∀r∈UniformFixedNetworkScheduleMachine.rawTerminalRecords,WellFormed r := by
 have h:=terminalTemplate_wellFormed ExplicitSeedBudget.h UniformFixedNetworkScheduleMachine.actualRoles UniformFixedNetwork.W
   (Finset.univ.toList:List (TripleNetwork.Bank (Fin ExplicitSeedBudget.h)))
 simpa only [terminalTemplate,UniformFixedNetworkScheduleMachine.rawTerminalRecords,UniformFixedNetworkScheduleMachine.bankPairs] using h
lemma terminal_wellFormed (q:ℕ) : ∀r∈UniformFixedNetworkScheduleMachine.terminalRecords q,WellFormed r := by
 intro r hr
 change r∈UniformFixedNetworkScheduleMachine.rawTerminalRecords.map (Record.withColumns q) at hr
 obtain ⟨t,ht,eq⟩:=(List.mem_map (f:=Record.withColumns q)).mp hr
 rw [←eq];exact withColumns_wellFormed q t (rawTerminal_wellFormed t ht)
lemma baseSchedule_wellFormed : ∀r∈UniformFixedNetworkScheduleMachine.baseSchedule,WellFormed r := by
 intro r hr
 rcases List.mem_cons.mp hr with rfl|hr
 · exact ⟨by change (6:ℕ)<7;omega,rfl⟩
 · rcases List.mem_append.mp hr with hr|hr
   · obtain ⟨rs,hrs,hr⟩:=List.mem_flatten.mp hr
     obtain ⟨a,_,rfl⟩:=List.mem_map.mp hrs
     rcases List.mem_cons.mp hr with rfl|hr
     · exact boundary_wellFormed 0 a
     · exact block_wellFormed 0 a r hr
   · exact terminal_wellFormed 0 r hr
lemma schedule_wellFormed (q:ℕ) : ∀r∈UniformFixedNetworkScheduleMachine.scheduleRecords q,WellFormed r := by
 intro r hr
 change r∈UniformFixedNetworkScheduleMachine.baseSchedule.map (Record.withColumns q) at hr
 obtain ⟨t,ht,eq⟩:=(List.mem_map (f:=Record.withColumns q)).mp hr
 rw [←eq];exact withColumns_wellFormed q t (baseSchedule_wellFormed t ht)
lemma schedule_width_bound (q:ℕ) (r:Record) (hr:r∈UniformFixedNetworkScheduleMachine.scheduleRecords q) :
 r.width+1≤UniformFixedNetworkScheduleMachine.literalCap (serialize UniformFixedNetworkScheduleMachine.baseSchedule)+1 := by
 change r∈UniformFixedNetworkScheduleMachine.baseSchedule.map (Record.withColumns q) at hr
 obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hr
 have mem:t.width∈t.data:=by simp [Record.data,Record.header]
 have bound:=UniformFixedNetworkScheduleMachine.member_le_cap (serialize UniformFixedNetworkScheduleMachine.baseSchedule) t.width (UniformFixedNetworkScheduleMachine.serialize_mem.mpr ⟨t,ht,mem⟩)
 change t.width+1≤_;omega

/-- This prologue installs both physical cursor and end from the caller's
base. The template length is fixed, and every installation is charged. -/
def callerSetup (rs:List Record) : List Op :=
 [.literal 2881 (serialize rs).length,.add 2880 2600 2881,
  .literal 2866 0,.add 2850 2600 2866]
def callerEntry (rs:List Record) : ℕ := (UniformFixedNetworkLiteralDecoderMachine.program rs).length
def callerLoop (rs:List Record) : ℕ := callerEntry rs+4
def callerHalt (rs:List Record) : ℕ := callerLoop rs+56
/-- One fixed template printer, runtime-q patch, literal cursor setup, and
physical opcode loop. The loop visits child descriptors; it does not execute
any residual, shear, correction or padding child. -/
def callerProgram (rs:List Record) : Program := UniformAssembly.embed
 ((UniformFixedNetworkLiteralDecoderMachine.program rs).map (UniformAssembly.relocate 0 (callerEntry rs))++
  (callerSetup rs).map Op.code) loopProgram [.halt] (callerHalt rs)
lemma callerProgram_length (rs:List Record) : (callerProgram rs).length=callerHalt rs+1 := by
 simp [callerProgram,UniformAssembly.embed_length,callerHalt,callerLoop,callerEntry,callerSetup,loopProgram_length]
lemma caller_printer_code (rs:List Record) :
 UniformAssembly.CodeAt (UniformFixedNetworkLiteralDecoderMachine.program rs) (callerProgram rs) 0 (callerEntry rs) := by
 intro i hi
 simp only [callerProgram,UniformAssembly.embed,Nat.zero_add,List.append_assoc]
 rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]
lemma caller_setup_code (rs:List Record) : BlockAt (callerSetup rs) (callerProgram rs) (callerEntry rs) := by
 intro i hi
 simp only [callerProgram,UniformAssembly.embed,List.append_assoc]
 rw [List.getElem?_append_right (by simp only [List.length_map];unfold callerEntry;omega)]
 simp only [List.length_map,callerEntry,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,List.getElem?_eq_getElem hi]
 rfl
lemma caller_loop_code (rs:List Record) : UniformAssembly.CodeAt loopProgram (callerProgram rs) (callerLoop rs) (callerHalt rs) := by
 have h:=UniformAssembly.embed_code
   ((UniformFixedNetworkLiteralDecoderMachine.program rs).map (UniformAssembly.relocate 0 (callerEntry rs))++
    (callerSetup rs).map Op.code) loopProgram [.halt] (callerHalt rs)
 have hl:((UniformFixedNetworkLiteralDecoderMachine.program rs).map (UniformAssembly.relocate 0 (callerEntry rs))++
    (callerSetup rs).map Op.code).length=callerLoop rs:=by simp [callerLoop,callerEntry,callerSetup]
 rw [hl] at h
 exact h
lemma caller_halt_code (rs:List Record) : (callerProgram rs)[callerHalt rs]?=some .halt := by
 let pre:=((UniformFixedNetworkLiteralDecoderMachine.program rs).map (UniformAssembly.relocate 0 (callerEntry rs))++
    (callerSetup rs).map Op.code)
 have hl:pre.length=callerLoop rs:=by simp [pre,callerLoop,callerEntry,callerSetup]
 change (pre++loopProgram.map (UniformAssembly.relocate pre.length (callerHalt rs))++[.halt])[callerHalt rs]?=_
 have total:(pre++loopProgram.map (UniformAssembly.relocate pre.length (callerHalt rs))).length=callerHalt rs:=by
   simp only [List.length_append,List.length_map,hl,loopProgram_length,callerHalt]
 rw [List.getElem?_append_right (by rw [total])]
 rw [total,Nat.sub_self]
 rfl
lemma callerSetup_spec (rs:List Record) (A:ℕ) (s:State) (base:s.natReg 2600=A) :
 (applyBlock (callerSetup rs) s).natReg 2850=A ∧
 (applyBlock (callerSetup rs) s).natReg 2880=A+(serialize rs).length := by
 simp [callerSetup,applyBlock,Op.apply,writeNat,next,base]
lemma callerSetup_safe (rs:List Record) (A B:ℕ) (s:State) (base:s.natReg 2600=A)
 (extent:A+(serialize rs).length≤B) : readable (callerSetup rs) s ∧ peak (callerSetup rs) s≤B := by
 simp [callerSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,base]
 omega

structure CallerFrame (s u:State) : Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀(j:ℕ),j<2850∨2882≤j→j≠2601→j≠2602→j≠2603→j≠2604→j≠2700→j≠2701→u.natReg j=s.natReg j
lemma callerSetup_frame (rs:List Record) (s:State) : CallerFrame s (applyBlock (callerSetup rs) s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro j hj _ _ _ _ _ _
 have a:j≠2881:=by omega
 have b:j≠2880:=by omega
 have c:j≠2866:=by omega
 have d:j≠2850:=by omega
 simp [callerSetup,applyBlock,Op.apply,writeNat,next,a,b,c,d]
lemma headCost_columns (q:ℕ) (r:Record) : headCost (r.withColumns q)=headCost r := rfl
lemma loopCost_columns (q:ℕ) (rs:List Record) : loopCost (rs.map (Record.withColumns q))=loopCost rs := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [List.map_cons,loopCost,headCost_columns,ih]

/-- Actual continuous finite-bytecode execution, from an unprinted bank.
All header reads, stores, comparisons, arithmetic and continuations are counted.
Only ordinary template body geometry and integer envelopes are supplied. -/
theorem caller_execution (rs:List Record) (A B q n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (hq:s.natReg 2599=q) (pc:s.pc=0) (hs:WordBound B s)
 (values:∀v∈serialize rs,v≤B) (extent:A+(serialize rs).length+1≤B)
 (code:callerHalt rs+1≤B) (good:∀r∈rs,WellFormed r) (width:∀r∈rs,r.width+1≤B) : ∃u,
 BoundedExecution (callerProgram rs) n x B s (callerEntry rs+4+loopCost rs+1) u ∧
 PrintedRecords A (rs.map (Record.withColumns q)) u ∧
 u.natReg 2850=A+(serialize rs).length ∧
 (∀z,z<A∨A+(serialize rs).length≤z→u.natHeap z=s.natHeap z) ∧ CallerFrame s u := by
 have len:callerEntry rs=3*(serialize rs).length+3*rs.length+7:=
   UniformFixedNetworkLiteralDecoderMachine.program_length rs
 obtain ⟨t,run,bank,outside,frame⟩:=UniformFixedNetworkLiteralDecoderMachine.execution rs A B q n x s base hq pc hs values extent
   (by unfold callerHalt callerLoop at code;rw [len] at code;omega)
 have call:=UniformBoundedAssembly.boundedExecution_placed (caller_printer_code rs)
   (by simp only [Nat.zero_add];change callerEntry rs≤B;unfold callerHalt callerLoop at code;omega)
   (by unfold callerHalt callerLoop at code;omega) run
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at call
 let t':State:={t with pc:=callerEntry rs}
 have bt:t'.natReg 2600=A:=by
   change t.natReg 2600=A
   rw [frame.natReg 2600 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
   exact base
 have safe:=callerSetup_safe rs A B t' bt (by omega)
 have setupRun:=block_runs (callerSetup rs) (callerProgram rs) (callerEntry rs) n B x t'
   (caller_setup_code rs) rfl call.final_bound (by change callerEntry rs+4≤B;unfold callerHalt callerLoop at code;omega) safe.1 safe.2
 let ready:=applyBlock (callerSetup rs) t'
 obtain ⟨pointer,endptr⟩:=callerSetup_spec rs A t' bt
 have readyBank:PrintedRecords A (rs.map (Record.withColumns q)) ready:=by
   apply UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport bank
   intro z _;rfl
 let start:State:={ready with pc:=0}
 have bstart:=changePC_bound B ready 0 setupRun.final_bound (by omega)
 have sbank:PrintedRecords A (rs.map (Record.withColumns q)) start:=by
   apply UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport readyBank
   intro z _;rfl
 have llength:=UniformFixedNetworkScheduleMachine.serialize_columns_length q rs
 obtain ⟨u,loop,up,lf⟩:=loop_execution (rs.map (Record.withColumns q)) A B n x start pointer
   (by simpa only [llength] using endptr) rfl bstart sbank
   (by intro r hr;obtain ⟨t,ht,eq⟩:=(List.mem_map (f:=Record.withColumns q)).mp hr;rw [←eq];exact withColumns_wellFormed q t (good t ht))
   (by intro r hr;obtain ⟨t,ht,eq⟩:=(List.mem_map (f:=Record.withColumns q)).mp hr;rw [←eq];exact width t ht)
   (by rw [llength];omega) (by unfold callerHalt callerLoop at code;omega)
 have loopRun:=UniformBoundedAssembly.boundedExecution_placed (caller_loop_code rs)
   (by rw [loopProgram_length];unfold callerHalt at code;omega) (by omega) loop
 have startEq:UniformAssembly.placed (callerLoop rs) start=ready:=by
   have rp:ready.pc=callerLoop rs:=by simp [ready,UniformTensorMonomialMachine.applyBlock_pc,t',callerLoop,callerSetup]
   change {ready with pc:=callerLoop rs}=ready
   rw [←rp]
 rw [startEq] at loopRun
 let done:State:={u with pc:=callerHalt rs}
 have halt:BoundedExecution (callerProgram rs) n x B done 1 done:=
   .halt loopRun.final_bound (by simp [step,done,caller_halt_code])
 refine ⟨done,?_,?_,?_,?_,?_⟩
 · convert call.executes (setupRun.executes (loopRun.executes halt)) using 1
   rw [←len,loopCost_columns,show (callerSetup rs).length=4 from rfl];omega
 · apply UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport readyBank
   intro z _;exact congrFun lf.natHeap z
 · simpa only [llength] using up
 · intro z hz
   change u.natHeap z=s.natHeap z
   rw [lf.natHeap]
   change t.natHeap z=s.natHeap z
   exact outside z hz
 · have sf:=callerSetup_frame rs t'
   refine ⟨lf.scalarHeap.trans sf.scalarHeap |>.trans frame.scalarHeap,
     lf.scalarReg.trans sf.scalarReg |>.trans frame.scalarReg,
     lf.outputs.trans sf.outputs |>.trans frame.outputs,
     lf.roots.trans sf.roots |>.trans frame.roots,?_⟩
   intro j hj h1 h2 h3 h4 h5 h6
   exact (lf.natReg j (by omega)).trans ((sf.natReg j hj h1 h2 h3 h4 h5 h6).trans (frame.natReg j h1 h2 h3 h4 h5 h6))

lemma base_width_bound (r:Record) (hr:r∈UniformFixedNetworkScheduleMachine.baseSchedule) :
 r.width+1≤UniformFixedNetworkScheduleMachine.literalCap (serialize UniformFixedNetworkScheduleMachine.baseSchedule)+1 := by
 have mem:r.width∈r.data:=by simp [Record.data,Record.header]
 have bound:=UniformFixedNetworkScheduleMachine.member_le_cap _ r.width
   (UniformFixedNetworkScheduleMachine.serialize_mem.mpr ⟨r,hr,mem⟩)
 omega
/-- One literal program independent of runtime q and input length. The huge
fixed seed stays symbolic; no finite seed enumeration is needed for this proof. -/
def fixedProgram : Program := callerProgram UniformFixedNetworkScheduleMachine.baseSchedule
def fixedCost : ℕ := callerEntry UniformFixedNetworkScheduleMachine.baseSchedule+4+
 loopCost UniformFixedNetworkScheduleMachine.baseSchedule+1
lemma fixedCost_bound : fixedCost≤3*(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+
 44*UniformFixedNetworkScheduleMachine.baseSchedule.length+14 := by
 have h:=loopCost_bound UniformFixedNetworkScheduleMachine.baseSchedule baseSchedule_wellFormed
 unfold fixedCost callerEntry
 rw [UniformFixedNetworkLiteralDecoderMachine.program_length]
 omega
/-- Fixed bytecode from an unprinted Nat bank through runtime-q headers and
actual seven-opcode traversal. All geometry is discharged for the real seed.
No intermediate table/header/action premise or host phase write is supplied.
Residual/scalar/padding child execution and a global uniform runtime remain open. -/
theorem fixed_execution (A B q n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (hq:s.natReg 2599=q) (pc:s.pc=0) (hs:WordBound B s)
 (literals:UniformFixedNetworkScheduleMachine.literalCap (serialize UniformFixedNetworkScheduleMachine.baseSchedule)+1≤B)
 (extent:A+(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+1≤B)
 (code:callerHalt UniformFixedNetworkScheduleMachine.baseSchedule+1≤B) : ∃u,
 BoundedExecution fixedProgram n x B s fixedCost u ∧
 PrintedRecords A (UniformFixedNetworkScheduleMachine.scheduleRecords q) u ∧
 u.natReg 2850=A+(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length ∧
 (∀z,z<A∨A+(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length≤z→u.natHeap z=s.natHeap z) ∧ CallerFrame s u := by
 exact caller_execution UniformFixedNetworkScheduleMachine.baseSchedule A B q n x s base hq pc hs
   (by intro v hv;exact (UniformFixedNetworkScheduleMachine.member_le_cap _ v hv).trans (by omega))
   extent code baseSchedule_wellFormed (by intro r hr;exact (base_width_bound r hr).trans literals)

end
end ExactFourierCircuits.UniformFixedNetworkOpcodeMachine
