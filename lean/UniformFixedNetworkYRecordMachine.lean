import UniformFixedNetworkChildDispatchMachine
import UniformPreparedYTranslationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkYRecordMachine
open UniformMachine UniformAssembly BinaryFrames
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed bitWords)
open UniformFixedNetworkShearChildMachine (Present roleBase role_bound)
open UniformXorTranslationMachine (volume)
namespace Y
export UniformPreparedYTranslationMachine (program execution Frame Changed runtime)
end Y
namespace V
export UniformFixedNetworkChildDispatchMachine (volumeProgram volume_execution VolumeFrame)
end V

/-- One row of the actual opcode3 descriptor: physical role then original-width bits. -/
structure Direction (R w : ℕ) where
 role : Fin R
 vector : Vec (Fin w)
def Direction.data {R w : ℕ} (d : Direction R w) : List ℕ := d.role.val :: bitWords d.vector
lemma Direction.data_length {R w : ℕ} (d : Direction R w) : d.data.length=w+1 := by simp [Direction.data,UniformFixedNetworkScheduleMachine.bitWords_length]
def body {R w : ℕ} (ds : List (Direction R w)) : List ℕ := (ds.map Direction.data).flatten
lemma body_length {R w : ℕ} (ds : List (Direction R w)) : (body ds).length=(w+1)*ds.length := by
 induction ds with
 | nil=>simp [body]
 | cons d ds ih=>
   simp only [body,List.map_cons,List.flatten_cons,List.length_append] at *
   rw [Direction.data_length,ih,List.length_cons];ring

def record {R : ℕ} (q w : ℕ) (ds : List (Direction R w)) : Record := ⟨3,q,w,0,0,0,ds.length,0,body ds⟩
lemma record_good {R : ℕ} (q w : ℕ) (ds : List (Direction R w)) : UniformFixedNetworkOpcodeMachine.WellFormed (record q w ds) := by
 constructor
 · norm_num [record]
 · simp [record,UniformFixedNetworkOpcodeMachine.bodyLength,body_length,Nat.mul_comm]
lemma record_length {R : ℕ} (q w : ℕ) (ds : List (Direction R w)) : (record q w ds).data.length=8+(w+1)*ds.length := by simp [record,Record.data_length,body_length]
def boot : List Op := [.literal 3383 1,.literal 3381 0,.mul 3380 2850 3383,
 .add 3380 3380 2860,.mul 3382 2857 3383,.add 3384 2853 3383]
def setup : List Op := [.getNat 3386 3380,.mul 3387 3386 3304,.add 3360 3300 3387,
 .add 3370 3380 3383,.mul 3369 2853 3383,.mul 3420 2852 3383,.mul 3421 3389 3383]
def tail : List Op := [.add 3381 3381 3383,.add 3380 3380 3384]
def finish : List Op := [.mul 2850 2865 3383]
/-- q,width,count and role/direction pointers are loaded from the real record;
all sizing, offsets and child transitions occur in this one finite program. -/
def program : Program := UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++
 V.volumeProgram.map (relocate 52 62)++boot.map Op.code++[.branchLT 3381 3382 69 195]++
 setup.map Op.code++Y.program.map (relocate 76 192)++tail.map Op.code++[.jump 68]++finish.map Op.code++[.halt]
lemma program_length : program.length=197 := by
 simp only [program,List.length_append,List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length,
  UniformFixedNetworkChildDispatchMachine.volumeProgram_length,UniformPreparedYTranslationMachine.program_length]
 rfl
lemma reader_code : CodeAt UniformFixedNetworkOpcodeMachine.headProgram program 0 52 := by intro i hi;change i<52 at hi;interval_cases i <;> rfl
lemma volume_code : CodeAt V.volumeProgram program 52 62 := by intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma boot_code : BlockAt boot program 62 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
lemma setup_code : BlockAt setup program 69 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma child_code : CodeAt Y.program program 76 192 := by intro i hi;change i<116 at hi;interval_cases i <;> rfl
lemma tail_code : BlockAt tail program 192 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma finish_code : BlockAt finish program 195 := by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma branch_at : program[68]?=some (.branchLT 3381 3382 69 195) := rfl
lemma jump_at : program[194]?=some (.jump 68) := rfl
lemma halt_at : program[196]?=some .halt := rfl

def runtime (q w rows : ℕ) := rows*(Y.runtime q w+11)+4*(q*w)+52
noncomputable section

def values {R : ℕ} (q w : ℕ) (d : Direction R w) (f : Fin R→Fin (volume q w)→Scalar) : Fin R→Fin (volume q w)→Scalar :=
 fun r j=>if r=d.role then UniformXorTranslationMachine.translated q w
  (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val
  (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).isLt (f r) j else f r j
def actions {R : ℕ} (q w : ℕ) (ds : List (Direction R w)) (f : Fin R→Fin (volume q w)→Scalar) :=
 ds.foldl (fun f d=>values q w d f) f
lemma actions_cons {R : ℕ} (q w : ℕ) (d : Direction R w) (ds : List (Direction R w)) (f : Fin R→Fin (volume q w)→Scalar) :
 actions q w (d::ds) f=actions q w ds (values q w d f) := rfl

/-- Scratch includes the child footprint; ordinary global inputs remain read-only. -/
def Changed (r : ℕ) : Prop := Y.Changed r ∨ r=3360 ∨ r=3369 ∨ r=3370 ∨ r=3380 ∨ r=3381 ∨ r=3386 ∨ r=3387
structure Frame (q A W E T w : ℕ) (s u : State) : Prop where
 natHeap : UniformXorTableMachine.Outside q T s.natHeap u
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg : ∀ r, r ≠ 100 → r ≠ 114 → u.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,(z<A∨A+W≤z)→(z<E∨E+volume q w≤z)→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (q A W E T w : ℕ) (s : State) : Frame q A W E T w s s := ⟨fun _ _=>rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.pc {q A W E T w : ℕ} {s u : State} (f : Frame q A W E T w s u) (p : ℕ) : Frame q A W E T w s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {q A W E T w : ℕ} {s u v : State} (f : Frame q A W E T w s u) (g : Frame q A W E T w u v) : Frame q A W E T w s v :=
 ⟨fun z h=>(g.natHeap z h).trans (f.natHeap z h),g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h j=>(g.scalarReg r h j).trans (f.scalarReg r h j),
 fun z h j=>(g.scalarHeap z h j).trans (f.scalarHeap z h j)⟩
lemma frame_setup (q A W E T w : ℕ) (s : State) : Frame q A W E T w s (applyBlock setup s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed at h;simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma frame_tail (q A W E T w : ℕ) (s : State) : Frame q A W E T w s (applyBlock tail s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [tail,applyBlock,Op.apply,writeNat,next]
lemma Frame.child {R q w E T : ℕ} (A : ℕ) (d : Direction R w) {s u : State}
 (f : Y.Frame q (roleBase A (volume q w) d.role.val) E T w s u) : Frame q A (R*volume q w) E T w s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,?_⟩
 · intro r h;exact f.natReg r (fun h'=>h (Or.inl h'))
 · intro z h j
   have bd:=role_bound A (volume q w) d.role
   have lb:A≤roleBase A (volume q w) d.role.val:=by unfold roleBase;omega
   exact f.scalarHeap z (by omega) j

structure Header (q w A E T cursor index count : ℕ) (s : State) : Prop where
 pc : s.pc=68
 base : s.natReg 3300=A
 volume : s.natReg 3304=UniformXorTranslationMachine.volume q w
 q : s.natReg 2852=q
 width : s.natReg 2853=w
 buffer : s.natReg 3364=E
 table : s.natReg 3389=T
 cursor : s.natReg 3380=cursor
 index : s.natReg 3381=index
 count : s.natReg 3382=count
 one : s.natReg 3383=1
 stride : s.natReg 3384=w+1

def PrintedDirections {R w : ℕ} (cursor : ℕ) : List (Direction R w)→State→Prop
 | [],_=>True
 | d::ds,s=>Printed cursor d.data s ∧ PrintedDirections (cursor+w+1) ds s
lemma printed_directions {R w : ℕ} (ds : List (Direction R w)) (P : ℕ) (s : State) (h : Printed P (body ds) s) : PrintedDirections P ds s := by
 induction ds generalizing P with
 | nil=>trivial
 | cons d ds ih=>
   have split:=h.split
   refine ⟨split.1,?_⟩
   simpa [Direction.data_length,Nat.add_assoc] using ih (P+d.data.length) split.2
lemma PrintedDirections.transport {R q w T P : ℕ} {ds : List (Direction R w)} {s u : State}
 (h : PrintedDirections P ds s) (endbound : P+(w+1)*ds.length≤T)
 (eq : UniformXorTableMachine.Outside q T s.natHeap u) : PrintedDirections P ds u := by
 induction ds generalizing P with
 | nil=>trivial
 | cons d ds ih=>
   refine ⟨?_,?_⟩
   · intro j hj
     rw [eq (P+j) (Or.inl (by rw [Direction.data_length] at hj;simp only [List.length_cons] at endbound;nlinarith))]
     exact h.1 j hj
   · exact ih h.2 (by simp only [List.length_cons] at endbound;nlinarith)

lemma round_execution {R : ℕ} (q w A E T P i count B n : ℕ) (x : Fin n→ℂ)
 (d : Direction R w) (f : Fin R→Fin (volume q w)→Scalar) (s : State)
 (h : Header q w A E T P i count s) (yes : i<count)
 (row : Printed P d.data s) (data : Present A R (volume q w) f s)
 (bound : WordBound B s) (code : 197≤B) (endbound : P+w+1≤T)
 (separate : A+R*volume q w≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+volume q w≤B) : ∃v,
 BoundedRuns program n x B s (Y.runtime q w+11) v ∧
 Header q w A E T (P+w+1) (i+1) count v ∧
 Present A R (volume q w) (values q w d f) v ∧ Frame q A (R*volume q w) E T w s v := by
 let entry:=setPC s 69
 have eb:=changePC_bound B s 69 bound (by omega)
 have enter : BoundedRuns program n x B s 1 entry := .next bound
  (by simp [step,h.pc,branch_at,h.index,h.count,yes,entry,setPC]) (.refl eb)
 have roleCell : s.natHeap P=some d.role.val:=by simpa [Direction.data] using row 0 (by simp [Direction.data])
 have roleB := (bound.2.2.1 P _ roleCell).2
 have rb:=role_bound A (volume q w) d.role
 have lower : A≤roleBase A (volume q w) d.role.val := by unfold roleBase;omega
 have db : A+d.role.val*volume q w≤B := by change A+d.role.val*volume q w+volume q w≤A+R*volume q w at rb;omega
 have vB : volume q w≤B := by omega
 have qB:=bound.2.1 2852
 have wB:=bound.2.1 2853
 have tB:=bound.2.1 3389
 have safe : readable setup entry∧peak setup entry≤B := by
  simp [entry,setPC,setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
   h.base,h.volume,h.cursor,h.one,h.q,h.width,h.table,roleCell]
  rw [h.q] at qB;rw [h.width] at wB;rw [h.table] at tB
  have prodB : d.role.val*volume q w≤B:=by omega
  omega
 have caller:=block_runs setup program 69 n B x entry setup_code rfl eb (by change 76≤B;omega) safe.1 safe.2
 let ready:=applyBlock setup entry
 let ce:=setPC ready 0
 have cb:=changePC_bound B ready 0 caller.final_bound (by omega)
 have ca : ce.natReg 3360=roleBase A (volume q w) d.role.val := by
  simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.cursor,h.base,h.volume,roleCell,roleBase]
 have cq : ce.natReg 3420=q := by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.q,h.one]
 have cw : ce.natReg 3369=w := by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.width,h.one]
 have ct : ce.natReg 3421=T := by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.table,h.one]
 have cu : ce.natReg 3370=P+1 := by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.cursor,h.one]
 have cE : ce.natReg 3364=E := by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,h.buffer]
 have desc : UniformRepeatedMaskMachine.Source (P+1) d.vector ce := by
  intro j
  have hh:=row (j.val+1) (by rw [Direction.data_length];have hj:=j.isLt;omega)
  simpa [UniformRepeatedMaskMachine.Source,ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next,
   Direction.data,bitWords,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
 have present : ∀j,ce.scalarHeap (roleBase A (volume q w) d.role.val+j.val)=some (f d.role j) := by
  intro j;exact data d.role j
 obtain ⟨child,cr,pc,out,cf⟩:=Y.execution q w (roleBase A (volume q w) d.role.val) E T (P+1) B n d.vector x
  (f d.role) ce rfl cq ct cw cu ca cE desc present (by omega) (by omega) cb (by omega) tableEnd extent
 have placed:=UniformBoundedAssembly.boundedExecution_placed child_code (by change 192≤B;omega) (by omega) cr
 have same : UniformAssembly.placed 76 ce=ready := by
  simp [UniformAssembly.placed,ce,ready,entry,setPC,setup,applyBlock,Op.apply,writeNat,next]
 rw [same] at placed
 let ret:=setPC child 192
 have keep (r : ℕ) (hr : ¬Y.Changed r) : ret.natReg r=ready.natReg r:=cf.natReg r hr
 have idx : ret.natReg 3381=i := by rw [keep 3381 (by unfold UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.index
 have cur : ret.natReg 3380=P := by rw [keep 3380 (by unfold UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.cursor
 have one : ret.natReg 3383=1 := by rw [keep 3383 (by unfold UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.one
 have stride : ret.natReg 3384=w+1 := by rw [keep 3384 (by unfold UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.stride
 have cbound : count≤B := by have b:=bound.2.1 3382;rw [h.count] at b;exact b
 have tailSafe : readable tail ret∧peak tail ret≤B := by
  simp [tail,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,idx,cur,one,stride];omega
 have tr:=block_runs tail program 192 n B x ret tail_code rfl placed.final_bound (by change 194≤B;omega) tailSafe.1 tailSafe.2
 let advanced:=applyBlock tail ret
 let v:=setPC advanced 68
 have vb:=changePC_bound B advanced 68 tr.final_bound (by omega)
 have jump : BoundedRuns program n x B advanced 1 v:=.next tr.final_bound
  (by simp [step,advanced,tail,applyBlock,Op.apply,writeNat,next,ret,setPC,jump_at,v]) (.refl vb)
 have frame : Frame q A (R*volume q w) E T w s v :=
  (((Frame.refl q A (R*volume q w) E T w s).pc 69).trans (frame_setup q A (R*volume q w) E T w entry) |>.pc 0)
   |>.trans (Frame.child A d cf) |>.pc 192 |>.trans (frame_tail q A (R*volume q w) E T w ret) |>.pc 68
 have head : Header q w A E T (P+w+1) (i+1) count v := by
  constructor
  · rfl
  · rw [frame.natReg 3300 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.base
  · rw [frame.natReg 3304 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.volume
  · rw [frame.natReg 2852 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.q
  · rw [frame.natReg 2853 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.width
  · rw [frame.natReg 3364 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.buffer
  · rw [frame.natReg 3389 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.table
  · simp [v,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next,cur,stride,Nat.add_assoc]
  · simp [v,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next,idx,one]
  · change ret.natReg 3382=count
    rw [keep 3382 (by unfold UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)];exact h.count
  · simpa [v,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next] using one
  · simpa [v,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next] using stride
 have result : Present A R (volume q w) (values q w d f) v := by
  intro r j
  by_cases eq : r=d.role
  · subst r
    simpa [v,setPC,advanced,tail,applyBlock,Op.apply,writeNat,next,ret,values,roleBase] using out j
  · have ne : r.val≠d.role.val := fun e=>eq (Fin.ext e)
    have hj:=j.isLt
    have lowbuf : A+r.val*volume q w+j.val<E := by
     have bd:=role_bound A (volume q w) r
     change A+r.val*volume q w+volume q w≤A+R*volume q w at bd
     omega
    have outside : A+r.val*volume q w+j.val<roleBase A (volume q w) d.role.val ∨
     roleBase A (volume q w) d.role.val+volume q w≤A+r.val*volume q w+j.val := by
     unfold roleBase
     rcases lt_or_gt_of_ne ne with lt|gt
     · have b:=Nat.mul_le_mul_right (volume q w) (show r.val+1≤d.role.val by omega)
       exact Or.inl (by nlinarith only [b,hj])
     · have b:=Nat.mul_le_mul_right (volume q w) (show d.role.val+1≤r.val by omega)
       exact Or.inr (by nlinarith only [b,hj])
    change child.scalarHeap (A+r.val*volume q w+j.val)=_
    rw [cf.scalarHeap _ outside (Or.inl lowbuf)]
    simp only [values,ite_eq_right_iff.mpr (fun e=>False.elim (eq e))]
    exact data r j
 refine ⟨v,?_,head,result,frame⟩
 convert enter.trans (caller.trans (placed.trans (tr.trans jump))) using 1
 simp only [setup,tail,List.length_cons,List.length_nil]
 omega

lemma loop_runs {R : ℕ} (q w A E T count B n : ℕ) (x : Fin n→ℂ) (ds : List (Direction R w))
 (code : 197≤B) (separate : A+R*volume q w≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+volume q w≤B) :
 ∀i P s (f : Fin R→Fin (volume q w)→Scalar), i+ds.length=count→Header q w A E T P i count s→
 PrintedDirections P ds s→Present A R (volume q w) f s→WordBound B s→P+(w+1)*ds.length≤T→∃v,
 BoundedRuns program n x B s ((Y.runtime q w+11)*ds.length+1) (setPC v 195) ∧
 Present A R (volume q w) (actions q w ds f) v ∧ Frame q A (R*volume q w) E T w s v := by
 induction ds with
 | nil=>
  intro i P s f eq h bank data bound endbound
  have stop : ¬i<count := by simp only [List.length_nil] at eq;omega
  refine ⟨s,?_,data,Frame.refl q A (R*volume q w) E T w s⟩
  exact .next bound (by simp [step,h.pc,branch_at,h.index,h.count,stop,setPC])
   (.refl (changePC_bound B s 195 bound (by omega)))
 | cons d ds ih=>
  intro i P s f eq h bank data bound endbound
  have yes : i<count := by simp only [List.length_cons] at eq;omega
  have rowEnd : P+w+1≤T := by simp only [List.length_cons] at endbound;nlinarith
  obtain ⟨mid,round,head,out,frame⟩:=round_execution q w A E T P i count B n x d f s h yes bank.1 data bound code rowEnd separate tableEnd extent
  have tailEnd : P+w+1+(w+1)*ds.length≤T := by simp only [List.length_cons] at endbound;nlinarith
  have nextBank:=PrintedDirections.transport bank.2 tailEnd frame.natHeap
  obtain ⟨v,last,result,rest⟩:=ih (i+1) (P+w+1) mid (values q w d f)
   (by simp only [List.length_cons] at eq;omega) head nextBank out round.final_bound tailEnd
  refine ⟨v,?_,result,frame.trans rest⟩
  convert round.trans last using 1
  simp only [List.length_cons];ring

def FullChanged (r : ℕ) : Prop := Changed r ∨ r=3382 ∨ r=3383 ∨ r=3384 ∨ (2850 ≤ r∧r<2877) ∨ (3302 ≤ r∧r<3307)
structure FullFrame (q A W E T w : ℕ) (s u : State) : Prop where
 natHeap : UniformXorTableMachine.Outside q T s.natHeap u
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬FullChanged r→u.natReg r=s.natReg r
 scalarReg : ∀ r, r ≠ 100 → r ≠ 114 → u.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,(z<A∨A+W≤z)→(z<E∨E+volume q w≤z)→u.scalarHeap z=s.scalarHeap z
lemma FullFrame.pc {q A W E T w : ℕ} {s u : State} (f : FullFrame q A W E T w s u) (p : ℕ) : FullFrame q A W E T w s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma FullFrame.trans {q A W E T w : ℕ} {s u v : State} (f : FullFrame q A W E T w s u) (g : FullFrame q A W E T w u v) : FullFrame q A W E T w s v :=
 ⟨fun z h=>(g.natHeap z h).trans (f.natHeap z h),g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h j=>(g.scalarReg r h j).trans (f.scalarReg r h j),
 fun z h j=>(g.scalarHeap z h j).trans (f.scalarHeap z h j)⟩
lemma FullFrame.reader (q A W E T w : ℕ) {s u : State} (f : UniformFixedNetworkOpcodeMachine.Frame s u) : FullFrame q A W E T w s u := by
 refine ⟨fun z _=>congrFun f.natHeap z,f.outputs,f.roots,?_,fun r _ _=>congrFun f.scalarReg r,fun z _ _=>congrFun f.scalarHeap z⟩
 intro r h;apply f.natReg;unfold FullChanged at h;omega
lemma FullFrame.volume (q A W E T w : ℕ) {s u : State} (f : V.VolumeFrame s u) : FullFrame q A W E T w s u := by
 refine ⟨fun z _=>congrFun f.natHeap z,f.outputs,f.roots,?_,fun r _ _=>congrFun f.scalarReg r,fun z _ _=>congrFun f.scalarHeap z⟩
 intro r h;apply f.natReg;unfold FullChanged at h;omega
lemma FullFrame.child {q A W E T w : ℕ} {s u : State} (f : Frame q A W E T w s u) : FullFrame q A W E T w s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,f.scalarHeap⟩
 intro r h;exact f.natReg r (fun h'=>h (Or.inl h'))
lemma full_boot (q A W E T w : ℕ) (s : State) : FullFrame q A W E T w s (applyBlock boot s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold FullChanged Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma full_finish (q A W E T w : ℕ) (s : State) : FullFrame q A W E T w s (applyBlock finish s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold FullChanged at h;simp (disch:=omega) [finish,applyBlock,Op.apply,writeNat,next]

/-- Execute the real opcode3 record, including its reader, binary sizing,
role offsets and every inline bit descriptor. Tables/masks/child headers
are produced by instructions, with arbitrary dirty fresh workspaces. -/
theorem execution {R : ℕ} (q w A E T P B n : ℕ) (x : Fin n→ℂ)
 (ds : List (Direction R w)) (f : Fin R→Fin (volume q w)→Scalar) (s : State)
 (pc : s.pc=0) (ptr : s.natReg 2850=P) (base : s.natReg 3300=A)
 (buffer : s.natReg 3364=E) (table : s.natReg 3389=T)
 (bank : Printed P (record q w ds).data s) (data : Present A R (volume q w) f s)
 (bound : WordBound B s) (code : 197≤B) (sourceBeforeTable : P+(record q w ds).data.length≤T)
 (separate : A+R*volume q w≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+volume q w≤B)
 (width : w+1≤B) : ∃u,
 BoundedExecution program n x B s (runtime q w ds.length) u ∧
 Present A R (volume q w) (actions q w ds f) u ∧ u.natReg 2850=P+(record q w ds).data.length ∧
 FullFrame q A (R*volume q w) E T w s u := by
 have vb : volume q w≤B := by omega
 have tablePtr : P+8+(w+1)*ds.length≤T := by rw [record_length] at sourceBeforeTable;omega
 obtain ⟨read,reader,fields,bodySize,nextptr,rf⟩:=UniformFixedNetworkOpcodeMachine.head_execution P B n (record q w ds) x s ptr pc bound bank
  (record_good q w ds) (by omega) width (by omega)
 have rr:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 52≤B;omega) (by omega) reader
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at rr
 let ve:=setPC read 0
 have vbe:=changePC_bound B read 0 reader.final_bound (by omega)
 obtain ⟨vol,vr,bits,volvalue,vf,_⟩:=V.volume_execution q w B n x ve rfl
  (by simpa [ve,setPC,record] using fields.columns) (by simpa [ve,setPC,record] using fields.width) vbe vb (by omega)
 have vv:=UniformBoundedAssembly.boundedExecution_placed volume_code (by change 62≤B;omega) (by omega) vr
 have ventry : placed 52 ve=setPC read 52 := rfl
 rw [ventry] at vv
 let bs:=setPC vol 62
 have keep (r : ℕ) (hr : r<3302∨3307≤r) : bs.natReg r=read.natReg r := vf.natReg r hr
 have cb : bs.natReg 2850=P := (keep 2850 (by omega)).trans fields.cursor
 have eight : bs.natReg 2860=8 := (keep 2860 (by omega)).trans fields.eight
 have dim : bs.natReg 2857=ds.length := (keep 2857 (by omega)).trans fields.dimension
 have wval : bs.natReg 2853=w := (keep 2853 (by omega)).trans fields.width
 have qval : bs.natReg 2852=q := (keep 2852 (by omega)).trans fields.columns
 have vval : bs.natReg 3304=volume q w := volvalue
 have rb : bs.natReg 3300=A := (keep 3300 (by omega)).trans ((rf.natReg 3300 (by omega)).trans base)
 have eb : bs.natReg 3364=E := (keep 3364 (by omega)).trans ((rf.natReg 3364 (by omega)).trans buffer)
 have tb : bs.natReg 3389=T := (keep 3389 (by omega)).trans ((rf.natReg 3389 (by omega)).trans table)
 have dimB : ds.length≤B := by have h:=vv.final_bound.2.1 2857;change bs.natReg 2857≤B at h;rw [dim] at h;exact h
 have safe : readable boot bs∧peak boot bs≤B := by
  simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,cb,eight,dim,wval];omega
 have br:=block_runs boot program 62 n B x bs boot_code rfl vv.final_bound (by change 68≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot bs
 have bsPc : bs.pc=62 := rfl
 have header : Header q w A E T (P+8) 0 ds.length ready := by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,rb,vval,qval,wval,eb,tb,cb,eight,dim,bsPc]
 have readyData : Present A R (volume q w) f ready := by
  intro r j;change vol.scalarHeap (A+r.val*volume q w+j.val)=_
  rw [vf.scalarHeap];change read.scalarHeap (A+r.val*volume q w+j.val)=_
  rw [rf.scalarHeap];exact data r j
 have readyBody : PrintedDirections (P+8) ds ready := by
  have pp:=printed_directions ds (P+8) s bank.split.2
  apply PrintedDirections.transport (q:=q) (T:=T) (u:=ready) pp tablePtr
  intro z _;change vol.natHeap z=s.natHeap z
  rw [vf.natHeap];exact congrFun rf.natHeap z
 obtain ⟨child,lr,out,lf⟩:=loop_runs q w A E T ds.length B n x ds code separate tableEnd extent
  0 (P+8) ready f (by simp) header readyBody readyData br.final_bound tablePtr
 let ret:=setPC child 195
 have one : ret.natReg 3383=1 := by
  change child.natReg 3383=1
  rw [lf.natReg 3383 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)]
  exact header.one
 have nextValue : ret.natReg 2865=P+(record q w ds).data.length := by
  change child.natReg 2865=_
  rw [lf.natReg 2865 (by unfold Changed UniformPreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)]
  change vol.natReg 2865=_
  rw [vf.natReg 2865 (by omega)]
  simpa [ve,setPC] using nextptr
 have endB : P+(record q w ds).data.length≤B := by omega
 have safeEnd : readable finish ret∧peak finish ret≤B := by simp [finish,readable,peak,Op.readable,Op.peak,nextValue,one];omega
 have fr:=block_runs finish program 195 n B x ret finish_code rfl lr.final_bound (by change 196≤B;omega) safeEnd.1 safeEnd.2
 let u:=applyBlock finish ret
 have halt : BoundedExecution program n x B u 1 u := .halt fr.final_bound
  (by simp [step,u,finish,applyBlock,Op.apply,writeNat,next,ret,setPC,halt_at])
 have frame : FullFrame q A (R*volume q w) E T w s u :=
  ((FullFrame.reader q A (R*volume q w) E T w rf).pc 0 |>.trans (FullFrame.volume q A (R*volume q w) E T w vf) |>.pc 62 |>.trans (full_boot q A (R*volume q w) E T w bs))
   |>.trans (FullFrame.child lf) |>.pc 195 |>.trans (full_finish q A (R*volume q w) E T w ret)
 refine ⟨u,?_,out,?_,frame⟩
 · convert rr.executes (vv.executes (br.executes (lr.executes (fr.executes halt)))) using 1
   norm_num [UniformFixedNetworkOpcodeMachine.headCost,record,boot,finish,runtime]
   ring
 · simp [u,finish,applyBlock,Op.apply,writeNat,next,nextValue,one]

/-- The actual generated table and descriptor work fit a fixed-width linear
array allowance. Width ≥3 is needed for the q-bit table cost absorption. -/
lemma runtime_linear (q w rows : ℕ) (hw : 3≤w) :
 runtime q w rows≤(rows*(17*w+101)+56)*volume q w := by
 have yr:=UniformPreparedYTranslationMachine.runtime_linear q w hw
 have m:=Nat.mul_le_mul_left rows (show Y.runtime q w+11≤(17*w+101)*volume q w by
  have v:=Nat.two_pow_pos (q*w);unfold volume at *;nlinarith only [yr,v])
 have bits : q*w≤volume q w := Nat.le_of_lt Nat.lt_two_pow_self
 have pos : 1≤volume q w := Nat.two_pow_pos (q*w)
 unfold runtime
 nlinarith only [m,bits,pos]

/-- Explicit binary coordinates identify the native role action with copied
F2 translation, with the Scalar dependency tag carried unchanged. -/
def coordinateValues {R : ℕ} (q w : ℕ) (d : Direction R w)
 (f : Fin R→Vec (Fin (q*w))→Scalar) : Fin R→Vec (Fin (q*w))→Scalar :=
 fun r z=>if r=d.role then f r (z+ColumnTerminalFlat.direction q d.vector) else f r z
lemma values_coordinates {R : ℕ} (q w : ℕ) (d : Direction R w)
 (f : Fin R→Vec (Fin (q*w))→Scalar) (r : Fin R) (j : Fin (volume q w)) :
 values q w d (fun r j=>f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j)) r j=
 coordinateValues q w d f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j) := by
 by_cases h : r=d.role
 · simp only [values,coordinateValues,h,ite_true,UniformXorTranslationMachine.translated,UniformXorTranslationMachine.partner]
   exact congrArg (f d.role) (UniformBinaryXorCoordinates.translated_address (k:=q*w) j (ColumnTerminalFlat.direction q d.vector))
 · simp only [values,coordinateValues,h,ite_false]
def coordinateActions {R : ℕ} (q w : ℕ) (ds : List (Direction R w)) (f : Fin R→Vec (Fin (q*w))→Scalar) :=
 ds.foldl (fun f d=>coordinateValues q w d f) f
lemma actions_coordinates {R : ℕ} (q w : ℕ) (ds : List (Direction R w))
 (f : Fin R→Vec (Fin (q*w))→Scalar) (r : Fin R) (j : Fin (volume q w)) :
 actions q w ds (fun r j=>f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j)) r j=
 coordinateActions q w ds f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j) := by
 induction ds generalizing f with
 | nil=>rfl
 | cons d ds ih=>
  rw [actions_cons]
  have eq : values q w d (fun r j=>f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j))=
   fun r j=>coordinateValues q w d f r (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j) := by
   funext r j;exact values_coordinates q w d f r j
  rw [eq]
  exact ih (coordinateValues q w d f)

end
end ExactFourierCircuits.UniformFixedNetworkYRecordMachine
