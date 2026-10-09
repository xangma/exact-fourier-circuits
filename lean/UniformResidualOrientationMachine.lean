import UniformRepeatedMaskMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualOrientationMachine
open UniformMachine UniformAssembly BinaryFrames
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformRepeatedMaskMachine (Source bits)
open scoped BigOperators
noncomputable section

def setPC (s:State)(p:ℕ):State:={s with pc:=p}
def boot:List Op:=[.literal 6220 0,.literal 6221 0,.literal 6222 1,.literal 6223 4,
 .literal 6224 0,.literal 6228 3,.binary .mul 4188 4131 6222]
def body:List Op:=[.binary .add 6225 4062 6220,.load 6226 6225,
 .binary .add 6224 6224 6226,.binary .mod 6224 6224 6223,.binary .add 6220 6220 6222]
def flip:List Op:=[.binary .add 4188 4188 6222,.literal 6229 2,.binary .mod 4188 4188 6229]
def program:Program:=boot.map Op.code++[.branchLT 6220 4061 8 14]++body.map Op.code++[.jump 7,
 .branchLT 6224 6228 18 15]++flip.map Op.code++[.halt]
lemma block_pc (ops:List Op)(s:State):(applyBlock ops s).pc=s.pc+ops.length:=by
 induction ops generalizing s with
 | nil=>rfl
 | cons o ops ih=>simp [applyBlock,ih,Op.apply_pc];omega
lemma program_length:program.length=19:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<7 at hi;interval_cases i <;>rfl
lemma body_code:BlockAt body program 8:=by intro i hi;change i<5 at hi;interval_cases i <;>rfl
lemma flip_code:BlockAt flip program 15:=by intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma branch_at:program[7]?=some (.branchLT 6220 4061 8 14):=rfl
lemma jump_at:program[13]?=some (.jump 7):=rfl
lemma choice_at:program[14]?=some (.branchLT 6224 6228 18 15):=rfl
lemma halt_at:program[18]?=some .halt:=rfl

def residue {w:ℕ}(v:Vec (Fin w))(i:ℕ):ℕ:=(∑j∈Finset.range i,bits v j)%4
lemma residue_zero {w:ℕ}(v:Vec (Fin w)):residue v 0=0:=by simp [residue]
lemma residue_succ {w:ℕ}(v:Vec (Fin w))(i:ℕ):residue v (i+1)=(residue v i+bits v i)%4:=by
 simp [residue,Finset.sum_range_succ,Nat.add_mod]
lemma residue_lt {w:ℕ}(v:Vec (Fin w))(i:ℕ):residue v i<4:=Nat.mod_lt _ (by decide)
def effective (raw weight:ℕ):ℕ:=if weight=3 then (raw+1)%2 else raw
def ticks {w:ℕ}(v:Vec (Fin w)):ℕ:=10+7*w+(if residue v w=3 then 3 else 0)
lemma ticks_bound {w:ℕ}(v:Vec (Fin w)):ticks v≤13+7*w:=by unfold ticks;split <;>omega

def Changed (j:ℕ):Prop:=j=4188∨j=6220∨j=6221∨j=6222∨j=6223∨j=6224∨j=6225∨j=6226∨j=6228∨j=6229
structure Frame (s t:State):Prop where
 natHeap:t.natHeap=s.natHeap
 scalarHeap:t.scalarHeap=s.scalarHeap
 scalarReg:t.scalarReg=s.scalarReg
 outputs:t.outputs=s.outputs
 roots:t.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→t.natReg j=s.natReg j
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s t u:State}(a:Frame s t)(b:Frame t u):Frame s u:=
 ⟨b.natHeap.trans a.natHeap,b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,
 b.outputs.trans a.outputs,b.roots.trans a.roots,fun j h=>(b.natReg j h).trans (a.natReg j h)⟩
lemma Frame.pc {s t:State}(a:Frame s t)(pc:ℕ):Frame s (setPC t pc):=
 ⟨a.natHeap,a.scalarHeap,a.scalarReg,a.outputs,a.roots,a.natReg⟩
lemma boot_frame (s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [boot,applyBlock,Op.apply,evalNat,writeNat,next]
lemma body_frame (s:State):Frame s (applyBlock body s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [body,applyBlock,Op.apply,evalNat,writeNat,next]
lemma flip_frame (s:State):Frame s (applyBlock flip s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj;unfold Changed at hj;simp (disch:=omega) [flip,applyBlock,Op.apply,evalNat,writeNat,next]

structure Fields (w U raw i:ℕ)(v:Vec (Fin w))(s:State):Prop where
 width:s.natReg 4061=w
 source:s.natReg 4062=U
 rawHeader:s.natReg 4131=raw
 value:s.natReg 4188=raw
 zero:s.natReg 6221=0
 one:s.natReg 6222=1
 four:s.natReg 6223=4
 three:s.natReg 6228=3
 index:s.natReg 6220=i
 weight:s.natReg 6224=residue v i
lemma Fields.pc {w U raw i:ℕ}{v:Vec (Fin w)}{s:State}
 (h:Fields w U raw i v s)(p:ℕ):Fields w U raw i v (setPC s p):=
 ⟨h.width,h.source,h.rawHeader,h.value,h.zero,h.one,h.four,h.three,h.index,h.weight⟩
lemma iteration (w U raw i B n:ℕ)(v:Vec (Fin w))(x:Fin n→ℂ)(s:State)
 (pc:s.pc=7)(h:Fields w U raw i v s)(src:Source U v s)(live:i<w)
 (bound:WordBound B s)(code:19≤B)(extent:U+w≤B):∃t,
 BoundedRuns program n x B s 7 t ∧ t.pc=7 ∧ Fields w U raw (i+1) v t ∧ Frame s t:=by
 have load:s.natHeap (U+i)=some (bits v i):=by simpa [bits,live] using src ⟨i,live⟩
 have bit:=UniformRepeatedMaskMachine.bits_lt v i
 have small:=residue_lt v i
 have nextSmall:=residue_lt v (i+1)
 let entry:=setPC s 8
 have eb:=changePC_bound B s 8 bound (by omega)
 have br:BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,pc,branch_at,h.index,h.width,live,entry,setPC]) (.refl eb)
 have safe:readable body entry∧peak body entry≤B:=by
  simp [body,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,entry,setPC,
   h.source,h.index,h.weight,h.one,h.four,load]
  omega
 have run:=block_runs body program 8 n B x entry body_code rfl eb (by change 13≤B;omega) safe.1 safe.2
 let ready:=applyBlock body entry
 let t:=setPC ready 7
 have tb:=changePC_bound B ready 7 run.final_bound (by omega)
 have jump:BoundedRuns program n x B ready 1 t:=.next run.final_bound
  (by simp [step,ready,body,applyBlock,Op.apply,evalNat,writeNat,next,entry,setPC,jump_at,t]) (.refl tb)
 have post:Fields w U raw (i+1) v t:=by
  constructor <;>simp [t,ready,setPC,body,applyBlock,Op.apply,evalNat,writeNat,next,entry,
   h.width,h.source,h.rawHeader,h.value,h.zero,h.one,h.four,h.three,h.index,h.weight,residue_succ,load]
 refine ⟨t,?_,rfl,post,(Frame.refl s).pc 8 |>.trans (body_frame entry) |>.pc 7⟩
 convert br.trans (run.trans jump) using 1; rfl
lemma loop_execution (w U raw i fuel B n:ℕ)(v:Vec (Fin w))(x:Fin n→ℂ)(s:State)
 (pc:s.pc=7)(h:Fields w U raw i v s)(src:Source U v s)(total:i+fuel=w)
 (bound:WordBound B s)(code:19≤B)(extent:U+w≤B):∃t,
 BoundedRuns program n x B s (7*fuel+1) t ∧ t.pc=14 ∧ Fields w U raw w v t ∧ Frame s t:=by
 induction fuel generalizing i s with
 | zero=>
  have eq:i=w:=by omega
  let t:=setPC s 14
  have tb:=changePC_bound B s 14 bound (by omega)
  refine ⟨t,.next bound ?_ (.refl tb),rfl,?_,(Frame.refl s).pc 14⟩
  · simp [step,pc,branch_at,h.index,h.width,eq,t,setPC]
  · simpa only [eq] using h.pc 14
 | succ fuel ih=>
  obtain ⟨u,run,up,hu,fr⟩:=iteration w U raw i B n v x s pc h src (by omega) bound code extent
  have source:Source U v u:=by simpa only [Source,fr.natHeap] using src
  obtain ⟨t,rt,tp,ht,ft⟩:=ih (i+1) u up hu source (by omega) run.final_bound
  refine ⟨t,?_,tp,ht,fr.trans ft⟩
  convert run.trans rt using 1
  ring

lemma finish (w U raw B n:ℕ)(v:Vec (Fin w))(x:Fin n→ℂ)(s:State)
 (pc:s.pc=14)(h:Fields w U raw w v s)(rawSmall:raw<2)(bound:WordBound B s)(code:19≤B):∃t,
 BoundedExecution program n x B s (2+if residue v w=3 then 3 else 0) t ∧ t.pc=18 ∧
 t.natReg 4188=effective raw (residue v w) ∧ Frame s t:=by
 by_cases weight:residue v w=3
 · let entry:=setPC s 15
   have eb:=changePC_bound B s 15 bound (by omega)
   have br:BoundedRuns program n x B s 1 entry:=.next bound
    (by simp [step,pc,choice_at,h.weight,h.three,weight,entry,setPC]) (.refl eb)
   have safe:readable flip entry∧peak flip entry≤B:=by
    simp [flip,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,entry,setPC,h.value,h.one]
    omega
   have run:=block_runs flip program 15 n B x entry flip_code rfl eb (by change 18≤B;omega) safe.1 safe.2
   let t:=applyBlock flip entry
   have tp:t.pc=18:=by rw [block_pc];rfl
   have done:BoundedExecution program n x B t 1 t:=.halt run.final_bound (by simp [step,tp,halt_at])
   refine ⟨t,?_,tp,?_,(Frame.refl s).pc 15 |>.trans (flip_frame entry)⟩
   · convert br.executes (run.executes done) using 1; simp [weight,flip]
   · simp [t,flip,applyBlock,Op.apply,evalNat,writeNat,next,entry,setPC,h.value,h.one,effective,weight]
 · simp only [ite_eq_right weight,Nat.add_zero]
   have small:=residue_lt v w
   have lt:residue v w<3:=by omega
   let t:=setPC s 18
   have tb:=changePC_bound B s 18 bound (by omega)
   refine ⟨t,.next bound ?_ (.halt tb ?_),rfl,?_,(Frame.refl s).pc 18⟩
   · simp [step,pc,choice_at,h.weight,h.three,lt,t,setPC]
   · simp [step,t,setPC,halt_at]
   · simp [t,setPC,h.value,effective,weight]

/-- Scan the actual original descriptor exactly once. Raw direction4131 is
retained; new4188 is the effective forward/inverse decision. -/
theorem execution (w U raw B n:ℕ)(v:Vec (Fin w))(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(width:s.natReg 4061=w)(source:s.natReg 4062=U)(flag:s.natReg 4131=raw)
 (rawSmall:raw<2)(src:Source U v s)(bound:WordBound B s)(code:19≤B)(extent:U+w≤B):∃t,
 BoundedExecution program n x B s (ticks v) t ∧ t.pc=18 ∧
 t.natReg 4188=effective raw (residue v w) ∧ Frame s t:=by
 have start:=block_runs boot program 0 n B x s boot_code pc bound (by change 7≤B;omega)
  (by simp [boot,readable,Op.readable,evalNat])
  (by simp [boot,peak,Op.peak,Op.apply,evalNat,writeNat,next,flag];omega)
 let u:=applyBlock boot s
 have up:u.pc=7:=by rw [block_pc,pc];rfl
 have h:Fields w U raw 0 v u:=by
  constructor <;>simp [u,boot,applyBlock,Op.apply,evalNat,writeNat,next,width,source,flag,residue_zero]
 have us:Source U v u:=src
 obtain ⟨ready,loop,rp,fields,lf⟩:=loop_execution w U raw 0 w B n v x u up h us (by omega) start.final_bound code extent
 obtain ⟨t,done,tp,value,ff⟩:=finish w U raw B n v x ready rp fields rawSmall loop.final_bound code
 refine ⟨t,?_,tp,value,(boot_frame s).trans (lf.trans ff)⟩
 convert start.executes (loop.executes done) using 1; simp [ticks,boot]; omega
end
end ExactFourierCircuits.UniformResidualOrientationMachine
