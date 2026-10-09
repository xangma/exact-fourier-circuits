import UniformFixedNetworkScheduleMachine
import UniformDirectToeplitz
import UniformPreparationRowTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafDescriptorMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformNewtonTableMachine (putWords putWords_append putWords_get putWords_before putWords_after)
open UniformFixedNetworkScheduleMachine (Printed)
open scoped BigOperators

/-- Addresses refer to the retained kernel prefix, independently of subtree offset. -/
def scaleWords (o K i:ℕ):List ℕ := [0,o+i,o+i,K]
lemma scaleWords_length (o K i:ℕ):(scaleWords o K i).length=4:=rfl
def shearWords (o K i j:ℕ):List ℕ := [1,o+i,o+j,K+(i-j)]
def shears (o K i j:ℕ):ℕ→List ℕ
 | 0=>[]
 | f+1=>shearWords o K i j++shears o K i (j+1) f
def rows (o K:ℕ):ℕ→List ℕ
 | 0=>[]
 | i+1=>scaleWords o K i++shears o K i 0 i++rows o K i
lemma shears_length (o K i j f:ℕ):(shears o K i j f).length=4*f:=by
 induction f generalizing j with
 | zero=>rfl
 | succ f ih=>simp [shears,shearWords,ih];omega
lemma rows_length (o K v:ℕ):(rows o K v).length=4*(v+∑j∈Finset.range v,j):=by
 induction v with
 | zero=>simp [rows]
 | succ v ih=>simp [rows,scaleWords,shears_length,ih,Finset.sum_range_succ];omega
lemma rows_length_closed (o K v:ℕ):(rows o K v).length=4*(v+v*(v-1)/2):=by
 rw [rows_length,Finset.sum_range_id]

/-- One fixed 34-instruction printer; no table, scalar, root or action is supplied. -/
def boot:List Op:=[.literal 5410 0,.literal 5411 1,.literal 5412 4,
 .add 5413 5400 5410,.add 5414 5403 5410,.literal 5415 0]
def beginRow:List Op:=[.sub 5413 5413 5411,.add 5416 5401 5413,.literal 5415 0,
 .putNat 5414 5410,.add 5414 5414 5411,.putNat 5414 5416,.add 5414 5414 5411,
 .putNat 5414 5416,.add 5414 5414 5411,.putNat 5414 5402,.add 5414 5414 5411]
def body:List Op:=[.add 5417 5401 5415,.sub 5418 5413 5415,.add 5418 5402 5418,
 .putNat 5414 5411,.add 5414 5414 5411,.putNat 5414 5416,.add 5414 5414 5411,
 .putNat 5414 5417,.add 5414 5414 5411,.putNat 5414 5418,.add 5414 5414 5411,
 .add 5415 5415 5411]
def program:Program:=boot.map Op.code++[.branchLT 5410 5413 7 33]++beginRow.map Op.code++
 [.branchLT 5415 5413 19 32]++body.map Op.code++[.jump 18,.jump 6,.halt]
lemma program_length:program.length=34:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<6 at hi;interval_cases i <;>rfl
lemma begin_code:BlockAt beginRow program 7:=by intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma body_code:BlockAt body program 19:=by intro i hi;change i<12 at hi;interval_cases i <;>rfl
lemma outer_at:program[6]?=some (.branchLT 5410 5413 7 33):=rfl
lemma inner_at:program[18]?=some (.branchLT 5415 5413 19 32):=rfl
lemma inner_jump:program[31]?=some (.jump 18):=rfl
lemma outer_jump:program[32]?=some (.jump 6):=rfl
lemma halt_at:program[33]?=some .halt:=rfl

noncomputable section
structure Header(v o K D:ℕ)(s:State):Prop where
 width:s.natReg 5400=v
 offset:s.natReg 5401=o
 kernel:s.natReg 5402=K
 base:s.natReg 5403=D
structure Constants(s:State):Prop where
 zero:s.natReg 5410=0
 one:s.natReg 5411=1
structure Cursor(v o K D i A:ℕ)(s:State):Prop where
 header:Header v o K D s
 constants:Constants s
 row:s.natReg 5413=i
 address:s.natReg 5414=A
structure Inner(v o K D i A j:ℕ)(s:State):Prop extends Cursor v o K D i A s where
 source:s.natReg 5415=j
 dest:s.natReg 5416=o+i
structure Frame(s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,r<5410∨5419≤r→u.natReg r=s.natReg r
lemma Frame.refl(s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans{s u v:State}(f:Frame s u)(g:Frame u v):Frame s v:=
 ⟨g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,
 g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma Frame.pc{s u:State}(f:Frame s u)(p:ℕ):Frame s (setPC u p):=
 ⟨f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Cursor.pc{v o K D i A:ℕ}{s:State}(h:Cursor v o K D i A s)(p:ℕ):Cursor v o K D i A (setPC s p):=
 ⟨⟨h.header.width,h.header.offset,h.header.kernel,h.header.base⟩,⟨h.constants.zero,h.constants.one⟩,h.row,h.address⟩
lemma Inner.pc{v o K D i A j:ℕ}{s:State}(h:Inner v o K D i A j s)(p:ℕ):Inner v o K D i A j (setPC s p):=
 ⟨h.toCursor.pc p,h.source,h.dest⟩

lemma boot_frame(s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma begin_frame(s:State):Frame s (applyBlock beginRow s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr;simp (disch:=omega) [beginRow,applyBlock,Op.apply,writeNat,next]
lemma body_frame(s:State):Frame s (applyBlock body s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr;simp (disch:=omega) [body,applyBlock,Op.apply,writeNat,next]
lemma initialized{v o K D:ℕ}(s:State)(h:Header v o K D s):Cursor v o K D v D (applyBlock boot s):=by
 refine ⟨?_,?_,?_,?_⟩
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,h.width,h.offset,h.kernel,h.base]
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.width]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.base]
lemma begun{v o K D i A:ℕ}(s:State)(h:Cursor v o K D (i+1) A s):
 Inner v o K D i (A+4) 0 (applyBlock beginRow s):=by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
 · constructor <;>simp [beginRow,applyBlock,Op.apply,writeNat,next,h.header.width,h.header.offset,h.header.kernel,h.header.base]
 · constructor <;>simp [beginRow,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one]
 · simp [beginRow,applyBlock,Op.apply,writeNat,next,h.row,h.constants.one]
 · simp [beginRow,applyBlock,Op.apply,writeNat,next,h.address,h.constants.one]
 · simp [beginRow,applyBlock,Op.apply,writeNat,next]
 · simp [beginRow,applyBlock,Op.apply,writeNat,next,h.row,h.constants.one,h.header.offset]
lemma advanced{v o K D i A j:ℕ}(s:State)(h:Inner v o K D i A j s):
 Inner v o K D i (A+4) (j+1) (applyBlock body s):=by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
 · constructor <;>simp [body,applyBlock,Op.apply,writeNat,next,h.header.width,h.header.offset,h.header.kernel,h.header.base]
 · constructor <;>simp [body,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one]
 · simpa [body,applyBlock,Op.apply,writeNat,next] using h.row
 · simp [body,applyBlock,Op.apply,writeNat,next,h.address,h.constants.one]
 · simp [body,applyBlock,Op.apply,writeNat,next,h.source,h.constants.one]
 · simpa [body,applyBlock,Op.apply,writeNat,next] using h.dest
lemma begin_heap{v o K D i A:ℕ}(s:State)(h:Cursor v o K D (i+1) A s):
 (applyBlock beginRow s).natHeap=putWords A (scaleWords o K i) s.natHeap:=by
 simp [beginRow,applyBlock,Op.apply,writeNat,next,h.row,h.address,h.header.offset,h.header.kernel,
 h.constants.zero,h.constants.one,scaleWords,putWords,Nat.add_assoc]
lemma body_heap{v o K D i A j:ℕ}(s:State)(h:Inner v o K D i A j s):
 (applyBlock body s).natHeap=putWords A (shearWords o K i j) s.natHeap:=by
 simp [body,applyBlock,Op.apply,writeNat,next,h.row,h.address,h.source,h.dest,h.header.offset,h.header.kernel,
 h.constants.one,shearWords,putWords,Nat.add_assoc]
lemma boot_safe{v o K D B:ℕ}(s:State)(h:Header v o K D s)(hs:WordBound B s)(code:34≤B):
 readable boot s∧peak boot s≤B:=by
 have vb:=hs.2.1 5400;rw [h.width] at vb
 have db:=hs.2.1 5403;rw [h.base] at db
 simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.width,h.base];omega
lemma begin_safe{v o K D i A B:ℕ}(s:State)(h:Cursor v o K D (i+1) A s)
 (iv:i < v)(_code:34≤B)(ob:o+v≤B)(kb:K+v≤B)(ab:A+4≤B):
 readable beginRow s∧peak beginRow s≤B:=by
 simp [beginRow,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.row,h.address,
 h.header.offset,h.header.kernel,h.constants.zero,h.constants.one];omega
lemma body_safe{v o K D i A j B:ℕ}(s:State)(h:Inner v o K D i A j s)
 (iv:i < v)(ji:j < i)(_code:34≤B)(ob:o+v≤B)(kb:K+v≤B)(ab:A+4≤B):
 readable body s∧peak body s≤B:=by
 simp [body,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.row,h.address,h.source,h.dest,
 h.header.offset,h.header.kernel,h.constants.one];omega

lemma inner_execution(n v o K D i A j f B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Inner v o K D i A j s)(pc:s.pc=18)(hs:WordBound B s)(eq:j+f=i)
 (iv:i < v)(code:34≤B)(ob:o+v≤B)(kb:K+v≤B)(ab:A+4*f≤B):
 ∃u,BoundedRuns program n x B s (14*f+1) u∧u.pc=32∧
 Inner v o K D i (A+4*f) i u∧u.natHeap=putWords A (shears o K i j f) s.natHeap∧Frame s u:=by
 induction f generalizing A j s with
 | zero=>
   have ji:j=i:=by omega
   have choose:step program n x s=.running (setPC s 32):=by
     simp [step,pc,inner_at,h.source,h.row,ji,setPC]
   have run:=UniformPreparationRowTableMachine.control_run program n B 32 x s hs (by omega) choose
   refine ⟨setPC s 32,by simpa only [setPC,Nat.mul_zero,Nat.zero_add] using run,rfl,?_,rfl,(Frame.refl s).pc 32⟩
   simpa [ji] using h.pc 32
 | succ f ih=>
   have ji:j < i:=by omega
   have choose:step program n x s=.running (setPC s 19):=by
     simp [step,pc,inner_at,h.source,h.row,ji,setPC]
   have branch:=UniformPreparationRowTableMachine.control_run program n B 19 x s hs (by omega) choose
   let a:=setPC s 19
   have ha:=h.pc 19
   have safe:=body_safe a ha iv ji code ob kb (by omega)
   have blocks:=block_runs body program 19 n B x a body_code rfl branch.final_bound (by change 31≤B;omega) safe.1 safe.2
   let z:=applyBlock body a
   have zp:z.pc=31:=by rw [applyBlock_pc];rfl
   have backStep:step program n x z=.running (setPC z 18):=by simp [step,zp,inner_jump,setPC]
   have back:=UniformPreparationRowTableMachine.control_run program n B 18 x z blocks.final_bound (by omega) backStep
   obtain ⟨u,tail,up,final,heap,frame⟩:=ih (A+4) (j+1) (setPC z 18)
     ((advanced a ha).pc 18) rfl back.final_bound (by omega) (by omega)
   refine ⟨u,?_,up,?_,?_,(((Frame.refl s).pc 19).trans ((body_frame a).pc 18)).trans frame⟩
   · convert branch.trans (blocks.trans (back.trans tail)) using 1;change 14*(f+1)+1=1+(12+(1+(14*f+1)));omega
   · simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
   · rw [heap]
     change putWords (A+4) (shears o K i (j+1) f) z.natHeap=putWords A (shears o K i j (f+1)) s.natHeap
     rw [show z.natHeap=putWords A (shearWords o K i j) s.natHeap from body_heap a ha]
     rw [shears,putWords_append];rfl

def printCost(v:ℕ):ℕ:=14*(v+∑j∈Finset.range v,j)
lemma printCost_succ(i:ℕ):printCost (i+1)=14*(i+1)+printCost i:=by
 simp only [printCost,Finset.sum_range_succ];omega

lemma rows_execution(n v o K D i A B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Cursor v o K D i A s)(pc:s.pc=6)(hs:WordBound B s)(iv:i≤v)
 (code:34≤B)(ob:o+v≤B)(kb:K+v≤B)(ab:A+(rows o K i).length≤B):
 ∃u,BoundedRuns program n x B s (printCost i) u∧u.pc=6∧
 Cursor v o K D 0 (A+(rows o K i).length) u∧u.natHeap=putWords A (rows o K i) s.natHeap∧Frame s u:=by
 induction i generalizing A s with
 | zero=>exact ⟨s,by simpa [printCost] using BoundedRuns.refl hs,pc,by simpa [rows] using h,rfl,Frame.refl s⟩
 | succ i ih=>
   have ib:i < v:=by omega
   have al:A+4+4*i+(rows o K i).length≤B:=by
     simpa only [rows,List.length_append,scaleWords_length,shears_length,Nat.add_assoc] using ab
   have choose:step program n x s=.running (setPC s 7):=by
     simp [step,pc,outer_at,h.constants.zero,h.row,setPC]
   have branch:=UniformPreparationRowTableMachine.control_run program n B 7 x s hs (by omega) choose
   let a:=setPC s 7
   have ha:=h.pc 7
   have safe:=begin_safe a ha ib code ob kb (by omega)
   have beginRun:=block_runs beginRow program 7 n B x a begin_code rfl branch.final_bound (by change 18≤B;omega) safe.1 safe.2
   let z:=applyBlock beginRow a
   have zp:z.pc=18:=by rw [applyBlock_pc];rfl
   obtain ⟨w,inner,wp,wh,wheap,wframe⟩:=inner_execution n v o K D i (A+4) 0 i B x z
     (begun a ha) zp beginRun.final_bound (by omega) ib code ob kb (by omega)
   have backStep:step program n x w=.running (setPC w 6):=by simp [step,wp,outer_jump,setPC]
   have back:=UniformPreparationRowTableMachine.control_run program n B 6 x w inner.final_bound (by omega) backStep
   obtain ⟨u,tail,up,final,heap,frame⟩:=ih (A+4+4*i) (setPC w 6)
     (wh.toCursor.pc 6) rfl back.final_bound (by omega) (by omega)
   refine ⟨u,?_,up,?_,?_,(((Frame.refl s).pc 7).trans ((begin_frame a).trans (wframe.pc 6))).trans frame⟩
   · convert branch.trans (beginRun.trans (inner.trans (back.trans tail))) using 1
     change printCost (i+1)=1+(11+((14*i+1)+(1+printCost i)))
     rw [printCost_succ];omega
   · simpa only [rows,List.length_append,scaleWords_length,shears_length,Nat.add_assoc] using final
   · rw [heap]
     change putWords (A+4+4*i) (rows o K i) w.natHeap=putWords A (rows o K (i+1)) s.natHeap
     rw [wheap,show z.natHeap=putWords A (scaleWords o K i) s.natHeap from begin_heap a ha]
     rw [rows,putWords_append,putWords_append]
     simp only [List.length_append,scaleWords,List.length_cons,List.length_nil,shears_length]
     simp only [Nat.reduceAdd,Nat.add_assoc]

/-- Charged reverse-row printer from ordinary headers. The complete destination
heap is derived; coefficients remain references to the genuine prepared bank. -/
theorem execution(n v o K D B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Header v o K D s)(pc:s.pc=0)(hs:WordBound B s)(code:34≤B)
 (ob:o+v≤B)(kb:K+v≤B)(db:D+(rows o K v).length≤B):
 ∃u,BoundedExecution program n x B s (printCost v+8) u∧u.pc=33∧
 Printed D (rows o K v) u∧u.natReg 5414=D+(rows o K v).length∧
 (∀z,z<D∨D+(rows o K v).length≤z→u.natHeap z=s.natHeap z)∧Frame s u:=by
 have safe:=boot_safe s h hs code
 have init:=block_runs boot program 0 n B x s boot_code pc hs (by change 6≤B;omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=6:=by rw [applyBlock_pc,pc];rfl
 obtain ⟨w,run,wp,final,heap,frame⟩:=rows_execution n v o K D v D B x a
   (initialized s h) ap init.final_bound (by omega) code ob kb db
 have choose:step program n x w=.running (setPC w 33):=by
   simp [step,wp,outer_at,final.constants.zero,final.row,setPC]
 have stop:=UniformPreparationRowTableMachine.control_run program n B 33 x w run.final_bound (by omega) choose
 have halt:BoundedExecution program n x B (setPC w 33) 1 (setPC w 33):=
   .halt stop.final_bound (by simp [step,setPC,halt_at])
 refine ⟨setPC w 33,?_,rfl,?_,final.address,?_,((boot_frame s).trans frame).pc 33⟩
 · convert init.executes (run.executes (stop.executes halt)) using 1
   change printCost v+8=6+(printCost v+(1+1));omega
 · intro j hj
   change w.natHeap (D+j)=some ((rows o K v)[j]'hj)
   rw [heap,putWords_get D (rows o K v) a.natHeap j hj,List.getElem?_eq_getElem hj]
 · intro z hz
   change w.natHeap z=s.natHeap z
   rw [heap]
   rcases hz with before|after
   · rw [putWords_before D (rows o K v) a.natHeap z before];rfl
   · rw [putWords_after D (rows o K v) a.natHeap z after];rfl

/-- The physical records preserve the exact topology, including zero shears. -/
def operationWords{v:ℕ}(o K:ℕ):UniformDirectToeplitz.Operation v→List ℕ
 | .scale i=>scaleWords o K i.val
 | .shear i j=>shearWords o K i.val j.val
lemma shears_ofFn(o K i:ℕ):(List.ofFn (fun j:Fin i=>shearWords o K i j.val)).flatten=shears o K i 0 i:=by
 have aux:∀f j,(List.ofFn (fun a:Fin f=>shearWords o K i (j+a.val))).flatten=shears o K i j f:=by
  intro f;induction f with
  | zero=>intro j;rfl
  | succ f ih=>
    intro j
    rw [List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    rw [show (fun a:Fin f=>shearWords o K i (j+(a.val+1)))=(fun a:Fin f=>shearWords o K i ((j+1)+a.val)) from by funext a;congr 1;omega,ih]
    rfl
 simpa using aux i 0
lemma rows_topology{v:ℕ}(o K i:ℕ)(iv:i≤v):
 ((UniformDirectToeplitz.partialTopology i iv).map (operationWords o K)).flatten=rows o K i:=by
 induction i with
 | zero=>rfl
 | succ i ih=>
   simp only [UniformDirectToeplitz.partialTopology,List.map_append,List.flatten_append,
     UniformDirectToeplitz.rowTopology,List.map_cons,List.flatten_cons,operationWords]
   rw [List.map_ofFn]
   simp only [Function.comp_def,operationWords]
   rw [shears_ofFn,ih (by omega)];rfl
lemma topology_words(o K v:ℕ):
 ((UniformDirectToeplitz.topology v).map (operationWords o K)).flatten=rows o K v:=rows_topology o K v (le_refl v)
lemma printCost_closed(v:ℕ):printCost v=14*(v+v*(v-1)/2):=by rw [printCost,Finset.sum_range_id]
end
end ExactFourierCircuits.UniformDirectLeafDescriptorMachine
