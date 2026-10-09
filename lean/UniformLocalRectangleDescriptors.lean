import UniformWorkspaceSearchMachine
import UniformBalancedToeplitz
import UniformLocalPreparationDAG
import UniformBoundedAssembly
import UniformTensorMonomialMachine
import UniformNewtonTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleDescriptors
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformWorkspacePlanner

/-- Integer kernel parameters and physical subtree translation stay distinct. -/
structure Row where
 width : ℕ
 offset : ℕ
 a : ℕ
 e : ℕ
 split : ℕ
 i0 : ℕ
 j0 : ℕ
 deriving DecidableEq, Repr

def Row.words (q : Row) : List ℕ := [q.width,q.offset,q.a,q.e,q.split,q.i0,q.j0]
def row (v o b i j : ℕ) : Row :=
 ⟨v,o,min b (v-v/2-i*b),min b (v/2-j*b),v/2,v/2+i*b,j*b⟩
def rows (v o b : ℕ) : List Row :=
 (List.range (chunkCount (v-v/2) b)).flatMap fun i=>
 (List.range (chunkCount (v/2) b)).map fun j=> row v o b i j
lemma rows_length (v o b:ℕ) : (rows v o b).length=
 chunkCount (v-v/2) b*chunkCount (v/2) b:=by
 simp [rows,List.length_flatMap,Nat.mul_comm]
lemma row_exact {v:ℕ} (o:ℕ) (_hv:0< selected v)
 (q:Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v))):
 row v o (selected v) q.1.val q.2.val=
 ⟨v,o,UniformBalancedToeplitz.size (v-v/2) (selected v) q.1,
 UniformBalancedToeplitz.size (v/2) (selected v) q.2,v/2,
 v/2+q.1.val*selected v,q.2.val*selected v⟩:=rfl
lemma rows_pairs (v o:ℕ):rows v o (selected v)=
 (UniformBalancedToeplitz.pairs v).map (fun q=> row v o (selected v) q.1.val q.2.val):=by
 have hr (n:ℕ):(List.finRange n).map Fin.val=List.range n:=by
  apply List.ext_getElem
  · simp
  · intro i h1 h2;simp
 unfold rows UniformBalancedToeplitz.pairs
 rw [←hr,←hr]
 simp only [List.flatMap_map,List.map_map,List.map_flatMap,Function.comp_def]

/-- Header4240 width,4241 subtree offset,4242 fresh tape; Search58 is physical. -/
def boot:List Op:=[.literal 4260 0,.literal 4261 1,.literal 4262 2,.literal 4263 7,
 .add 290 4240 4260]
def splitSetup:List Op:=[.add 4250 291 4260]
def halves:List Op:=[.sub 4252 4240 4251,.literal 4256 0,.literal 4257 0]
def targetSetup:List Op:=[.sub 4253 4252 4256,.sub 4253 4250 4253,.sub 4253 4250 4253,
 .add 4255 4251 4256,.literal 4258 0]
def sourceSetup:List Op:=[.sub 4254 4251 4258,.sub 4254 4250 4254,.sub 4254 4250 4254]
def emit:List Op:=[.mul 4259 4257 4263,.add 4259 4242 4259,
 .putNat 4259 4240,.add 4259 4259 4261,.putNat 4259 4241,
 .add 4259 4259 4261,.putNat 4259 4253,.add 4259 4259 4261,.putNat 4259 4254,
 .add 4259 4259 4261,.putNat 4259 4251,.add 4259 4259 4261,.putNat 4259 4255,
 .add 4259 4259 4261,.putNat 4259 4258,.add 4257 4257 4261,.add 4258 4258 4250]
-- boot0..4,search5..62,setup63,division64,halves65..67;
-- width branch68,positive branch69,outer70,setup71..75,inner76;
-- source77..79,emit80..96,jump97,target advance98,jump99,halt100.
def head:Program:=boot.map Op.code++UniformWorkspaceSearchMachine.program.map (relocate 5 63)++
 splitSetup.map Op.code++[.natBinary .div 4251 4240 4262]++halves.map Op.code

def program:Program:=head++[.branchLT 4240 4262 100 69,.branchLT 4260 4250 70 100,
 .branchLT 4256 4252 71 100]++targetSetup.map Op.code++[.branchLT 4258 4251 77 98]++
 sourceSetup.map Op.code++emit.map Op.code++[.jump 76,.natBinary .add 4256 4256 4250,.jump 70,.halt]
lemma head_length:head.length=68:=by
 simp only [head,List.length_append,List.length_map,UniformWorkspaceSearchMachine.program_length];rfl
lemma program_length:program.length=101:=by
 simp only [program,List.length_append,List.length_map,head_length];rfl
lemma search_code:CodeAt UniformWorkspaceSearchMachine.program program 5 63:=by
 let tail:=splitSetup.map Op.code++[.natBinary .div 4251 4240 4262]++halves.map Op.code++
 [.branchLT 4240 4262 100 69,.branchLT 4260 4250 70 100,.branchLT 4256 4252 71 100]++
 targetSetup.map Op.code++[.branchLT 4258 4251 77 98]++sourceSetup.map Op.code++emit.map Op.code++
 [.jump 76,.natBinary .add 4256 4256 4250,.jump 70,.halt]
 have he:program=boot.map Op.code++UniformWorkspaceSearchMachine.program.map (relocate 5 63)++tail:=by
  simp only [program,head,tail,List.append_assoc]
 rw [he]
 intro i hi
 have hil:=hi
 rw [UniformWorkspaceSearchMachine.program_length] at hil
 rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];change 5+i<5+58;omega)]
 rw [List.getElem?_append_right (by change 5≤5+i;omega)]
 simp only [show (boot.map Op.code).length=5 from rfl,show 5+i-5=i by omega,List.getElem?_map]

noncomputable section
structure Header (v o d:ℕ) (s:State):Prop where
 width:s.natReg 4240=v
 offset:s.natReg 4241=o
 destination:s.natReg 4242=d
structure Base (v o d b:ℕ) (s:State):Prop extends Header v o d s where
 selected:s.natReg 4250=b
 half:s.natReg 4251=v/2
 target:s.natReg 4252=v-v/2
 zero:s.natReg 4260=0
 one:s.natReg 4261=1
 two:s.natReg 4262=2
 seven:s.natReg 4263=7
structure Cursor (v o d b i j c:ℕ) (s:State):Prop extends Base v o d b s where
 targetOffset:s.natReg 4256=i*b
 sourceOffset:s.natReg 4258=j*b
 count:s.natReg 4257=c
 a:s.natReg 4253=min b (v-v/2-i*b)
 i0:s.natReg 4255=v/2+i*b
lemma min_sub (a b:ℕ):a-(a-b)=min a b:=by omega
lemma target_result {v o d b i c:ℕ} (s:State) (h:Base v o d b s)
 (hi:s.natReg 4256=i*b) (hc:s.natReg 4257=c):
 Cursor v o d b i 0 c (applyBlock targetSetup s):=by
 constructor
 · constructor
   · constructor <;> simp [targetSetup,applyBlock,Op.apply,writeNat,next,h.width,h.offset,h.destination]
   all_goals simp [targetSetup,applyBlock,Op.apply,writeNat,next,h.selected,h.half,h.target,h.zero,h.one,h.two,h.seven]
 all_goals simp [targetSetup,applyBlock,Op.apply,writeNat,next,hi,hc,h.half,h.target,h.selected,min_sub]
lemma emit_result {v o d b i j c:ℕ} (s:State) (h:Cursor v o d b i j c s):
 (applyBlock (sourceSetup++emit) s).natReg 4257=c+1 ∧
 (applyBlock (sourceSetup++emit) s).natReg 4258=(j+1)*b:=by
 simp [sourceSetup,emit,applyBlock,Op.apply,writeNat,next,h.count,h.sourceOffset,h.selected,
 h.one,h.seven,Nat.add_mul]
lemma emit_words {v o d b i j c:ℕ} (s:State) (h:Cursor v o d b i j c s) (t:Fin 7):
 (applyBlock (sourceSetup++emit) s).natHeap (d+7*c+t.val)=some ((row v o b i j).words[t.val]'(by exact t.isLt)):=by
 fin_cases t <;>
 simp (disch:=omega) [sourceSetup,emit,applyBlock,Op.apply,writeNat,next,h.width,h.offset,h.destination,
 h.selected,h.half,h.sourceOffset,h.count,h.a,h.i0,h.one,h.seven,row,Row.words,min_sub,Nat.mul_comm]
lemma emit_outside {v o d b i j c:ℕ} (s:State) (h:Cursor v o d b i j c s) (q:ℕ)
 (outside:q< d+7*c ∨ d+7*c+7≤ q):
 (applyBlock (sourceSetup++emit) s).natHeap q=s.natHeap q:=by
 simp (disch:=omega) [sourceSetup,emit,applyBlock,Op.apply,writeNat,next,h.destination,
 h.count,h.one,h.seven]
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma split_code:BlockAt splitSetup program 63:=by
 intro i hi
 change i<1 at hi
 have hi0:i=0:=by omega
 subst i;rfl
lemma halves_code:BlockAt halves program 65:=by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma target_code:BlockAt targetSetup program 71:=by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma source_emit_code:BlockAt (sourceSetup++emit) program 77:=by
 intro i hi;change i<20 at hi;interval_cases i <;> rfl

lemma startup (n v o d B:ℕ) (x:Fin n→ℂ) (s:State) (hh:Header v o d s)
 (hp:s.pc=0) (hs:WordBound B s) (hb:UniformWorkspaceSearchMachine.budget v≤ B):
 ∃u t,BoundedRuns program n x B s t u ∧t≤256*(v+1)^4+10∧u.pc=68∧
 Base v o d (selected v) u ∧u.natReg 4256=0∧u.natReg 4257=0∧u.natHeap=s.natHeap:=by
 have code:101≤ B:=by unfold UniformWorkspaceSearchMachine.budget at hb;omega
 have first:=block_runs boot program 0 n B x s boot_code hp hs (by change 5≤ B;omega)
  (by simp [boot,readable,Op.readable]) (by
   have vb:=hs.2.1 4240
   simp [boot,peak,Op.peak,Op.apply,writeNat,next,hh.width] at vb ⊢
   unfold UniformWorkspaceSearchMachine.budget at hb;omega)
 let a:=applyBlock boot s
 have ap:a.pc=5:=by rw [applyBlock_pc,hp];rfl
 let e:=setPC a 0
 have ep:e.pc=0:=rfl
 have er:e.natReg 290=v:=by simp [e,a,setPC,applyBlock,boot,Op.apply,writeNat,next,hh.width]
 have eb:WordBound B e:=changePC_bound B a 0 first.final_bound (by omega)
 obtain ⟨u,t,run,cost,up,sel,frame⟩:=UniformWorkspaceSearchMachine.execution_polynomial n v B x e ep er eb hb
 have placed:=UniformBoundedAssembly.boundedExecution_placed search_code (by rw [UniformWorkspaceSearchMachine.program_length];omega) (by omega) run
 have same:UniformAssembly.placed 5 e=a:=by
  change {a with pc:=5+0}=a
  rw [←ap];cases a;rfl
 -- The input to the placed helper is exactly the actual preceding state.
 have placed':BoundedRuns program n x B a t (setPC u 63):=by
  simpa only [setPC,show UniformAssembly.placed 5 e=a from same] using placed
 let b:=setPC u 63
 have retained(q:ℕ)(hq:313≤ q):b.natReg q=a.natReg q:=frame.2.2.2.2.2 q (Or.inr (by omega))
 have bc:b.natReg 4260=0∧b.natReg 4261=1∧b.natReg 4262=2∧b.natReg 4263=7:=by
  constructor
  · rw [retained 4260 (by omega)];simp [a,boot,applyBlock,Op.apply,writeNat,next]
  constructor
  · rw [retained 4261 (by omega)];simp [a,boot,applyBlock,Op.apply,writeNat,next]
  constructor
  · rw [retained 4262 (by omega)];simp [a,boot,applyBlock,Op.apply,writeNat,next]
  · rw [retained 4263 (by omega)];simp [a,boot,applyBlock,Op.apply,writeNat,next]
 have bh:Header v o d b:=by
  constructor
  · rw [retained 4240 (by omega)];simpa [a,boot,applyBlock,Op.apply,writeNat,next] using hh.width
  · rw [retained 4241 (by omega)];simpa [a,boot,applyBlock,Op.apply,writeNat,next] using hh.offset
  · rw [retained 4242 (by omega)];simpa [a,boot,applyBlock,Op.apply,writeNat,next] using hh.destination
 have copy:=block_runs splitSetup program 63 n B x b split_code rfl placed'.final_bound (by change 63+1≤ B;omega)
  (by simp [splitSetup,readable,Op.readable]) (by
   have sb:=placed'.final_bound.2.1 291
   simp [splitSetup,peak,Op.peak,bc.1] at sb ⊢;omega)
 let c:=applyBlock splitSetup b
 have cp:c.pc=64:=by rw [applyBlock_pc];rfl
 have cv:c.natReg 4240=v:=by simpa [c,splitSetup,applyBlock,Op.apply,writeNat,next] using bh.width
 have ct:c.natReg 4262=2:=by simpa [c,splitSetup,applyBlock,Op.apply,writeNat,next] using bc.2.2.1
 have division:=UniformWorkspaceSearchMachine.division_run program n B 4251 4240 4262 x c
  (by rw [cp];rfl) (by rw [ct];omega) copy.final_bound (by rw [cp];omega)
 let f:=writeNat c 4251 (c.natReg 4240/c.natReg 4262)
 have fp:f.pc=65:=by simp [f,writeNat,next,cp]
 have half:f.natReg 4251=v/2:=by simp [f,writeNat,next,cv,ct]
 have fw:f.natReg 4240=v:=by simpa [f,writeNat,next] using cv
 have finish:=block_runs halves program 65 n B x f halves_code fp division.final_bound (by change 65+3≤ B;omega)
  (by simp [halves,readable,Op.readable]) (by
   have vb:=division.final_bound.2.1 4240
   simp [halves,peak,Op.peak,writeNat,next,fw] at vb ⊢;omega)
 let z:=applyBlock halves f
 refine ⟨z,5+t+1+1+3,(((first.trans placed').trans copy).trans division).trans finish,by omega,?_,?_,?_,?_,?_⟩
 · rw [applyBlock_pc,fp];rfl
 · constructor
   · constructor
     · simp [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next,bh.width]
     · simp [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next,bh.offset]
     · simp [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next,bh.destination]
   · have cs:c.natReg 4250=selected v:=by
      change b.natReg 291+b.natReg 4260=selected v
      rw [show b.natReg 291=selected v from sel,bc.1];simp
     simpa [z,f,halves,applyBlock,Op.apply,writeNat,next] using cs
   · simpa [z,halves,applyBlock,Op.apply,writeNat,next] using half
   · simp [z,halves,applyBlock,Op.apply,writeNat,next,half,fw]
   · simpa [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next] using bc.1
   · simpa [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next] using bc.2.1
   · simpa [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next] using bc.2.2.1
   · simpa [z,f,c,halves,splitSetup,applyBlock,Op.apply,writeNat,next] using bc.2.2.2
 · simp [z,halves,applyBlock,Op.apply,writeNat,next]
 · simp [z,halves,applyBlock,Op.apply,writeNat,next]
 · change u.natHeap=s.natHeap
   rw [frame.2.2.1];rfl

lemma chunk_offset (s b j:ℕ) (hb:0< b):j< chunkCount s b↔j*b< s:=by
 constructor
 · intro hj;exact UniformBalancedToeplitz.offset_lt s b hb ⟨j,hj⟩
 · intro hj
   by_contra hn
   have hc:=UniformBalancedToeplitz.ceiling_cover s b hb
   have hm:=Nat.mul_le_mul_right b (show chunkCount s b≤ j by omega)
   omega

lemma div_index (i j m:ℕ) (hm:0 < m) (hj:j < m):(i*m+j)/m=i:=by
 rw [Nat.mul_comm i m,Nat.mul_add_div hm,Nat.div_eq_of_lt hj,Nat.add_zero]
lemma mod_index (i j m:ℕ) (hj:j < m):(i*m+j)%m=j:=by
 rw [Nat.mul_comm i m,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
lemma pair_index_injective (i j a q m:ℕ) (hm:0 < m) (hj:j < m) (hq:q < m)
 (eq:i*m+j=a*m+q):i=a∧j=q:=by
 constructor
 · have h:=congrArg (fun x=> x/m) eq
   simpa only [div_index _ _ _ hm hj,div_index _ _ _ hm hq] using h
 · have h:=congrArg (fun x=> x%m) eq
   simpa only [mod_index _ _ _ hj,mod_index _ _ _ hq] using h

def Done (v o d b c:ℕ) (s:State):Prop:=
 ∀(i:Fin (chunkCount (v-v/2) b))(j:Fin (chunkCount (v/2) b)),
 i.val*chunkCount (v/2) b+j.val< c→∀t:Fin 7,
 s.natHeap (d+7*(i.val*chunkCount (v/2) b+j.val)+t.val)=
 some ((row v o b i.val j.val).words[t.val]'t.isLt)

def Outside (d length:ℕ) (s u:State):Prop:=
 ∀q,(q<d ∨d+7*length≤q)→u.natHeap q=s.natHeap q
lemma Outside.trans {d length:ℕ} {s u v:State} (h:Outside d length s u) (g:Outside d length u v):
 Outside d length s v:=fun q hq=>(g q hq).trans (h q hq)

def Table (v o d b:ℕ) (s:State):Prop:=Done v o d b
 (chunkCount (v-v/2) b*chunkCount (v/2) b) s

lemma table_row (v o d b:ℕ) (s:State) (h:Table v o d b s)
 (i:Fin (chunkCount (v-v/2) b))(j:Fin (chunkCount (v/2) b))(t:Fin 7):
 s.natHeap (d+7*(i.val*chunkCount (v/2) b+j.val)+t.val)=
 some ((row v o b i.val j.val).words[t.val]'t.isLt):=by
 apply h i j
 have hi:=i.isLt;have hj:=j.isLt
 have mul:=Nat.mul_le_mul_right (chunkCount (v/2) b) (show i.val+1≤ chunkCount (v-v/2) b by omega)
 rw [Nat.add_mul,Nat.one_mul] at mul;omega

lemma done_zero (v o d b:ℕ) (s:State):Done v o d b 0 s:=by intro i j hi;omega
lemma emit_done {v o d b i j:ℕ} (s:State) (h:Cursor v o d b i j (i*chunkCount (v/2) b+j) s)
 (_hb:0< b) (hj:j< chunkCount (v/2) b)
 (prior:Done v o d b (i*chunkCount (v/2) b+j) s):
 Done v o d b (i*chunkCount (v/2) b+j+1) (applyBlock (sourceSetup++emit) s):=by
 intro u w bound t
 by_cases he:u.val*chunkCount (v/2) b+w.val=i*chunkCount (v/2) b+j
 · have hm:0< chunkCount (v/2) b:=by omega
   obtain ⟨hu,hw⟩:=pair_index_injective u.val w.val i j _ hm w.isLt hj he
   simp only [hu,hw];exact emit_words s h t
 · have hold :u.val*chunkCount (v/2) b+w.val< i*chunkCount (v/2) b+j:=by omega
   rw [emit_outside s h _ (Or.inl (by have ht:=t.isLt;omega))]
   exact prior u w hold t

lemma emit_cursor {v o d b i j c:ℕ} (s:State) (h:Cursor v o d b i j c s):
 Cursor v o d b i (j+1) (c+1) (applyBlock (sourceSetup++emit) s):=by
 constructor
 · constructor
   · constructor <;> simp [sourceSetup,emit,applyBlock,Op.apply,writeNat,next,h.width,h.offset,h.destination]
   all_goals simp [sourceSetup,emit,applyBlock,Op.apply,writeNat,next,h.selected,h.half,h.target,
     h.zero,h.one,h.two,h.seven]
 · simpa [sourceSetup,emit,applyBlock,Op.apply,writeNat,next] using h.targetOffset
 · exact (emit_result s h).2
 · exact (emit_result s h).1
 · simpa [sourceSetup,emit,applyBlock,Op.apply,writeNat,next] using h.a
 · simpa [sourceSetup,emit,applyBlock,Op.apply,writeNat,next] using h.i0

lemma emit_safe {v o d b i j c B:ℕ} (s:State) (h:Cursor v o d b i j c s)
 (hb:b≤ v) (hi:i*b< v-v/2) (hj:j*b< v/2)
 (hd:d+7*(c+1)≤ B) (ho:o≤ B) (hv:2*v+7≤ B):
 readable (sourceSetup++emit) s∧peak (sourceSetup++emit) s≤ B:=by
 have ha:min b (v-v/2-i*b)≤ b:=min_le_left _ _
 have he:min b (v/2-j*b)≤ b:=min_le_left _ _
 simp [readable,sourceSetup,emit,Op.readable]
 simp [peak,Op.peak,Op.apply,writeNat,next,h.width,h.offset,
 h.destination,h.selected,h.half,h.sourceOffset,h.count,h.a,h.i0,h.one,h.seven,min_sub]
 omega


lemma inner_branch:program[76]?=some (.branchLT 4258 4251 77 98):=rfl
lemma inner_jump:program[97]?=some (.jump 76):=rfl
lemma Cursor.withPC {v o d b i j c:ℕ} {s:State} (h:Cursor v o d b i j c s) (pc:ℕ):
 Cursor v o d b i j c (setPC s pc):=by
 rcases h with ⟨base,ti,sj,count,a,i0⟩
 rcases base with ⟨header,sel,half,target,zero,one,two,seven⟩
 rcases header with ⟨width,offset,destination⟩
 exact ⟨⟨⟨width,offset,destination⟩,sel,half,target,zero,one,two,seven⟩,ti,sj,count,a,i0⟩

lemma source_loop (n v o d b i j fuel B:ℕ) (x:Fin n→ℂ) (s:State)
 (hb:0< b) (hbv:b≤ v) (hi:i< chunkCount (v-v/2) b)
 (endj:j+fuel=chunkCount (v/2) b)
 (h:Cursor v o d b i j (i*chunkCount (v/2) b+j) s)
 (prior:Done v o d b (i*chunkCount (v/2) b+j) s) (hp:s.pc=76)
 (hs:WordBound B s) (hd:d+7*(chunkCount (v-v/2) b*chunkCount (v/2) b)≤ B)
 (ho:o≤ B) (hv:2*v+101≤ B):
 ∃u,BoundedRuns program n x B s (22*fuel+1) u∧u.pc=98∧
 Cursor v o d b i (chunkCount (v/2) b) ((i+1)*chunkCount (v/2) b) u∧
 Done v o d b ((i+1)*chunkCount (v/2) b) u∧
 Outside d (chunkCount (v-v/2) b*chunkCount (v/2) b) s u:=by
 induction fuel generalizing j s with
 | zero=>
   have je:j=chunkCount (v/2) b:=by omega
   have no:v/2≤ j*b:=by
    rw [je];exact UniformBalancedToeplitz.ceiling_cover _ _ hb
   have step:UniformMachine.step program n x s=.running (setPC s 98):=by
    simp [UniformMachine.step,hp,inner_branch,h.sourceOffset,h.half,setPC,show ¬j*b< v/2 by omega]
   have run:=UniformPreparationRowTableMachine.control_run program n B 98 x s hs (by omega) step
   refine ⟨setPC s 98,?_,rfl,?_,?_,fun q hq=>rfl⟩
   · simpa [setPC] using run
   · simpa only [je,show i*chunkCount (v/2) b+chunkCount (v/2) b=(i+1)*chunkCount (v/2) b by ring] using h.withPC 98
   · simpa only [je,show i*chunkCount (v/2) b+chunkCount (v/2) b=(i+1)*chunkCount (v/2) b by ring,Done,setPC] using prior
 | succ fuel ih=>
   have jl:j< chunkCount (v/2) b:=by omega
   have jo:= (chunk_offset (v/2) b j hb).mp jl
   have io:= (chunk_offset (v-v/2) b i hb).mp hi
   have step:UniformMachine.step program n x s=.running (setPC s 77):=by
    simp [UniformMachine.step,hp,inner_branch,h.sourceOffset,h.half,setPC,jo]
   have branch:=UniformPreparationRowTableMachine.control_run program n B 77 x s hs (by omega) step
   let a:=setPC s 77
   have ac:Cursor v o d b i j (i*chunkCount (v/2) b+j) a:=h.withPC 77
   have less:i*chunkCount (v/2) b+j+1≤ chunkCount (v-v/2) b*chunkCount (v/2) b:=by
    have mul:=Nat.mul_le_mul_right (chunkCount (v/2) b) (show i+1≤ chunkCount (v-v/2) b by omega)
    rw [Nat.add_mul,Nat.one_mul] at mul;omega
   have safe:=emit_safe a ac hbv io jo (by nlinarith) ho (by omega)
   have emitRun:=block_runs (sourceSetup++emit) program 77 n B x a source_emit_code rfl branch.final_bound
    (by change 77+20≤ B;omega) safe.1 safe.2
   let e:=applyBlock (sourceSetup++emit) a
   have ep:e.pc=97:=by rw [applyBlock_pc];rfl
   have ec:=emit_cursor a ac
   have done:=emit_done a ac hb jl prior
   have jump:UniformMachine.step program n x e=.running (setPC e 76):=by
    simp [UniformMachine.step,ep,inner_jump,setPC]
   have back:=UniformPreparationRowTableMachine.control_run program n B 76 x e emitRun.final_bound (by omega) jump
   obtain ⟨u,tail,up,uc,ud,outside⟩:=ih (j+1) (setPC e 76) (by omega)
    (by simpa only [Nat.add_assoc] using ec.withPC 76) done rfl back.final_bound
   refine ⟨u,?_,up,uc,ud,?_⟩
   · simpa only [show (sourceSetup++emit).length=20 from rfl,
      show 1+20+1+(22*fuel+1)=22*(fuel+1)+1 by omega] using ((branch.trans emitRun).trans back).trans tail
   · intro q hq
     rw [outside q hq]
     exact emit_outside a ac q (by
      rcases hq with hq|hq
      · left;omega
      · right;have hm:=Nat.mul_le_mul_left 7 less;omega)

structure Outer (v o d b i:ℕ) (s:State):Prop extends Base v o d b s where
 targetOffset:s.natReg 4256=i*b
 count:s.natReg 4257=i*chunkCount (v/2) b
lemma Outer.withPC {v o d b i:ℕ} {s:State} (h:Outer v o d b i s) (pc:ℕ):
 Outer v o d b i (setPC s pc):=by
 rcases h with ⟨base,ti,count⟩
 rcases base with ⟨header,sel,half,target,zero,one,two,seven⟩
 rcases header with ⟨width,offset,destination⟩
 exact ⟨⟨⟨width,offset,destination⟩,sel,half,target,zero,one,two,seven⟩,ti,count⟩
lemma outer_branch:program[70]?=some (.branchLT 4256 4252 71 100):=rfl
lemma advance_at:program[98]?=some (.natBinary .add 4256 4256 4250):=rfl
lemma outer_jump:program[99]?=some (.jump 70):=rfl
lemma outer_halt:program[100]?=some .halt:=rfl
lemma advance_result {v o d b i:ℕ} {s:State}
 (h:Cursor v o d b i (chunkCount (v/2) b) ((i+1)*chunkCount (v/2) b) s):
 Outer v o d b (i+1) (writeNat s 4256 (s.natReg 4256+s.natReg 4250)):=by
 constructor
 · constructor
   · exact ⟨by simpa [writeNat,next] using h.width,
      by simpa [writeNat,next] using h.offset,by simpa [writeNat,next] using h.destination⟩
   · simpa [writeNat,next] using h.selected
   · simpa [writeNat,next] using h.half
   · simpa [writeNat,next] using h.target
   · simpa [writeNat,next] using h.zero
   · simpa [writeNat,next] using h.one
   · simpa [writeNat,next] using h.two
   · simpa [writeNat,next] using h.seven
 · simp [writeNat,next,h.targetOffset,h.selected,Nat.add_mul]
 · simpa [writeNat,next] using h.count

lemma target_safe {v o d b i B:ℕ} (s:State) (h:Outer v o d b i s)
 (hb:b≤ v) (hi:i*b< v-v/2) (hv:2*v+101≤ B):
 readable targetSetup s∧peak targetSetup s≤ B:=by
 have ha:min b (v-v/2-i*b)≤ b:=min_le_left _ _
 simp [targetSetup,readable,Op.readable]
 simp [peak,Op.peak,Op.apply,writeNat,next,h.target,h.targetOffset,h.selected,h.half,min_sub]
 omega

lemma target_loop (n v o d b i fuel B:ℕ) (x:Fin n→ℂ) (s:State)
 (hb:0< b) (hbv:b≤ v) (endi:i+fuel=chunkCount (v-v/2) b)
 (h:Outer v o d b i s) (prior:Done v o d b (i*chunkCount (v/2) b) s)
 (hp:s.pc=70) (hs:WordBound B s)
 (hd:d+7*(chunkCount (v-v/2) b*chunkCount (v/2) b)≤ B)
 (ho:o≤ B) (hv:2*v+101≤ B):
 ∃u,BoundedRuns program n x B s ((22*chunkCount (v/2) b+9)*fuel+1) u∧u.pc=100∧
 Outer v o d b (chunkCount (v-v/2) b) u∧Table v o d b u∧
 Outside d (chunkCount (v-v/2) b*chunkCount (v/2) b) s u:=by
 induction fuel generalizing i s with
 | zero=>
   have ie:i=chunkCount (v-v/2) b:=by omega
   have no:v-v/2≤ i*b:=by rw [ie];exact UniformBalancedToeplitz.ceiling_cover _ _ hb
   have step:UniformMachine.step program n x s=.running (setPC s 100):=by
    simp [UniformMachine.step,hp,outer_branch,h.targetOffset,h.target,setPC,show ¬i*b< v-v/2 by omega]
   have run:=UniformPreparationRowTableMachine.control_run program n B 100 x s hs (by omega) step
   refine ⟨setPC s 100,?_,rfl,?_,?_,fun q hq=>rfl⟩
   · simpa [setPC] using run
   · simpa only [ie] using h.withPC 100
   · simpa only [Table,Done,setPC,ie] using prior
 | succ fuel ih=>
   have il:i< chunkCount (v-v/2) b:=by omega
   have io: i*b< v-v/2:=(chunk_offset _ _ _ hb).mp il
   have step:UniformMachine.step program n x s=.running (setPC s 71):=by
    simp [UniformMachine.step,hp,outer_branch,h.targetOffset,h.target,setPC,io]
   have branch:=UniformPreparationRowTableMachine.control_run program n B 71 x s hs (by omega) step
   let a:=setPC s 71
   have ac:=h.withPC 71
   have safe:=target_safe a ac hbv io hv
   have setup:=block_runs targetSetup program 71 n B x a target_code rfl branch.final_bound
    (by change 71+5≤ B;omega) safe.1 safe.2
   let e:=applyBlock targetSetup a
   have ep:e.pc=76:=by rw [applyBlock_pc];rfl
   have ec:=target_result a ac.toBase ac.targetOffset ac.count
   have ed:Done v o d b (i*chunkCount (v/2) b) e:=prior
   obtain ⟨u,inner,up,uc,ud,innerOutside⟩:=source_loop n v o d b i 0 (chunkCount (v/2) b) B x e hb hbv il (by omega)
    (by simpa using ec) ed ep setup.final_bound hd ho hv
   let f:=writeNat u 4256 (u.natReg 4256+u.natReg 4250)
   have ub:WordBound B f:=writeNat_bound B u 4256 _ inner.final_bound (by rw [up];omega)
    (by rw [uc.targetOffset,uc.selected];omega)
   have advance:BoundedRuns program n x B u 1 f:=.next inner.final_bound
    (by simp [UniformMachine.step,up,advance_at,evalNat,f]) (.refl ub)
   have fp:f.pc=99:=by simp [f,writeNat,next,up]
   have fc:=advance_result uc
   have backStep:UniformMachine.step program n x f=.running (setPC f 70):=by
    simp [UniformMachine.step,fp,outer_jump,setPC]
   have back:=UniformPreparationRowTableMachine.control_run program n B 70 x f ub (by omega) backStep
   have nextDone:Done v o d b ((i+1)*chunkCount (v/2) b) (setPC f 70):=ud
   obtain ⟨z,tail,zp,zc,zt,outside⟩:=ih (i+1) (setPC f 70) (by omega) (fc.withPC 70) nextDone rfl back.final_bound
   refine ⟨z,?_,zp,zc,zt,?_⟩
   have time:1+5+(22*chunkCount (v/2) b+1)+1+1+((22*chunkCount (v/2) b+9)*fuel+1)=
     (22*chunkCount (v/2) b+9)*(fuel+1)+1:=by ring
   · simpa only [show targetSetup.length=5 from rfl,time] using
      ((((branch.trans setup).trans inner).trans advance).trans back).trans tail
   · intro q hq
     exact (outside q hq).trans (innerOutside q hq)


lemma Base.withPC {v o d b:ℕ} {s:State} (h:Base v o d b s) (pc:ℕ):
 Base v o d b (setPC s pc):=by
 rcases h with ⟨⟨width,offset,destination⟩,sel,half,target,zero,one,two,seven⟩
 exact ⟨⟨width,offset,destination⟩,sel,half,target,zero,one,two,seven⟩
lemma width_branch:program[68]?=some (.branchLT 4240 4262 100 69):=rfl
lemma positive_branch:program[69]?=some (.branchLT 4260 4250 70 100):=rfl

def emittedCount (v:ℕ):ℕ:=if v<2 ∨ selected v=0 then 0 else
 chunkCount (v-v/2) (selected v)*chunkCount (v/2) (selected v)
structure Result (v o d:ℕ) (s:State):Prop extends Base v o d (selected v) s where
 count:s.natReg 4257=emittedCount v
 table:2≤ v→0<UniformWorkspacePlanner.selected v→Table v o d (UniformWorkspacePlanner.selected v) s

lemma branch_execution (n v o d B:ℕ) (x:Fin n→ℂ) (s:State)
 (h:Base v o d (selected v) s) (count:s.natReg 4257=0) (offset:s.natReg 4256=0)
 (hp:s.pc=68) (hs:WordBound B s)
 (hd:d+7*(chunkCount (v-v/2) (selected v)*chunkCount (v/2) (selected v))≤ B)
 (ho:o≤ B) (hv:2*v+101≤ B):
 ∃u t,BoundedExecution program n x B s t u∧
 t≤(22*chunkCount (v/2) (selected v)+9)*chunkCount (v-v/2) (selected v)+4∧
 u.pc=100∧Result v o d u∧Outside d
  (chunkCount (v-v/2) (selected v)*chunkCount (v/2) (selected v)) s u:=by
 have code:101≤ B:=by omega
 by_cases small:v<2
 · have step:UniformMachine.step program n x s=.running (setPC s 100):=by
    simp [UniformMachine.step,hp,width_branch,h.width,h.two,setPC,small]
   have run:=UniformPreparationRowTableMachine.control_run program n B 100 x s hs (by omega) step
   have halt:BoundedExecution program n x B (setPC s 100) 1 (setPC s 100):=
    .halt run.final_bound (by simp [UniformMachine.step,setPC,outer_halt])
   refine ⟨setPC s 100,2,by simpa using run.executes halt,by omega,rfl,?_,fun q hq=>rfl⟩
   exact ⟨h.withPC 100,by simpa [emittedCount,small,setPC] using count,by intro big positive;omega⟩
 · have firstStep:UniformMachine.step program n x s=.running (setPC s 69):=by
    simp [UniformMachine.step,hp,width_branch,h.width,h.two,setPC,small]
   have first:=UniformPreparationRowTableMachine.control_run program n B 69 x s hs (by omega) firstStep
   let a:=setPC s 69
   have ac:=h.withPC 69
   by_cases empty:selected v=0
   · have step:UniformMachine.step program n x a=.running (setPC a 100):=by
      simp [UniformMachine.step,a,positive_branch,h.zero,h.selected,setPC,empty]
     have run:=UniformPreparationRowTableMachine.control_run program n B 100 x a first.final_bound (by omega) step
     have halt:BoundedExecution program n x B (setPC a 100) 1 (setPC a 100):=
      .halt run.final_bound (by simp [UniformMachine.step,setPC,outer_halt])
     refine ⟨setPC a 100,3,by simpa using first.executes (run.executes halt),by omega,rfl,?_,fun q hq=>rfl⟩
     exact ⟨ac.withPC 100,by simpa [emittedCount,empty,setPC,a] using count,
       by intro big positive;omega⟩
   · have positive:0<selected v:=by omega
     have step:UniformMachine.step program n x a=.running (setPC a 70):=by
      simp [UniformMachine.step,a,positive_branch,h.zero,h.selected,setPC,positive]
     have second:=UniformPreparationRowTableMachine.control_run program n B 70 x a first.final_bound (by omega) step
     let e:=setPC a 70
     have ec:Outer v o d (selected v) 0 e:=⟨ac.withPC 70,by simpa [e,a,setPC] using offset,
      by simpa [e,a,setPC] using count⟩
     obtain ⟨u,run,up,uc,table,outside⟩:=target_loop n v o d (selected v) 0
      (chunkCount (v-v/2) (selected v)) B x e positive (selected_le v) (by omega)
      ec (by simpa only [Nat.zero_mul] using done_zero v o d (selected v) e) rfl second.final_bound hd ho hv
     have halt:BoundedExecution program n x B u 1 u:=
      .halt run.final_bound (by simp [UniformMachine.step,up,outer_halt])
     refine ⟨u,2+((22*chunkCount (v/2) (selected v)+9)*chunkCount (v-v/2) (selected v)+1)+1,
      ((first.trans second).trans run).executes halt,by omega,up,?_,outside⟩
     exact ⟨uc.toBase,by simpa [emittedCount,small,empty] using uc.count,by intro big positive;exact table⟩

/-- A fixed charged printer for ALL real rectangles at one actual balanced node.
The subtree offset changes physical placement, never the algebraic kernel i0/j0. -/
theorem execution (n v o d B:ℕ) (x:Fin n→ℂ) (s:State) (hh:Header v o d s)
 (hp:s.pc=0) (hs:WordBound B s) (hb:UniformWorkspaceSearchMachine.budget v≤ B)
 (hd:d+7*(chunkCount (v-v/2) (selected v)*chunkCount (v/2) (selected v))≤ B)
 (ho:o≤ B) (hv:2*v+101≤ B):
 ∃u t,BoundedExecution program n x B s t u∧
 t≤256*(v+1)^4+(22*chunkCount (v/2) (selected v)+9)*chunkCount (v-v/2) (selected v)+14∧
 u.pc=100∧Result v o d u∧Outside d
  (chunkCount (v-v/2) (selected v)*chunkCount (v/2) (selected v)) s u:=by
 obtain ⟨a,ta,run,cost,ap,base,offset,count,heap⟩:=startup n v o d B x s hh hp hs hb
 obtain ⟨u,tu,finish,time,up,result,outside⟩:=branch_execution n v o d B x a base count offset ap run.final_bound hd ho hv
 exact ⟨u,ta+tu,run.executes finish,by omega,up,result,fun q hq=>(outside q hq).trans (congrFun heap q)⟩


/-- Exact syntactic register footprint, used by the fixed tree driver. -/
def natCeiling:Instruction→ℕ
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>d+1
 | _=>0
lemma high_nat (q:ℕ) (hq:4264≤q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 have top:program.all (fun ins=>decide (natCeiling ins≤4264))=true:=by decide
 intro ins hi
 have hb: natCeiling ins≤4264:=of_decide_eq_true ((List.all_eq_true.mp top) ins hi)
 cases ins <;> simp only [natCeiling] at hb
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega
lemma execution_high_nat {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u) (q:ℕ) (hq:4264≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat h.executes (high_nat q hq)

/-- No scalar/input/root/output opcode is hidden inside Search58 or this printer. -/
def NatOnly:Instruction→Prop
 | .natLiteral _ _ | .natBinary _ _ _ _ | .loadNat _ _ | .storeNat _ _ |
   .branchLT _ _ _ _ | .jump _ | .halt=>True
 | _=>False
instance (ins:Instruction):Decidable (NatOnly ins):=by cases ins <;> simp [NatOnly] <;> infer_instance
lemma program_natOnly:∀ins∈program,NatOnly ins:=by
 have top:program.all (fun ins=>decide (NatOnly ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp top) ins hi)
structure ScalarFrame (s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 rootOrders:u.rootOrders=s.rootOrders
lemma ScalarFrame.trans {s u v:State} (h:ScalarFrame s u) (g:ScalarFrame u v):ScalarFrame s v:=
 ⟨g.scalarHeap.trans h.scalarHeap,g.scalarReg.trans h.scalarReg,
  g.outputs.trans h.outputs,g.rootOrders.trans h.rootOrders⟩
lemma natOnly_step {p:Program} {n:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀ins∈p,NatOnly ins) (run:step p n x s=.running u):ScalarFrame s u:=by
 cases hc:p[s.pc]? with
 | none=>simp [step,hc] at run
 | some ins=>
   obtain ⟨hp,he⟩:=List.getElem?_eq_some_iff.1 hc
   have allowed:=code ins (List.mem_of_getElem he)
   cases ins <;> simp only [NatOnly] at allowed
   all_goals simp only [step,hc] at run
   all_goals try simp only [StepResult.running.injEq] at run
   all_goals try cases run
   all_goals try exact ⟨rfl,rfl,rfl,rfl⟩
   all_goals repeat' (first | (subst u;exact ⟨rfl,rfl,rfl,rfl⟩) |
    (split at run <;> simp_all [writeNat,next]))
lemma natOnly_runs {p:Program} {n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀ins∈p,NatOnly ins) (run:Runs p n x s t u):ScalarFrame s u:=by
 induction run with
 | refl=>exact ⟨rfl,rfl,rfl,rfl⟩
 | next step tail ih=>exact (natOnly_step code step).trans ih
lemma natOnly_execution {p:Program} {n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀ins∈p,NatOnly ins) (run:Executes p n x s t u):ScalarFrame s u:=by
 induction run with
 | halt=>exact ⟨rfl,rfl,rfl,rfl⟩
 | next step tail ih=>exact (natOnly_step code step).trans ih
lemma execution_scalarFrame {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u):ScalarFrame s u:=
 natOnly_execution program_natOnly h.executes

end
end ExactFourierCircuits.UniformLocalRectangleDescriptors
