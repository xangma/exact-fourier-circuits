import UniformLocalCacheTreeCoverage

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalReplaySlotMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformLocalCacheChronology

def bit (b:Bool):ℕ:=if b then 1 else 0

def levelCount (H:ℕ) (broadcast:Bool):ℕ:=if broadcast then 1 else H+1

def decodedSlot (H:ℕ) (broadcast enabled inverse:Bool) (d c:ℕ):Slot:=
 ⟨broadcast,enabled,inverse,if broadcast then 0 else if inverse then H-d else d,
  if inverse then 10-c else c⟩

def Slot.words(s:Slot):List ℕ:=[bit s.broadcast,bit s.enabled,bit s.inverse,s.depth,s.color]

def slots (H:ℕ) (broadcast enabled inverse:Bool):List Slot:=
 (List.range (levelCount H broadcast)).flatMap fun d=>
 (List.range 11).map (decodedSlot H broadcast enabled inverse d)

lemma slots_length(H:ℕ)(broadcast enabled inverse:Bool):
 (slots H broadcast enabled inverse).length=11*levelCount H broadcast:=by
 simp [slots,List.length_flatMap,Nat.mul_comm]

/-- One fixed integer-only phase printer. The inverse phase reverses depths and
colors physically, before storing its five-field slot records. -/
def boot:List Op:=[.literal 4210 0,.literal 4211 1,.literal 4212 5,.literal 4213 11,.literal 4214 10,
 .sub 4219 4211 4202,.mul 4215 4219 4200,.add 4215 4215 4211,.sub 4218 4211 4204,
 .literal 4216 0,.add 4226 4201 4210]
def body:List Op:=[.sub 4220 4200 4216,.mul 4220 4204 4220,.mul 4221 4218 4216,
 .add 4222 4220 4221,.mul 4222 4219 4222,.sub 4223 4214 4217,.mul 4223 4204 4223,
 .mul 4224 4218 4217,.add 4225 4223 4224,
 .putNat 4226 4202,.add 4226 4226 4211,.putNat 4226 4203,.add 4226 4226 4211,
 .putNat 4226 4204,.add 4226 4226 4211,.putNat 4226 4222,.add 4226 4226 4211,
 .putNat 4226 4225,.add 4226 4226 4211,.add 4217 4217 4211]
def advance:List Op:=[.add 4216 4216 4211]
def program:Program:=boot.map Op.code++[.branchLT 4216 4215 12 37,.natLiteral 4217 0,
 .branchLT 4217 4213 14 35]++body.map Op.code++[.jump 13]++advance.map Op.code++[.jump 11,.halt]
lemma boot_length:boot.length=11:=rfl
lemma body_length:body.length=20:=rfl
lemma program_length:program.length=38:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma body_code:BlockAt body program 14:=by intro i hi;change i<20 at hi;interval_cases i <;>rfl
lemma advance_code:BlockAt advance program 35:=by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma outer_at:program[11]?=some (.branchLT 4216 4215 12 37):=rfl
lemma colorInit_at:program[12]?=some (.natLiteral 4217 0):=rfl
lemma color_at:program[13]?=some (.branchLT 4217 4213 14 35):=rfl
lemma colorJump_at:program[34]?=some (.jump 13):=rfl
lemma levelJump_at:program[36]?=some (.jump 11):=rfl
lemma halt_at:program[37]?=some .halt:=rfl

structure Header(H A:ℕ)(broadcast enabled inverse:Bool)(s:State):Prop where
 height:s.natReg 4200=H
 base:s.natReg 4201=A
 broadcast:s.natReg 4202=bit broadcast
 enabled:s.natReg 4203=bit enabled
 inverse:s.natReg 4204=bit inverse
structure Constants(H:ℕ)(broadcast inverse:Bool)(s:State):Prop where
 zero:s.natReg 4210=0
 one:s.natReg 4211=1
 five:s.natReg 4212=5
 eleven:s.natReg 4213=11
 ten:s.natReg 4214=10
 levels:s.natReg 4215=levelCount H broadcast
 notBroadcast:s.natReg 4219=1-bit broadcast
 notInverse:s.natReg 4218=1-bit inverse
structure Cursor(H A:ℕ)(broadcast enabled inverse:Bool)(d c:ℕ)(s:State):Prop where
 header:Header H A broadcast enabled inverse s
 constants:Constants H broadcast inverse s
 depth:s.natReg 4216=d
 color:s.natReg 4217=c
 address:s.natReg 4226=A+5*(11*d+c)

def Done(H A:ℕ)(broadcast enabled inverse:Bool)(used:ℕ)(s:State):Prop:=
 ∀(d:Fin (levelCount H broadcast))(c:Fin 11),11*d.val+c.val<used→∀f:Fin 5,
 s.natHeap (A+5*(11*d.val+c.val)+f.val)=some ((Slot.words (decodedSlot H broadcast enabled inverse d.val c.val))[f.val]'f.isLt)

def Outside(A length:ℕ)(s u:State):Prop:=∀q,q<A∨A+5*length≤q→u.natHeap q=s.natHeap q
lemma Outside.trans{A l:ℕ}{s u v:State}(h:Outside A l s u)(g:Outside A l u v):Outside A l s v:=
 fun q hq=>(g q hq).trans (h q hq)
lemma Cursor.withPC{H A d c:ℕ}{b e i:Bool}{s:State}(h:Cursor H A b e i d c s)(pc:ℕ):
 Cursor H A b e i d c (setPC s pc):=
 ⟨⟨h.header.height,h.header.base,h.header.broadcast,h.header.enabled,h.header.inverse⟩,
 ⟨h.constants.zero,h.constants.one,h.constants.five,h.constants.eleven,h.constants.ten,
 h.constants.levels,h.constants.notBroadcast,h.constants.notInverse⟩,h.depth,h.color,h.address⟩
lemma Done.withPC{H A used:ℕ}{b e i:Bool}{s:State}(h:Done H A b e i used s)(pc:ℕ):
 Done H A b e i used (setPC s pc):=by
 simpa only [Done,setPC] using h

lemma boot_header {H A:ℕ}{b e i:Bool}(s:State)(h:Header H A b e i s):
 Header H A b e i (applyBlock boot s):=by
 constructor
 · simpa [boot,applyBlock,Op.apply,writeNat,next] using h.height
 · simpa [boot,applyBlock,Op.apply,writeNat,next] using h.base
 · simpa [boot,applyBlock,Op.apply,writeNat,next] using h.broadcast
 · simpa [boot,applyBlock,Op.apply,writeNat,next] using h.enabled
 · simpa [boot,applyBlock,Op.apply,writeNat,next] using h.inverse
lemma boot_constants {H A:ℕ}{b e i:Bool}(s:State)(h:Header H A b e i s):
 Constants H b i (applyBlock boot s):=by
 constructor
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,h.height,h.broadcast,h.inverse,bit,levelCount]
 all_goals cases b <;>simp
lemma boot_safe {H A B:ℕ}{b e i:Bool}(s:State)(h:Header H A b e i s)(hs:WordBound B s)
 (hb:38≤B)(hh:H+1≤B):readable boot s∧peak boot s≤B:=by
 have ha:=hs.2.1 4201;rw [h.base] at ha
 constructor
 · simp [boot,readable,Op.readable]
 · cases b <;>cases i <;>simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.height,h.base,h.broadcast,h.inverse,bit]
   all_goals omega

lemma body_heap {H A d c:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d c s):
 (applyBlock body s).natHeap=
 Function.update (Function.update (Function.update (Function.update (Function.update s.natHeap
 (A+5*(11*d+c)) (some (bit b))) (A+5*(11*d+c)+1) (some (bit e)))
 (A+5*(11*d+c)+2) (some (bit i))) (A+5*(11*d+c)+3)
 (some ((decodedSlot H b e i d c).depth))) (A+5*(11*d+c)+4)
 (some ((decodedSlot H b e i d c).color)):=by
 cases b <;>cases i <;>simp [body,applyBlock,Op.apply,writeNat,next,h.header.broadcast,h.header.enabled,
 h.header.inverse,h.header.height,h.constants.one,h.constants.ten,h.constants.notBroadcast,
 h.constants.notInverse,h.depth,h.color,h.address,bit,decodedSlot]

lemma body_cursor {H A d c:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d c s):
 Cursor H A b e i d (c+1) (applyBlock body s):=by
 constructor
 · constructor <;>first |simpa [body,applyBlock,Op.apply,writeNat,next] using h.header.height |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.header.base |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.header.broadcast |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.header.enabled |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.header.inverse
 · constructor <;>first |simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.zero |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.one |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.five |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.eleven |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.ten |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.levels |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.notBroadcast |
    simpa [body,applyBlock,Op.apply,writeNat,next] using h.constants.notInverse
 · simpa [body,applyBlock,Op.apply,writeNat,next] using h.depth
 · simp [body,applyBlock,Op.apply,writeNat,next,h.color,h.constants.one]
 · simp [body,applyBlock,Op.apply,writeNat,next,h.address,h.constants.one];ring

lemma body_done {H A d c:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d c s)
 (_hd:d<levelCount H b)(hc:c<11)(old:Done H A b e i (11*d+c) s):
 Done H A b e i (11*d+c+1) (applyBlock body s):=by
 intro dd cc before f
 rw [body_heap s h]
 by_cases same:11*dd.val+cc.val=11*d+c
 · have cd:cc.val=c∧dd.val=d:=by have ccLt:=cc.isLt;omega
   rcases cd with ⟨ccEq,ddEq⟩
   fin_cases f <;>simp (disch:=omega) [Slot.words,Function.update,ccEq,ddEq,decodedSlot]
 · have past:11*dd.val+cc.val<11*d+c:=by omega
   have field:=old dd cc past f
   have ff:=f.isLt
   rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
   exact field

lemma body_outside {H A d c l:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d c s)
 (hc:11*d+c<l):Outside A l s (applyBlock body s):=by
 intro q hq
 rw [body_heap s h]
 rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
  Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

lemma body_safe {H A d c B:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d c s)
 (hd:d<levelCount H b)(hc:c<11)(hB:38≤B)(hH:H+1≤B)
 (hA:A+5*(11*d+c+1)≤B):readable body s∧peak body s≤B:=by
 constructor
 · simp [body,readable,Op.readable]
 · cases b <;>cases i
   all_goals simp only [levelCount,Bool.false_eq_true,ite_false,ite_true] at hd
   all_goals simp [body,peak,Op.peak,Op.apply,writeNat,next,h.header.height,h.header.broadcast,
     h.header.enabled,h.header.inverse,h.constants.one,h.constants.ten,h.constants.notBroadcast,
     h.constants.notInverse,h.depth,h.color,h.address,bit]
   all_goals cases e <;>simp
   all_goals omega

lemma one_color (n H A B d c:ℕ)(b e i:Bool)(x:Fin n→ℂ)(s:State)
 (h:Cursor H A b e i d c s)(hp:s.pc=13)(hs:WordBound B s)
 (hd:d<levelCount H b)(hc:c<11)(hB:38≤B)(hH:H+1≤B)(hA:A+5*11*levelCount H b≤B)
 (old:Done H A b e i (11*d+c) s):
 ∃u,BoundedRuns program n x B s 22 u∧u.pc=13∧Cursor H A b e i d (c+1) u∧
 Done H A b e i (11*d+c+1) u∧Outside A (11*levelCount H b) s u:=by
 have choose:UniformMachine.step program n x s=.running (setPC s 14):=by
   simp [UniformMachine.step,hp,color_at,h.color,h.constants.eleven,hc,setPC]
 have branch:=UniformPreparationRowTableMachine.control_run program n B 14 x s hs (by omega) choose
 let a:=setPC s 14
 have cursor:=h.withPC 14
 have safe:=body_safe a cursor hd hc hB hH (by nlinarith)
 have blocks:=block_runs body program 14 n B x a body_code rfl branch.final_bound
  (by rw [body_length];omega) safe.1 safe.2
 let z:=applyBlock body a
 have zp:z.pc=34:=by rw [applyBlock_pc,body_length];rfl
 have jump:UniformMachine.step program n x z=.running (setPC z 13):=by
   simp [UniformMachine.step,zp,colorJump_at,setPC]
 have back:=UniformPreparationRowTableMachine.control_run program n B 13 x z blocks.final_bound (by omega) jump
 refine ⟨setPC z 13,?_,rfl,(body_cursor a cursor).withPC 13,
   (body_done a cursor hd hc (old.withPC 14)).withPC 13,?_⟩
 · simpa [body_length,setPC] using branch.trans (blocks.trans back)
 · exact body_outside a cursor (by omega)

lemma colors (n H A B d c fuel:ℕ)(b e i:Bool)(x:Fin n→ℂ)(s:State)
 (h:Cursor H A b e i d c s)(hp:s.pc=13)(hs:WordBound B s)
 (hd:d<levelCount H b)(hc:c+fuel≤11)(hB:38≤B)(hH:H+1≤B)(hA:A+5*11*levelCount H b≤B)
 (old:Done H A b e i (11*d+c) s):
 ∃u,BoundedRuns program n x B s (22*fuel) u∧u.pc=13∧Cursor H A b e i d (c+fuel) u∧
 Done H A b e i (11*d+c+fuel) u∧Outside A (11*levelCount H b) s u:=by
 induction fuel generalizing c s with
 | zero=>exact ⟨s,.refl hs,hp,by simpa using h,by simpa using old,fun q hq=>rfl⟩
 | succ fuel ih=>
   obtain ⟨a,first,ap,cursor,done,outside⟩:=one_color n H A B d c b e i x s h hp hs hd (by omega) hB hH hA old
   obtain ⟨u,tail,up,final,table,frame⟩:=ih (c+1) a cursor ap first.final_bound (by omega) done
   refine ⟨u,?_,up,?_,?_,outside.trans frame⟩
   · convert first.trans tail using 1;omega
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using table

structure LevelCursor(H A:ℕ)(b e i:Bool)(d:ℕ)(s:State):Prop where
 header:Header H A b e i s
 constants:Constants H b i s
 depth:s.natReg 4216=d
 address:s.natReg 4226=A+5*11*d
lemma LevelCursor.withPC{H A d:ℕ}{b e i:Bool}{s:State}(h:LevelCursor H A b e i d s)(pc:ℕ):
 LevelCursor H A b e i d (setPC s pc):=
 ⟨⟨h.header.height,h.header.base,h.header.broadcast,h.header.enabled,h.header.inverse⟩,
 ⟨h.constants.zero,h.constants.one,h.constants.five,h.constants.eleven,h.constants.ten,
 h.constants.levels,h.constants.notBroadcast,h.constants.notInverse⟩,h.depth,h.address⟩
lemma initialized {H A:ℕ}{b e i:Bool}(s:State)(h:Header H A b e i s):
 LevelCursor H A b e i 0 (applyBlock boot s):=by
 refine ⟨boot_header s h,boot_constants s h,?_,?_⟩
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.base]
lemma colorInit_code:BlockAt [.literal 4217 0] program 12:=by
 intro j hj;change j<1 at hj;interval_cases j;rfl
lemma color_initialized{H A d:ℕ}{b e i:Bool}(s:State)(h:LevelCursor H A b e i d s):
 Cursor H A b e i d 0 (applyBlock [.literal 4217 0] s):=by
 constructor
 · constructor <;>simp [applyBlock,Op.apply,writeNat,next,h.header.height,h.header.base,
    h.header.broadcast,h.header.enabled,h.header.inverse]
 · constructor <;>simp [applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one,h.constants.five,
    h.constants.eleven,h.constants.ten,h.constants.levels,h.constants.notBroadcast,h.constants.notInverse]
 · simpa [applyBlock,Op.apply,writeNat,next] using h.depth
 · simp [applyBlock,Op.apply,writeNat,next]
 · simp [applyBlock,Op.apply,writeNat,next,h.address];ring

lemma advanced {H A d:ℕ}{b e i:Bool}(s:State)(h:Cursor H A b e i d 11 s):
 LevelCursor H A b e i (d+1) (applyBlock advance s):=by
 constructor
 · constructor <;>simp [advance,applyBlock,Op.apply,writeNat,next,h.header.height,h.header.base,
    h.header.broadcast,h.header.enabled,h.header.inverse]
 · constructor <;>simp [advance,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one,h.constants.five,
    h.constants.eleven,h.constants.ten,h.constants.levels,h.constants.notBroadcast,h.constants.notInverse]
 · simp [advance,applyBlock,Op.apply,writeNat,next,h.depth,h.constants.one]
 · simp [advance,applyBlock,Op.apply,writeNat,next,h.address];ring

lemma one_level (n H A B d:ℕ)(b e i:Bool)(x:Fin n→ℂ)(s:State)
 (h:LevelCursor H A b e i d s)(hp:s.pc=11)(hs:WordBound B s)
 (hd:d<levelCount H b)(hB:38≤B)(hH:H+1≤B)(hA:A+5*11*levelCount H b≤B)
 (old:Done H A b e i (11*d) s):
 ∃u,BoundedRuns program n x B s 247 u∧u.pc=11∧LevelCursor H A b e i (d+1) u∧
 Done H A b e i (11*(d+1)) u∧Outside A (11*levelCount H b) s u:=by
 have choose:UniformMachine.step program n x s=.running (setPC s 12):=by
  simp [UniformMachine.step,hp,outer_at,h.depth,h.constants.levels,hd,setPC]
 have branch:=UniformPreparationRowTableMachine.control_run program n B 12 x s hs (by omega) choose
 let a:=setPC s 12
 have init:=block_runs [.literal 4217 0] program 12 n B x a colorInit_code rfl branch.final_bound
   (by simp;omega) (by simp [readable,Op.readable]) (by simp [peak,Op.peak])
 let z:=applyBlock [.literal 4217 0] a
 have zp:z.pc=13:=by rw [applyBlock_pc];rfl
 have cur:=color_initialized a (h.withPC 12)
 obtain ⟨v,run,vp,vc,table,frame⟩:=colors n H A B d 0 11 b e i x z cur zp init.final_bound hd (by omega)
   hB hH hA (by simpa only [Done,Nat.add_zero,z,a,applyBlock,Op.apply,writeNat,next,setPC] using old)
 have exitStep:UniformMachine.step program n x v=.running (setPC v 35):=by
   simp [UniformMachine.step,vp,color_at,vc.color,vc.constants.eleven,setPC]
 have exit:=UniformPreparationRowTableMachine.control_run program n B 35 x v run.final_bound (by omega) exitStep
 let v':=setPC v 35
 have adv:=block_runs advance program 35 n B x v' advance_code rfl exit.final_bound
   (by change 36≤B;omega) (by simp [advance,readable,Op.readable])
   (by simp [advance,peak,Op.peak,v',vc.depth,vc.constants.one,setPC];
       cases b <;>simp [levelCount] at hd <;>omega)
 let w:=applyBlock advance v'
 have wp:w.pc=36:=by rw [applyBlock_pc];rfl
 have stepBack:UniformMachine.step program n x w=.running (setPC w 11):=by
   simp [UniformMachine.step,wp,levelJump_at,setPC]
 have back:=UniformPreparationRowTableMachine.control_run program n B 11 x w adv.final_bound (by omega) stepBack
 refine ⟨setPC w 11,?_,rfl,(advanced v' (vc.withPC 35)).withPC 11,?_,?_⟩
 · simpa [List.length_cons,List.length_nil,advance,setPC] using
    branch.trans (init.trans (run.trans (exit.trans (adv.trans back))))
 · simpa only [Done,w,v',advance,applyBlock,Op.apply,writeNat,next,setPC,Nat.mul_add,Nat.mul_one,Nat.add_zero] using table
 · intro q hq
   exact frame q hq

lemma levels (n H A B d fuel:ℕ)(b e i:Bool)(x:Fin n→ℂ)(s:State)
 (h:LevelCursor H A b e i d s)(hp:s.pc=11)(hs:WordBound B s)
 (hd:d+fuel≤levelCount H b)(hB:38≤B)(hH:H+1≤B)(hA:A+5*11*levelCount H b≤B)
 (old:Done H A b e i (11*d) s):
 ∃u,BoundedRuns program n x B s (247*fuel) u∧u.pc=11∧LevelCursor H A b e i (d+fuel) u∧
 Done H A b e i (11*(d+fuel)) u∧Outside A (11*levelCount H b) s u:=by
 induction fuel generalizing d s with
 | zero=>exact ⟨s,.refl hs,hp,by simpa using h,by simpa using old,fun q hq=>rfl⟩
 | succ fuel ih=>
   obtain ⟨a,first,ap,cursor,done,outside⟩:=one_level n H A B d b e i x s h hp hs (by omega) hB hH hA old
   obtain ⟨u,tail,up,final,table,frame⟩:=ih (d+1) a cursor ap first.final_bound (by omega) done
   refine ⟨u,?_,up,?_,?_,outside.trans frame⟩
   · convert first.trans tail using 1;omega
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using table

theorem execution (n H A B:ℕ)(b e i:Bool)(x:Fin n→ℂ)(s:State)
 (h:Header H A b e i s)(hp:s.pc=0)(hs:WordBound B s)(hB:38≤B)
 (hH:H+1≤B)(hA:A+5*11*levelCount H b≤B):
 ∃u,BoundedExecution program n x B s (247*levelCount H b+13) u∧u.pc=37∧
 Done H A b e i (11*levelCount H b) u∧u.natReg 4226=A+5*11*levelCount H b∧Outside A (11*levelCount H b) s u:=by
 have safe:=boot_safe s h hs hB hH
 have bootRun:=block_runs boot program 0 n B x s boot_code hp hs (by rw [boot_length];omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=11:=by rw [applyBlock_pc,hp,boot_length]
 obtain ⟨z,run,zp,final,table,frame⟩:=levels n H A B 0 (levelCount H b) b e i x a
   (initialized s h) ap bootRun.final_bound (by omega) hB hH hA
   (by intro d c impossible;omega)
 have exitStep:UniformMachine.step program n x z=.running (setPC z 37):=by
   simp [UniformMachine.step,zp,outer_at,final.depth,final.constants.levels,setPC]
 have exit:=UniformPreparationRowTableMachine.control_run program n B 37 x z run.final_bound (by omega) exitStep
 have halt:BoundedExecution program n x B (setPC z 37) 1 (setPC z 37):=
   .halt exit.final_bound (by simp [UniformMachine.step,setPC,halt_at])
 refine ⟨setPC z 37,?_,rfl,?_,?_,?_⟩
 · convert bootRun.executes (run.executes (exit.executes halt)) using 1
   simp [boot_length];omega
 · simpa only [Done,Nat.zero_add,setPC] using table
 · simpa only [Nat.zero_add,setPC] using final.address
 · intro q hq
   exact (frame q hq).trans (by simp [a,boot,applyBlock,Op.apply,writeNat,next])

lemma reverse_range (N:ℕ):(List.range N).reverse=(List.range N).map (fun j=>N-1-j):=by
 have h:=@List.reverse_range' 0 N
 simpa only [Nat.zero_add,←List.range_eq_range'] using h

lemma slots_forward (H:ℕ)(b e:Bool):slots H b e false=
 if b then broadcastSlots e else sweepSlots H e:=by
 cases b <;>simp [slots,levelCount,decodedSlot,sweepSlots,broadcastSlots]
 all_goals rfl

lemma slots_inverse (H:ℕ)(b e:Bool):slots H b e true=invertSlots (slots H b e false):=by
 cases b
 · unfold slots levelCount decodedSlot invertSlots
   simp only [Bool.false_eq_true,ite_false,ite_true]
   rw [List.reverse_flatMap]
   simp only [List.map_flatMap,Function.comp_def,←List.map_reverse]
   simp only [reverse_range,List.flatMap_map,List.map_map,Function.comp_def]
   apply List.flatMap_congr
   intro d hd
   simp only [Bool.not_false,Nat.add_sub_cancel]
 · simp only [slots,levelCount,ite_true,List.range_one,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,invertSlots,←List.map_reverse]
   rw [reverse_range]
   simp [List.map_map,decodedSlot,Function.comp_def]

lemma slots_all_phases (H:ℕ):
 slots H false true false++slots H true true false++slots H false true true++
 slots H false false false++slots H true false true++slots H false false true=replaySlots H:=by
 simp only [slots_inverse,slots_forward,Bool.false_eq_true,ite_false,ite_true,replaySlots]

def destinations(ins:Instruction):Prop:=match ins with
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>4210≤d∧d<4227
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by cases ins <;>simp [destinations] <;>infer_instance
lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 have all:program.all (fun ins=>decide (UniformLocalRectangleDescriptors.NatOnly ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp all) ins hi)
lemma program_destinations:∀ins∈program,destinations ins:=by
 have all:program.all (fun ins=>decide (destinations ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp all) ins hi)
lemma keeps_nat(q:ℕ)(hq:q<4210∨4227≤q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have allowed:=program_natOnly ins hi
 have bounds:=program_destinations ins hi
 cases ins <;>simp only [destinations] at bounds
 all_goals simp only [UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega
lemma execution_natFrame{n B t:ℕ}{x:Fin n→ℂ}{s u:State}(run:BoundedExecution program n x B s t u)
 (q:ℕ)(hq:q<4210∨4227≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_nat q hq)
lemma execution_scalarFrame{n B t:ℕ}{x:Fin n→ℂ}{s u:State}(run:BoundedExecution program n x B s t u):
 UniformLocalRectangleDescriptors.ScalarFrame s u:=
 UniformLocalRectangleDescriptors.natOnly_execution program_natOnly run.executes

end ExactFourierCircuits.UniformLocalReplaySlotMachine
