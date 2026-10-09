import UniformLocalRequestAdvanceMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestCursorMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine

def before:List Op:=[.literal 6190 0,.literal 6191 1,.literal 6193 7,.literal 6194 4,
 .add 6173 4274 6190,.add 6161 6177 6190,.literal 6174 0,.sub 6179 4282 4274]
def after:List Op:=[.add 6160 6820 6190,.add 6162 6813 6190,
 .add 6163 6162 6800,.add 6164 6163 6800,.add 6165 6164 6800,.add 6166 6165 6194,
 .add 6168 6400 6190,.add 6169 6416 6190,.add 6170 6431 6190,
 .add 6171 6421 6190,.add 6172 6171 6191]
def program:Program:=before.map Op.code++[.natBinary .div 6179 6179 6193]++after.map Op.code++[.halt]
lemma program_length:program.length=21:=rfl
lemma before_length:before.length=8:=rfl
lemma after_length:after.length=11:=rfl
lemma before_code:BlockAt before program 0:=by intro i hi;change i<8 at hi;interval_cases i <;>rfl
lemma after_code:BlockAt after program 9:=by intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma div_at:program[8]?=some (.natBinary .div 6179 6179 6193):=rfl
lemma halt_at:program[20]?=some .halt:=rfl

/-- These are retained physical allocator/forest/timing fields, not a printed
request count or an initialized request controller. -/
structure Header (r R M T P S z:ℕ)(s:State):Prop where
 radix:s.natReg 6800=r
 requests:s.natReg 4274=R
 requestsEnd:s.natReg 4282=R+7*M
 times:s.natReg 6177=T
 permutation:s.natReg 6813=P
 pool:s.natReg 6820=S
 lowRow:s.natReg 6400=z
 control:s.natReg 6416=17*z
 inverse:s.natReg 6431=32*z
 mu:s.natReg 6421=22*z

structure Cursor (r R M T P S z:ℕ)(s:State):Prop where
 pool:s.natReg 6160=S
 permutation:s.natReg 6162=P
 widths:s.natReg 6163=P+r
 markers:s.natReg 6164=P+2*r
 axis:s.natReg 6165=P+3*r
 abi:s.natReg 6166=P+3*r+4
 lowRow:s.natReg 6168=z
 control:s.natReg 6169=17*z
 inverse:s.natReg 6170=32*z
 mu:s.natReg 6171=22*z
 conjugateMu:s.natReg 6172=22*z+1
 pointer:s.natReg 6173=R
 timePointer:s.natReg 6161=T
 index:s.natReg 6174=0
 count:s.natReg 6179=M

noncomputable section
def started(s:State):State:=applyBlock before s
def divided(s:State):State:=writeNat (started s) 6179
 ((s.natReg 4282-s.natReg 4274)/7)
def finished(s:State):State:=applyBlock after (divided s)
lemma started_pc(s:State):(started s).pc=s.pc+8:=applyBlock_pc before s
lemma started_keep(s:State)(q:ℕ)(hi:6200 ≤ q):(started s).natReg q=s.natReg q:=by
 apply block_keeps
 intro o ho
 simp only [before,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp [Op.code,UniformNewtonTableMachine.KeepsNat];omega
lemma before_safe{B:ℕ}(s:State)(wb:WordBound B s)(code:7 ≤ B):
 readable before s ∧ peak before s ≤ B:=by
 constructor
 · simp [before,readable,Op.readable]
 · have a:=wb.2.1 4274
   have b:=wb.2.1 6177
   have c: s.natReg 4282-s.natReg 4274 ≤ B:=Nat.sub_le _ _ |>.trans (wb.2.1 4282)
   simp only [before,peak,Op.peak,Op.apply,writeNat,next,Function.update_apply]
   simp only [Nat.reduceEqDiff,ite_false,ite_true,Nat.add_zero]
   omega
lemma divided_header{r R M T P S z:ℕ}{s:State}(h:Header r R M T P S z s):
 Header r R M T P S z (divided s):=by
 constructor
 all_goals simp [divided,started,before,applyBlock,Op.apply,writeNat,next,
  h.radix,h.requests,h.requestsEnd,h.times,h.permutation,h.pool,h.lowRow,h.control,h.inverse,h.mu]
lemma divided_special{r R M T P S z:ℕ}{s:State}(h:Header r R M T P S z s):
 (divided s).natReg 6190=0 ∧ (divided s).natReg 6191=1 ∧ (divided s).natReg 6194=4 ∧
 (divided s).natReg 6173=R ∧ (divided s).natReg 6161=T ∧
 (divided s).natReg 6174=0 ∧ (divided s).natReg 6179=M:=by
 simp [divided,started,before,applyBlock,Op.apply,writeNat,next,h.requests,h.requestsEnd,h.times,
  Nat.mul_comm]
lemma after_safe{r R M T P S z B:ℕ}{s:State}(h:Header r R M T P S z s)
 (wb:WordBound B s)(room:P+3*r+4 ≤ B)(temporary:22*z+1 ≤ B):
 readable after (divided s) ∧ peak after (divided s) ≤ B:=by
 have h':=divided_header h
 obtain ⟨zero,one,four,_,_,_,_⟩:=divided_special h
 constructor
 · simp [after,readable,Op.readable]
 · have poolBound:S ≤ B:=h.pool ▸ wb.2.1 6820
   have lowBound:z ≤ B:=h.lowRow ▸ wb.2.1 6400
   have controlBound:17*z ≤ B:=h.control ▸ wb.2.1 6416
   have inverseBound:32*z ≤ B:=h.inverse ▸ wb.2.1 6431
   simp only [after,peak,Op.peak,Op.apply,writeNat,next,Function.update_apply]
   simp only [Nat.reduceEqDiff,ite_false,ite_true,zero,one,four,h'.pool,h'.permutation,h'.radix,
    h'.lowRow,h'.control,h'.inverse,h'.mu,Nat.add_zero]
   omega
lemma finished_cursor{r R M T P S z:ℕ}{s:State}(h:Header r R M T P S z s):
 Cursor r R M T P S z (finished s):=by
 have h':=divided_header h
 obtain ⟨zero,one,four,pointer,time,index,count⟩:=divided_special h
 constructor
 all_goals simp [finished,after,applyBlock,Op.apply,writeNat,next,zero,one,four,
  h'.pool,h'.permutation,h'.radix,h'.lowRow,h'.control,h'.inverse,h'.mu,pointer,time,index,count]
 all_goals omega
lemma finished_heaps(s:State):(finished s).natHeap=s.natHeap ∧ (finished s).scalarHeap=s.scalarHeap ∧
 (finished s).scalarReg=s.scalarReg ∧ (finished s).outputs=s.outputs ∧ (finished s).rootOrders=s.rootOrders:=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Literal21 derives the real count by subtraction/division of the produced
request end, and all initial cache addresses by charged Nat instructions. -/
theorem execution {n r R M T P S z B:ℕ}(x:Fin n → ℂ)(s:State)(h:Header r R M T P S z s)
 (room:P+3*r+4 ≤ B)(temporary:22*z+1 ≤ B)(code:21 ≤ B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution program n x B s 21 u ∧ u.pc=20 ∧ Cursor r R M T P S z u ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders:=by
 have safe:=before_safe s wb (by omega)
 have first:=block_runs before program 0 n B x s before_code pc wb
  (by rw [before_length];omega) safe.1 safe.2
 have ap:(started s).pc=8:=by rw [started_pc,pc]
 have mBound:M ≤ B:=by have b:=wb.2.1 4282;rw [h.requestsEnd] at b;omega
 have dv:((s.natReg 4282-s.natReg 4274)/7)=M:=by
  rw [h.requestsEnd,h.requests];simp [Nat.mul_comm]
 have bw:WordBound B (divided s):=by
  apply writeNat_bound B (started s) 6179 _ first.final_bound
  · rw [ap];omega
  · rw [dv];exact mBound
 have stepDiv:step program n x (started s)=.running (divided s):=by
  have seven:(started s).natReg 6193=7:=by
   simp [started,before,applyBlock,Op.apply,writeNat,next]
  have source:(started s).natReg 6179=s.natReg 4282-s.natReg 4274:=by
   simp [started,before,applyBlock,Op.apply,writeNat,next]
  rw [step,ap,div_at]
  simp only [evalNat,seven,source,show (7:ℕ) ≠ 0 by decide,ite_false]
  rfl
 have divider:BoundedRuns program n x B (started s) 1 (divided s):=
  .next first.final_bound stepDiv (.refl bw)
 have dp:(divided s).pc=9:=by simp [divided,writeNat,next,ap]
 have endSafe:=after_safe h wb room temporary
 have last:=block_runs after program 9 n B x (divided s) after_code dp bw
  (by rw [after_length];omega) endSafe.1 endSafe.2
 have hp:(finished s).pc=20:=by rw [finished,applyBlock_pc,after_length,dp]
 have stop:BoundedExecution program n x B (finished s) 1 (finished s):=.halt last.final_bound
  (by simp [step,hp,halt_at])
 obtain ⟨nh,sh,sr,out,roots⟩:=finished_heaps s
 refine ⟨finished s,?_,hp,finished_cursor h,nh,sh,sr,out,roots⟩
 convert first.executes (divider.executes (last.executes stop)) using 1
 simp only [before_length,after_length]

attribute [irreducible] started divided finished
end
end ExactFourierCircuits.UniformLocalRequestCursorMachine
