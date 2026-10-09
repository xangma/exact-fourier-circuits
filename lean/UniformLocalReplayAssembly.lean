import UniformLocalReplaySlotMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalReplayAssembly
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
namespace S
abbrev program:=UniformLocalReplaySlotMachine.program
abbrev Header:=UniformLocalReplaySlotMachine.Header
abbrev Done:=UniformLocalReplaySlotMachine.Done
end S

structure Flags where
 broadcast:Bool
 enabled:Bool
 inverse:Bool
 deriving Repr,DecidableEq

def flags(j:Fin 6):Flags:=
 if j.val=0 then ⟨false,true,false⟩ else if j.val=1 then ⟨true,true,false⟩ else
 if j.val=2 then ⟨false,true,true⟩ else if j.val=3 then ⟨false,false,false⟩ else
 if j.val=4 then ⟨true,false,true⟩ else ⟨false,false,true⟩
def phaseBase(j:ℕ):ℕ:=6+42*j

def boot:List Op:=[.literal 4207 0,.literal 4208 8,.literal 4209 6,
 .mul 4200 4205 4208,.add 4200 4200 4209,.add 4201 4206 4207]
def setup(j:Fin 6):List Op:=[.literal 4202 (UniformLocalReplaySlotMachine.bit (flags j).broadcast),
 .literal 4203 (UniformLocalReplaySlotMachine.bit (flags j).enabled),
 .literal 4204 (UniformLocalReplaySlotMachine.bit (flags j).inverse)]
def copy:List Op:=[.add 4201 4226 4207]
def piece(j:Fin 6):Program:=(setup j).map Op.code ++
 S.program.map (relocate 3 41)++copy.map Op.code
def program:Program:=boot.map Op.code++
 (List.finRange 6).flatMap (fun j=>(piece j).map (relocate (phaseBase j.val) 258))++[.halt]
lemma boot_length:boot.length=6:=rfl
lemma setup_length(j:Fin 6):(setup j).length=3:=rfl
lemma copy_length:copy.length=1:=rfl
lemma piece_length(j:Fin 6):(piece j).length=42:=by
 simp only [piece,List.length_append,List.length_map,setup_length,
  UniformLocalReplaySlotMachine.program_length,copy_length]
lemma program_length:program.length=259:=by
 simp only [program,List.length_append,List.length_map,boot_length,List.length_flatMap]
 have h:(List.map (fun j:Fin 6=>((piece j).map (relocate (phaseBase j.val) 258)).length) (List.finRange 6)).sum=252:=by
  simp [piece_length]
 exact congrArg (fun j=>6+j+1) h
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<6 at hi;interval_cases i <;>rfl
lemma setup_code(j:Fin 6):BlockAt (setup j) program (phaseBase j.val):=by
 intro i hi;change i<3 at hi;fin_cases j <;>interval_cases i <;>rfl
lemma phase_code(j:Fin 6):CodeAt S.program program (phaseBase j.val+3) (phaseBase j.val+41):=by
 intro i hi;change i<38 at hi;fin_cases j <;>interval_cases i <;>rfl
lemma copy_code(j:Fin 6):BlockAt copy program (phaseBase j.val+41):=by
 intro i hi;change i<1 at hi;interval_cases i
 fin_cases j <;>rfl
lemma halt_at:program[258]?=some .halt:=by
 have middle:((List.finRange 6).flatMap (fun j=>(piece j).map (relocate (phaseBase j.val) 258))).length=252:=by
  simp [List.length_flatMap,piece_length]
 rw [program,List.getElem?_append_right (by rw [List.length_append,List.length_map,boot_length,middle])]
 simp only [List.length_append,List.length_map,boot_length,middle];rfl

def levels(H:ℕ)(j:Fin 6):ℕ:=UniformLocalReplaySlotMachine.levelCount H (flags j).broadcast
def phasePrefix(H:ℕ):ℕ→ℕ
 | 0=>0
 | j+1=>phasePrefix H j+(if h:j<6 then levels H ⟨j,h⟩ else 0)
lemma prefix_next(H:ℕ)(j:Fin 6):phasePrefix H (j.val+1)=phasePrefix H j.val+levels H j:=by
 simp only [phasePrefix,show j.val<6 from j.isLt,dite_eq_left]
lemma prefix_mono(H:ℕ){i j:ℕ}(h:i≤j):phasePrefix H i≤phasePrefix H j:=by
 induction h with
 | refl=>rfl
 | step h ih=>rw [phasePrefix];omega
lemma prefix_total(H:ℕ):phasePrefix H 6=4*(H+1)+2:=by
 simp [phasePrefix,levels,flags,UniformLocalReplaySlotMachine.levelCount];ring

structure Cursor(K A j:ℕ)(s:State):Prop where
 exponent:s.natReg 4205=K
 original:s.natReg 4206=A
 zero:s.natReg 4207=0
 height:s.natReg 4200=8*K+6
 base:s.natReg 4201=A+55*phasePrefix (8*K+6) j

def Generated(K A k:ℕ)(s:State):Prop:=∀j:Fin 6,j.val<k→
 S.Done (8*K+6) (A+55*phasePrefix (8*K+6) j.val) (flags j).broadcast (flags j).enabled (flags j).inverse
 (11*levels (8*K+6) j) s

def Outside(A K:ℕ)(s u:State):Prop:=UniformLocalReplaySlotMachine.Outside A (11*phasePrefix (8*K+6) 6) s u

lemma Cursor.withPC {K A j:ℕ}{s:State}(h:Cursor K A j s)(pc:ℕ):Cursor K A j (setPC s pc):=
 ⟨h.exponent,h.original,h.zero,h.height,h.base⟩
lemma Generated.withPC{K A k:ℕ}{s:State}(h:Generated K A k s)(pc:ℕ):Generated K A k (setPC s pc):=
 fun j hj=>(h j hj).withPC pc
lemma setup_header{K A:ℕ}(j:Fin 6)(s:State)(h:Cursor K A j.val s):
 S.Header (8*K+6) (A+55*phasePrefix (8*K+6) j.val) (flags j).broadcast (flags j).enabled (flags j).inverse
 (applyBlock (setup j) s):=by
 constructor
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.height
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.base
 · simp [setup,applyBlock,Op.apply,writeNat,next]
 · simp [setup,applyBlock,Op.apply,writeNat,next]
 · simp [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_heap(j:Fin 6)(s:State):(applyBlock (setup j) s).natHeap=s.natHeap:=by
 simp [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_keeps(j:Fin 6)(s:State)(q:ℕ)(hq:q≠4202∧q≠4203∧q≠4204):
 (applyBlock (setup j) s).natReg q=s.natReg q:=by
 simp [setup,applyBlock,Op.apply,writeNat,next,hq.1,hq.2.1,hq.2.2]
lemma setup_safe(j:Fin 6)(s:State)(B:ℕ)(hB:259≤B):readable (setup j) s∧peak (setup j) s≤B:=by
 constructor
 · simp [setup,readable,Op.readable]
 · fin_cases j <;>simp [setup,flags,UniformLocalReplaySlotMachine.bit,peak,Op.peak] <;>omega

lemma Generated.transport {K A k:ℕ}{s u:State}(h:Generated K A k s)
 (heap:∀q,q<A+55*phasePrefix (8*K+6) k→u.natHeap q=s.natHeap q):Generated K A k u:=by
 intro j hj d c prior f
 have stop:=prefix_mono (8*K+6) (show j.val+1≤k by omega)
 rw [prefix_next] at stop
 have hd:=d.isLt;have hc:=c.isLt;have hf:=f.isLt
 rw [heap _ (by change d.val<levels (8*K+6) j at hd;omega)]
 exact h j hj d c prior f

lemma phase_execution (n K A B:ℕ)(j:Fin 6)(x:Fin n→ℂ)(s:State)
 (h:Cursor K A j.val s)(hp:s.pc=phaseBase j.val)(hs:WordBound B s)
 (hB:259≤B)(hH:8*K+7≤B)(hA:A+55*phasePrefix (8*K+6) 6≤B)(old:Generated K A j.val s):
 ∃u,BoundedRuns program n x B s (247*levels (8*K+6) j+17) u∧u.pc=phaseBase (j.val+1)∧
 Cursor K A (j.val+1) u∧Generated K A (j.val+1) u∧Outside A K s u:=by
 have safe:=setup_safe j s B hB
 have first:=block_runs (setup j) program (phaseBase j.val) n B x s (setup_code j) hp hs
   (by rw [setup_length];have hj:=j.isLt;unfold phaseBase;omega) safe.1 safe.2
 let a:=applyBlock (setup j) s
 have ap:a.pc=phaseBase j.val+3:=by rw [applyBlock_pc,hp,setup_length]
 let entry:=setPC a 0
 have header:=setup_header j s h
 have bounds:WordBound B entry:=changePC_bound B a 0 first.final_bound (by omega)
 have sum:=prefix_mono (8*K+6) (show j.val+1≤6 by have hj:=j.isLt;omega)
 rw [prefix_next] at sum
 have envelope:A+55*phasePrefix (8*K+6) j.val+5*11*levels (8*K+6) j≤B:=by omega
 obtain ⟨v,run,vp,done,address,outside⟩:=UniformLocalReplaySlotMachine.execution n (8*K+6)
   (A+55*phasePrefix (8*K+6) j.val) B (flags j).broadcast (flags j).enabled (flags j).inverse x entry
   ⟨header.height,header.base,header.broadcast,header.enabled,header.inverse⟩ rfl bounds (by omega) (by omega) envelope
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed (phase_code j)
   (by rw [UniformLocalReplaySlotMachine.program_length];have hj:=j.isLt;unfold phaseBase;omega)
   (by have hj:=j.isLt;unfold phaseBase;omega) run
 have entrance:placed (phaseBase j.val+3) entry=a:=by
  dsimp only [placed,entry,setPC]
  rw [←ap]
 rw [entrance] at placedRun
 let v':=setPC v (phaseBase j.val+41)
 have copied:=block_runs copy program (phaseBase j.val+41) n B x v' (copy_code j) rfl placedRun.final_bound
   (by rw [copy_length];have hj:=j.isLt;unfold phaseBase;omega)
   (by simp [copy,readable,Op.readable]) (by
    have keep:=UniformLocalReplaySlotMachine.execution_natFrame run 4207 (by omega)
    have ze:entry.natReg 4207=0:=(setup_keeps j s 4207 (by omega)).trans h.zero
    simpa [copy,peak,Op.peak,v',setPC,address,keep,ze,levels] using envelope)
 let u:=applyBlock copy v'
 have retained(q:ℕ)(hq:q<4210)(hne:q≠4202∧q≠4203∧q≠4204):v.natReg q=s.natReg q:=by
  exact (UniformLocalReplaySlotMachine.execution_natFrame run q (Or.inl hq)).trans (setup_keeps j s q hne)
 have current:Cursor K A (j.val+1) u:=by
  constructor
  · simpa [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC] using (retained 4205 (by omega) (by omega)).trans h.exponent
  · simpa [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC] using (retained 4206 (by omega) (by omega)).trans h.original
  · simpa [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC] using (retained 4207 (by omega) (by omega)).trans h.zero
  · simpa [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC] using (retained 4200 (by omega) (by omega)).trans h.height
  · have keep:=retained 4207 (by omega) (by omega)
    simp [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC,address,keep,h.zero,prefix_next,levels];ring
 have past:Generated K A j.val u:=old.transport (by
  intro q hq
  simpa only [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC,entry,a,setup_heap] using outside q (Or.inl hq))
 refine ⟨u,?_,?_,current,?_,?_⟩
 · convert first.trans (placedRun.trans copied) using 1
   simp only [setup_length,copy_length,levels];omega
 · rw [applyBlock_pc,copy_length];simp only [v',setPC,phaseBase];omega
 · intro k hk
   by_cases same:k=j
   · subst k
     simpa only [S.Done,UniformLocalReplaySlotMachine.Done,u,copy,applyBlock,Op.apply,writeNat,next,v',setPC,levels] using done
   · exact past k (by have kj:=k.isLt;have jj:=j.isLt;have ne: k.val≠j.val:=fun eq=>same (Fin.ext eq);omega)
 · intro q hq
   have lo:phasePrefix (8*K+6) 0≤phasePrefix (8*K+6) j.val:=prefix_mono _ (by omega)
   have hi:=sum
   have miss:q<A+55*phasePrefix (8*K+6) j.val∨A+55*phasePrefix (8*K+6) j.val+5*(11*levels (8*K+6) j)≤q:=by
     rcases hq with hq|hq <;>omega
   simpa only [u,copy,applyBlock,Op.apply,writeNat,next,v',setPC,entry,a,setup_heap] using outside q miss

def phaseCost(H j:ℕ):ℕ:=if h:j<6 then 247*levels H ⟨j,h⟩+17 else 0

def rangeCost(H:ℕ):ℕ→ℕ→ℕ
 | _,0=>0
 | j,k+1=>phaseCost H j+rangeCost H (j+1) k
lemma rangeCost_total(H:ℕ):rangeCost H 0 6=247*phasePrefix H 6+102:=by
 simp [rangeCost,phaseCost,phasePrefix,levels,flags,UniformLocalReplaySlotMachine.levelCount];ring

lemma phases (n K A B j fuel:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Cursor K A j s)(hp:s.pc=phaseBase j)(hs:WordBound B s)(within:j+fuel≤6)
 (hB:259≤B)(hH:8*K+7≤B)(hA:A+55*phasePrefix (8*K+6) 6≤B)(old:Generated K A j s):
 ∃u,BoundedRuns program n x B s (rangeCost (8*K+6) j fuel) u∧u.pc=phaseBase (j+fuel)∧
 Cursor K A (j+fuel) u∧Generated K A (j+fuel) u∧Outside A K s u:=by
 induction fuel generalizing j s with
 | zero=>exact ⟨s,.refl hs,by simpa using hp,by simpa using h,by simpa using old,fun q hq=>rfl⟩
 | succ fuel ih=>
   have hj:j<6:=by omega
   obtain ⟨a,first,ap,cursor,done,outside⟩:=phase_execution n K A B ⟨j,hj⟩ x s h hp hs hB hH hA old
   obtain ⟨u,tail,up,final,table,frame⟩:=ih (j+1) a cursor ap first.final_bound (by omega) done
   refine ⟨u,?_,?_,?_,?_,?_⟩
   · simpa only [rangeCost,phaseCost,hj,dite_eq_left] using first.trans tail
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using up
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
   · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using table
   · exact UniformLocalReplaySlotMachine.Outside.trans outside frame

lemma boot_cursor(K A:ℕ)(s:State)(hk:s.natReg 4205=K)(ha:s.natReg 4206=A):
 Cursor K A 0 (applyBlock boot s):=by
 constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,hk,ha,phasePrefix]
 all_goals exact Nat.mul_comm _ _
lemma boot_safe(K A B:ℕ)(s:State)(hk:s.natReg 4205=K)(ha:s.natReg 4206=A)
 (hs:WordBound B s)(hB:259≤B)(hH:8*K+7≤B):readable boot s∧peak boot s≤B:=by
 have bound:=hs.2.1 4206;rw [ha] at bound
 constructor
 · simp [boot,readable,Op.readable]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,hk,ha];omega

/-- A single fixed literal prints every complete six-phase slot, computing the
height from the actual exponent register. No phase list/table is assumed. -/
theorem execution(n K A B:ℕ)(x:Fin n→ℂ)(s:State)
 (hk:s.natReg 4205=K)(ha:s.natReg 4206=A)(hp:s.pc=0)(hs:WordBound B s)
 (hB:259≤B)(hH:8*K+7≤B)(hA:A+55*phasePrefix (8*K+6) 6≤B):
 ∃u,BoundedExecution program n x B s (247*phasePrefix (8*K+6) 6+109) u∧u.pc=258∧
 Generated K A 6 u∧Cursor K A 6 u∧Outside A K s u:=by
 have safe:=boot_safe K A B s hk ha hs hB hH
 have first:=block_runs boot program 0 n B x s boot_code hp hs (by rw [boot_length];omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=phaseBase 0:=by rw [applyBlock_pc,hp,boot_length];rfl
 obtain ⟨u,run,up,final,table,frame⟩:=phases n K A B 0 6 x a (boot_cursor K A s hk ha) ap first.final_bound
   (by omega) hB hH hA (by intro j hj;omega)
 have halt:BoundedExecution program n x B u 1 u:=.halt run.final_bound (by
  simp [UniformMachine.step,up,phaseBase,halt_at])
 refine ⟨u,?_,by simpa only [phaseBase] using up,table,final,?_⟩
 · convert first.executes (run.executes halt) using 1
   simp only [boot_length,rangeCost_total];omega
 · intro q hq
   exact (frame q hq).trans (by simp [a,boot,applyBlock,Op.apply,writeNat,next])

lemma natOnly_relocate(base ret:ℕ)(ins:Instruction)
 (h:UniformLocalRectangleDescriptors.NatOnly ins):UniformLocalRectangleDescriptors.NatOnly (relocate base ret ins):=by
 cases ins <;>simp_all [UniformLocalRectangleDescriptors.NatOnly,relocate]
lemma boot_natOnly:∀ins∈boot.map Op.code,UniformLocalRectangleDescriptors.NatOnly ins:=by
 simp [boot,Op.code,UniformLocalRectangleDescriptors.NatOnly]
lemma setup_natOnly(j:Fin 6):∀ins∈(setup j).map Op.code,UniformLocalRectangleDescriptors.NatOnly ins:=by
 simp [setup,Op.code,UniformLocalRectangleDescriptors.NatOnly]
lemma copy_natOnly:∀ins∈copy.map Op.code,UniformLocalRectangleDescriptors.NatOnly ins:=by
 simp [copy,Op.code,UniformLocalRectangleDescriptors.NatOnly]
lemma piece_natOnly(j:Fin 6):∀ins∈piece j,UniformLocalRectangleDescriptors.NatOnly ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · rcases List.mem_append.mp hi with hi|hi
   · exact setup_natOnly j ins hi
   · obtain ⟨original,hp,rfl⟩:=List.mem_map.mp hi
     exact natOnly_relocate 3 41 original (UniformLocalReplaySlotMachine.program_natOnly original hp)
 · exact copy_natOnly ins hi
lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · rcases List.mem_append.mp hi with hi|hi
   · exact boot_natOnly ins hi
   · obtain ⟨j,hj,hi⟩:=List.mem_flatMap.mp hi
     obtain ⟨original,hp,rfl⟩:=List.mem_map.mp hi
     exact natOnly_relocate _ _ original (piece_natOnly j original hp)
 · simp only [List.mem_singleton] at hi
   subst ins
   trivial
lemma execution_scalarFrame{n B t:ℕ}{x:Fin n→ℂ}{s u:State}(run:BoundedExecution program n x B s t u):
 UniformLocalRectangleDescriptors.ScalarFrame s u:=
 UniformLocalRectangleDescriptors.natOnly_execution program_natOnly run.executes

end ExactFourierCircuits.UniformLocalReplayAssembly
