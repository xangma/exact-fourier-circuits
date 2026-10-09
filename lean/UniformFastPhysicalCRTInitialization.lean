import UniformFastPhysicalCRTMachine
import UniformPhysicalCRTArithmetic

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT index enumeration after (5.5), PDF p.22
(`eq:crt-fourier`), and prefix bound (4.1), PDF p.18.

Mixed-radix carry enumeration is an implementation refinement of the paper's
linear traversal. Initialization, carry visits, frames and instruction counts
have no one-to-one paper lemma; the final caller charges this actual producer.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTInitialization
open UniformMachine UniformNatBlockMachine UniformFastPhysicalCRTMachine UniformCRTTraversalCycle
open scoped BigOperators
noncomputable section

def Work {a:ℕ} (r:Fin a→ℕ) (L:Addresses) (ds:Fin a→ℕ) (s:State):Prop:=
 ∀i,s.natHeap (L.work+2*i.val)=some (ds i) ∧
 s.natHeap (L.work+2*i.val+1)=some (place r i.val)
def Outside (a:ℕ) (L:Addresses) (heap:ℕ→Option ℕ) (s:State):Prop:=
 ∀q,q<L.work∨L.work+2*a≤q→s.natHeap q=heap q
structure Data {a:ℕ}(r:Fin a→ℕ) (L:Addresses) (j:ℕ) (s:State):Prop where
 index:s.natReg 7805=j
 weight:s.natReg 7814=place r j
 physical:s.natReg 7803=0
 normal:s.natReg 7806=0
 cells:∀i:Fin a,i.val<j→s.natHeap (L.work+2*i.val)=some 0∧
  s.natHeap (L.work+2*i.val+1)=some (place r i.val)
def entered (s:State):State:={s with pc:=8}
def rowEnd (s:State):State:={applyBlock initBody (entered s) with pc:=7}

lemma body_heap{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(j:Fin a)(s:State)
 (args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s):
 (rowEnd s).natHeap=Function.update
  (Function.update s.natHeap (L.work+2*j.val) (some 0))
  (L.work+2*j.val+1) (some (place r j.val)):=by
 simp [rowEnd,entered,initBody,applyBlock,Op.apply,writeNat,next,evalNat,
  args.work,c.two,c.one,c.zero,d.index,d.weight]
lemma body_frame (s:State):Frame s (rowEnd s):=by
 constructor <;>try rfl
 intro q hq
 simp (disch:=omega) [rowEnd,entered,initBody,applyBlock,Op.apply,writeNat,next]
lemma body_constants (s:State)(c:Constants s):Constants (rowEnd s):=by
 constructor <;>simp [rowEnd,entered,initBody,applyBlock,Op.apply,writeNat,next,
  c.zero,c.one,c.two]

lemma body_values{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(j:Fin a)(s:State)
 (args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s)
 (read:s.natHeap (L.directory+2*j.val+1)=some (r j))
 (before:L.directory+2*a≤L.work):
 (rowEnd s).natReg 7805=j.val+1∧(rowEnd s).natReg 7814=place r (j.val+1)∧
 (rowEnd s).natReg 7803=0∧(rowEnd s).natReg 7806=0:=by
 have e0:L.directory+2*j.val+1≠L.work+2*j.val:=by omega
 have e1:L.directory+2*j.val+1≠L.work+2*j.val+1:=by omega
 rw [place_succ]
 simp [rowEnd,entered,initBody,applyBlock,Op.apply,writeNat,next,evalNat,
  args.directory,args.work,c.two,c.one,c.zero,d.index,d.weight,d.physical,d.normal]
 rw [Function.update_of_ne e1,Function.update_of_ne e0,read]
 simp

lemma body_data{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(j:Fin a)(s:State)
 (args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s)
 (read:s.natHeap (L.directory+2*j.val+1)=some (r j))
 (before:L.directory+2*a≤L.work):Data r L (j.val+1) (rowEnd s):=by
 have v:=body_values r L j s args c d read before
 refine ⟨v.1,v.2.1,v.2.2.1,v.2.2.2,?_⟩
 intro i hi
 rw [body_heap r L j s args c d]
 by_cases same:i=j
 · subst i
   constructor <;>simp
 · have ne:i.val≠j.val:=by intro e;exact same (Fin.ext e)
   have old:=d.cells i (by omega)
   constructor
   · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
     exact old.1
   · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
     exact old.2

lemma body_outside{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(j:Fin a)(s:State)
 (args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s):
 Outside a L s.natHeap (rowEnd s):=by
 intro q hq
 rw [body_heap r L j s args c d,Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

lemma body_safe{a B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)(j:Fin a)(s:State)
 (args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s)
 (read:s.natHeap (L.directory+2*j.val+1)=some (r j))
 (before:L.directory+2*a≤L.work)(wf:L.work+2*a≤B)(volume:(∏i,r i)≤B):
 readable initBody (entered s)∧peak initBody (entered s)≤B:=by
 have e0:L.directory+2*j.val+1≠L.work+2*j.val:=by omega
 have e1:L.directory+2*j.val+1≠L.work+2*j.val+1:=by omega
 have weight:=UniformPhysicalCRTArithmetic.place_le r hr j.val
 have weightNext:=UniformPhysicalCRTArithmetic.place_le r hr (j.val+1)
 rw [place_succ] at weightNext
 have pos:=place_pos r hr j.val
 have radix:r j≤∏i,r i:=by nlinarith
 simp [readable,peak,initBody,entered,Op.readable,Op.peak,Op.apply,writeNat,next,evalNat,
  args.directory,args.work,c.two,c.one,c.zero,d.index,d.weight]
 rw [Function.update_of_ne e1,Function.update_of_ne e0,read]
 simp only [Option.getD_some,Option.isSome_some]
 constructor
 · trivial
 · omega

lemma row_execution{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)(j:Fin a)
 (x:Fin n→ℂ)(s:State)(args:Args a (∏i,r i) L s)(c:Constants s)(d:Data r L j.val s)
 (read:s.natHeap (L.directory+2*j.val+1)=some (r j))
 (before:L.directory+2*a≤L.work)(wf:L.work+2*a≤B)(volume:(∏i,r i)≤B)
 (code:53≤B)(pc:s.pc=7)(wb:WordBound B s):
 BoundedRuns program n x B s 12 (rowEnd s):=by
 have he:WordBound B (entered s):=changePC_bound B s 8 wb (by omega)
 have branch:BoundedRuns program n x B s 1 (entered s):=.next wb
  (by simp [step,pc,init_test,d.index,args.axes,j.isLt,entered]) (.refl he)
 have safe:=body_safe r hr L j s args c d read before wf volume
 have body:=block_runs initBody program 8 n B x (entered s) init_code rfl he
  (by change 8+10≤B;omega) safe.1 safe.2
 have bp:(applyBlock initBody (entered s)).pc=18:=by rw[block_pc];rfl
 have jump:BoundedRuns program n x B (applyBlock initBody (entered s)) 1 (rowEnd s):=
  .next body.final_bound (by simp [step,bp,init_jump,rowEnd])
   (.refl (changePC_bound B _ 7 body.final_bound (by omega)))
 exact (branch.trans body).trans jump

lemma init_loop{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)
 (x:Fin n→ℂ)(heap:ℕ→Option ℕ)(reads:∀i:Fin a,heap (L.directory+2*i.val+1)=some (r i))
 (before:L.directory+2*a≤L.work)(wf:L.work+2*a≤B)(volume:(∏i,r i)≤B)(code:53≤B)
 (j fuel:ℕ)(s:State)(eq:j+fuel=a)(args:Args a (∏i,r i) L s)(c:Constants s)
 (d:Data r L j s)(outside:Outside a L heap s)(pc:s.pc=7)(wb:WordBound B s):∃u,
 BoundedRuns program n x B s (12*fuel+1) u∧u.pc=19∧Args a (∏i,r i) L u∧Constants u∧
 Frame s u∧Outside a L heap u∧u.natReg 7803=0∧u.natReg 7806=0∧Work r L (fun _=>0) u:=by
 induction fuel generalizing j s with
 | zero=>
  have ja:j=a:=by omega
  let u:State:={s with pc:=19}
  have run:BoundedRuns program n x B s 1 u:=.next wb
   (by simp [step,pc,init_test,d.index,args.axes,ja,u])
   (.refl (changePC_bound B s 19 wb (by omega)))
  refine ⟨u,?_,rfl,args_pc args 19,constants_pc c 19,Frame.pc (.refl s) 19,
   outside,d.physical,d.normal,?_⟩
  · simpa using run
  · intro i;exact d.cells i (by omega)
 | succ fuel ih=>
  have ja:j<a:=by omega
  let i:Fin a:=⟨j,ja⟩
  have read:s.natHeap (L.directory+2*j+1)=some (r i):=by
   rw [outside _ (Or.inl (by omega))];exact reads i
  have run:=row_execution r hr L i x s args c d read before wf volume code pc wb
  have frame:=body_frame s
  have nextArgs:=frame.args args
  have nextConstants:=body_constants s c
  have nextData:=body_data r L i s args c d read before
  have nextOutside:Outside a L heap (rowEnd s):=by
   intro q hq;rw [body_outside r L i s args c d q hq];exact outside q hq
  obtain ⟨u,tail,up,ua,uc,uf,uh,ui,un,uw⟩:=ih (j+1) (rowEnd s) (by omega)
   nextArgs nextConstants nextData nextOutside rfl run.final_bound
  refine ⟨u,?_,up,ua,uc,frame.trans uf,uh,ui,un,uw⟩
  convert run.trans tail using 1
  omega

lemma boot_frame (s:State):Frame s (applyBlock boot s):=by
 constructor <;>try rfl
 intro q hq
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_constants (s:State):Constants (applyBlock boot s):=by
 constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_data{a:ℕ}(r:Fin a→ℕ)(L:Addresses)(s:State):Data r L 0 (applyBlock boot s):=by
 constructor
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next,place_zero]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · intro i hi;omega

/-- The fixed initializer charges seven constants and one actual scan of each
axis, and derives every digit/weight cell before the first emission. -/
theorem execution{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)
 (x:Fin n→ℂ)(s:State)(args:Args a (∏i,r i) L s)
 (reads:∀i:Fin a,s.natHeap (L.directory+2*i.val+1)=some (r i))
 (before:L.directory+2*a≤L.work)(wf:L.work+2*a≤B)(volume:(∏i,r i)≤B)
 (code:53≤B)(pc:s.pc=0)(wb:WordBound B s):∃u,
 BoundedRuns program n x B s (12*a+8) u∧u.pc=19∧Args a (∏i,r i) L u∧Constants u∧
 Frame s u∧Outside a L s.natHeap u∧u.natReg 7803=0∧u.natReg 7806=0∧Work r L (fun _=>0) u:=by
 have bootRun:=block_runs boot program 0 n B x s boot_code pc wb (by change 0+7≤B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let b:=applyBlock boot s
 have bp:b.pc=7:=by rw[block_pc,pc];rfl
 obtain ⟨u,run,up,ua,uc,uf,uh,ui,un,uw⟩:=init_loop r hr L x s.natHeap reads before wf volume code
  0 a b (by omega) ((boot_frame s).args args) (boot_constants s) (boot_data r L s)
  (fun _ _=>rfl) bp bootRun.final_bound
 refine ⟨u,?_,up,ua,uc,(boot_frame s).trans uf,uh,ui,un,uw⟩
 convert bootRun.trans run using 1
 change 12*a+8=7+(12*a+1)
 omega
end
end ExactFourierCircuits.UniformFastPhysicalCRTInitialization
