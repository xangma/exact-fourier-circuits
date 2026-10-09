import UniformScalarCopyMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformScalarZeroFillMachine
open UniformMachine
/-- The actual product W*V and every zero store are charged. -/
def program : Program := [
 .natLiteral 6310 0,.natLiteral 6311 1,.natBinary .mul 6312 6300 6301,
 .scalarLiteral 94 0,.branchLT 6310 6312 5 9,
 .natBinary .add 6313 6302 6310,.storeScalar 6313 94,
 .natBinary .add 6310 6310 6311,.jump 4,.halt]
lemma program_length : program.length=10 := rfl
noncomputable section
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j<6310∨6314≤j→u.natReg j=s.natReg j
 scalarReg:∀j,j≠94→u.scalarReg j=s.scalarReg j
lemma Frame.trans {s t u:State}(a:Frame s t)(b:Frame t u):Frame s u:=
 ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,
  fun j h=>(b.natReg j h).trans (a.natReg j h),fun j h=>(b.scalarReg j h).trans (a.scalarReg j h)⟩
lemma Frame.withPC {s u:State}(h:Frame s u)(pc:ℕ):Frame s {u with pc:=pc}:=by
 cases h;constructor <;> assumption
structure Invariant (W V S k:ℕ)(heap:ℕ→Option Scalar)(s:State):Prop where
 roles:s.natReg 6300=W
 width:s.natReg 6301=V
 base:s.natReg 6302=S
 total:s.natReg 6312=W*V
 index:s.natReg 6310=k
 one:s.natReg 6311=1
 zero:s.scalarReg 94=Scalar.zero
 filled:∀j,j<k→s.scalarHeap (S+j)=some Scalar.zero
 outside:∀j,j<S∨S+W*V≤j→s.scalarHeap j=heap j

def address(s:State):State:=writeNat {s with pc:=5} 6313 (s.natReg 6302+s.natReg 6310)
def stored(s:State):State:={next (address s) with
 scalarHeap:=Function.update s.scalarHeap (s.natReg 6302+s.natReg 6310) (some (s.scalarReg 94))}
def advanced(s:State):State:=writeNat (stored s) 6310 (s.natReg 6310+1)
def iterationEnd(s:State):State:={advanced s with pc:=4}
lemma iteration_heap(s:State):(iterationEnd s).scalarHeap=Function.update s.scalarHeap
 (s.natReg 6302+s.natReg 6310) (some (s.scalarReg 94)):=rfl
lemma iteration_frame(s:State):Frame s (iterationEnd s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   simp [iterationEnd,advanced,stored,address,writeNat,next,show j≠6310 by omega,show j≠6313 by omega]
 · intro j _;rfl
lemma iteration_invariant {W V S k:ℕ}{heap:ℕ→Option Scalar}{s:State}
 (h:Invariant W V S k heap s)(hk:k<W*V):Invariant W V S (k+1) heap (iterationEnd s):=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa [iterationEnd,advanced,stored,address,writeNat,next] using h.roles
 · simpa [iterationEnd,advanced,stored,address,writeNat,next] using h.width
 · simpa [iterationEnd,advanced,stored,address,writeNat,next] using h.base
 · simpa [iterationEnd,advanced,stored,address,writeNat,next] using h.total
 · simp [iterationEnd,advanced,stored,address,writeNat,next,h.index]
 · simpa [iterationEnd,advanced,stored,address,writeNat,next] using h.one
 · exact h.zero
 · intro j hj
   rw [iteration_heap,h.base,h.index,h.zero]
   by_cases eq:j=k
   · subst j;simp
   · rw [Function.update_of_ne (by omega)];exact h.filled j (by omega)
 · intro j hj
   rw [iteration_heap,h.base,h.index,Function.update_of_ne (by omega)]
   exact h.outside j hj

lemma iteration(n B W V S k:ℕ)(x:Fin n→ℂ)(heap:ℕ→Option Scalar)(s:State)
 (h:Invariant W V S k heap s)(hk:k<W*V)(extent:S+W*V≤B)(code:9≤B)
 (pc:s.pc=4)(bound:WordBound B s):∃u,BoundedRuns program n x B s 5 u∧
 Invariant W V S (k+1) heap u∧u.pc=4∧Frame s u:=by
 have h0:WordBound B {s with pc:=5}:=changePC_bound _ _ _ bound (by omega)
 have h1:WordBound B (address s):=writeNat_bound _ _ _ _ h0 (by change 5+1≤B;omega)
  (by rw[h.base,h.index];omega)
 have h2:WordBound B (stored s):=UniformScalarCopyMachine.store_bound B (address s) (s.natReg 6302+s.natReg 6310) (s.scalarReg 94) h1
  (by change 6+1≤B;omega) (by rw[h.base,h.index];omega)
 have h3:WordBound B (advanced s):=writeNat_bound _ _ _ _ h2 (by change 7+1≤B;omega)
  (by rw[h.index];omega)
 have h4:WordBound B (iterationEnd s):=changePC_bound _ _ _ h3 (by omega)
 have t0:step program n x s=.running {s with pc:=5}:=by simp[step,program,pc,h.index,h.total,hk]
 have t1:step program n x {s with pc:=5}=.running (address s):=by simp[step,program,address,evalNat]
 have t2:step program n x (address s)=.running (stored s):=by simp[step,program,stored,address,writeNat,next]
 have t3:step program n x (stored s)=.running (advanced s):=by
  simp[step,program,advanced,stored,address,writeNat,next,h.one,evalNat]
 have t4:step program n x (advanced s)=.running (iterationEnd s):=by
  simp[step,program,iterationEnd,advanced,stored,address,writeNat,next]
 exact ⟨iterationEnd s,.next bound t0 (.next h0 t1 (.next h1 t2 (.next h2 t3 (.next h3 t4 (.refl h4))))),
  iteration_invariant h hk,rfl,iteration_frame s⟩

lemma loop(n B W V S k fuel:ℕ)(x:Fin n→ℂ)(heap:ℕ→Option Scalar)(s:State)
 (h:Invariant W V S k heap s)(endIndex:k+fuel=W*V)(extent:S+W*V≤B)(code:9≤B)
 (pc:s.pc=4)(bound:WordBound B s):∃u,BoundedRuns program n x B s (5*fuel) u∧
 Invariant W V S (W*V) heap u∧u.pc=4∧Frame s u:=by
 induction fuel generalizing k s with
 | zero=>
   have eq:k=W*V:=by omega
   subst k;exact ⟨s,.refl bound,h,pc,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩⟩
 | succ fuel ih=>
   obtain ⟨t,run,ht,pt,ft⟩:=iteration n B W V S k x heap s h (by omega) extent code pc bound
   obtain ⟨u,more,hu,pu,fu⟩:=ih (k+1) t ht (by omega) pt run.final_bound
   refine ⟨u,?_,hu,pu,ft.trans fu⟩
   convert run.trans more using 1;omega

def initialized(s:State):State:=writeScalar (writeNat (writeNat (writeNat s 6310 0) 6311 1)
 6312 (s.natReg 6300*s.natReg 6301)) 94 Scalar.zero
lemma initialize_frame(s:State):Frame s (initialized s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj;simp[initialized,writeNat,writeScalar,next,show j≠6310 by omega,show j≠6311 by omega,show j≠6312 by omega]
 · intro j hj;simp[initialized,writeNat,writeScalar,next,hj]
lemma initialize_invariant(W V S:ℕ)(s:State)(hw:s.natReg 6300=W)(hv:s.natReg 6301=V)
 (hs:s.natReg 6302=S):Invariant W V S 0 s.scalarHeap (initialized s):=by
 constructor <;> simp[initialized,writeNat,writeScalar,next,hw,hv,hs]

/-- All dirty destination cells are replaced by a literal prepared zero. -/
theorem execution(n B W V S:ℕ)(x:Fin n→ℂ)(s:State)(pc:s.pc=0)
 (hw:s.natReg 6300=W)(hv:s.natReg 6301=V)(hs:s.natReg 6302=S)
 (extent:S+W*V≤B)(code:9≤B)(bound:WordBound B s):∃u,
 BoundedExecution program n x B s (5*(W*V)+6) u∧u.pc=9∧
 (∀j,j<W*V→u.scalarHeap (S+j)=some Scalar.zero)∧
 (∀j,j<S∨S+W*V≤j→u.scalarHeap j=s.scalarHeap j)∧Frame s u∧u.natReg 6310=W*V∧u.natReg 6311=1:=by
 let a:=writeNat s 6310 0
 let b:=writeNat a 6311 1
 let c:=writeNat b 6312 (W*V)
 have ha:WordBound B a:=writeNat_bound _ _ _ _ bound (by omega) (by omega)
 have hb:WordBound B b:=writeNat_bound _ _ _ _ ha (by change s.pc+2≤B;omega) (by omega)
 have hc:WordBound B c:=writeNat_bound _ _ _ _ hb (by change s.pc+3≤B;omega) (by omega)
 have hd:WordBound B (initialized s):=by
  have h:=writeScalar_bound B c 94 Scalar.zero hc (by change s.pc+4≤B;omega)
  simpa[initialized,c,b,a,hw,hv] using h
 have t0:step program n x s=.running a:=by simp[step,program,pc,a]
 have t1:step program n x a=.running b:=by simp[step,program,a,b,writeNat,next,pc]
 have t2:step program n x b=.running c:=by simp[step,program,a,b,c,writeNat,next,pc,evalNat,hw,hv]
 have t3:step program n x c=.running (initialized s):=by
  simp[step,program,initialized,a,b,c,writeNat,writeScalar,next,pc,hw,hv,Scalar.zero]
 have boot:BoundedRuns program n x B s 4 (initialized s):=
  .next bound t0 (.next ha t1 (.next hb t2 (.next hc t3 (.refl hd))))
 have pp:(initialized s).pc=4:=by simp[initialized,writeNat,writeScalar,next,pc]
 obtain ⟨u,run,hi,pu,fu⟩:=loop n B W V S 0 (W*V) x s.scalarHeap (initialized s)
  (initialize_invariant W V S s hw hv hs) (by omega) extent code pp hd
 let z:State:={u with pc:=9}
 have hz:WordBound B z:=changePC_bound _ _ _ run.final_bound code
 have halt:BoundedExecution program n x B z 1 z:=.halt hz (by simp[step,program,z])
 have stop:BoundedExecution program n x B u 2 z:=by
  refine .next run.final_bound ?_ halt
  simp[step,program,pu,hi.index,hi.total,z]
 refine ⟨z,?_,rfl,hi.filled,hi.outside,((initialize_frame s).trans fu).withPC 9,hi.index,hi.one⟩
 convert boot.executes (run.executes stop) using 1;omega
end
end ExactFourierCircuits.UniformScalarZeroFillMachine
