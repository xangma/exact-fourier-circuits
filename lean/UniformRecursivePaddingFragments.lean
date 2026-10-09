import UniformRecursivePaddingFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingFragments
open UniformMachine UniformNatBlockMachine UniformRecursivePaddingFrames
namespace C
export UniformRecursivePaddingControl (initOps testOps nextOps finishOps)
end C
namespace R
export UniformRecursiveParentReturn (code_bound start_bound)
end R
noncomputable section

lemma init_bits_generic (main:Program)(start ret:ℕ)
 (link:BlockAt C.initOps main start)(jump:main[start+10]?=some (.jump ret))
 (n B F saved role count:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=start)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=role)(c:s.natReg 2855=count)
 (low:6≤F)(bound:WordBound B s)(extent:start+11≤B)(retBound:ret≤B)(endBound:role+count≤B)
 (run:BoundedRuns main n x B s 11 u):u.natReg 5300=s.natReg 5300:=by
 have wb:F≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have sb:saved≤B:=by have h:=bound.2.1 2865;rwa[sp] at h
 have cs:=UniformRecursivePaddingControl.coordinates F low
 have safe:readable C.initOps s∧peak C.initOps s≤B:=by
  simp [C.initOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,sp,d,c,cs.1,sb,endBound]
  omega
 exact block_jump_register_len main (start) (ret) n B 5300 10 C.initOps UniformRecursivePaddingControl.init_length x s u
  link jump pc bound
  extent retBound safe
  (by intro o ho; simp only [C.initOps,List.mem_cons,List.mem_nil_iff,or_false] at ho;rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>simp[keeps]) run

lemma test_bits_generic (main:Program)(start yes no:ℕ)
 (link:BlockAt C.testOps main start)(branch:main[start+5]?=some (.branchLT 4175 4176 yes no))
 (n B F role last:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=start)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (current:s.natHeap (F-4)=some role)(endpoint:s.natHeap (F-3)=some last)(low:6≤F)
 (bound:WordBound B s)(extent:start+6≤B)(yb:yes≤B)(nb:no≤B)
 (run:BoundedRuns main n x B s 6 u):u.natReg 5300=s.natReg 5300:=by
 have wb:F≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have rb:role≤B:=(bound.2.2.1 _ _ current).2
 have lb:last≤B:=(bound.2.2.1 _ _ endpoint).2
 have cs:F-4+1=F-3:=by omega
 have safe:readable C.testOps s∧peak C.testOps s≤B:=by
  simp [C.testOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,current,endpoint,cs,rb,lb]
  omega
 exact block_branch_register_len main (start) (yes) (no)
  4175 4176 n B 5300 5 C.testOps UniformRecursivePaddingControl.test_length x s u link branch
  pc bound extent yb
  nb safe
  (by intro o ho;simp only [C.testOps,List.mem_cons,List.mem_nil_iff,or_false] at ho;rcases ho with rfl|rfl|rfl|rfl|rfl <;>simp[keeps]) run

lemma next_bits_generic (main:Program)(start ret:ℕ)
 (link:BlockAt C.nextOps main start)(jump:main[start+5]?=some (.jump ret))
 (n B F role:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=start)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (current:s.natHeap (F-4)=some role)(_low:6≤F)(bound:WordBound B s)(extent:start+6≤B)(retBound:ret≤B)(increment:role+1≤B)
 (run:BoundedRuns main n x B s 6 u):u.natReg 5300=s.natReg 5300:=by
 have wb:F≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have safe:readable C.nextOps s∧peak C.nextOps s≤B:=by
  simp[C.nextOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,one,current]
  omega
 exact block_jump_register_len main (start) (ret) n B 5300 5 C.nextOps UniformRecursivePaddingControl.next_length x s u
  link jump pc bound
  extent retBound safe
  (by intro o ho;simp only [C.nextOps,List.mem_cons,List.mem_nil_iff,or_false] at ho;rcases ho with rfl|rfl|rfl|rfl|rfl <;>simp[keeps]) run

lemma finish_bits_generic (main:Program)(start ret:ℕ)
 (link:BlockAt C.finishOps main start)(jump:main[start+3]?=some (.jump ret))
 (n B F saved:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=start)(w:s.natReg 4123=F)
 (stored:s.natHeap (F-5)=some saved)(low:6≤F)(bound:WordBound B s)(extent:start+4≤B)(retBound:ret≤B)
 (run:BoundedRuns main n x B s 4 u):u.natReg 5300=s.natReg 5300:=by
 have wb:F≤B:=by have h:=bound.2.1 4123;rwa[w] at h
 have sb:saved≤B:=(bound.2.2.1 _ _ stored).2
 have safe:readable C.finishOps s∧peak C.finishOps s≤B:=by
  simp[C.finishOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,stored,sb]
  omega
 exact block_jump_register_len main (start) (ret) n B 5300 3 C.finishOps UniformRecursivePaddingControl.finish_length x s u
  link jump pc bound
  extent retBound safe
  (by intro o ho;simp only [C.finishOps,List.mem_cons,List.mem_nil_iff,or_false] at ho;rcases ho with rfl|rfl|rfl <;>simp[keeps]) run

lemma residual_init_cursor_generic (main:Program)(start ret:ℕ)
 (link:BlockAt UniformRecursiveResidualControl.initOps main start)(jump:main[start+4]?=some (.jump ret))
 (n B _F dimension recordEnd inverse:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=start)(one:s.natReg 4153=1)(dim:s.natReg 2857=dimension)
 (endHeader:s.natReg 2865=recordEnd)(iv:s.natReg 2856=inverse)(bound:WordBound B s)(extent:start+5≤B)(retBound:ret≤B)
 (run:BoundedRuns main n x B s 5 u):u.natReg 2850=s.natReg 2850:=by
 have db:dimension≤B:=by have h:=bound.2.1 2857;rwa[dim] at h
 have eb:recordEnd≤B:=by have h:=bound.2.1 2865;rwa[endHeader] at h
 have ib:inverse≤B:=by have h:=bound.2.1 2856;rwa[iv] at h
 have safe:readable UniformRecursiveResidualControl.initOps s∧peak UniformRecursiveResidualControl.initOps s≤B:=by
  simp [UniformRecursiveResidualControl.initOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,dim,endHeader,iv,db,eb,ib]
 exact block_jump_register_len main (start) (ret) n B 2850 4
  UniformRecursiveResidualControl.initOps rfl x s u link
  jump pc bound extent
  retBound safe
  (by intro o ho;simp only [UniformRecursiveResidualControl.initOps,List.mem_cons,List.mem_nil_iff,or_false] at ho;rcases ho with rfl|rfl|rfl|rfl <;>simp[keeps]) run
end
end ExactFourierCircuits.UniformRecursivePaddingFragments
