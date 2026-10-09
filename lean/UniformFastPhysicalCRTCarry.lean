import UniformFastPhysicalCRTMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT index enumeration after (5.5), PDF p.22
(`eq:crt-fourier`), and prefix bound (4.1), PDF p.18.

Mixed-radix carry enumeration is an implementation refinement of the paper's
linear traversal. Initialization, carry visits, frames and instruction counts
have no one-to-one paper lemma; the final caller charges this actual producer.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTCarry
open UniformMachine UniformNatBlockMachine UniformFastPhysicalCRTMachine
noncomputable section

lemma body_regs {a V:ℕ} (L:Addresses) (i:Fin a) (s:State) (args:Args a V L s)
 (c:Constants s) (idx:s.natReg 7804=i.val+1) (N d w r:ℕ) (value:s.natReg 7806=N)
 (rd:s.natHeap (L.directory+2*i.val+1)=some r)
 (dd:s.natHeap (L.work+2*i.val)=some d) (wd:s.natHeap (L.work+2*i.val+1)=some w):
 (applyBlock carryBody s).natReg 7804=i.val∧
 (applyBlock carryBody s).natReg 7806=N-d*w∧
 (applyBlock carryBody s).natReg 7809=r∧
 (applyBlock carryBody s).natReg 7811=w∧
 (applyBlock carryBody s).natReg 7813=d+1∧
 (applyBlock carryBody s).natReg 7815=L.work+2*i.val:=by
 have rd':s.natHeap (L.directory+(2*i.val+1))=some r:=by simpa only[Nat.add_assoc] using rd
 have wd':s.natHeap (L.work+(2*i.val+1))=some w:=by simpa only[Nat.add_assoc] using wd
 simp[carryBody,applyBlock,Op.apply,writeNat,next,evalNat,c.one,c.two,idx,value,
  args.directory,args.work,rd',dd,wd',Nat.add_assoc]
lemma body_readable {a V:ℕ} (L:Addresses) (i:Fin a) (s:State) (args:Args a V L s)
 (c:Constants s) (idx:s.natReg 7804=i.val+1) (d w r:ℕ)
 (rd:s.natHeap (L.directory+2*i.val+1)=some r)
 (dd:s.natHeap (L.work+2*i.val)=some d) (wd:s.natHeap (L.work+2*i.val+1)=some w):readable carryBody s:=by
 have rd':s.natHeap (L.directory+(2*i.val+1))=some r:=by simpa only[Nat.add_assoc] using rd
 have wd':s.natHeap (L.work+(2*i.val+1))=some w:=by simpa only[Nat.add_assoc] using wd
 simp[carryBody,readable,Op.readable,Op.apply,writeNat,next,evalNat,c.one,c.two,idx,
  args.directory,args.work,rd',dd,wd',Nat.add_assoc]
lemma body_peak {a V:ℕ} (L:Addresses) (i:Fin a) (s:State) (args:Args a V L s)
 (c:Constants s) (idx:s.natReg 7804=i.val+1) (N d w r B:ℕ) (value:s.natReg 7806=N)
 (rd:s.natHeap (L.directory+2*i.val+1)=some r)
 (dd:s.natHeap (L.work+2*i.val)=some d) (wd:s.natHeap (L.work+2*i.val+1)=some w)
 (digit:d<r) (term:d*w≤N) (directory:L.directory+2*a≤B) (work:L.work+2*a≤B)
 (bound:WordBound B s):peak carryBody s≤B:=by
 have rd':s.natHeap (L.directory+(2*i.val+1))=some r:=by simpa only[Nat.add_assoc] using rd
 have wd':s.natHeap (L.work+(2*i.val+1))=some w:=by simpa only[Nat.add_assoc] using wd
 have rb: r≤B:=(bound.2.2.1 _ _ rd).2
 have db: d≤B:=(bound.2.2.1 _ _ dd).2
 have wb: w≤B:=(bound.2.2.1 _ _ wd).2
 have nb:N≤B:=value ▸ bound.2.1 7806
 simp[carryBody,peak,Op.peak,Op.apply,writeNat,next,evalNat,c.one,c.two,idx,value,
  args.directory,args.work,rd',dd,wd',Nat.add_assoc]
 omega
lemma body_frame (s:State):Frame s (applyBlock carryBody s):=by
 constructor <;>try rfl
 intro j hj
 simp[carryBody,applyBlock,Op.apply,writeNat,next,show j≠7804 by omega,
  show j≠7808 by omega,show j≠7809 by omega,show j≠7810 by omega,
  show j≠7811 by omega,show j≠7812 by omega,show j≠7806 by omega,
  show j≠7813 by omega,show j≠7815 by omega,show j≠7816 by omega]
lemma body_constants {s:State} (c:Constants s):Constants (applyBlock carryBody s):=by
 constructor <;>simp[carryBody,applyBlock,Op.apply,writeNat,next,c.zero,c.one,c.two]
lemma success_frame (s:State):Frame s (applyBlock successBody s):=by
 constructor <;>try rfl
 intro j hj
 simp[successBody,applyBlock,Op.apply,writeNat,next,show j≠7812 by omega,show j≠7806 by omega]
lemma wrap_frame (s:State):Frame s (applyBlock wrapBody s):=by
 constructor <;>try rfl
 intro j hj
 simp[wrapBody,applyBlock,Op.apply,writeNat,next,show j≠7813 by omega]
lemma success_constants {s:State} (c:Constants s):Constants (applyBlock successBody s):=by
 constructor <;>simp[successBody,applyBlock,Op.apply,writeNat,next,c.zero,c.one,c.two]
lemma wrap_constants {s:State} (c:Constants s):Constants (applyBlock wrapBody s):=by
 constructor <;>simp[wrapBody,applyBlock,Op.apply,writeNat,next,c.zero,c.one,c.two]

/-- One actual carry visits one physical axis. All control, address arithmetic,
three loads, digit store and continuation are charged; no scalar operation. -/
theorem execution {a V n B:ℕ} (L:Addresses) (i:Fin a) (x:Fin n→ℂ) (s:State)
 (args:Args a V L s) (c:Constants s) (pc:s.pc=31) (idx:s.natReg 7804=i.val+1)
 (N d w r:ℕ) (value:s.natReg 7806=N)
 (rd:s.natHeap (L.directory+2*i.val+1)=some r)
 (dd:s.natHeap (L.work+2*i.val)=some d) (wd:s.natHeap (L.work+2*i.val+1)=some w)
 (digit:d<r) (term:d*w≤N)
 (newBound:d+1<r→N-d*w+(d+1)*w≤B)
 (directory:L.directory+2*a≤B) (work:L.work+2*a≤B)
 (code:53≤B) (bound:WordBound B s):∃u,
 BoundedRuns program n x B s (if d+1<r then 18 else 17) u∧
 u.pc=(if d+1<r then 19 else 31)∧u.natReg 7804=i.val∧
 u.natReg 7806=N-d*w+(if d+1<r then (d+1)*w else 0)∧
 u.natHeap=Function.update s.natHeap (L.work+2*i.val) (some (if d+1<r then d+1 else 0))∧
 Args a V L u∧Constants u∧Frame s u∧u.natReg 7803=s.natReg 7803:=by
 have radixBound:r≤B:=(bound.2.2.1 _ _ rd).2
 let b:State:={s with pc:=32}
 have branch:BoundedRuns program n x B s 1 b:=.next bound
  (by simp[step,pc,carry_test,c.zero,idx,b])
  (.refl (changePC_bound B s 32 bound (by omega)))
 have ba:=args_pc args 32
 have bc:=constants_pc c 32
 have run:=block_runs carryBody program 32 n B x b carry_code rfl branch.final_bound
  (by change 32+12≤B;omega) (body_readable L i b ba bc idx d w r rd dd wd)
  (body_peak L i b ba bc idx N d w r B value rd dd wd digit term directory work branch.final_bound)
 let t:=applyBlock carryBody b
 have tp:t.pc=44:=by rw[block_pc];rfl
 obtain ⟨ti,tn,tr,tw,td,ta⟩:=body_regs L i b ba bc idx N d w r value rd dd wd
 change t.natReg 7804=i.val at ti
 change t.natReg 7806=N-d*w at tn
 change t.natReg 7809=r at tr
 change t.natReg 7811=w at tw
 change t.natReg 7813=d+1 at td
 change t.natReg 7815=L.work+2*i.val at ta
 have th:t.natHeap=s.natHeap:=rfl
 have tc:=body_constants bc
 have tf:Frame s t:=(Frame.pc (.refl s) 32).trans (body_frame b)
 by_cases h:d+1<r
 · let v:State:={t with pc:=45}
   have choose:BoundedRuns program n x B t 1 v:=.next run.final_bound
    (by simp[step,tp,success_test,td,tr,h,v])
    (.refl (changePC_bound B t 45 run.final_bound (by omega)))
   have scale:=block_runs successBody program 45 n B x v success_code rfl choose.final_bound
    (by change 45+3≤B;omega)
    (by simp[successBody,readable,Op.readable,Op.apply,writeNat,next,evalNat])
    (by simp[successBody,peak,Op.peak,Op.apply,writeNat,next,evalNat,v,td,tw,tn,ta]
        have nv:=newBound h
        omega)
   let z:=applyBlock successBody v
   have zp:z.pc=48:=by rw[block_pc];rfl
   let u:State:={z with pc:=19}
   have jump:BoundedRuns program n x B z 1 u:=.next scale.final_bound
    (by simp[step,zp,success_jump,u]) (.refl (changePC_bound B z 19 scale.final_bound (by omega)))
   refine ⟨u,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · simp only[h,reduceIte];convert ((branch.trans run).trans choose).trans (scale.trans jump) using 1
     rfl
   · simp[h,u]
   · simpa[successBody,applyBlock,Op.apply,writeNat,next,u,z,v] using ti
   · simp[h,u,z,v,successBody,applyBlock,Op.apply,writeNat,next,evalNat,tn,td,tw]
   · simp[h,u,z,v,successBody,applyBlock,Op.apply,writeNat,next,evalNat,ta,td,th]
   · exact args_pc ((success_frame v).args (args_pc (tf.args args) 45)) 19
   · exact constants_pc (success_constants (constants_pc tc 45)) 19
   · exact (tf.pc 45).trans ((success_frame v).pc 19)
   · simp[u,z,v,t,b,carryBody,successBody,applyBlock,Op.apply,writeNat,next]
 · let v:State:={t with pc:=49}
   have choose:BoundedRuns program n x B t 1 v:=.next run.final_bound
    (by simp[step,tp,success_test,td,tr,h,v])
    (.refl (changePC_bound B t 49 run.final_bound (by omega)))
   have reset:=block_runs wrapBody program 49 n B x v wrap_code rfl choose.final_bound
    (by change 49+2≤B;omega) (by simp[wrapBody,readable,Op.readable])
    (by simp[wrapBody,peak,Op.peak,Op.apply,writeNat,next,v,ta];omega)
   let z:=applyBlock wrapBody v
   have zp:z.pc=51:=by rw[block_pc];rfl
   let u:State:={z with pc:=31}
   have jump:BoundedRuns program n x B z 1 u:=.next reset.final_bound
    (by simp[step,zp,wrap_jump,u]) (.refl (changePC_bound B z 31 reset.final_bound (by omega)))
   refine ⟨u,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · simp only[h,reduceIte];convert ((branch.trans run).trans choose).trans (reset.trans jump) using 1
     rfl
   · simp[h,u]
   · simpa[wrapBody,applyBlock,Op.apply,writeNat,next,u,z,v] using ti
   · simp[h,u,z,v,wrapBody,applyBlock,Op.apply,writeNat,next,tn]
   · simp[h,u,z,v,wrapBody,applyBlock,Op.apply,writeNat,next,ta,th]
   · exact args_pc ((wrap_frame v).args (args_pc (tf.args args) 49)) 31
   · exact constants_pc (wrap_constants (constants_pc tc 49)) 31
   · exact (tf.pc 49).trans ((wrap_frame v).pc 31)
   · simp[u,z,v,t,b,carryBody,wrapBody,applyBlock,Op.apply,writeNat,next]
end
end ExactFourierCircuits.UniformFastPhysicalCRTCarry
