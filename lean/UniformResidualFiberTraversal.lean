import UniformResidualFiberAddressMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualFiberTraversal
open UniformMachine UniformAssembly UniformResidualFiberAddressMachine
open UniformNatBlockMachine (Op applyBlock readable peak block_runs)
noncomputable section

def address (image : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
 | 0,a,_=>a
 | h+1,a,j=>if j < 2^h then address image h a j
             else address image h (a^^^image h) (j-2^h)

theorem address_small (q w h a j : ℕ) (image : ℕ → ℕ)
 (ha : a < 2^(q*w)) (hi : ∀i < h,image i < 2^(q*w)) :
 address image h a j < 2^(q*w) := by
 induction h generalizing a j with
 | zero=>exact ha
 | succ h ih=>
   simp only [address]
   split
   · exact ih a j ha (by intro i hl;exact hi i (by omega))
   · exact ih _ _ (Nat.xor_lt_two_pow ha (hi h (by omega)))
       (by intro i hl;exact hi i (by omega))

structure Effect (k q w images stack output table d h a c : ℕ)
 (image : ℕ → ℕ) (s u : State) : Prop where
 pc : u.pc=62
 header : Header k q w images stack output table u
 depth : u.natReg 4020=d
 native : u.natReg 4021=a
 count : u.natReg 4023=c+2^h
 outside : ∀z,(z < stack+2*d ∨ stack+2*k ≤ z) → 
   (z < output+c ∨ output+c+2^h ≤ z) → u.natHeap z=s.natHeap z
 written : ∀j,j < 2^h → u.natHeap (output+c+j)=some (address image h a j)
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders

lemma entry_runs (n B k q w images stack output table d a c : ℕ)
 (x : Fin n → ℂ) (s : State) (head : Header k q w images stack output table s)
 (pc : s.pc=7) (depth : s.natReg 4020=d) (count : s.natReg 4023=c)
 (native : s.natReg 4021=a) (low : d < k) (bound : WordBound B s) (code : 71 ≤ B) :
 ∃u,BoundedRuns program n x B s 2 u ∧ u.pc=9 ∧
 Header k q w images stack output table u ∧ u.natReg 4020=d ∧
 u.natReg 4021=a ∧ u.natReg 4022=0 ∧ u.natReg 4023=c ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let entry:State:={s with pc:=8}
 have er:BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,pc,node_at,depth,head.bits,low,entry])
  (.refl (changePC_bound B s 8 bound (by omega)))
 have safe : readable enter entry ∧ peak enter entry ≤ B := by simp [enter,readable,peak,Op.readable,Op.peak]
 have ar:=block_runs enter program 8 n B x entry enter_code rfl er.final_bound
  (by change 9 ≤ B;omega) safe.1 safe.2
 let u:=applyBlock enter entry
 refine ⟨u,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
 · convert er.trans ar using 1
   rfl
 · simp [u,enter,applyBlock,Op.apply,writeNat,next,entry]
 · constructor  <;> simp [u,enter,applyBlock,Op.apply,writeNat,next,entry,
   head.bits,head.images,head.stack,head.output,head.table,head.width,head.size,head.one,head.two,head.zero]
 all_goals simp [u,enter,applyBlock,Op.apply,writeNat,next,entry,depth,native,count]

lemma exhausted_runs (n B : ℕ) (x : Fin n → ℂ) (s : State)
 (pc : s.pc=9) (digit : s.natReg 4022=2) (two : s.natReg 4025=2)
 (bound : WordBound B s) (code : 71 ≤ B) :
 BoundedRuns program n x B s 1 {s with pc:=62} := .next bound
  (by simp [step,pc,child_at,digit,two])
  (.refl (changePC_bound B s 62 bound (by omega)))

/-- Actual complete DFS execution, including both children, stack restoration,
XOR table reads and every address write. Incoming images are an explicit physical
bank interface; the descriptor-to-image producer is a separate caller obligation. -/
theorem tree_execution (n B k q w images stack output table d h a c : ℕ)
 (image : ℕ → ℕ) (x : Fin n → ℂ) (s : State)
 (head : Header k q w images stack output table s) (pc : s.pc=7)
 (depth : s.natReg 4020=d) (native : s.natReg 4021=a) (count : s.natReg 4023=c)
 (total : d+h=k) (bound : WordBound B s) (code : 71 ≤ B)
 (imagesBefore : images+k  ≤  stack) (stackBefore : stack+2*k ≤ output)
 (outputBefore : output+c+2^h ≤ table) (tableBound : table+2^q*2^q ≤ B)
 (volume : 2^(q*w) ≤ B) (small : a < 2^(q*w))
 (bank : ∀i,i < k → s.natHeap (images+i)=some (image i))
 (imageSmall : ∀i,i < k → image i < 2^(q*w))
 (entries : UniformXorTableMachine.Entries q table (2^q*2^q) s) :
 ∃u,BoundedRuns program n x B s (treeCost w h) u ∧
 Effect k q w images stack output table d h a c image s u := by
 induction h generalizing d a c s with
 | zero=>
   have dk:d=k:=by omega
   obtain ⟨u,run,up,uh,ud,ua,uc,uw,uf,sh,sr,out,roots⟩:=leaf_runs n B k q w images stack output table a c
    x s head pc (by simpa [dk] using depth) native count bound code (by omega)
    (small.le.trans volume) (by omega)
   refine ⟨u,run,up,uh,?_,ua,?_,?_,?_,sh,sr,out,roots⟩
   · simpa [dk] using ud
   · simpa using uc
   · intro z _ outside
     exact uf z (by simp only [pow_zero] at outside;omega)
   · intro j hj
     have j0:j=0:=by simpa using hj
     subst j
     simpa [address] using uw
 | succ h ih=>
   have low:d < k:=by omega
   have pow : 2^(h+1)=2^h+2^h := by rw [Nat.pow_succ];omega
   have positive : 0 < 2^h:=Nat.two_pow_pos h
   obtain ⟨entry,er,ep,eh,ed,ea,ej,ec,eheap,esh,esr,eout,eroot⟩:=entry_runs n B k q w images stack output table d a c
    x s head pc depth count native low bound code
   obtain ⟨left,lr,lp,lh,ld,la,lc,lheap,lsh,lsr,lout,lroot⟩:=zero_child_runs n B k q w images stack output table d a
    x entry eh ep ed ea ej low er.final_bound code (by omega)
   have lb : ∀i,i < k → left.natHeap (images+i)=some (image i) := by
    intro i hi
    rw [lheap,eheap]
    simpa (disch:=omega) using bank i hi
   have le : UniformXorTableMachine.Entries q table (2^q*2^q) left := by
    intro j hj
    rw [lheap,eheap]
    simpa (disch:=omega) using entries j hj
   obtain ⟨lv,lvRun,lvE⟩:=ih (d+1) a c left lh lp ld la (lc.trans ec) (by omega) lr.final_bound
    (by rw [pow] at outputBefore;omega) small lb le
   have stackL : lv.natHeap (stack+2*d)=some a := by
    rw [lvE.outside _ (by omega) (by omega),lheap]
    simp
   have stackR : lv.natHeap (stack+2*d+1)=some 1 := by
    rw [lvE.outside _ (by omega) (by omega),lheap]
    simp
   obtain ⟨mid,mr,mp,mh,mc,md,ma,mj,mheap,msh,msr,mout,mroot⟩:=pop_runs n B k q w images stack output table d a 1
    x lv lvE.header lvE.pc lvE.depth stackL stackR lvRun.final_bound code (by omega)
   have mb : ∀i,i < k → mid.natHeap (images+i)=some (image i) := by
    intro i hi
    rw [mheap,lvE.outside _ (by omega) (by omega)]
    exact lb i hi
   have me : UniformXorTableMachine.Entries q table (2^q*2^q) mid := by
    intro j hj
    rw [mheap,lvE.outside _ (by omega) (by omega)]
    exact le j hj
   obtain ⟨right,rr,rp,rh,rd,ra,rc,rheap,rsh,rsr,rout,rroot⟩:=one_child_runs n B k q w images stack output table d a (image h)
    x mid mh mp md ma mj low mr.final_bound code (by omega) imagesBefore (by omega) tableBound volume small
    (imageSmall h (by omega)) (by convert mb h (by omega) using 1;congr 1;omega) me
   have rb : ∀i,i < k → right.natHeap (images+i)=some (image i) := by
    intro i hi
    rw [rheap]
    simpa (disch:=omega) using mb i hi
   have re : UniformXorTableMachine.Entries q table (2^q*2^q) right := by
    intro j hj
    rw [rheap]
    simpa (disch:=omega) using me j hj
   obtain ⟨rv,rvRun,rvE⟩:=ih (d+1) (a^^^image h) (c+2^h) right rh rp rd ra
    (rc.trans (mc.trans lvE.count)) (by omega) rr.final_bound (by rw [pow] at outputBefore;omega)
    (Nat.xor_lt_two_pow small (imageSmall h (by omega))) rb re
   have stackL' : rv.natHeap (stack+2*d)=some a := by
    rw [rvE.outside _ (by omega) (by omega),rheap]
    simp
   have stackR' : rv.natHeap (stack+2*d+1)=some 2 := by
    rw [rvE.outside _ (by omega) (by omega),rheap]
    simp
   obtain ⟨last,pr,pp,ph,pcnt,pd,pa,pj,pheap,psh,psr,pout,proot⟩:=pop_runs n B k q w images stack output table d a 2
    x rv rvE.header rvE.pc rvE.depth stackL' stackR' rvRun.final_bound code (by omega)
   have endRun:=exhausted_runs n B x last pp pj ph.two pr.final_bound code
   let u:State:={last with pc:=62}
   have uh : Header k q w images stack output table u :=
    ⟨ph.bits,ph.images,ph.stack,ph.output,ph.table,ph.width,ph.size,ph.one,ph.two,ph.zero⟩
   refine ⟨u,?_,rfl,uh,pd,pa,?_,?_,?_,?_,?_,?_,?_⟩
   · convert er.trans (lr.trans (lvRun.trans (mr.trans (rr.trans (rvRun.trans (pr.trans endRun)))))) using 1
     simp only [treeCost]
     omega
   · change last.natReg 4023=_
     rw [pcnt,rvE.count,pow]
     omega
   · intro z hs ho
     change last.natHeap z=_
     rw [pheap,rvE.outside z (by omega) (by omega),rheap]
     rw [Function.update_of_ne (show z≠stack+2*d+1 by omega),Function.update_of_ne (show z≠stack+2*d by omega)]
     rw [mheap,lvE.outside z (by omega) (by rw [pow] at ho;omega),lheap]
     rw [Function.update_of_ne (show z≠stack+2*d+1 by omega),Function.update_of_ne (show z≠stack+2*d by omega),eheap]
   · intro j hj
     change last.natHeap (output+c+j)=_
     rw [pheap]
     by_cases jl:j < 2^h
     · rw [rvE.outside _ (by omega) (by omega),rheap]
       rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),mheap]
       simpa only [address,ite_eq_left jl] using lvE.written j jl
     · have rest:j-2^h < 2^h:=by rw [pow] at hj;omega
       have eq:output+(c+2^h)+(j-2^h)=output+c+j:=by omega
       simpa only [eq,address,ite_eq_right jl] using rvE.written (j-2^h) rest
   · exact psh.trans (rvE.scalarHeap.trans (rsh.trans (msh.trans (lvE.scalarHeap.trans (lsh.trans esh)))))
   · exact psr.trans (rvE.scalarReg.trans (rsr.trans (msr.trans (lvE.scalarReg.trans (lsr.trans esr)))))
   · exact pout.trans (rvE.outputs.trans (rout.trans (mout.trans (lvE.outputs.trans (lout.trans eout)))))
   · exact proot.trans (rvE.roots.trans (rroot.trans (mroot.trans (lvE.roots.trans (lroot.trans eroot)))))


structure Inputs (k q w images stack output table : ℕ) (s : State) : Prop where
 bits : s.natReg 4008=k
 images : s.natReg 4009=images
 stack : s.natReg 4010=stack
 output : s.natReg 4011=output
 table : s.natReg 4012=table
 width : s.natReg 4014=w
 size : s.natReg 4015=2^q

/-- The complete fixed printer includes its own counter/constant initialization
and final halt. Every output address is physically written by the DFS. -/
theorem execution (n B k q w images stack output table : ℕ) (image : ℕ→ℕ)
 (x : Fin n→ℂ) (s : State) (pc : s.pc=0)
 (input : Inputs k q w images stack output table s) (bound : WordBound B s)
 (code : 71 ≤ B) (imagesBefore : images+k ≤ stack)
 (stackBefore : stack+2*k ≤ output) (outputBefore : output+2^k ≤ table)
 (tableBound : table+2^q*2^q ≤ B) (volume : 2^(q*w) ≤ B)
 (bank : ∀i, i<k → s.natHeap (images+i)=some (image i))
 (imageSmall : ∀i, i<k → image i<2^(q*w))
 (entries : UniformXorTableMachine.Entries q table (2^q*2^q) s) : ∃u,
 BoundedExecution program n x B s (treeCost w k+9) u ∧ u.pc=70 ∧
 u.natReg 4023=2^k ∧ (∀j, j<2^k → u.natHeap (output+j)=some (address image k 0 j)) ∧
 (∀z, (z<stack ∨ stack+2*k≤z) → (z<output ∨ output+2^k≤z) → u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have safe : readable boot s ∧ peak boot s≤B := by
  simp [boot,readable,peak,Op.readable,Op.peak];omega
 have br:=block_runs boot program 0 n B x s boot_code pc bound (by change 7≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have rp : ready.pc=7 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc]
 have header : Header k q w images stack output table ready := by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,input.bits,input.images,input.stack,
   input.output,input.table,input.width,input.size]
 have depth : ready.natReg 4020=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have native : ready.natReg 4021=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have count : ready.natReg 4023=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 obtain ⟨v,run,e⟩:=tree_execution n B k q w images stack output table 0 k 0 0 image x ready header rp depth native count
  (by omega) br.final_bound code imagesBefore stackBefore (by simpa using outputBefore) tableBound volume
  (Nat.two_pow_pos _) bank imageSmall entries
 let u:State:={v with pc:=70}
 have finish : BoundedExecution program n x B v 2 u:=.next run.final_bound
  (by simp [step,e.pc,return_at,e.header.zero,e.depth,u])
  (.halt (changePC_bound B v 70 run.final_bound (by omega)) (by simp [step,u,halt_at]))
 refine ⟨u,?_,rfl,?_,?_,?_,e.scalarHeap,e.scalarReg,e.outputs,e.roots⟩
 · convert br.executes (run.executes finish) using 1
   change treeCost w k+9=7+(treeCost w k+2)
   omega
 · simpa [u] using e.count
 · intro j hj
   simpa [u] using e.written j hj
 · intro z hstack hout
   simpa [u,ready,boot,applyBlock,Op.apply,writeNat,next] using e.outside z (by simpa using hstack) (by simpa using hout)

def Safe : Instruction→Prop
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _ =>
   (3350≤d ∧ d≤3446) ∨ (4000≤d ∧ d≤4028)
 | .storeNat _ _ | .branchLT _ _ _ _ | .jump _ | .halt => True
 | _=>False
instance (q : Instruction) : Decidable (Safe q) := by cases q <;> unfold Safe <;> infer_instance

theorem program_safe : ∀q∈program, Safe q := by
 have all : program.all (fun q=>decide (Safe q))=true := by decide
 intro q hq
 exact of_decide_eq_true ((List.all_eq_true.mp all) q hq)

structure Frame (s u : State) : Prop where
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r, ((r<3350 ∨ 3446<r) ∧ (r<4000 ∨ 4028<r)) → u.natReg r=s.natReg r
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u v : State} (f : Frame s u) (g : Frame u v) : Frame s v :=
 ⟨g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,
  g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma write_frame (s : State) (d v : ℕ) (safe : (3350≤d ∧ d≤3446) ∨ (4000≤d ∧ d≤4028)) :
 Frame s (writeNat s d v) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r keep
 simp [writeNat,next,Function.update_of_ne (show r≠d by omega)]

theorem step_frame (n : ℕ) (x : Fin n→ℂ) (s u : State)
 (h : step program n x s=.running u) : Frame s u := by
 cases code : program[s.pc]? with
 | none=>simp [step,code] at h
 | some q=>
   have safe:=program_safe q (List.mem_of_getElem? code)
   cases q <;> try {change False at safe;exact False.elim safe}
   case natLiteral d v=>
    simp only [step,code,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case natBinary op d l r=>
    cases value : evalNat op (s.natReg l) (s.natReg r) with
    | none=>simp [step,code,value] at h
    | some v=>simp only [step,code,value,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case loadNat d a=>
    cases value : s.natHeap (s.natReg a) with
    | none=>simp [step,code,value] at h
    | some v=>simp only [step,code,value,StepResult.running.injEq] at h;subst u;exact write_frame s d v safe
   case storeNat a r=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case branchLT l r yes no=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case jump pc=>simp only [step,code,StepResult.running.injEq] at h;subst u;exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
   case halt=>simp [step,code] at h

theorem execution_frame {n t : ℕ} {x : Fin n→ℂ} {s u : State}
 (run : Executes program n x s t u) : Frame s u := by
 induction run with
 | halt _=>exact Frame.refl _
 | next h _ ih=>exact (step_frame _ _ _ _ h).trans ih

end
end ExactFourierCircuits.UniformResidualFiberTraversal
