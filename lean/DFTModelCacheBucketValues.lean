import DFTModelCacheBucketProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
open DFTModelCacheDAGDepth (nat)
attribute [local irreducible] step scan selector scanBody scanCount selectorCount zeroState

def gateBill (x:Input.T) (l q:ℕ) (s:State.T) (j:ℕ):Bill State.T:=
  Bill.steps s (fun i s=>run step ((x,(l,q)),(i,s))) j
def levelBill (x:Input.T) (L q j:ℕ):Bill State.T:=
  Bill.steps (0,0) (fun l s=>run next ((x,(L,q)),(l,s))) j

theorem steps_pay_six (s:State.T) (f:ℕ→State.T→Bill State.T) (j:ℕ):
    Bill.steps s (fun i s=>(f i s).pay 6 0) j=
      ⟨(Bill.steps s f j).val,(Bill.steps s f j).work+6*j,
        (Bill.steps s f j).peak,(Bill.steps s f j).valid⟩ := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    rw [Bill.steps,ih]
    simp only [Bill.pay,Bill.steps,Bill.pass,max_zero]
    congr 1
    omega

theorem scanBody_run (x:Input.T) (l q i:ℕ) (s a:State.T):
    run scanBody
      (((x,(l,q)),s),(i,a))=(run step ((x,(l,q)),(i,a))).pay 6 0 := by
  rw [scanBody]
  simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem scan_billing (G:ℕ) (s:State.T) (b:Bill State.T):
    (((⟨G,7,0,True⟩:Bill ℕ).pass (fun _=>(Bill.one s).pass
      (fun _=>(⟨b.val,b.work+6*G,b.peak,b.valid⟩:Bill State.T)))).pay 1 0)=
      ⟨b.val,b.work+6*G+9,b.peak,b.valid⟩ := by
  simp only [Bill.one,Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  congr 1
  omega

theorem scan_billing_beta (G:ℕ) (b:Bill State.T):
    (⟨b.val,7+(1+(b.work+6*G)),b.peak,b.valid⟩:Bill State.T).pay 1 0=
      ⟨b.val,b.work+6*G+9,b.peak,b.valid⟩ := by
  simp only [Bill.pay,max_zero]
  congr 1
  omega

theorem selector_billing (L:ℕ) (b:Bill State.T):
    (((⟨L,3,0,True⟩:Bill ℕ).pass (fun _=>(⟨(0,0),3,0,True⟩:Bill State.T).pass
      (fun _=>b))).pay 1 0)=⟨b.val,b.work+7,b.peak,b.valid⟩ := by
  simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  congr 1
  omega

theorem scan_run (x:Input.T) (l q:ℕ) (s:State.T):
    run scan ((x,(l,q)),s)=⟨(gateBill x l q s x.2.1).val,
      (gateBill x l q s x.2.1).work+6*x.2.1+9,
      (gateBill x l q s x.2.1).peak,(gateBill x l q s x.2.1).valid⟩ := by
  have hc:run scanCount ((x,(l,q)),s)=
      ⟨x.2.1,7,0,True⟩:=by simp [scanCount,count,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [scan]
  change (((run scanCount ((x,(l,q)),s)).pass (fun G=>(Bill.one s).pass
    (fun a=>Bill.steps a (fun i a=>
      run scanBody
        (((x,(l,q)),s),(i,a))) G))).pay 1 0)=_
  rw [hc]
  have hb:(fun i a=>run scanBody (((x,(l,q)),s),(i,a)))=
      (fun i a=>(run step ((x,(l,q)),(i,a))).pay 6 0):=by
    funext i a
    exact scanBody_run x l q i s a
  rw [hb]
  simp only [Bill.pass,Bill.one,true_and,zero_max]
  have hp:=steps_pay_six s (fun i a=>run step ((x,(l,q)),(i,a))) x.2.1
  rw [hp]
  exact scan_billing_beta x.2.1 (gateBill x l q s x.2.1)

theorem next_run (x:Input.T) (L q l:ℕ) (s:State.T):
    run next ((x,(L,q)),(l,s))=(run scan ((x,(l,q)),s)).pay 18 0 := by
  rw [next]
  simp [root,index,query,current,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem selector_run (x:Input.T) (L q:ℕ):
    run selector (x,(L,q))=⟨(levelBill x L q L).val,
      (levelBill x L q L).work+7,(levelBill x L q L).peak,(levelBill x L q L).valid⟩ := by
  have hc:run selectorCount (x,(L,q))=⟨L,3,0,True⟩:=by
    simp [selectorCount,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  have hi:run zeroState (x,(L,q))=
      (⟨(0,0),3,0,True⟩:Bill State.T):=by
    simp [zeroState,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass]
  rw [selector]
  change (((run selectorCount (x,(L,q))).pass (fun (n:ℕ)=>
    (run zeroState (x,(L,q))).pass
      (fun s=>Bill.steps s (fun l s=>run next ((x,(L,q)),(l,s))) n))).pay 1 0)=_
  rw [hc,hi]
  exact selector_billing L (levelBill x L q L)

theorem choice_append (xs:List ℕ) (q i:ℕ):
    choice (xs++[i]) q=(xs.length+1,if xs.length=q then i else (choice xs q).2) := by
  unfold choice
  simp only [List.length_append,List.length_singleton,Prod.mk.injEq]
  refine ⟨trivial,?_⟩
  by_cases hq:q<xs.length
  · have hn:xs.length≠q:=by omega
    simp [List.getElem?_append,hq,hn]
  · by_cases he:xs.length=q
    · subst q
      simp
    · have hh:xs.length<q:=by omega
      simp [List.getElem?_append,hq,he,
        show q-xs.length≠0 by omega]

theorem selected_succ (d:ℕ→ℕ) (l j:ℕ):
    selected d l (j+1)=selected d l j++(if d j=l then [j] else []) := by
  by_cases h:d j=l <;> simp [selected,List.range_succ,List.filter_append,h]

theorem gateBill_value (x:Input.T) (l q:ℕ) (xs:List ℕ) (j:ℕ):
    (gateBill x l q (choice xs q) j).val=
      choice (xs++selected (depthValue x) l j) q := by
  induction j with
  | zero=>simp [gateBill,Bill.steps,Bill.one,selected]
  | succ j ih=>
    change (run step ((x,(l,q)),(j,(gateBill x l q (choice xs q) j).val))).val=_
    rw [step_value,ih,selected_succ]
    by_cases he:depthValue x j=l
    · simp only [he,ite_true,advance]
      rw [←List.append_assoc]
      exact (choice_append (xs++selected (depthValue x) l j) q j).symm
    · simp [he,advance]

theorem scan_value (x:Input.T) (l q:ℕ) (xs:List ℕ):
    (run scan ((x,(l,q)),choice xs q)).val=
      choice (xs++UniformDAGBucketMachine.selected x.2.1 l (depthValue x)) q := by
  rw [scan_run,gateBill_value]
  rfl

theorem processed_succ (G L:ℕ) (d:ℕ→ℕ):
    processed G (L+1) d=processed G L d++UniformDAGBucketMachine.selected G L d := by
  simp [processed,List.range_succ,List.flatMap_append]

theorem levelBill_value (x:Input.T) (L q j:ℕ):
    (levelBill x L q j).val=choice (processed x.2.1 j (depthValue x)) q := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    change (run next ((x,(L,q)),(j,(levelBill x L q j).val))).val=_
    rw [next_run,ih]
    change (run scan ((x,(j,q)),choice (processed x.2.1 j (depthValue x)) q)).val=_
    rw [scan_value,processed_succ]

theorem selector_value (x:Input.T) (L q:ℕ):
    (run selector (x,(L,q))).val=choice (processed x.2.1 L (depthValue x)) q := by
  rw [selector_run,levelBill_value]

theorem tab_run_value {s t:Ty} (n:Prog false s w) (b:Prog false (p s w) t) (x:s.T):
    (run (.tab n b) x).val=Tape.tab (run n x).val (fun j=>(run b (x,j)).val) := by
  simp only [run,Code.run,Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_value]

/-- Native stable order and directory, including zero-depth rows and omitted
out-of-range labels. No externally supplied sorting certificate occurs. -/
theorem program_value (x:Input.T):
    (run program x).val=
      (Tape.tab (UniformDAGBucketMachine.order x.2.1 (depthValue x)).length
        (fun j=>(UniformDAGBucketMachine.order x.2.1 (depthValue x))[j]?.getD 0),
       Tape.tab (x.2.1+2) (fun l=>UniformDAGBucketMachine.offset x.2.1 l (depthValue x))) := by
  have hl:(run length x).val=(UniformDAGBucketMachine.order x.2.1 (depthValue x)).length := by
    simp only [length,fullRequest,count,nat,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
    rw [show Code.run selector () (x,(x.2.1+1,0))=run selector (x,(x.2.1+1,0)) from rfl,
      selector_value]
    rfl
  have ho:∀j,(run orderCell (x,j)).val=
      (UniformDAGBucketMachine.order x.2.1 (depthValue x))[j]?.getD 0 := by
    intro j
    simp only [orderCell,count,nat,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
    rw [show Code.run selector () (x,(x.2.1+1,j))=run selector (x,(x.2.1+1,j)) from rfl,
      selector_value]
    rfl
  have hd:∀l,(run directoryCell (x,l)).val=UniformDAGBucketMachine.offset x.2.1 l (depthValue x) := by
    intro l
    simp only [directoryCell,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    rw [show Code.run selector () (x,(l,0))=run selector (x,(l,0)) from rfl,selector_value]
    rfl
  rw [program]
  change ((run order x).val,(run directory x).val)=_
  congr 1
  · rw [order]
    rw [tab_run_value,hl]
    exact congrArg (Tape.tab _) (funext ho)
  · rw [directory]
    rw [tab_run_value]
    have hc:(run (nat .add count (.atom (.lit 2))) x).val=x.2.1+2:=by
      simp [nat,count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    rw [hc]
    exact congrArg (Tape.tab _) (funext hd)

end
end ExactFourierCircuits.DFTModelCacheBucket
