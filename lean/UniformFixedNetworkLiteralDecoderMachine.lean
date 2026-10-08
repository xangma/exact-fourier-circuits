import UniformFixedNetworkScheduleMachine
import UniformAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkLiteralDecoderMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords serialize)

/-- Runtime q is read from Nat2599; the original template and all strides are
fixed. Each record charges a field store, stride literal and pointer addition.
This is a fixed compiled-stride patcher, not an opcode/child interpreter. -/
def setup : List Op := [.literal 2701 1,.add 2700 2600 2701]
def patches : List Record→List Op
 | []=>[]
 | r::rs=>[.putNat 2700 2599,.literal 2701 r.data.length,.add 2700 2700 2701]++patches rs
def patchBlock (rs:List Record) : List Op := setup++patches rs
def continuation (rs:List Record) : ℕ := 3*(serialize rs).length+4
def program (rs:List Record) : Program :=
 UniformAssembly.embed [] (UniformFixedNetworkScheduleMachine.program (serialize rs)) ((patchBlock rs).map Op.code++[.halt]) (continuation rs)
lemma patches_length (rs:List Record) : (patches rs).length=3*rs.length := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp [patches,ih];omega
lemma patchBlock_length (rs:List Record) : (patchBlock rs).length=2+3*rs.length := by simp [patchBlock,setup,patches_length];omega
lemma program_length (rs:List Record) : (program rs).length=3*(serialize rs).length+3*rs.length+7 := by
 simp [program,UniformAssembly.embed_length,UniformFixedNetworkScheduleMachine.program_length,patchBlock_length];omega

noncomputable section

lemma data_columns_length (q:ℕ) (r:Record) : (r.withColumns q).data.length=r.data.length := by
 rw [Record.data_length,Record.data_length];rfl
lemma data_length_positive (r:Record) : 8≤r.data.length := by rw [Record.data_length];omega
lemma serialize_cons (r:Record) (rs:List Record) : serialize (r::rs)=r.data++serialize rs := rfl
lemma serialize_length_cons (r:Record) (rs:List Record) :
 (serialize (r::rs)).length=r.data.length+(serialize rs).length := by rw [serialize_cons,List.length_append]
lemma header_columns (q:ℕ) (r:Record) (j:Fin 8) :
 (r.withColumns q).header[j.val]'(by rw [Record.header_length];exact j.isLt)=
 if j.val=1 then q else r.header[j.val]'(by rw [Record.header_length];exact j.isLt) := by
 fin_cases j <;> rfl
lemma data_columns (q:ℕ) (r:Record) (j:ℕ) (hj:j<r.data.length) :
 (r.withColumns q).data[j]'(by rw [data_columns_length];exact hj)=
 if j=1 then q else r.data[j]'hj := by
 by_cases hh:j<8
 · have hl:j<(r.withColumns q).header.length:=by rw [Record.header_length];exact hh
   have hr:j<r.header.length:=by rw [Record.header_length];exact hh
   have left:(r.withColumns q).data[j]'(by rw [data_columns_length];exact hj)=
     (r.withColumns q).header[j]'hl := @List.getElem_append_left ℕ j _ _ hl _
   have right:r.data[j]'hj=r.header[j]'hr := @List.getElem_append_left ℕ j _ _ hr _
   exact left.trans ((header_columns q r ⟨j,hh⟩).trans
     (congrArg (fun v=>if j=1 then q else v) right.symm))
 · have hl:(r.withColumns q).header.length≤j:=by rw [Record.header_length];omega
   have hr:r.header.length≤j:=by rw [Record.header_length];omega
   have hb:j-8<r.directions.length:=by rw [Record.data_length] at hj;omega
   have left:(r.withColumns q).data[j]'(by rw [data_columns_length];exact hj)=r.directions[j-8]'hb :=
     @List.getElem_append_right ℕ _ _ j hl _
   have right:r.data[j]'hj=r.directions[j-8]'hb := @List.getElem_append_right ℕ _ _ j hr _
   rw [ite_eq_right (show j≠1 by omega)]
   exact left.trans right.symm

structure Frame (s u:State) : Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg : ∀ (r : ℕ), r ≠ 2601 → r ≠ 2602 → r ≠ 2603 → r ≠ 2604 → r ≠ 2700 → r ≠ 2701 → u.natReg r = s.natReg r
lemma Frame.trans {s t u:State} (a:Frame s t) (b:Frame t u) : Frame s u :=
 ⟨b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,b.outputs.trans a.outputs,b.roots.trans a.roots,
 fun r h1 h2 h3 h4 h5 h6=>(b.natReg r h1 h2 h3 h4 h5 h6).trans (a.natReg r h1 h2 h3 h4 h5 h6)⟩
lemma Frame.of_printer {s t:State} (h:UniformFixedNetworkScheduleMachine.Frame s t) : Frame s t :=
 ⟨h.scalarHeap,h.scalarReg,h.outputs,h.roots,fun r h1 h2 h3 h4 _ _=>h.natReg r h1 h2 h3 h4⟩
lemma Frame.pc {s t:State} (h:Frame s t) (c:ℕ) : Frame s {t with pc:=c} :=
 ⟨h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩
lemma placed_zero (s:State) : UniformAssembly.placed 0 s=s := by cases s;simp [UniformAssembly.placed]
lemma setup_frame (s:State) : Frame s (applyBlock setup s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r _ _ _ _ h5 h6;simp [setup,applyBlock,Op.apply,writeNat,next,h5,h6]
lemma patches_frame (rs:List Record) (s:State) : Frame s (applyBlock (patches rs) s) := by
 induction rs generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,fun _ _ _ _ _ _ _=>rfl⟩
 | cons r rs ih=>
   have head:Frame s (applyBlock [.putNat 2700 2599,.literal 2701 r.data.length,.add 2700 2700 2701] s):=by
     refine ⟨rfl,rfl,rfl,rfl,?_⟩
     intro z _ _ _ _ h5 h6;simp [applyBlock,Op.apply,writeNat,next,h5,h6]
   rw [patches,UniformFixedNetworkScheduleMachine.applyBlock_append];exact head.trans (ih _)

lemma patches_safe (rs:List Record) (A B q:ℕ) (s:State)
 (ptr:s.natReg 2700=A+1) (hq:s.natReg 2599=q) (qb:q≤B)
 (extent:A+(serialize rs).length+1≤B) : readable (patches rs) s ∧ peak (patches rs) s≤B := by
 induction rs generalizing A s with
 | nil=>simp [patches,readable,peak]
 | cons r rs ih=>
   let t:=applyBlock [.putNat 2700 2599,.literal 2701 r.data.length,.add 2700 2700 2701] s
   have p:t.natReg 2700=(A+r.data.length)+1:=by simp [t,applyBlock,Op.apply,writeNat,next,ptr];omega
   have qe:t.natReg 2599=q:=by simp [t,applyBlock,Op.apply,writeNat,next,hq]
   have rest:=ih (A+r.data.length) t p qe (by rw [serialize_length_cons] at extent;omega)
   have pa:A+1≤B:=by omega
   have rl:r.data.length≤B:=by rw [serialize_length_cons] at extent;omega
   have pe:A+1+r.data.length≤B:=by rw [serialize_length_cons] at extent;omega
   simpa [patches,readable,peak,Op.readable,Op.peak,Op.apply,applyBlock,writeNat,next,ptr,hq,
     max_le_iff,pa,rl,pe,qb,t] using rest

lemma PrintedRecords.transport {rs:List Record} {A:ℕ} {s u:State}
 (h:PrintedRecords A rs s) (same:∀z,A≤z→u.natHeap z=s.natHeap z) : PrintedRecords A rs u := by
 induction rs generalizing A with
 | nil=>trivial
 | cons r rs ih=>
   refine ⟨?_,ih h.2 ?_⟩
   · intro j hj;rw [same (A+j) (by omega)];exact h.1 j hj
   · intro z hz;exact same z (by omega)

/-- Actual field1 stores patch every record, including zero-dimensional/empty
child bodies. All other cells are retained; q is an unchanged runtime input. -/
lemma patches_spec (rs:List Record) (A q:ℕ) (s:State)
 (ptr:s.natReg 2700=A+1) (hq:s.natReg 2599=q) (bank:PrintedRecords A rs s) :
 PrintedRecords A (rs.map (Record.withColumns q)) (applyBlock (patches rs) s) ∧
 (∀z,z<A∨A+(serialize rs).length≤z→(applyBlock (patches rs) s).natHeap z=s.natHeap z) ∧
 (applyBlock (patches rs) s).natReg 2700=A+(serialize rs).length+1 := by
 induction rs generalizing A s with
 | nil=>exact ⟨trivial,fun _ _=>rfl,by simpa [patches,applyBlock,serialize] using ptr⟩
 | cons r rs ih=>
   let t:=applyBlock [.putNat 2700 2599,.literal 2701 r.data.length,.add 2700 2700 2701] s
   have hp:t.natReg 2700=(A+r.data.length)+1:=by simp [t,applyBlock,Op.apply,writeNat,next,ptr];omega
   have hq':t.natReg 2599=q:=by simp [t,applyBlock,Op.apply,writeNat,next,hq]
   have len:=data_length_positive r
   have tail:PrintedRecords (A+r.data.length) rs t:=by
     apply PrintedRecords.transport bank.2
     intro z hz
     have ne:z≠A+1:=by omega
     simp [t,applyBlock,Op.apply,writeNat,next,ptr,ne]
   obtain ⟨nextbank,outside,endptr⟩:=ih (A+r.data.length) t hp hq' tail
   rw [patches,UniformFixedNetworkScheduleMachine.applyBlock_append]
   refine ⟨⟨?_,?_⟩,?_,?_⟩
   · intro j hj
     have hj':j<r.data.length:=by simpa only [data_columns_length] using hj
     rw [outside (A+j) (Or.inl (by omega)),data_columns q r j hj']
     by_cases j1:j=1
     · subst j;simp [t,applyBlock,Op.apply,writeNat,next,ptr,hq]
     · have ne:A+j≠A+1:=by omega
       simp only [j1,ite_false]
       rw [show t.natHeap (A+j)=s.natHeap (A+j) by
         change Function.update s.natHeap (s.natReg 2700) (some (s.natReg 2599)) (A+j)=s.natHeap (A+j)
         rw [ptr];exact Function.update_of_ne ne _ _]
       exact bank.1 j hj'
   · simpa only [data_columns_length] using nextbank
   · intro z hz
     have tailout:z<A+r.data.length∨A+r.data.length+(serialize rs).length≤z:=by
       rw [serialize_length_cons] at hz;omega
     rw [outside z tailout]
     have ne:z≠A+1:=by rw [serialize_length_cons] at hz;omega
     simp [t,applyBlock,Op.apply,writeNat,next,ptr,ne]
   · rw [serialize_length_cons];simpa only [Nat.add_assoc] using endptr

lemma printer_code (rs:List Record) :
 UniformAssembly.CodeAt (UniformFixedNetworkScheduleMachine.program (serialize rs)) (program rs) 0 (continuation rs) :=
 UniformAssembly.embed_code [] _ _ _
lemma patch_code (rs:List Record) : BlockAt (patchBlock rs) (program rs) (continuation rs) := by
 intro i hi
 simp only [program,UniformAssembly.embed,List.nil_append]
 rw [List.getElem?_append_right (by simp [continuation,UniformFixedNetworkScheduleMachine.program_length])]
 simp only [List.length_map,UniformFixedNetworkScheduleMachine.program_length,continuation,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,List.getElem?_eq_getElem hi]
 rfl
lemma halt_at (rs:List Record) :
 (program rs)[continuation rs+(patchBlock rs).length]?=some .halt := by
 simp [program,UniformAssembly.embed,continuation,UniformFixedNetworkScheduleMachine.program_length]

/-- One fixed finite program for a fixed template, independent of runtime q
and input length. There are no host writes between template and patch phases. -/
theorem execution (rs:List Record) (A B q n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (hq:s.natReg 2599=q) (pc:s.pc=0) (hs:WordBound B s)
 (values:∀v∈serialize rs,v≤B) (extent:A+(serialize rs).length+1≤B)
 (code:3*(serialize rs).length+3*rs.length+7≤B) : ∃u,
 BoundedExecution (program rs) n x B s (3*(serialize rs).length+3*rs.length+7) u ∧
 PrintedRecords A (rs.map (Record.withColumns q)) u ∧
 (∀z,z<A∨A+(serialize rs).length≤z→u.natHeap z=s.natHeap z) ∧ Frame s u := by
 obtain ⟨t,run,bank,oldOutside,oldFrame,_ptr⟩:=UniformFixedNetworkScheduleMachine.printer_execution (serialize rs) A B n x s base pc hs values
   (by omega) (by omega)
 let t':State:={t with pc:=continuation rs}
 have placed:BoundedRuns (program rs) n x B s (continuation rs) t':=by
   have h:=UniformAssembly.BoundedExecution.placed (C:=B) (printer_code rs) (by omega) (by unfold continuation;omega) run
   rw [placed_zero] at h
   exact h
 have bt:t'.natReg 2600=A:=by
   change t.natReg 2600=A
   rw [oldFrame.natReg 2600 (by decide) (by decide) (by decide) (by decide)];exact base
 have qt:t'.natReg 2599=q:=by
   change t.natReg 2599=q
   rw [oldFrame.natReg 2599 (by decide) (by decide) (by decide) (by decide)];exact hq
 let ready:=applyBlock setup t'
 have pointer:ready.natReg 2700=A+1:=by simp [ready,setup,applyBlock,Op.apply,writeNat,next,bt]
 have qr:ready.natReg 2599=q:=by simp [ready,setup,applyBlock,Op.apply,writeNat,next,qt]
 have qb:q≤B:=by rw [← hq];exact hs.2.1 2599
 have safe:=patches_safe rs A B q ready pointer qr qb extent
 have read:readable (patchBlock rs) t':=by simpa [patchBlock,setup,readable,Op.readable,ready,applyBlock] using safe.1
 have peakb:peak (patchBlock rs) t'≤B:=by
   have ab:A+1≤B:=by omega
   have ob:1≤B:=by omega
   simpa [patchBlock,setup,peak,Op.peak,Op.apply,writeNat,next,bt,max_le_iff,ab,ob,ready,applyBlock] using safe.2
 have patchRun:=block_runs (patchBlock rs) (program rs) (continuation rs) n B x t' (patch_code rs) rfl placed.final_bound
   (by rw [patchBlock_length];unfold continuation;omega) read peakb
 let u:=applyBlock (patchBlock rs) t'
 have up:u.pc=continuation rs+(patchBlock rs).length:=by simp [u,UniformTensorMonomialMachine.applyBlock_pc,t']
 have halt:BoundedExecution (program rs) n x B u 1 u:=.halt patchRun.final_bound (by simp [step,up,halt_at])
 have source:PrintedRecords A rs ready:=by
   apply PrintedRecords.transport bank.records
   intro z _;rfl
 obtain ⟨newBank,outside,_endptr⟩:=patches_spec rs A q ready pointer qr source
 refine ⟨u,?_,?_,?_,?_⟩
 · convert placed.executes (patchRun.executes halt) using 1
   rw [patchBlock_length];unfold continuation;omega
 · simpa [u,patchBlock,UniformFixedNetworkScheduleMachine.applyBlock_append,ready] using newBank
 · intro z hz
   rw [show u=applyBlock (patches rs) ready by change applyBlock (setup++patches rs) t'=applyBlock (patches rs) (applyBlock setup t');exact UniformFixedNetworkScheduleMachine.applyBlock_append _ _ _]
   rw [outside z hz]
   change t.natHeap z=s.natHeap z
   exact oldOutside z hz
 · exact (Frame.of_printer oldFrame).pc (continuation rs) |>.trans ((setup_frame t').trans (patches_frame rs ready))

/-- The astronomical template stays symbolic. Only q is runtime state, so the
same finite bytecode works for all q and all unrelated input lengths. -/
def fixedProgram : Program := program UniformFixedNetworkScheduleMachine.baseSchedule
theorem fixed_execution (A B q n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (hq:s.natReg 2599=q) (pc:s.pc=0) (hs:WordBound B s)
 (literals:UniformFixedNetworkScheduleMachine.literalCap (serialize UniformFixedNetworkScheduleMachine.baseSchedule)≤B)
 (extent:A+(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+1≤B)
 (code:3*(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+3*UniformFixedNetworkScheduleMachine.baseSchedule.length+7≤B) : ∃u,
 BoundedExecution fixedProgram n x B s (3*(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+3*UniformFixedNetworkScheduleMachine.baseSchedule.length+7) u ∧
 PrintedRecords A (UniformFixedNetworkScheduleMachine.scheduleRecords q) u ∧
 (∀z,z<A∨A+(serialize UniformFixedNetworkScheduleMachine.baseSchedule).length≤z→u.natHeap z=s.natHeap z) ∧ Frame s u := by
 exact execution UniformFixedNetworkScheduleMachine.baseSchedule A B q n x s base hq pc hs
   (fun v hv=>(UniformFixedNetworkScheduleMachine.member_le_cap _ v hv).trans literals) extent code

end
end ExactFourierCircuits.UniformFixedNetworkLiteralDecoderMachine
