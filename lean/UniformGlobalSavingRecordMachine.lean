import UniformFixedNetworkScheduleMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalSavingRecordMachine
open UniformMachine UniformTensorMonomialMachine

/-- A fixed field is printed literally; a column field is read from Nat4300.
Only the column header varies with the input. There is no graph/action oracle. -/
def resolve (q : ℕ) (xs : List (Option ℕ)) : List ℕ := xs.map (fun x => x.getD q)
def cells : List (Option ℕ) → List Op
 | [] => []
 | x :: xs => [match x with
     | some v => .literal 2602 v
     | none => .add 2602 4300 2604,
    .putNat 2601 2602, .add 2601 2601 2603] ++ cells xs
def boot : List Op := [.literal 2603 1,.literal 2604 0,.add 2601 4301 2604]
def template (r : UniformFixedNetworkScheduleMachine.Record) : List (Option ℕ) :=
 [some r.opcode,none,some r.width,some r.dest,some r.source,
  some r.inverse,some r.dimension,some r.scalar] ++ r.directions.map some
def templates (rs : List UniformFixedNetworkScheduleMachine.Record) : List (Option ℕ) := (rs.map template).flatten
noncomputable def fixedTemplate := templates UniformFixedNetworkScheduleMachine.baseSchedule
noncomputable def program : Program := (boot ++ cells fixedTemplate).map Op.code ++ [.halt]

lemma resolve_cons (q : ℕ) (x : Option ℕ) (xs : List (Option ℕ)) :
 resolve q (x::xs)=x.getD q::resolve q xs := rfl
lemma resolve_length (q : ℕ) (xs : List (Option ℕ)) : (resolve q xs).length=xs.length := by
 simp [resolve]
lemma resolve_template (q : ℕ) (r : UniformFixedNetworkScheduleMachine.Record) : resolve q (template r)=(r.withColumns q).data := by
 simp [resolve,template,UniformFixedNetworkScheduleMachine.Record.data,UniformFixedNetworkScheduleMachine.Record.header,UniformFixedNetworkScheduleMachine.Record.withColumns,List.map_map]
lemma resolve_templates (q : ℕ) (rs : List UniformFixedNetworkScheduleMachine.Record) :
 resolve q (templates rs)=UniformFixedNetworkScheduleMachine.serialize (rs.map (UniformFixedNetworkScheduleMachine.Record.withColumns q)) := by
 simp only [resolve,templates,List.map_flatten,List.map_map,UniformFixedNetworkScheduleMachine.serialize]
 congr 1
 apply List.map_congr_left
 intro r _
 exact resolve_template q r
lemma resolve_fixed (q : ℕ) : resolve q fixedTemplate=UniformFixedNetworkScheduleMachine.scheduleData q :=
 resolve_templates q UniformFixedNetworkScheduleMachine.baseSchedule
lemma cells_length (xs : List (Option ℕ)) : (cells xs).length=3*xs.length := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp [cells,ih];omega
lemma program_length : program.length=3*fixedTemplate.length+4 := by
 simp [program,boot,cells_length]

noncomputable section
lemma cells_apply (xs : List (Option ℕ)) (q : ℕ) (s : State)
 (hq:s.natReg 4300=q) (hz:s.natReg 2604=0) :
 applyBlock (cells xs) s=applyBlock (UniformFixedNetworkScheduleMachine.cells (resolve q xs)) s := by
 induction xs generalizing s with
 | nil => rfl
 | cons x xs ih =>
   cases x with
   | none =>
     simp only [cells,resolve_cons,Option.getD_none,UniformFixedNetworkScheduleMachine.cells,UniformFixedNetworkScheduleMachine.applyBlock_append]
     have head:applyBlock [.add 2602 4300 2604,.putNat 2601 2602,.add 2601 2601 2603] s=
       applyBlock [.literal 2602 q,.putNat 2601 2602,.add 2601 2601 2603] s := by
       simp [applyBlock,Op.apply,hq,hz]
     rw [head]
     apply ih
     · simpa [applyBlock,Op.apply,writeNat,next] using hq
     · simpa [applyBlock,Op.apply,writeNat,next] using hz
   | some v =>
     simp only [cells,resolve_cons,Option.getD_some,UniformFixedNetworkScheduleMachine.cells,UniformFixedNetworkScheduleMachine.applyBlock_append]
     apply ih
     · simpa [applyBlock,Op.apply,writeNat,next] using hq
     · simpa [applyBlock,Op.apply,writeNat,next] using hz
lemma cells_readable (xs : List (Option ℕ)) (s : State) : readable (cells xs) s := by
 induction xs generalizing s with
 | nil => trivial
 | cons x xs ih =>
   cases x <;> simp [cells,readable,Op.readable,ih]
lemma cells_peak (xs : List (Option ℕ)) (q : ℕ) (s : State)
 (hq:s.natReg 4300=q) (hz:s.natReg 2604=0) :
 peak (cells xs) s=peak (UniformFixedNetworkScheduleMachine.cells (resolve q xs)) s := by
 induction xs generalizing s with
 | nil => rfl
 | cons x xs ih =>
   cases x with
   | none =>
     have hq':(applyBlock [.literal 2602 q,.putNat 2601 2602,.add 2601 2601 2603] s).natReg 4300=q := by
       simpa [applyBlock,Op.apply,writeNat,next] using hq
     have hz':(applyBlock [.literal 2602 q,.putNat 2601 2602,.add 2601 2601 2603] s).natReg 2604=0 := by
       simpa [applyBlock,Op.apply,writeNat,next] using hz
     have tail:=ih _ hq' hz'
     simpa [cells,resolve_cons,UniformFixedNetworkScheduleMachine.cells,peak,Op.peak,Op.apply,writeNat,next,applyBlock,hq,hz] using congrArg (fun z=>max q (max (s.natReg 2601+s.natReg 2603) z)) tail
   | some v =>
     have hq':(applyBlock [.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603] s).natReg 4300=q := by
       simpa [applyBlock,Op.apply,writeNat,next] using hq
     have hz':(applyBlock [.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603] s).natReg 2604=0 := by
       simpa [applyBlock,Op.apply,writeNat,next] using hz
     have tail:=ih _ hq' hz'
     simpa [cells,resolve_cons,UniformFixedNetworkScheduleMachine.cells,peak,Op.peak,Op.apply,writeNat,next,applyBlock,hq,hz] using congrArg (fun z=>max v (max (s.natReg 2601+s.natReg 2603) z)) tail
lemma whole_code : BlockAt (boot++cells fixedTemplate) program 0 := by
 intro i hi
 simp only [program,Nat.zero_add]
 rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,
   List.getElem?_eq_getElem hi,Option.map_some]
lemma halt_at : program[3*fixedTemplate.length+3]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simp [boot,cells_length])]
 simp [boot,cells_length]

/-- A single literal program, outside forall q, writes the actual complete
stage-major record tape. Every literal, column-header write, store and pointer
increment is charged. The output tape is a conclusion, not an entry. -/
theorem execution (q A B n : ℕ) (x : Fin n → ℂ) (s : State)
 (column:s.natReg 4300=q) (address:s.natReg 4301=A) (pc:s.pc=0) (hs:WordBound B s)
 (literals:q+UniformFixedNetworkScheduleMachine.literalCap (UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule)≤B)
 (extent:A+(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length≤B)
 (code:3*(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+4≤B) :
 ∃u,BoundedExecution program n x B s (3*(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+4) u ∧
 UniformFixedNetworkScheduleMachine.PrintedRecords A (UniformFixedNetworkScheduleMachine.scheduleRecords q) u ∧
 (∀z,z<A∨A+(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length≤z→u.natHeap z=s.natHeap z) ∧
 UniformFixedNetworkScheduleMachine.Frame s u ∧ u.pc=3*(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+3 := by
 have len:fixedTemplate.length=(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length := by
   rw [←resolve_length 0 fixedTemplate,resolve_fixed,UniformFixedNetworkScheduleMachine.schedule_size_independent]
 let ready:=applyBlock boot s
 have ptr:ready.natReg 2601=A := by simp [ready,boot,applyBlock,Op.apply,writeNat,next,address]
 have one:ready.natReg 2603=1 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have zero:ready.natReg 2604=0 := by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have cq:ready.natReg 4300=q := by simpa [ready,boot,applyBlock,Op.apply,writeNat,next] using column
 have values:∀v∈resolve q fixedTemplate,v≤B := by
   rw [resolve_fixed]
   intro v hv;exact (UniformFixedNetworkScheduleMachine.schedule_literal_bound q v hv).trans literals
 have size:A+(resolve q fixedTemplate).length≤B := by simpa [resolve_length,len] using extent
 have safe:=UniformFixedNetworkScheduleMachine.cells_safe (resolve q fixedTemplate) A B ready ptr one values size
 have read:readable (boot++cells fixedTemplate) s := by
   simpa [boot,readable,Op.readable,ready,applyBlock] using cells_readable fixedTemplate ready
 have bound:peak (boot++cells fixedTemplate) s≤B := by
   have ab:A≤B := by omega
   have ob:1≤B := by omega
   have cs:peak (cells fixedTemplate) ready≤B := by rw [cells_peak _ q ready cq zero];exact safe.2
   simpa [boot,peak,Op.peak,Op.apply,writeNat,next,address,max_le_iff,ab,ob,ready,applyBlock] using cs
 have run:=block_runs (boot++cells fixedTemplate) program 0 n B x s whole_code pc hs
   (by simp [boot,cells_length,len];omega) read bound
 let u:=applyBlock (boot++cells fixedTemplate) s
 have up:u.pc=3*fixedTemplate.length+3 := by
   simp [u,UniformTensorMonomialMachine.applyBlock_pc,pc,boot,cells_length]
 have halt:BoundedExecution program n x B u 1 u := .halt run.final_bound (by simp [step,up,halt_at])
 have eq:u=applyBlock (UniformFixedNetworkScheduleMachine.cells (resolve q fixedTemplate)) ready := by
   dsimp [u]
   rw [UniformFixedNetworkScheduleMachine.applyBlock_append];exact cells_apply _ q ready cq zero
 obtain ⟨bank,outside,_endptr⟩:=UniformFixedNetworkScheduleMachine.cells_printed (resolve q fixedTemplate) A ready ptr one
 have bootFrame:UniformFixedNetworkScheduleMachine.Frame s ready := by
   refine ⟨rfl,rfl,rfl,rfl,?_⟩
   intro r h1 h2 h3 h4;simp [ready,boot,applyBlock,Op.apply,writeNat,next,h1,h3,h4]
 refine ⟨u,?_,?_,?_,?_,?_⟩
 · convert run.executes halt using 1; simp [boot,cells_length,len]
 · rw [←eq,resolve_fixed] at bank
   exact bank.records
 · intro z hz
   rw [eq,outside z (by simpa [resolve_length,len] using hz)]
   rfl
 · rw [eq];exact bootFrame.trans (UniformFixedNetworkScheduleMachine.cells_frame _ ready)
 · simpa only [len] using up
end
end ExactFourierCircuits.UniformGlobalSavingRecordMachine
