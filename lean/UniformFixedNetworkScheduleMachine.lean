import UniformFixedCoefficientCodec
import UniformTensorMonomialMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkScheduleMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open OAI.ExactFourier BinaryFrames BinaryTensor FramedScheduleWords UniformFixedNetwork
open UniformFixedCoefficientCodec
open scoped BigOperators

/-- One fixed Nat-only writer. Header2600 is an ordinary fresh output address.
Each cell charges its literal, store and pointer increment. There is no input,
root, scalar literal, coefficient callback or supplied table. -/
def boot : List Op := [.literal 2603 1,.literal 2604 0,.add 2601 2600 2604]
def cells : List ℕ→List Op
 | []=>[]
 | v::vs=>[.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603]++cells vs
def program (data:List ℕ) : Program := (boot++cells data).map Op.code++[.halt]
lemma cells_length (data:List ℕ) : (cells data).length=3*data.length := by
 induction data with
 | nil=>rfl
 | cons v vs ih=>simp [cells,ih];omega
lemma program_length (data:List ℕ) : (program data).length=3*data.length+4 := by
 simp [program,boot,cells_length]

noncomputable section

lemma applyBlock_append (a b:List Op) (s:State) : applyBlock (a++b) s=applyBlock b (applyBlock a s) := by
 induction a generalizing s with
 | nil=>rfl
 | cons o a ih=>simp [applyBlock,ih]

lemma cells_safe (data:List ℕ) (A B:ℕ) (s:State)
 (ptr:s.natReg 2601=A) (one:s.natReg 2603=1)
 (values:∀v∈data,v≤B) (extent:A+data.length≤B) :
 readable (cells data) s ∧ peak (cells data) s≤B := by
 induction data generalizing A s with
 | nil=>simp [cells,readable,peak]
 | cons v vs ih=>
   have hv:v≤B:=values v (by simp)
   have rest:=ih (A+1) (applyBlock [.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603] s)
     (by simp [applyBlock,Op.apply,writeNat,next,ptr,one])
     (by simp [applyBlock,Op.apply,writeNat,next,one])
     (by intro u hu;exact values u (by simp [hu])) (by simp only [List.length_cons] at extent;omega)
   simpa [cells,readable,peak,applyBlock,Op.readable,Op.peak,Op.apply,writeNat,next,ptr,one,
     max_le_iff,hv,show A≤B by simp only [List.length_cons] at extent;omega,
     show A+1≤B by simp only [List.length_cons] at extent;omega] using rest

structure Frame (s u:State) : Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg : ∀ (r : ℕ), r ≠ 2601 → r ≠ 2602 → r ≠ 2603 → r ≠ 2604 → u.natReg r = s.natReg r
lemma Frame.trans {s u v:State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h1 h2 h3 h4=>(g.natReg r h1 h2 h3 h4).trans (f.natReg r h1 h2 h3 h4)⟩
lemma boot_frame (s:State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r h1 h2 h3 h4;simp [boot,applyBlock,Op.apply,writeNat,next,h1,h3,h4]
lemma cells_frame (data:List ℕ) (s:State) : Frame s (applyBlock (cells data) s) := by
 induction data generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,fun _ _ _ _ _=>rfl⟩
 | cons v vs ih=>
   have head:Frame s (applyBlock [.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603] s):=by
     refine ⟨rfl,rfl,rfl,rfl,?_⟩
     intro r h1 h2 h3 h4;simp [applyBlock,Op.apply,writeNat,next,h1,h2]
   simp only [cells,applyBlock_append];exact head.trans (ih _)

def Printed (A:ℕ) (data:List ℕ) (s:State) : Prop := ∀j (hj:j<data.length),s.natHeap (A+j)=some (data[j]'hj)
lemma cells_printed (data:List ℕ) (A:ℕ) (s:State) (ptr:s.natReg 2601=A) (one:s.natReg 2603=1) :
 Printed A data (applyBlock (cells data) s) ∧
 (∀z,z<A∨A+data.length≤z→(applyBlock (cells data) s).natHeap z=s.natHeap z) ∧
 (applyBlock (cells data) s).natReg 2601=A+data.length := by
 induction data generalizing A s with
 | nil=>exact ⟨by intro j hj;simp at hj,fun _ _=>rfl,by simpa [cells,applyBlock] using ptr⟩
 | cons v vs ih=>
   let t:=applyBlock [.literal 2602 v,.putNat 2601 2602,.add 2601 2601 2603] s
   have hp:t.natReg 2601=A+1:=by simp [t,applyBlock,Op.apply,writeNat,next,ptr,one]
   have ho:t.natReg 2603=1:=by simp [t,applyBlock,Op.apply,writeNat,next,one]
   obtain ⟨bank,outside,endptr⟩:=ih (A+1) t hp ho
   rw [cells,applyBlock_append]
   refine ⟨?_,?_,?_⟩
   · intro j hj
     cases j with
     | zero=>
       change (applyBlock (cells vs) t).natHeap A=some v
       rw [outside A (Or.inl (by omega))];simp [t,applyBlock,Op.apply,writeNat,next,ptr]
     | succ j=>
       have h:=bank j (by simp only [List.length_cons] at hj;omega)
       simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
   · intro z hz
     rw [outside z (by simp only [List.length_cons] at hz;omega)]
     have ne:z≠A:=by simp only [List.length_cons] at hz;omega
     simp [t,applyBlock,Op.apply,writeNat,next,ptr,ne]
   · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endptr

lemma whole_code (data:List ℕ) : BlockAt (boot++cells data) (program data) 0 := by
 intro i hi
 simp only [program,Nat.zero_add]
 rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,
   List.getElem?_eq_getElem hi,Option.map_some]
lemma halt_at (data:List ℕ) : (program data)[3*data.length+3]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simp [boot,cells_length])]
 simp [boot,cells_length]

/-- All metadata/index stores are counted. Every literal and touched address
is bounded; data/root/scalar/output state and the heap outside the new bank
are retained. The output bank is derived, never an entry premise. -/
theorem printer_execution (data:List ℕ) (A B n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (pc:s.pc=0) (hs:WordBound B s)
 (values:∀v∈data,v≤B) (extent:A+data.length≤B) (code:3*data.length+4≤B) :
 ∃u,BoundedExecution (program data) n x B s (3*data.length+4) u ∧
 Printed A data u ∧ (∀z,z<A∨A+data.length≤z→u.natHeap z=s.natHeap z) ∧
 Frame s u ∧ u.natReg 2601=A+data.length := by
 let ready:=applyBlock boot s
 have pointer:ready.natReg 2601=A:=by simp [ready,boot,applyBlock,Op.apply,writeNat,next,base]
 have one:ready.natReg 2603=1:=by simp [ready,boot,applyBlock,Op.apply,writeNat,next]
 have safe:=cells_safe data A B ready pointer one values extent
 have read:readable (boot++cells data) s:=by
   simpa [boot,readable,Op.readable,ready,applyBlock] using safe.1
 have bound:peak (boot++cells data) s≤B:=by
   have ab:A≤B:=by omega
   have ob:1≤B:=by omega
   simpa [boot,peak,Op.peak,Op.apply,writeNat,next,base,max_le_iff,ab,ob,ready,applyBlock] using safe.2
 have run:=block_runs (boot++cells data) (program data) 0 n B x s (whole_code data) pc hs
   (by simp [boot,cells_length];omega) read bound
 let u:=applyBlock (boot++cells data) s
 have up:u.pc=3*data.length+3:=by simp [u,UniformTensorMonomialMachine.applyBlock_pc,pc,boot,cells_length]
 have halt:BoundedExecution (program data) n x B u 1 u:=.halt run.final_bound (by simp [step,up,halt_at])
 obtain ⟨bank,outside,finalptr⟩:=cells_printed data A ready pointer one
 refine ⟨u,?_,?_,?_,?_,?_⟩
 · convert run.executes halt using 1; simp [boot,cells_length]
 · simpa [u,applyBlock_append,ready] using bank
 · intro z hz;simpa [u,applyBlock_append,ready,boot,applyBlock,Op.apply,writeNat,next] using outside z hz
 · rw [show u=applyBlock (cells data) ready from applyBlock_append _ _ _]
   exact (boot_frame s).trans (cells_frame data ready)
 · simpa [u,applyBlock_append,ready] using finalptr

/-- Eight literal fields per descriptor. Direction words are inline binary
coordinate tables. Opcode0=residual child,1=pointwise shear,2=block boundary,
3=Y translation,4=signed bank exchange,5=ordinary padding,6=global layout.
No field stores a complex value or executable callback. -/
structure Record where
 opcode : ℕ
 columns : ℕ
 width : ℕ
 dest : ℕ
 source : ℕ
 inverse : ℕ
 dimension : ℕ
 scalar : ℕ
 directions : List ℕ

def Record.header (r:Record) : List ℕ :=
 [r.opcode,r.columns,r.width,r.dest,r.source,r.inverse,r.dimension,r.scalar]
lemma Record.header_length (r:Record) : r.header.length=8 := rfl
def Record.data (r:Record) : List ℕ := r.header++r.directions
lemma Record.data_length (r:Record) : r.data.length=8+r.directions.length := by rw [Record.data,List.length_append,Record.header_length]

def serialize (rs:List Record) : List ℕ := (rs.map Record.data).flatten

def PrintedRecords (A:ℕ) : List Record→State→Prop
 | [],_=>True
 | r::rs,s=>Printed A r.data s ∧ PrintedRecords (A+r.data.length) rs s

lemma Printed.split {A:ℕ} {a b:List ℕ} {s:State} (h:Printed A (a++b) s) :
 Printed A a s ∧ Printed (A+a.length) b s := by
 constructor
 · intro j hj
   have hh:=h j (by simp;omega)
   simpa only [List.getElem_append_left hj] using hh
 · intro j hj
   have hh:=h (a.length+j) (by simp;omega)
   have eq:(a++b)[a.length+j]'(by simp;omega)=b[j]'hj:=by
     rw [List.getElem_append_right (by omega)];simp
   rw [eq] at hh
   simpa only [Nat.add_assoc] using hh

lemma Printed.records {A:ℕ} {rs:List Record} {s:State} (h:Printed A (serialize rs) s) : PrintedRecords A rs s := by
 induction rs generalizing A with
 | nil=>trivial
 | cons r rs ih=>
   change Printed A (r.data++serialize rs) s at h
   exact ⟨h.split.1,ih h.split.2⟩

/-- A child can read every header field and every direction coordinate at its
charged offset. This theorem is about physical cells, not a child execution. -/
lemma Printed.body {A:ℕ} {r:Record} {s:State} (h:Printed A r.data s) (j:ℕ) (hj:j<r.directions.length) :
 s.natHeap (A+8+j)=some (r.directions[j]'hj) := by
 have bank:Printed (A+r.header.length) r.directions s:=h.split.2
 simpa only [Record.header_length,Nat.add_assoc] using bank j hj
lemma Printed.header {A:ℕ} {r:Record} {s:State} (h:Printed A r.data s) (j:Fin 8) :
 s.natHeap (A+j.val)=some (r.header[j.val]'(by rw [Record.header_length];exact j.isLt)) := by
 have hj:j.val<r.header.length:=by rw [Record.header_length];exact j.isLt
 have hh:=h j.val (by rw [Record.data_length];omega)
 simpa only [Record.data,List.getElem_append_left hj] using hh

def bitWords {n:ℕ} (z:Vec (Fin n)) : List ℕ := List.ofFn (fun j=> (z j).val)
lemma bitWords_length {n:ℕ} (z:Vec (Fin n)) : (bitWords z).length=n := by simp [bitWords]
lemma bitWords_bound {n:ℕ} (z:Vec (Fin n)) (v:ℕ) (hv:v∈bitWords z) : v≤1 := by
 obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hv
 have h: (z j).val<2:=ZMod.val_lt (z j)
 omega

def edgeBits {n:ℕ} {A B:Label n} (e:NestedEdge A B) : List ℕ :=
 List.ofFn (fun z:Fin (e.dimension*n)=>
   ((edgeVectors e ((finProdFinEquiv.symm z).1)) ((finProdFinEquiv.symm z).2)).val)
lemma edgeBits_length {n:ℕ} {A B:Label n} (e:NestedEdge A B) : (edgeBits e).length=e.dimension*n := by simp [edgeBits]
lemma edgeBits_bound {n:ℕ} {A B:Label n} (e:NestedEdge A B) (v:ℕ) (hv:v∈edgeBits e) : v≤1 := by
 obtain ⟨z,rfl⟩:=List.mem_ofFn.mp hv
 have h: ((edgeVectors e ((finProdFinEquiv.symm z).1)) ((finProdFinEquiv.symm z).2)).val<2:=ZMod.val_lt _
 omega
lemma edgeBits_coordinate {n:ℕ} {A B:Label n} (e:NestedEdge A B) (k:Fin e.dimension) (j:Fin n) :
 (edgeBits e)[(finProdFinEquiv (k,j)).val]'(by rw [edgeBits_length];exact (finProdFinEquiv (k,j)).isLt)=
 (edgeVectors e k j).val := by
 simp only [edgeBits,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

/-- Original-width directions are shared across columns. q changes one header
field, not the basis table, and no binary address-space enumeration is printed. -/
def macroRecord {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R) : EncodedMacro r n→Record
 | .edge _ _ role e=>⟨0,q,n,(embedding role).val,0,if edgeInverse e then 1 else 0,e.dimension,0,edgeBits e⟩
 | .shear d s _ k _=>⟨1,q,n,(embedding d).val,(embedding s).val,0,0,k.val,[]⟩
lemma macroRecord_length {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R) (a:EncodedMacro r n) :
 (macroRecord q embedding a).data.length=8+(decodeMacro a).residuals*n := by
 cases a <;> simp [Record.data_length,macroRecord,edgeBits_length,decodeMacro,Macro.residuals]
lemma macroRecord_size_independent {r R n:ℕ} (q t:ℕ) (embedding:Fin r↪Fin R) (a:EncodedMacro r n) :
 (macroRecord q embedding a).data.length=(macroRecord t embedding a).data.length := by rw [macroRecord_length,macroRecord_length]
lemma macroRecord_geometry {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R) (a:EncodedMacro r n) :
 ∀v∈(macroRecord q embedding a).data,v≤R+q+n+(decodeMacro a).residuals+8 := by
 cases a with
 | edge A B role e=>
   intro v hv
   rcases List.mem_append.mp hv with hv | hv
   · simp only [macroRecord,Record.header,List.mem_cons,List.not_mem_nil,or_false] at hv
     have hr:=(embedding role).isLt
     rcases hv with h|h|h|h|h|h|h|h <;> subst v
     all_goals simp only [decodeMacro,Macro.residuals]
     all_goals first | omega | split <;> omega
   · have b:=edgeBits_bound e v hv
     simp only [decodeMacro,Macro.residuals];omega
 | shear d s ne k nz=>
   intro v hv
   simp only [macroRecord,Record.data,Record.header,List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hv
   have hd:=(embedding d).isLt;have hs:=(embedding s).isLt;have hk:=k.isLt
   rcases hv with h|h|h|h|h|h|h|h <;> subst v <;> simp only [decodeMacro,Macro.residuals] <;> omega

/-- The physical edge descriptor supplies orientation and each exact bit of
its actual residual basis. The copied directions are specified by the existing
literal column-coordinate theorem; executing that child remains separate. -/
theorem residual_descriptor {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R) {A B:Label n}
 (role:Fin r) (e:NestedEdge A B) (base:ℕ) (s:State)
 (printed:Printed base (macroRecord q embedding (.edge A B role e)).data s) :
 s.natHeap (base+3)=some (embedding role).val ∧
 s.natHeap (base+5)=some (if edgeInverse e then 1 else 0) ∧
 s.natHeap (base+6)=some e.dimension ∧
 (∀k:Fin e.dimension,∀j:Fin n,s.natHeap (base+8+(finProdFinEquiv (k,j)).val)=some (edgeVectors e k j).val) := by
 refine ⟨?_,?_,?_,?_⟩
 · simpa [macroRecord,Record.header] using printed.header (3:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (5:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (6:Fin 8)
 · intro k j
   have h:=printed.body (finProdFinEquiv (k,j)).val (by simp [macroRecord,edgeBits_length];exact (finProdFinEquiv (k,j)).isLt)
   simp only [macroRecord] at h
   rw [edgeBits_coordinate] at h
   exact h

/-- A scalar child receives the original finite code, rather than a complex
literal. Decoding that code is exactly the existing five-valued compiler. -/
theorem shear_descriptor {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R)
 (d t:Fin r) (distinct:d≠t) (k:Fin 5) (nonzero:decode k≠0) (base:ℕ) (s:State)
 (printed:Printed base (macroRecord (n:=n) q embedding (.shear d t distinct k nonzero)).data s) :
 s.natHeap base=some 1 ∧ s.natHeap (base+1)=some q ∧
 s.natHeap (base+3)=some (embedding d).val ∧
 s.natHeap (base+4)=some (embedding t).val ∧ s.natHeap (base+7)=some k.val := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · simpa [macroRecord,Record.header] using printed.header (0:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (1:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (3:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (4:Fin 8)
 · simpa [macroRecord,Record.header] using printed.header (7:Fin 8)

abbrev seedWidth := ExplicitSeedBudget.h^3
abbrev actualRoles := TripleSchedule.Global.size ExplicitSeedBudget.h
abbrev Invocation := MasterBudget.Invocation ExplicitSeedBudget.h

def encodedBlock (a:Invocation) : List (EncodedMacro (fixedBlock a).width seedWidth) :=
 encodeTape (blockTape (fixedBlock a)) (by exact fixed_block_small a)
def blockRecords (q:ℕ) (a:Invocation) : List Record :=
 (encodedBlock a).map (macroRecord q (fixedBlock a).embedding)
def blockBoundary (q:ℕ) (a:Invocation) : Record :=
 ⟨2,q,seedWidth,a.1.val,(fixedBlock a).width,0,0,0,
  List.ofFn (fun i:Fin (fixedBlock a).width=>((fixedBlock a).embedding i).val)⟩
def bankPairs : List (ℕ×ℕ) :=
 (Finset.univ.toList:List (TripleNetwork.Bank (Fin ExplicitSeedBudget.h))).map (fun d=>
  ((TripleSchedule.Global.coordinates ExplicitSeedBudget.h (.inl (0,d))).val,
   (TripleSchedule.Global.coordinates ExplicitSeedBudget.h (.inl (1,d))).val))
def Record.withColumns (q:ℕ) (r:Record) : Record := {r with columns:=q}
lemma Record.withColumns_literal (q o n d t i k c:ℕ) (b:List ℕ) :
 Record.withColumns q ⟨o,0,n,d,t,i,k,c,b⟩=⟨o,q,n,d,t,i,k,c,b⟩ := rfl
lemma Record.withColumns_twice (q t:ℕ) (r:Record) :
 Record.withColumns q (Record.withColumns t r)=Record.withColumns q r := by cases r;rfl
def rawTerminalRecords : List Record :=
 [⟨3,0,seedWidth,0,0,0,bankPairs.length,0,
   ((Finset.univ.toList:List (TripleNetwork.Bank (Fin ExplicitSeedBudget.h))).map (fun d=>
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h (.inl (1,d))).val::
    bitWords (TripleColumnAction.globalDirection 1 d))).flatten⟩,
  ⟨4,0,seedWidth,0,0,0,bankPairs.length,0,
   (bankPairs.map (fun p=>[p.1,p.2,4,0])).flatten⟩,
  ⟨5,0,seedWidth,actualRoles,W-actualRoles,0,0,0,[]⟩]
def terminalRecords (q:ℕ) : List Record := rawTerminalRecords.map (Record.withColumns q)
/-- All seed geometry is a fixed finite table; only column headers vary. -/
def baseSchedule : List Record :=
 ⟨6,0,seedWidth,actualRoles,W,0,ExplicitSeedBudget.roleBits,0,[]⟩::
 (fixedInvocations.map (fun a=>blockBoundary 0 a::blockRecords 0 a)).flatten++terminalRecords 0
def scheduleRecords (q:ℕ) : List Record := baseSchedule.map (Record.withColumns q)
def scheduleData (q:ℕ) : List ℕ := serialize (scheduleRecords q)

lemma Record.withColumns_macro {r R n:ℕ} (q:ℕ) (embedding:Fin r↪Fin R) (a:EncodedMacro r n) :
 Record.withColumns q (macroRecord 0 embedding a)=macroRecord q embedding a := by
 cases a <;> rfl
lemma Record.withColumns_block (q:ℕ) (a:Invocation) :
 Record.withColumns q (blockBoundary 0 a)=blockBoundary q a := rfl
lemma Record.withColumns_terminal (q:ℕ) :
 (terminalRecords 0).map (Record.withColumns q)=terminalRecords q := by
 unfold terminalRecords
 rw [List.map_map]
 apply congrArg (fun f=>rawTerminalRecords.map f)
 funext r;exact Record.withColumns_twice q 0 r
lemma Record.withColumns_blockRecords (q:ℕ) (a:Invocation) :
 (blockRecords 0 a).map (Record.withColumns q)=blockRecords q a := by
 unfold blockRecords
 rw [List.map_map]
 apply congrArg (fun f=>(encodedBlock a).map f)
 funext m;exact Record.withColumns_macro q _ m
/-- Stage-major invocation order and each actual forward/reversed block tape
are retained. Terminal translation/exchange and ordinary padding come last. -/
lemma schedule_chronology (q:ℕ) : scheduleRecords q=
 ⟨6,q,seedWidth,actualRoles,W,0,ExplicitSeedBudget.roleBits,0,[]⟩::
 (fixedInvocations.map (fun a=>blockBoundary q a::blockRecords q a)).flatten++terminalRecords q := by
 unfold scheduleRecords baseSchedule
 simp only [List.map_cons,List.map_append,List.map_flatten,List.map_map]
 rw [Record.withColumns_terminal]
 have funcs:(fun a=>List.map (Record.withColumns q) (blockBoundary 0 a::blockRecords 0 a))=
   (fun a=>blockBoundary q a::blockRecords q a):=by
   funext a
   rw [List.map_cons,Record.withColumns_block,Record.withColumns_blockRecords]
 change _::(List.map (fun a=>List.map (Record.withColumns q) (blockBoundary 0 a::blockRecords 0 a)) fixedInvocations).flatten++_=_
 rw [Record.withColumns_literal,funcs]

/-- Mathematical meaning of the printed child descriptors. This operation is
not an instruction and does not assume any child action. -/
def decodedTapeWord {R n:ℕ} (q:ℕ) (b:MasterBudget.InvocationBlock R n) (small:TapeSmall (blockTape b)) :
 List (WordStep C (R*2^(q*n))) :=
 TripleSchedule.Global.liftWord b.embedding (compileTape q ((encodeTape (blockTape b) small).map decodeMacro))
lemma decodedTapeWord_actual {R n:ℕ} (q:ℕ) (b:MasterBudget.InvocationBlock R n) (small:TapeSmall (blockTape b)) :
 decodedTapeWord q b small=b.word q := by
 unfold decodedTapeWord
 rw [decode_encodeTape,blockTape_compile]
def decodedBlockWord (q:ℕ) (a:Invocation) : List (WordStep C (actualRoles*2^(q*seedWidth))) :=
 decodedTapeWord q (fixedBlock a) (by exact fixed_block_small a)
lemma decodedBlockWord_actual (q:ℕ) (a:Invocation) : decodedBlockWord q a=(fixedBlock a).word q :=
 decodedTapeWord_actual q (fixedBlock a) _
def decodedMasterWord (q:ℕ) : List (WordStep C (actualRoles*2^(q*seedWidth))) :=
 (fixedInvocations.map (decodedBlockWord q)).flatten
lemma decodedMasterWord_actual (q:ℕ) : decodedMasterWord q=TripleSchedule.Global.masterWordColumns q hh := by
 unfold decodedMasterWord
 have h:decodedBlockWord q=(fun a=>(fixedBlock a).word q):=by funext a;exact decodedBlockWord_actual q a
 rw [h];exact fixedInvocations_compile q

def decodedCorrectedWord (q:ℕ) : List (WordStep C (actualRoles*2^(q*seedWidth))) :=
 decodedMasterWord q++TerminalWords.correctionWord
  (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection q)
lemma decodedCorrectedWord_actual (q:ℕ) : decodedCorrectedWord q=correctedWord q := by
 rw [decodedCorrectedWord,decodedMasterWord_actual]
 rfl

def decodedPaddedWord (q:ℕ) : List (WordStep C (W*2^(q*m))) :=
 PaddingWords.fillWord (q*m)
  (PaddingWords.paddingRoles actualRoles ExplicitSeedBudget.roleBits MasterBudget.seed_actual_padding)
  (PaddingWords.canonicalNetworkWord actualRoles (q*m) (decodedCorrectedWord q))
lemma padding_congr {w r n:ℕ} (hw:w≤2^r) (T U:List (WordStep C (w*2^n))) (h:T=U) :
 PaddingWords.fillWord n (PaddingWords.paddingRoles w r hw) (PaddingWords.canonicalNetworkWord w n T)=
 PaddingWords.fillWord n (PaddingWords.paddingRoles w r hw) (PaddingWords.canonicalNetworkWord w n U) := by
 rw [h]
/-- One finite printer for each fixed q, for every unrelated input length n.
The code does not read n or input data. Physical tables/directions/codes are
all produced; no prepared metadata or action certificate is supplied. -/
theorem schedule_execution (q A B n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (pc:s.pc=0) (hs:WordBound B s)
 (values:∀v∈scheduleData q,v≤B) (extent:A+(scheduleData q).length≤B)
 (code:3*(scheduleData q).length+4≤B) : ∃u,
 BoundedExecution (program (scheduleData q)) n x B s (3*(scheduleData q).length+4) u ∧
 PrintedRecords A (scheduleRecords q) u ∧
 (∀z,z<A∨A+(scheduleData q).length≤z→u.natHeap z=s.natHeap z) ∧ Frame s u := by
 obtain ⟨u,run,bank,outside,frame,_ptr⟩:=printer_execution (scheduleData q) A B n x s base pc hs values extent code
 exact ⟨u,run,bank.records,outside,frame⟩

def literalCap (data:List ℕ) : ℕ := data.foldr max 0
lemma member_le_cap (data:List ℕ) (v:ℕ) (hv:v∈data) : v≤literalCap data := by
 induction data with
 | nil=>simp at hv
 | cons a data ih=>
   rcases List.mem_cons.mp hv with h|h
   · subst v;exact le_max_left _ _
   · exact (ih h).trans (le_max_right _ _)
lemma serialize_mem {rs:List Record} {v:ℕ} : v∈serialize rs↔∃r∈rs,v∈r.data := by simp [serialize]
lemma Record.withColumns_mem (q:ℕ) (r:Record) (v:ℕ) (hv:v∈(r.withColumns q).data) : v=q∨v∈r.data := by
 rcases List.mem_append.mp hv with hv|hv
 · simp only [Record.header,Record.withColumns,List.mem_cons,List.not_mem_nil,or_false] at hv
   rcases hv with h|h|h|h|h|h|h|h <;> subst v
   all_goals first | exact Or.inl rfl | right;simp [Record.data,Record.header]
 · right;exact List.mem_append.mpr (Or.inr hv)
lemma serialize_columns_length (q:ℕ) (rs:List Record) :
 (serialize (rs.map (Record.withColumns q))).length=(serialize rs).length := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>
   simp only [serialize,List.map_cons,List.flatten_cons,List.length_append] at ih ⊢
   rw [Record.data_length,Record.data_length,ih]
   rfl
lemma schedule_size_independent (q:ℕ) : (scheduleData q).length=(serialize baseSchedule).length :=
 serialize_columns_length q baseSchedule
lemma schedule_literal_bound (q v:ℕ) (hv:v∈scheduleData q) : v≤q+literalCap (serialize baseSchedule) := by
 have mem:v∈serialize (baseSchedule.map (Record.withColumns q)):=hv
 obtain ⟨r,hr,hv⟩:=serialize_mem.mp mem
 rcases List.mem_map.mp hr with ⟨original, original_mem, image⟩
 rw [← image] at hv
 rcases Record.withColumns_mem q original v hv with h|h
 · subst v;omega
 · have mem:v∈serialize baseSchedule:=serialize_mem.mpr ⟨original,original_mem,h⟩
   have b:=member_le_cap _ v mem;omega

/-- Explicit fixed metadata and code envelopes, independent of input length.
There are no assumed ready tables, arbitrary complex constants, child actions
or callback instructions. The shared direction table has q-independent size. -/
theorem fixed_execution (q A B n:ℕ) (x:Fin n→ℂ) (s:State)
 (base:s.natReg 2600=A) (pc:s.pc=0) (hs:WordBound B s)
 (literals:q+literalCap (serialize baseSchedule)≤B)
 (extent:A+(serialize baseSchedule).length≤B) (code:3*(serialize baseSchedule).length+4≤B) : ∃u,
 BoundedExecution (program (scheduleData q)) n x B s (3*(serialize baseSchedule).length+4) u ∧
 PrintedRecords A (scheduleRecords q) u ∧
 (∀z,z<A∨A+(serialize baseSchedule).length≤z→u.natHeap z=s.natHeap z) ∧ Frame s u := by
 have length:=schedule_size_independent q
 obtain ⟨u,run,bank,outside,frame⟩:=schedule_execution q A B n x s base pc hs
   (by intro v hv;exact (schedule_literal_bound q v hv).trans literals)
   (by rw [length];exact extent) (by rw [length];exact code)
 exact ⟨u,by simpa only [length] using run,bank,by simpa only [length] using outside,frame⟩

end
end ExactFourierCircuits.UniformFixedNetworkScheduleMachine
