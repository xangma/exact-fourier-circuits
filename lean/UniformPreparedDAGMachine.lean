import UniformDAGLeafPreparationMachine
import UniformPreparationRowTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedDAGMachine
open UniformMachine UniformAssembly
open UniformOffsetPreparationMachine (DProgram RootsReady LiteralsReady Values)
open scoped BigOperators

/-- Persistent caller registers: Nat273=k, 274=r, 275=root source,
276=leaf origin b, 277=rational triple source, 278=typed-node tape,
279=row destination, 280=result base. Nat281 is charged zero scratch.
Every phase argument is copied by actual bytecode. -/
def leafSetup : Program := [.natLiteral 281 0,.natBinary .add 253 274 281,
 .natBinary .add 254 275 281,.natBinary .add 255 276 281,
 .natBinary .add 256 277 281,.natBinary .add 257 273 281]
def rowSetup : Program := [.natBinary .add 220 273 281,.natBinary .add 221 278 281,
 .natBinary .add 222 279 281,.natBinary .add 223 276 281,
 .natBinary .add 224 280 281,.natBinary .add 225 274 281]
def evalSetup : Program := [.natBinary .add 0 273 281,.natBinary .add 9 280 281,.natBinary .add 137 279 281]
def program : Program := leafSetup ++ UniformDAGLeafPreparationMachine.program.map (relocate 6 76) ++
 rowSetup ++ UniformPreparationRowTableMachine.program.map (relocate 82 121) ++
 evalSetup ++ UniformOffsetPreparationMachine.program.map (relocate 124 156) ++ [.halt]
theorem program_length : program.length=157 := by
 simp only [program,List.length_append,List.length_map,UniformDAGLeafPreparationMachine.program_length,UniformPreparationRowTableMachine.program_length,UniformOffsetPreparationMachine.program_length]
 rfl
theorem leaf_code : CodeAt UniformDAGLeafPreparationMachine.program program 6 76 := by
 intro i hi;rw [UniformDAGLeafPreparationMachine.program_length] at hi;interval_cases i <;> rfl
theorem row_code : CodeAt UniformPreparationRowTableMachine.program program 82 121 := by
 intro i hi;rw [UniformPreparationRowTableMachine.program_length] at hi;interval_cases i <;> rfl
theorem eval_code : CodeAt UniformOffsetPreparationMachine.program program 124 156 := by
 intro i hi;rw [UniformOffsetPreparationMachine.program_length] at hi;interval_cases i <;> rfl

noncomputable section

def runtime {r k : ℕ} (p : DProgram r k) (b a : ℕ) : ℕ :=
 UniformDAGLeafPreparationMachine.runtime p+
 UniformPreparationRowTableMachine.rangeCost (UniformPreparationRowTableMachine.nodes p) 0 k+7+
 UniformOffsetLinearMachine.totalCost (UniformOffsetPreparationMachine.compile p b a)+5+16

def Protected (i : ℕ) : Prop := 10 ≤ i ∧ (i < 147 ∨ 154 ≤ i) ∧
 (i < 220 ∨ 226 ≤ i) ∧ (i < 230 ∨ 260 ≤ i) ∧ i≠137 ∧ i≠281
instance protectedDecidable (i : ℕ) : Decidable (Protected i) :=
 inferInstanceAs (Decidable (10 ≤ i ∧ (i < 147 ∨ 154 ≤ i) ∧
 (i < 220 ∨ 226 ≤ i) ∧ (i < 230 ∨ 260 ≤ i) ∧ i≠137 ∧ i≠281))
def OutsideScalar (b r k a : ℕ) (s u : State) : Prop :=
 ∀i,(i < b ∨ b+1+r+k ≤ i)→(i < a ∨ a+k ≤ i)→u.scalarHeap i=s.scalarHeap i
def OutsideNat (d k : ℕ) (s u : State) : Prop :=
 ∀i,(i < d ∨ d+3*k ≤ i)→u.natHeap i=s.natHeap i
def Frame (s u : State) : Prop := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 ∀i,Protected i→u.natReg i=s.natReg i
structure Header (r k source b literals tape rows a : ℕ) (s : State) : Prop where
 length : s.natReg 273=k
 roots : s.natReg 274=r
 rootSource : s.natReg 275=source
 leafOrigin : s.natReg 276=b
 literalTape : s.natReg 277=literals
 nodeTape : s.natReg 278=tape
 rowDest : s.natReg 279=rows
 resultBase : s.natReg 280=a

/-- Literal natural-only straight-line blocks, with individually bounded writes. -/
inductive Op where
  | lit (d v : ℕ)
  | add (d l r : ℕ)
  deriving DecidableEq
def Op.code : Op→UniformMachine.Instruction
  | .lit d v => .natLiteral d v
  | .add d l r => .natBinary .add d l r
def Op.value : Op→State→ℕ
  | .lit _ v,_ => v
  | .add _ l r,s => s.natReg l+s.natReg r
def Op.apply (o : Op) (s : State) : State := match o with
  | .lit d _ => writeNat s d (o.value s)
  | .add d _ _ => writeNat s d (o.value s)
def applyBlock : List Op→State→State
  | [],s => s
  | o::os,s => applyBlock os (o.apply s)
def peak : List Op→State→ℕ
  | [],_ => 0
  | o::os,s => max (o.value s) (peak os (o.apply s))
def BlockAt (os : List Op) (base : ℕ) : Prop :=
  ∀i,(hi:i < os.length)→program[base+i]?=some (os[i]'hi).code
theorem Op.pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl
theorem applyBlock_pc (os : List Op) (s : State) :
    (applyBlock os s).pc=s.pc+os.length := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp only [applyBlock,ih,Op.pc,List.length_cons];omega
theorem block_runs (os : List Op) (base n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:BlockAt os base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+os.length ≤ B) (hv:peak os s ≤ B) :
    BoundedRuns program n x B s os.length (applyBlock os s) := by
  induction os generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have hp1:s.pc+1 ≤ B := by simp only [List.length_cons] at hb;omega
    have ho:WordBound B (o.apply s):=by
      cases o <;> exact writeNat_bound B s _ _ hs hp1 ((le_max_left _ _).trans hv)
    have ht:BlockAt os (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change program[base+(i+1)]?=some (os[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have tail:=ih (base+1) (o.apply s) ht (by rw [Op.pc,hp]) ho
      (by simp only [List.length_cons] at hb;omega) ((le_max_right _ _).trans hv)
    have hfirst:=hc 0 (by simp)
    change program[base]?=some o.code at hfirst
    refine .next hs ?_ tail
    cases o <;> simp [UniformMachine.step,hp,hfirst,Op.code,Op.apply,Op.value,evalNat]


def leafOps : List Op := [.lit 281 0,.add 253 274 281,.add 254 275 281,
 .add 255 276 281,.add 256 277 281,.add 257 273 281]
def rowOps : List Op := [.add 220 273 281,.add 221 278 281,.add 222 279 281,
 .add 223 276 281,.add 224 280 281,.add 225 274 281]
def evalOps : List Op := [.add 0 273 281,.add 9 280 281,.add 137 279 281]
theorem leafOps_code : BlockAt leafOps 0 := by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem rowOps_code : BlockAt rowOps 76 := by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem evalOps_code : BlockAt evalOps 121 := by
 intro i hi;change i < 3 at hi;interval_cases i <;> rfl


theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,fun i hi=>(h'.2.2 i hi).trans (h.2.2 i hi)⟩
theorem Header.transport {r k source b l c d a : ℕ} {s u : State}
 (h:Header r k source b l c d a s) (hf:Frame s u) : Header r k source b l c d a u := by
 constructor
 · exact (hf.2.2 273 (by decide)).trans h.length
 · exact (hf.2.2 274 (by decide)).trans h.roots
 · exact (hf.2.2 275 (by decide)).trans h.rootSource
 · exact (hf.2.2 276 (by decide)).trans h.leafOrigin
 · exact (hf.2.2 277 (by decide)).trans h.literalTape
 · exact (hf.2.2 278 (by decide)).trans h.nodeTape
 · exact (hf.2.2 279 (by decide)).trans h.rowDest
 · exact (hf.2.2 280 (by decide)).trans h.resultBase

def Op.dest : Op→ℕ
 | .lit d _ | .add d _ _ => d

theorem block_frame (os : List Op) (s : State)
 (h:∀o∈os,¬Protected o.dest) : Frame s (applyBlock os s) := by
 induction os generalizing s with
 | nil => exact ⟨rfl,rfl,fun _ _=>rfl⟩
 | cons o os ih =>
  have ho:=h o (by simp)
  have ht:=ih (o.apply s) (fun t ht=>h t (by simp [ht]))
  apply Frame.trans (u:=o.apply s) ?_ ht
  refine ⟨?_,?_,?_⟩
  · cases o <;> rfl
  · cases o <;> rfl
  · intro i hi
    have he:i≠o.dest:=by intro he;apply ho;simpa [←he] using hi
    cases o <;> simp_all [Op.apply,Op.dest,writeNat,next]

theorem leafOps_frame (s : State) : Frame s (applyBlock leafOps s) := by
 apply block_frame
 intro o ho
 simp [leafOps] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem rowOps_frame (s : State) : Frame s (applyBlock rowOps s) := by
 apply block_frame
 intro o ho
 simp [rowOps] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem evalOps_frame (s : State) : Frame s (applyBlock evalOps s) := by
 apply block_frame
 intro o ho
 simp [evalOps] at ho
 rcases ho with rfl|rfl|rfl <;> decide

theorem block_natHeap (os : List Op) (s : State) : (applyBlock os s).natHeap=s.natHeap := by
 induction os generalizing s with
 | nil => rfl
 | cons o os ih => cases o <;> exact ih _
theorem block_scalarHeap (os : List Op) (s : State) : (applyBlock os s).scalarHeap=s.scalarHeap := by
 induction os generalizing s with
 | nil => rfl
 | cons o os ih => cases o <;> exact ih _

/-- Each setup is natural arithmetic alone; it cannot alter prepared root or
literal readiness while computing the next phase's actual arguments. -/
theorem roots_after_block {r : ℕ} (b : ℕ) (roots : Fin r→ℂ) (s : State) (os : List Op)
 (h:RootsReady b roots s) : RootsReady b roots (applyBlock os s) := by
 simpa only [UniformOffsetPreparationMachine.RootsReady,block_scalarHeap] using h

theorem literals_after_block {r k : ℕ} (p : DProgram r k) (b : ℕ) (s : State) (os : List Op)
 (h:LiteralsReady p b s) : LiteralsReady p b (applyBlock os s) :=
 (UniformOffsetPreparationMachine.literals_heap_eq p b s (applyBlock os s) (block_scalarHeap os s)).mpr h



/-- A coarse single envelope discharges every helper address/code bound.
All unrelated original banks must also satisfy the caller's original WordBound. -/
def wordBudget (l c d b a r k : ℕ) : ℕ := l+c+d+b+a+r+8*k+200

theorem wordBudget_polynomial (l c d b a r k : ℕ) :
 wordBudget l c d b a r k ≤ 200*(l+c+d+b+a+r+k+1) := by
 unfold wordBudget
 simp only [Nat.mul_add,Nat.mul_one]
 omega

theorem runtime_bound {r k : ℕ} (p : DProgram r k) (l B b a : ℕ) (s : State)
 (hl:UniformDAGLeafPreparationMachine.LiteralSource p l s) (hs:WordBound B s) :
 runtime p b a ≤ 7*r+50+k*(14*(Nat.log2 (B+1)+1)+77) := by
 have hleaf:=UniformDAGLeafPreparationMachine.runtime_log_bound p l B s hl hs
 have hrows:=UniformPreparationRowTableMachine.rangeCost_le (UniformPreparationRowTableMachine.nodes p) 0 k
 have heval:=UniformOffsetLinearMachine.totalCost_bound (UniformOffsetPreparationMachine.compile p b a)
 rw [UniformOffsetPreparationMachine.compile_length] at heval
 unfold runtime
 simp only [Nat.mul_add] at *
 omega



theorem leaf_arguments {r k source b l c d a : ℕ} (s : State) (h:Header r k source b l c d a s) :
 (applyBlock leafOps s).natReg 253=r ∧ (applyBlock leafOps s).natReg 254=source ∧
 (applyBlock leafOps s).natReg 255=b ∧ (applyBlock leafOps s).natReg 256=l ∧
 (applyBlock leafOps s).natReg 257=k ∧ (applyBlock leafOps s).natReg 281=0 := by
 simp [applyBlock,leafOps,Op.apply,Op.value,writeNat,next,h.roots,h.rootSource,h.leafOrigin,h.literalTape,h.length]

theorem row_arguments {r k source b l c d a : ℕ} (s : State) (h:Header r k source b l c d a s)
 (hz:s.natReg 281=0) : UniformPreparationRowTableMachine.Header k c d b a r (applyBlock rowOps s) := by
 simp [UniformPreparationRowTableMachine.Header,applyBlock,rowOps,Op.apply,Op.value,writeNat,next,
   h.length,h.nodeTape,h.rowDest,h.leafOrigin,h.resultBase,h.roots,hz]

theorem eval_arguments {r k source b l c d a : ℕ} (s : State) (h:Header r k source b l c d a s)
 (hz:s.natReg 281=0) : (applyBlock evalOps s).natReg 0=k ∧
 (applyBlock evalOps s).natReg 9=a ∧ (applyBlock evalOps s).natReg 137=d := by
 simp [applyBlock,evalOps,Op.apply,Op.value,writeNat,next,h.length,h.resultBase,h.rowDest,hz]

/-- The initial prepared source bank and the two original integer tapes are
honest input contracts. This theorem builds every prepared leaf and actual
interpreter row internally, and then executes every shared typed DAG node. -/
theorem execution {r k : ℕ} (p : DProgram r k) (roots : Fin r→ℂ) (valid:p.Admissible roots)
 (n : ℕ) (x : Fin n→ℂ) (source b l c d a B : ℕ) (s : State)
 (hroots:UniformDAGLeafPreparationMachine.RootSource source roots s)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hdisjoint:UniformPreparationRowTableMachine.Disjoint k c d)
 (hsource:source+r ≤ b) (hb:0 < b) (hspace:b+1+r+k ≤ a)
 (hbudget:wordBudget l c d b a r k ≤ B) (hh:Header r k source b l c d a s)
 (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b a) u ∧ Values p roots a u ∧
 RootsReady b roots u ∧ LiteralsReady p b u ∧
 UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d u ∧
 OutsideScalar b r k a s u ∧ OutsideNat d k s u ∧ Frame s u ∧
 u.scalarHeap 0=s.scalarHeap 0 ∧
 (∀j:Fin r,u.scalarHeap (source+j.val)=s.scalarHeap (source+j.val)) ∧
 Header r k source b l c d a u ∧ u.pc=156 := by
 have hB:l+c+d+b+a+r+8*k+200 ≤ B:=hbudget
 have hstart:BoundedRuns program n x B s 6 (applyBlock leafOps s):=by
   apply block_runs leafOps 0 n B x s leafOps_code hpc hs (by change 0+6 ≤ B;omega)
   simp [peak,leafOps,Op.value,Op.apply,writeNat,next,hh.roots,hh.rootSource,hh.leafOrigin,hh.literalTape,hh.length]
   omega
 let first:=applyBlock leafOps s
 obtain ⟨h253,h254,h255,h256,h257,h281⟩:=leaf_arguments s hh
 have hfirstPC:first.pc=6:=by rw [applyBlock_pc,hpc];rfl
 have hrootFirst:UniformDAGLeafPreparationMachine.RootSource source roots {first with pc:=0}:=by
   simpa only [UniformDAGLeafPreparationMachine.RootSource,first,block_scalarHeap] using hroots
 have hliteralFirst:UniformDAGLeafPreparationMachine.LiteralSource p l {first with pc:=0}:=by
   simpa only [UniformDAGLeafPreparationMachine.LiteralSource,UniformDAGLiteralBankMachine.RationalSource,
     UniformDAGLiteralBankMachine.Source,first,block_natHeap] using hliterals
 have hfirstB:WordBound B {first with pc:=0}:=changePC_bound B _ 0 hstart.final_bound (by omega)
 obtain ⟨v,hv,hvRoots,hvLiterals,_hvslots,_hvmaster,_hvsource,hvFrame,hvOutside,_hvhalt⟩:=
   UniformDAGLeafPreparationMachine.execution p roots n x source b l B {first with pc:=0}
     hrootFirst hliteralFirst hsource hb (by omega) (by omega) (by omega) rfl
     h253 h254 h255 h256 h257 hfirstB
 have hleaf:=UniformBoundedAssembly.boundedExecution_placed leaf_code
   (by rw [UniformDAGLeafPreparationMachine.program_length];omega) (by omega) hv
 rw [UniformDAGLeafPreparationMachine.reset_placed first 6 hfirstPC] at hleaf
 let leaves:State:={v with pc:=76}
 have hlf:Frame first leaves:=by
   refine ⟨hvFrame.2.1,hvFrame.2.2.1,?_⟩
   intro i hi
   exact hvFrame.2.2.2 i (by unfold Protected UniformDAGLeafPreparationMachine.Protected at *;omega)
 have hleafFrame:Frame s leaves:=(leafOps_frame s).trans hlf
 have hleafHeader:Header r k source b l c d a leaves:=hh.transport hleafFrame
 have hzero:leaves.natReg 281=0:=(hvFrame.2.2.2 281 (by decide)).trans h281
 have hrowBoot:BoundedRuns program n x B leaves 6 (applyBlock rowOps leaves):=by
   apply block_runs rowOps 76 n B x leaves rowOps_code rfl hleaf.final_bound (by change 76+6 ≤ B;omega)
   simp [peak,rowOps,Op.value,Op.apply,writeNat,next,hzero,hleafHeader.length,
     hleafHeader.nodeTape,hleafHeader.rowDest,hleafHeader.leafOrigin,hleafHeader.resultBase,hleafHeader.roots]
   omega
 let beforeRows:=applyBlock rowOps leaves
 have hrowPC:beforeRows.pc=82:=by rw [applyBlock_pc];rfl
 have hrowH:UniformPreparationRowTableMachine.Header k c d b a r beforeRows:=row_arguments leaves hleafHeader hzero
 have hrowHeap:beforeRows.natHeap=s.natHeap:=(block_natHeap rowOps leaves).trans
   (hvFrame.1.trans (block_natHeap leafOps s))
 have hrowTape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c beforeRows.natHeap:=by
   simpa only [hrowHeap] using htape
 have hrowB:WordBound B {beforeRows with pc:=0}:=changePC_bound B _ 0 hrowBoot.final_bound (by omega)
 obtain ⟨w,hw,_hrowcost,hwTable,hwFrame,hwOutside,_hwhalt,_hwcount⟩:=
   UniformPreparationRowTableMachine.typed_execution p n c d b a B x {beforeRows with pc:=0}
     hrowTape hdisjoint hrowH rfl hrowB (by omega)
 have hrows:=UniformBoundedAssembly.boundedExecution_placed row_code
   (by rw [UniformPreparationRowTableMachine.program_length];omega) (by omega) hw
 rw [UniformDAGLeafPreparationMachine.reset_placed beforeRows 82 hrowPC] at hrows
 let rows:State:={w with pc:=121}
 have hrf:Frame beforeRows rows:=by
   refine ⟨hwFrame.2.2.1,hwFrame.2.2.2.1,?_⟩
   intro i hi
   exact hwFrame.2.2.2.2 i (by unfold Protected at hi;omega)
 have hrowsFrame:Frame s rows:=hleafFrame.trans ((rowOps_frame leaves).trans hrf)
 have hrowsHeader:Header r k source b l c d a rows:=hh.transport hrowsFrame
 have hrowsZero:rows.natReg 281=0:=(hwFrame.2.2.2.2 281 (by omega)).trans
   (by simpa [beforeRows,applyBlock,rowOps,Op.apply,Op.value,writeNat,next] using hzero)
 have hbeforeRoots:RootsReady b roots beforeRows:=roots_after_block b roots leaves rowOps hvRoots
 have hbeforeLiterals:LiteralsReady p b beforeRows:=literals_after_block p b leaves rowOps
   ((UniformOffsetPreparationMachine.literals_heap_eq p b v leaves rfl).mpr hvLiterals)
 obtain ⟨hrowsRoots,hrowsLiterals⟩:=UniformPreparationRowTableMachine.leaf_readiness_retained
   p roots b beforeRows rows hwFrame hbeforeRoots hbeforeLiterals
 have hevalBoot:BoundedRuns program n x B rows 3 (applyBlock evalOps rows):=by
   apply block_runs evalOps 121 n B x rows evalOps_code rfl hrows.final_bound (by change 121+3 ≤ B;omega)
   simp [peak,evalOps,Op.value,Op.apply,writeNat,next,hrowsZero,hrowsHeader.length,
     hrowsHeader.resultBase,hrowsHeader.rowDest]
   omega
 let beforeEval:=applyBlock evalOps rows
 have hevalPC:beforeEval.pc=124:=by rw [applyBlock_pc];rfl
 obtain ⟨h0,h9,h137⟩:=eval_arguments rows hrowsHeader hrowsZero
 have htableEval:UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d beforeEval:=by
   simpa only [UniformOffsetPreparationMachine.NatTable,beforeEval,rows,block_natHeap] using hwTable
 have hrootsEval:RootsReady b roots beforeEval:=roots_after_block b roots rows evalOps hrowsRoots
 have hliteralsEval:LiteralsReady p b beforeEval:=literals_after_block p b rows evalOps hrowsLiterals
 have hevalB:WordBound B {beforeEval with pc:=0}:=changePC_bound B _ 0 hevalBoot.final_bound (by omega)
 obtain ⟨z,hz,_hcost,hvalues,hbase,hevalFrame,hevalOutside⟩:=UniformOffsetPreparationMachine.interpreted_DAG
   p roots valid n x b a d B {beforeEval with pc:=0} (by omega) (by omega) rfl h0 h9 h137 hevalB
     hrootsEval
     ((UniformOffsetPreparationMachine.literals_heap_eq p b beforeEval {beforeEval with pc:=0} rfl).mpr hliteralsEval)
     htableEval
 have heval:=UniformBoundedAssembly.boundedExecution_placed eval_code
   (by rw [UniformOffsetPreparationMachine.program_length];omega) (by omega) hz
 rw [UniformDAGLeafPreparationMachine.reset_placed beforeEval 124 hevalPC] at heval
 let final:State:={z with pc:=156}
 have hef:Frame beforeEval final:=by
   refine ⟨hevalFrame.2.1,hevalFrame.2.2.1,?_⟩
   intro i hi
   exact hevalFrame.2.2.2.1 i (Or.inr (by unfold Protected at hi;omega))
 have hfinalFrame:Frame s final:=hrowsFrame.trans ((evalOps_frame rows).trans hef)
 have hfinalScalar:OutsideScalar b r k a s final:=by
   intro i hleaf hresult
   rw [hevalOutside i hresult,block_scalarHeap evalOps rows,hwFrame.1,block_scalarHeap rowOps leaves]
   exact (hvOutside i hleaf).trans (by simp only [first,block_scalarHeap])
 have hfinalNat:OutsideNat d k s final:=by
   intro i hi
   rw [hevalFrame.1,block_natHeap evalOps rows]
   exact (hwOutside i hi).trans (congrFun hrowHeap i)
 have hfinalRoots:RootsReady b roots final:=by
   refine ⟨?_,?_⟩
   · rw [hbase b (by omega)];exact hrootsEval.1
   · intro j
     rw [hbase _ (by have hj:=j.isLt;omega)];exact hrootsEval.2 j
 have hfinalLiterals:LiteralsReady p b final:=by
   apply UniformDAGLeafPreparationMachine.literalsReady_of_bank
   intro j
   rw [hbase _ (by have hj:=j.isLt;omega),block_scalarHeap evalOps rows,hwFrame.1,block_scalarHeap rowOps leaves]
   change v.scalarHeap (b+1+r+j.val)=_
   exact _hvslots j
 have hfinalTable:UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d final:=by
   change UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d {z with pc:=156}
   simpa only [UniformOffsetPreparationMachine.NatTable,hevalFrame.1,beforeEval,rows,block_natHeap] using hwTable
 have halt:BoundedExecution program n x B final 1 final:=.halt heval.final_bound
   (by rw [UniformMachine.step];rfl)
 refine ⟨final,?_,hvalues,hfinalRoots,hfinalLiterals,hfinalTable,hfinalScalar,hfinalNat,hfinalFrame,
   hfinalScalar 0 (Or.inl hb) (Or.inl (by omega)),?_,hh.transport hfinalFrame,rfl⟩
 · have hall:=(((((hstart.trans hleaf).trans hrowBoot).trans hrows).trans hevalBoot).trans heval).executes halt
   convert hall using 1
   unfold runtime
   omega
 · intro j
   apply hfinalScalar
   · left;have hj:=j.isLt;omega
   · left;have hj:=j.isLt;omega

/-- In the single-master case the actual retained scalar at address zero is
copied. No additional root request, value certificate, or retagging occurs. -/
theorem execution_single_master {k : ℕ} (p : DProgram 1 k) (omega : ℂ)
 (valid:p.Admissible (fun _:Fin 1=>omega)) (n : ℕ) (x : Fin n→ℂ)
 (b l c d a B : ℕ) (s : State)
 (hmaster:s.scalarHeap 0=some ⟨omega,false⟩)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hdisjoint:UniformPreparationRowTableMachine.Disjoint k c d)
 (hb:0<b) (hspace:b+1+1+k≤a) (hbudget:wordBudget l c d b a 1 k≤B)
 (hh:Header 1 k 0 b l c d a s) (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b a) u ∧ Values p (fun _:Fin 1=>omega) a u ∧
 RootsReady b (fun _:Fin 1=>omega) u ∧ LiteralsReady p b u ∧
 UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d u ∧
 OutsideScalar b 1 k a s u ∧ OutsideNat d k s u ∧ Frame s u ∧
 u.scalarHeap 0=s.scalarHeap 0 ∧
 (∀j:Fin 1,u.scalarHeap j.val=s.scalarHeap j.val) ∧
 Header 1 k 0 b l c d a u ∧ u.pc=156 := by
 have hroots:UniformDAGLeafPreparationMachine.RootSource 0 (fun _:Fin 1=>omega) s:=by
   intro j
   have hj:j.val=0:=by have hj:=j.isLt;omega
   simpa only [hj,Nat.add_zero] using hmaster
 simpa only [Nat.zero_add] using execution p (fun _:Fin 1=>omega) valid n x 0 b l c d a B s hroots hliterals htape
   hdisjoint (by omega) hb hspace hbudget hh hpc hs

/-- A selected global scalar prefix is retained whenever both fresh scalar
regions start beyond it. This does not invent a global allocator. -/
theorem scalar_prefix_retained (b r k a endAddr : ℕ) (s u : State)
 (h:OutsideScalar b r k a s u) (hb:endAddr≤b) (ha:endAddr≤a) :
 ∀i,i<endAddr→u.scalarHeap i=s.scalarHeap i := by
 intro i hi
 exact h i (Or.inl (by omega)) (Or.inl (by omega))

/-- The complete protected Nat metadata prefix survives when the actual row
array is allocated beyond it. -/
theorem nat_prefix_retained (d k endAddr : ℕ) (s u : State)
 (h:OutsideNat d k s u) (hd:endAddr≤d) :
 ∀i,i<endAddr→u.natHeap i=s.natHeap i := by
 intro i hi
 exact h i (Or.inl (by omega))

theorem saved_headers_retained (s u : State) (h:Frame s u) (i : Fin 7) :
 u.natReg (100+i.val)=s.natReg (100+i.val) :=
 h.2.2 _ (by have hi:=i.isLt;unfold Protected;omega)


end
end ExactFourierCircuits.UniformPreparedDAGMachine
