import UniformChunkPortMachine
import UniformCrossDepthReplayPreparation
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformChunkRowTableMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInPlaceMachine (Row)
open UniformCrossShearTableMachine (RowFields Table)

/-- Original caller1080..1088: row count, logical input, physical output,
e,g,a,source offset,target offset,borrowed table. Scratch1090..1100.
Every original coefficient address is copied unchanged; there are no scalar
operations and no absolute scalar-memory base added to the coordinates. -/
def boot : List Op := [.literal 1090 0,.literal 1091 0,.literal 1092 1,.literal 1093 3]
def reads : List Op := [.mul 1094 1090 1093,.add 1094 1081 1094,
 .getNat 1095 1094,.add 1094 1094 1092,.getNat 1096 1094,
 .add 1094 1094 1092,.getNat 1097 1094]
def firstSetup : List Op := [.add 1020 1095 1091,.add 1021 1083 1091,
 .add 1022 1084 1091,.add 1023 1086 1091,.add 1024 1087 1091,.add 1025 1088 1091]
def saveFirst : List Op := [.add 1098 1030 1091]
def secondSetup : List Op := [.add 1020 1096 1091]
def stores : List Op := [.add 1099 1030 1091,.mul 1100 1090 1093,.add 1100 1082 1100,
 .putNat 1100 1098,.add 1100 1100 1092,.putNat 1100 1099,
 .add 1100 1100 1092,.putNat 1100 1097,.add 1090 1090 1092]
def beforeFirst : Program := boot.map Op.code ++ [.branchLT 1090 1080 5 58] ++
 reads.map Op.code ++ firstSetup.map Op.code
def beforeSecond : Program := beforeFirst ++
 UniformChunkPortMachine.program.map (relocate 18 32) ++ saveFirst.map Op.code ++ secondSetup.map Op.code
def program : Program := beforeSecond ++ UniformChunkPortMachine.program.map (relocate 34 48) ++
 stores.map Op.code ++ [.jump 4,.halt]
theorem boot_length : boot.length=4 := rfl
theorem reads_length : reads.length=7 := rfl
theorem firstSetup_length : firstSetup.length=6 := rfl
theorem saveFirst_length : saveFirst.length=1 := rfl
theorem secondSetup_length : secondSetup.length=1 := rfl
theorem stores_length : stores.length=9 := rfl
theorem beforeFirst_length : beforeFirst.length=18 := by
 simp [beforeFirst,boot_length,reads_length,firstSetup_length]
theorem beforeSecond_length : beforeSecond.length=34 := by
 simp [beforeSecond,beforeFirst_length,UniformChunkPortMachine.program_length,saveFirst_length,secondSetup_length]
theorem program_length : program.length=59 := by
 simp [program,beforeSecond_length,UniformChunkPortMachine.program_length,stores_length]

theorem segment_code (before after p : Program) (base returnPC : ℕ)
 (hb:before.length=base) : CodeAt p (before ++ p.map (relocate base returnPC) ++ after) base returnPC := by
 intro i hi
 rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,hb];omega)]
 rw [List.getElem?_append_right (by omega)]
 simp only [hb,show base+i-base=i by omega,List.getElem?_map]

theorem portFirst_code : CodeAt UniformChunkPortMachine.program program 18 32 := by
 let after:=saveFirst.map Op.code ++ secondSetup.map Op.code ++
  UniformChunkPortMachine.program.map (relocate 34 48) ++ stores.map Op.code ++ [.jump 4,.halt]
 have he:program=beforeFirst ++ UniformChunkPortMachine.program.map (relocate 18 32) ++ after:=by
  simp [program,beforeSecond,after,List.append_assoc]
 rw [he]
 exact segment_code beforeFirst after UniformChunkPortMachine.program 18 32 beforeFirst_length

theorem portSecond_code : CodeAt UniformChunkPortMachine.program program 34 48 := by
 simpa only [program,List.append_assoc] using segment_code beforeSecond (stores.map Op.code ++ [.jump 4,.halt])
  UniformChunkPortMachine.program 34 48 beforeSecond_length

theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem reads_code : BlockAt reads program 5 := by
 intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem firstSetup_code : BlockAt firstSetup program 12 := by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem saveFirst_code : BlockAt saveFirst program 32 := by
 intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem secondSetup_code : BlockAt secondSetup program 33 := by
 intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem stores_code : BlockAt stores program 48 := by
 intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem loop_branch : program[4]?=some (.branchLT 1090 1080 5 58) := rfl
theorem loop_jump : program[57]?=some (.jump 4) := rfl
theorem final_halt : program[58]?=some .halt := rfl

structure Parameters where
 v : ℕ
 e : ℕ
 g : ℕ
 a : ℕ
 source : ℕ
 target : ℕ
 borrowed : ℕ
 logical : ℕ
 output : ℕ

structure Geometry (p : Parameters) (count B : ℕ) : Prop where
 code : 59 ≤ B
 width : p.v ≤ B
 sourceRange : p.source+p.e ≤ p.v
 targetRange : p.target+p.a ≤ p.v
 separated : p.source+p.e ≤ p.target ∨ p.target+p.a ≤ p.source
 capacity : p.g+p.e+p.a ≤ p.v
 inputGateEnd : p.e+1+p.g ≤ B
 inputFresh : p.logical+3*count ≤ p.output
 borrowedFresh : p.borrowed+p.g ≤ p.output
 outputBound : p.output+3*count ≤ B

noncomputable section

def borrowed (p : Parameters) (fit:p.g+p.e+p.a ≤ p.v) :=
 UniformChunkPortMachine.borrowedCoordinate p.v p.source p.e p.target p.a p.g fit

def mappedRow (p : Parameters) (fit:p.g+p.e+p.a ≤ p.v) (row : Row) : Row :=
 ⟨UniformChunkPortMachine.mapped p.e p.g p.source p.target (borrowed p fit) row.dst,
  UniformChunkPortMachine.mapped p.e p.g p.source p.target (borrowed p fit) row.src,row.coefficient⟩
def RowsDomain (p : Parameters) (rows : List Row) : Prop := ∀row∈rows,
 UniformChunkPortMachine.Domain p.e p.g p.a row.dst ∧ UniformChunkPortMachine.Domain p.e p.g p.a row.src

structure Header (p : Parameters) (count : ℕ) (s : State) : Prop where
 count : s.natReg 1080=count
 logical : s.natReg 1081=p.logical
 output : s.natReg 1082=p.output
 inputs : s.natReg 1083=p.e
 gates : s.natReg 1084=p.g
 targets : s.natReg 1085=p.a
 source : s.natReg 1086=p.source
 target : s.natReg 1087=p.target
 borrowed : s.natReg 1088=p.borrowed
structure Fixed (p : Parameters) (count : ℕ) (s : State) : Prop where
 header : Header p count s
 zero : s.natReg 1091=0
 one : s.natReg 1092=1
 three : s.natReg 1093=3
structure Cursor (p : Parameters) (count i : ℕ) (s : State) : Prop where
 fixed : Fixed p count s
 index : s.natReg 1090=i

/-- Preserve all registers outside mapper/setup and loop scratch. -/
def Preserved (r : ℕ) := (r < 1020 ∨ 1035 ≤ r) ∧ (r < 1090 ∨ 1101 ≤ r)
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ∀r,Preserved r → u.natReg r=s.natReg r

def Outside (p : Parameters) (count : ℕ) (s u : State) : Prop :=
 ∀q,(q < p.output ∨ p.output+3*count ≤ q) → u.natHeap q=s.natHeap q

theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (f:Frame s u) (f':Frame u v) : Frame s v :=
 ⟨f'.1.trans f.1,f'.2.1.trans f.2.1,f'.2.2.1.trans f.2.2.1,
 f'.2.2.2.1.trans f.2.2.2.1,fun r hr=>(f'.2.2.2.2 r hr).trans (f.2.2.2.2 r hr)⟩
theorem outside_refl (p : Parameters) (count : ℕ) (s : State) : Outside p count s s := fun _ _=>rfl
theorem outside_trans {p : Parameters} {count : ℕ} {s u v : State}
 (f:Outside p count s u) (f':Outside p count u v) : Outside p count s v :=
 fun q hq=>(f' q hq).trans (f q hq)

theorem Frame.withPC {s u : State} (f:Frame s u) (pc : ℕ) : Frame s (setPC u pc) := f
theorem Header.withPC {p : Parameters} {count : ℕ} {s : State} (h:Header p count s) (pc : ℕ) : Header p count (setPC s pc) :=
 ⟨h.count,h.logical,h.output,h.inputs,h.gates,h.targets,h.source,h.target,h.borrowed⟩
theorem Fixed.withPC {p : Parameters} {count : ℕ} {s : State} (h:Fixed p count s) (pc : ℕ) : Fixed p count (setPC s pc) :=
 ⟨h.header.withPC pc,h.zero,h.one,h.three⟩
theorem Cursor.withPC {p : Parameters} {count i : ℕ} {s : State} (h:Cursor p count i s) (pc : ℕ) : Cursor p count i (setPC s pc) :=
 ⟨h.fixed.withPC pc,h.index⟩


def ConstRegister (r : ℕ) : Prop := (1080 ≤ r ∧ r ≤ 1088) ∨ (1091 ≤ r ∧ r ≤ 1093)

theorem Header.transport {p : Parameters} {count : ℕ} {s u : State} (h:Header p count s)
 (f:∀r,ConstRegister r → u.natReg r=s.natReg r) : Header p count u := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals first
  | exact (f _ (by unfold ConstRegister;omega)).trans h.count
  | exact (f _ (by unfold ConstRegister;omega)).trans h.logical
  | exact (f _ (by unfold ConstRegister;omega)).trans h.output
  | exact (f _ (by unfold ConstRegister;omega)).trans h.inputs
  | exact (f _ (by unfold ConstRegister;omega)).trans h.gates
  | exact (f _ (by unfold ConstRegister;omega)).trans h.targets
  | exact (f _ (by unfold ConstRegister;omega)).trans h.source
  | exact (f _ (by unfold ConstRegister;omega)).trans h.target
  | exact (f _ (by unfold ConstRegister;omega)).trans h.borrowed

theorem Fixed.transport {p : Parameters} {count : ℕ} {s u : State} (h:Fixed p count s)
 (f:∀r,ConstRegister r → u.natReg r=s.natReg r) : Fixed p count u :=
 ⟨h.header.transport f,(f 1091 (by unfold ConstRegister;omega)).trans h.zero,
 (f 1092 (by unfold ConstRegister;omega)).trans h.one,(f 1093 (by unfold ConstRegister;omega)).trans h.three⟩

def CoreBlock (b : List Op) : Prop := b=reads ∨ b=firstSetup ∨ b=saveFirst ∨ b=secondSetup ∨ b=stores

theorem block_constants (b : List Op) (s : State) (hb:CoreBlock b) :
 ∀r,ConstRegister r → (applyBlock b s).natReg r=s.natReg r := by
 rcases hb with rfl|rfl|rfl|rfl|rfl
 all_goals intro r hr
 all_goals unfold ConstRegister at hr
 all_goals simp (disch:=omega) [reads,firstSetup,saveFirst,secondSetup,stores,applyBlock,Op.apply,writeNat,next]

theorem block_frame (b : List Op) (s : State) (hb:b=boot ∨ CoreBlock b) : Frame s (applyBlock b s) := by
 rcases hb with rfl|hb
 · refine ⟨rfl,rfl,rfl,rfl,?_⟩
   intro r hr
   unfold Preserved at hr
   simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
 · rcases hb with rfl|rfl|rfl|rfl|rfl
   all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
   all_goals intro r hr
   all_goals unfold Preserved at hr
   all_goals simp (disch:=omega) [reads,firstSetup,saveFirst,secondSetup,stores,applyBlock,Op.apply,writeNat,next]

structure Cache (row : Row) (s : State) : Prop where
 dst : s.natReg 1095=row.dst
 src : s.natReg 1096=row.src
 coefficient : s.natReg 1097=row.coefficient

theorem Cache.withPC {row : Row} {s : State} (h:Cache row s) (pc : ℕ) : Cache row (setPC s pc) :=
 ⟨h.dst,h.src,h.coefficient⟩

theorem reads_spec {p : Parameters} {count i : ℕ} {row : Row} {s : State}
 (h:Cursor p count i s) (fields:RowFields (p.logical+3*i) row s.natHeap) :
 Cache row (applyBlock reads s) := by
 rcases fields with ⟨hd,hs,hc⟩
 simp only [Nat.mul_comm,Nat.add_assoc] at hd hs hc
 constructor
 all_goals simp [reads,applyBlock,Op.apply,writeNat,next,h.fixed.header.logical,h.index,h.fixed.three,h.fixed.one,
  Nat.add_assoc,hd,hs,hc]

theorem reads_safe {p : Parameters} {count i B : ℕ} {row : Row} {s : State}
 (h:Cursor p count i s) (fields:RowFields (p.logical+3*i) row s.natHeap)
 (hi:i < count) (geo:Geometry p count B) (bound:WordBound B s) :
 readable reads s ∧ peak reads s ≤ B := by
 rcases fields with ⟨hd,hs,hc⟩
 have db:row.dst ≤ B:=(bound.2.2.1 _ _ hd).2
 have sb:row.src ≤ B:=(bound.2.2.1 _ _ hs).2
 have cb:row.coefficient ≤ B:=(bound.2.2.1 _ _ hc).2
 have ptr:p.logical+3*i+2 ≤ B:=by have :=geo.inputFresh;have :=geo.outputBound;omega
 have hd' : s.natHeap (p.logical+i*3)=some row.dst:=by simpa only [Nat.mul_comm] using hd
 have hs' : s.natHeap (p.logical+(i*3+1))=some row.src:=by simpa only [Nat.mul_comm,Nat.add_assoc] using hs
 have hc' : s.natHeap (p.logical+(i*3+2))=some row.coefficient:=by simpa only [Nat.mul_comm,Nat.add_assoc] using hc
 simp [reads,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.fixed.header.logical,h.index,
  h.fixed.three,h.fixed.one,Nat.add_assoc,hd',hs',hc']
 omega

theorem firstSetup_spec {p : Parameters} {count : ℕ} {row : Row} {s : State}
 (h:Fixed p count s) (cache:Cache row s) :
 UniformChunkPortMachine.Header row.dst p.e p.g p.source p.target p.borrowed (applyBlock firstSetup s) := by
 constructor
 all_goals simp [firstSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.header.inputs,h.header.gates,
  h.header.source,h.header.target,h.header.borrowed,cache.dst]

theorem firstSetup_safe {p : Parameters} {count : ℕ} {row : Row} {s : State} {B : ℕ}
 (h:Fixed p count s) (_cache:Cache row s) (bound:WordBound B s) :
 readable firstSetup s ∧ peak firstSetup s ≤ B := by
 have hd:=bound.2.1 1095
 have he:=bound.2.1 1083
 have hg:=bound.2.1 1084
 have hs:=bound.2.1 1086
 have ht:=bound.2.1 1087
 have hq:=bound.2.1 1088
 simp [readable,peak,firstSetup,Op.readable,Op.peak,Op.apply,writeNat,next,h.zero]
 omega

theorem port_bounds {p : Parameters} {count B : ℕ} (geo:Geometry p count B) :
 UniformChunkPortMachine.Bounds p.e p.g p.a p.source p.target p.borrowed B :=
 ⟨by have :=geo.code;omega,geo.inputGateEnd,geo.sourceRange.trans geo.width,
 geo.targetRange.trans geo.width,by have :=geo.borrowedFresh;have :=geo.outputBound;omega⟩

theorem port_frame {s u : State} (f:UniformChunkPortMachine.Frame s u) : Frame s u :=
 ⟨f.1,f.2.1,f.2.2.2.1,f.2.2.2.2.1,fun r hr=>f.2.2.2.2.2 r (by have :=hr.1;omega)⟩

theorem Fixed.port_transport {p : Parameters} {count : ℕ} {s u : State}
 (h:Fixed p count s) (f:UniformChunkPortMachine.Frame s u) : Fixed p count u :=
 h.transport (fun r hr=>f.2.2.2.2.2 r (by unfold ConstRegister at hr;omega))

theorem Cache.port_transport {row : Row} {s u : State}
 (h:Cache row s) (f:UniformChunkPortMachine.Frame s u) : Cache row u :=
 ⟨(f.2.2.2.2.2 1095 (by omega)).trans h.dst,
 (f.2.2.2.2.2 1096 (by omega)).trans h.src,
 (f.2.2.2.2.2 1097 (by omega)).trans h.coefficient⟩

theorem port_header_transport {d e g s t Q : ℕ} {u w : State}
 (h:UniformChunkPortMachine.Header d e g s t Q u) (f:UniformChunkPortMachine.Frame u w) :
 UniformChunkPortMachine.Header d e g s t Q w :=
 ⟨(f.2.2.2.2.2 1020 (by omega)).trans h.port,
 (f.2.2.2.2.2 1021 (by omega)).trans h.inputs,
 (f.2.2.2.2.2 1022 (by omega)).trans h.gates,
 (f.2.2.2.2.2 1023 (by omega)).trans h.source,
 (f.2.2.2.2.2 1024 (by omega)).trans h.target,
 (f.2.2.2.2.2 1025 (by omega)).trans h.borrowed⟩

theorem port_call {p : Parameters} {count B n base ret d : ℕ} {x : Fin n → ℂ} {s : State}
 (geo:Geometry p count B) (h:UniformChunkPortMachine.Header d p.e p.g p.source p.target p.borrowed s)
 (domain:UniformChunkPortMachine.Domain p.e p.g p.a d)
 (bank:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) s)
 (code:CodeAt UniformChunkPortMachine.program program base ret)
 (codeBound:base+14 ≤ B) (retBound:ret ≤ B) (pc:s.pc=base) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (UniformChunkPortMachine.runtime p.e p.g d) u ∧
 u.pc=ret ∧ u.natReg 1030=UniformChunkPortMachine.mapped p.e p.g p.source p.target (borrowed p geo.capacity) d ∧
 UniformChunkPortMachine.Frame s u := by
 obtain ⟨u,run,val,frame⟩:=UniformChunkPortMachine.execution n B d p.e p.g p.a p.source p.target p.borrowed
  (borrowed p geo.capacity) x (setPC s 0) (h.withPC 0) domain bank (port_bounds geo) rfl
  (changePC_bound B s 0 bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed code codeBound retBound run
 have eqn:placed base (setPC s 0)=s:=by cases s; simp_all [placed,setPC]
 rw [eqn] at placedRun
 exact ⟨setPC u ret,placedRun,rfl,val,frame⟩

theorem runtime_bound (e g d : ℕ) : UniformChunkPortMachine.runtime e g d ≤ 9 := by
 unfold UniformChunkPortMachine.runtime;split <;> first | omega | (split <;> omega)

theorem Cache.core_transport {row : Row} {s : State} {b : List Op} (h:Cache row s)
 (hb:b=firstSetup ∨ b=saveFirst ∨ b=secondSetup) : Cache row (applyBlock b s) := by
 rcases hb with rfl|rfl|rfl
 all_goals constructor
 all_goals simp [firstSetup,saveFirst,secondSetup,applyBlock,Op.apply,writeNat,next,h.dst,h.src,h.coefficient]

theorem core_index {s : State} {b : List Op} (hb:b=reads ∨ b=firstSetup ∨ b=saveFirst ∨ b=secondSetup) :
 (applyBlock b s).natReg 1090=s.natReg 1090 := by
 rcases hb with rfl|rfl|rfl|rfl
 all_goals simp [reads,firstSetup,saveFirst,secondSetup,applyBlock,Op.apply,writeNat,next]

theorem secondSetup_spec {p : Parameters} {row : Row} {s : State}
 (h:UniformChunkPortMachine.Header row.dst p.e p.g p.source p.target p.borrowed s)
 (cache:Cache row s) (zero:s.natReg 1091=0) :
 UniformChunkPortMachine.Header row.src p.e p.g p.source p.target p.borrowed (applyBlock secondSetup s) := by
 constructor
 all_goals simp [secondSetup,applyBlock,Op.apply,writeNat,next,zero,cache.src,h.inputs,h.gates,h.source,h.target,h.borrowed]

theorem save_spec {s : State} {dst : ℕ} (zero:s.natReg 1091=0) (val:s.natReg 1030=dst) :
 (applyBlock saveFirst s).natReg 1098=dst := by simp [saveFirst,applyBlock,Op.apply,writeNat,next,zero,val]

theorem save_safe {s : State} {B : ℕ} (zero:s.natReg 1091=0) (bound:WordBound B s) :
 readable saveFirst s ∧ peak saveFirst s ≤ B := by
 have :=bound.2.1 1030
 simp [saveFirst,readable,peak,Op.readable,Op.peak,zero]
 omega

theorem second_safe {s : State} {B : ℕ} (zero:s.natReg 1091=0) (bound:WordBound B s) :
 readable secondSetup s ∧ peak secondSetup s ≤ B := by
 have :=bound.2.1 1096
 simp [secondSetup,readable,peak,Op.readable,Op.peak,zero]
 omega

theorem stores_spec {p : Parameters} {count i : ℕ} {row : Row} {s : State}
 (fit:p.g+p.e+p.a ≤ p.v) (h:Cursor p count i s) (cache:Cache row s)
 (dst:s.natReg 1098=(mappedRow p fit row).dst) (src:s.natReg 1030=(mappedRow p fit row).src) :
 (applyBlock stores s).natHeap=UniformCrossShearTableMachine.putRow (p.output+3*i) (mappedRow p fit row) s.natHeap ∧
 Cursor p count (i+1) (applyBlock stores s) := by
 refine ⟨?_,⟨h.fixed.transport (block_constants stores s (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),?_⟩⟩
 · simp [stores,applyBlock,Op.apply,writeNat,next,h.fixed.header.output,h.index,h.fixed.one,
   h.fixed.three,h.fixed.zero,dst,src,cache.coefficient,mappedRow,UniformCrossShearTableMachine.putRow,Nat.add_assoc,Nat.mul_comm]
 · simp [stores,applyBlock,Op.apply,writeNat,next,h.index,h.fixed.one]

theorem stores_safe {p : Parameters} {count i B : ℕ} {row : Row} {s : State}
 (h:Cursor p count i s) (_cache:Cache row s) (hi:i < count) (geo:Geometry p count B) (bound:WordBound B s) :
 readable stores s ∧ peak stores s ≤ B := by
 have dst:=bound.2.1 1098
 have src:=bound.2.1 1030
 have coef:=bound.2.1 1097
 have countBound:count ≤ B:=by have :=geo.outputBound;omega
 have ptr:p.output+3*i+2 ≤ B:=by have :=geo.outputBound;omega
 simp [stores,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.index,h.fixed.header.output,
  h.fixed.one,h.fixed.three,h.fixed.zero,Nat.add_assoc]
 omega

theorem pc_run (n B : ℕ) (x : Fin n → ℂ) (s : State) (pc : ℕ)
 (bound:WordBound B s) (pcBound:pc ≤ B) (code:step program n x s=.running (setPC s pc)) :
 BoundedRuns program n x B s 1 (setPC s pc) :=
 .next bound code (.refl (changePC_bound B s pc bound pcBound))

/-- One physically executed row, with both literal port subroutine calls. -/
theorem iteration {p : Parameters} {count i B n : ℕ} {row : Row} {s : State} {x : Fin n → ℂ}
 (geo:Geometry p count B) (h:Cursor p count i s) (hi:i < count)
 (fields:RowFields (p.logical+3*i) row s.natHeap)
 (domain:UniformChunkPortMachine.Domain p.e p.g p.a row.dst ∧ UniformChunkPortMachine.Domain p.e p.g p.a row.src)
 (bank:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) s)
 (pc:s.pc=4) (bound:WordBound B s) : ∃t u,
 t ≤ 44 ∧ BoundedRuns program n x B s t u ∧ Cursor p count (i+1) u ∧ u.pc=4 ∧
 u.natHeap=UniformCrossShearTableMachine.putRow (p.output+3*i) (mappedRow p geo.capacity row) s.natHeap ∧ Frame s u := by
 have b:=geo.code
 let v:=setPC s 5
 have r0:BoundedRuns program n x B s 1 v:=pc_run n B x s 5 bound (by omega) (by
  simp [step,pc,loop_branch,h.index,h.fixed.header.count,hi,setPC])
 let w:=applyBlock reads v
 have safeR:=reads_safe (h.withPC 5) fields hi geo r0.final_bound
 have r1:=block_runs reads program 5 n B x v reads_code rfl r0.final_bound (by change 5+7 ≤ B;omega) safeR.1 safeR.2
 have cw:Cursor p count i w:=⟨(h.fixed.withPC 5).transport (block_constants reads v (Or.inl rfl)),
  (core_index (s:=v) (Or.inl rfl)).trans h.index⟩
 have cacheW:Cache row w:=reads_spec (h.withPC 5) fields
 have pcW:w.pc=12:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 let z:=applyBlock firstSetup w
 have safeF:=firstSetup_safe cw.fixed cacheW r1.final_bound
 have r2:=block_runs firstSetup program 12 n B x w firstSetup_code pcW r1.final_bound (by change 12+6 ≤ B;omega) safeF.1 safeF.2
 have cz:Cursor p count i z:=⟨cw.fixed.transport (block_constants firstSetup w (Or.inr (Or.inl rfl))),
  (core_index (s:=w) (Or.inr (Or.inl rfl))).trans cw.index⟩
 have cacheZ:Cache row z:=cacheW.core_transport (Or.inl rfl)
 have hz:=firstSetup_spec cw.fixed cacheW
 have pcZ:z.pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pcW];rfl
 have heapW:w.natHeap=s.natHeap:=rfl
 have heapZ:z.natHeap=s.natHeap:=rfl
 have bankZ:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) z:=by intro j hj;rw [heapZ];exact bank j hj
 obtain ⟨a,r3,pcA,dstA,frameA⟩:=port_call (n:=n) (x:=x) geo hz domain.1 bankZ portFirst_code (by omega) (by omega) pcZ r2.final_bound
 have ca:Cursor p count i a:=⟨cz.fixed.port_transport frameA,(frameA.2.2.2.2.2 1090 (by omega)).trans cz.index⟩
 have cacheA:=cacheZ.port_transport frameA
 have ha:=port_header_transport hz frameA
 let q:=applyBlock saveFirst a
 have safeS:=save_safe ca.fixed.zero r3.final_bound
 have r4:=block_runs saveFirst program 32 n B x a saveFirst_code pcA r3.final_bound (by change 32+1 ≤ B;omega) safeS.1 safeS.2
 have cq:Cursor p count i q:=⟨ca.fixed.transport (block_constants saveFirst a (Or.inr (Or.inr (Or.inl rfl)))),
  (core_index (s:=a) (Or.inr (Or.inr (Or.inl rfl)))).trans ca.index⟩
 have cacheQ:=cacheA.core_transport (Or.inr (Or.inl rfl))
 have hq:UniformChunkPortMachine.Header row.dst p.e p.g p.source p.target p.borrowed q:=by
  constructor
  all_goals simp [q,saveFirst,applyBlock,Op.apply,writeNat,next,ha.port,ha.inputs,ha.gates,ha.source,ha.target,ha.borrowed]
 have dstQ:q.natReg 1098=(mappedRow p geo.capacity row).dst:=save_spec ca.fixed.zero dstA
 have pcQ:q.pc=33:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pcA];rfl
 let y:=applyBlock secondSetup q
 have safe2:=second_safe cq.fixed.zero r4.final_bound
 have r5:=block_runs secondSetup program 33 n B x q secondSetup_code pcQ r4.final_bound (by change 33+1 ≤ B;omega) safe2.1 safe2.2
 have cy:Cursor p count i y:=⟨cq.fixed.transport (block_constants secondSetup q (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
  (core_index (s:=q) (Or.inr (Or.inr (Or.inr rfl)))).trans cq.index⟩
 have cacheY:=cacheQ.core_transport (Or.inr (Or.inr rfl))
 have hy:=secondSetup_spec hq cacheQ cq.fixed.zero
 have pcY:y.pc=34:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pcQ];rfl
 have dstY:y.natReg 1098=(mappedRow p geo.capacity row).dst:=by
  simpa [y,secondSetup,applyBlock,Op.apply,writeNat,next] using dstQ
 have heapY:y.natHeap=s.natHeap:=frameA.2.2.1.trans heapZ
 have bankY:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) y:=by intro j hj;rw [heapY];exact bank j hj
 obtain ⟨c,r6,pcC,srcC,frameC⟩:=port_call (n:=n) (x:=x) geo hy domain.2 bankY portSecond_code (by omega) (by omega) pcY r5.final_bound
 have cc:Cursor p count i c:=⟨cy.fixed.port_transport frameC,(frameC.2.2.2.2.2 1090 (by omega)).trans cy.index⟩
 have cacheC:=cacheY.port_transport frameC
 have dstC:c.natReg 1098=(mappedRow p geo.capacity row).dst:=(frameC.2.2.2.2.2 1098 (by omega)).trans dstY
 let d:=applyBlock stores c
 have safeT:=stores_safe cc cacheC hi geo r6.final_bound
 have r7:=block_runs stores program 48 n B x c stores_code pcC r6.final_bound (by change 48+9 ≤ B;omega) safeT.1 safeT.2
 have spec:=stores_spec geo.capacity cc cacheC dstC srcC
 have pcD:d.pc=57:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pcC];rfl
 have r8:BoundedRuns program n x B d 1 (setPC d 4):=pc_run n B x d 4 r7.final_bound (by omega) (by simp [step,pcD,loop_jump,setPC])
 refine ⟨26+UniformChunkPortMachine.runtime p.e p.g row.dst+UniformChunkPortMachine.runtime p.e p.g row.src,
  setPC d 4,by have :=runtime_bound p.e p.g row.dst;have :=runtime_bound p.e p.g row.src;omega,?_,spec.2.withPC 4,rfl,?_,?_⟩
 · convert r0.trans (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans r8))))))) using 1
   simp only [reads_length,firstSetup_length,saveFirst_length,secondSetup_length,stores_length]
   omega
 · change d.natHeap=_
   rw [spec.1,frameC.2.2.1,heapY]
 · have f1:Frame s w:=block_frame reads v (Or.inr (Or.inl rfl))
   have f2:=block_frame firstSetup w (Or.inr (Or.inr (Or.inl rfl)))
   have f3:=port_frame frameA
   have f4:=block_frame saveFirst a (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
   have f5:=block_frame secondSetup q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
   have f6:=port_frame frameC
   have f7:=block_frame stores c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
   exact (frame_trans f1 (frame_trans f2 (frame_trans f3 (frame_trans f4 (frame_trans f5 (frame_trans f6 f7)))))).withPC 4

/-- Execute a suffix of the physical input table, preserving all source reads. -/
theorem runRows {p : Parameters} {count B n : ℕ} {x : Fin n → ℂ}
 (geo:Geometry p count B) (rows : List Row) (i : ℕ) (s : State)
 (length:i+rows.length=count) (h:Cursor p count i s)
 (table:Table (p.logical+3*i) rows s) (domain:RowsDomain p rows)
 (bank:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) s)
 (pc:s.pc=4) (bound:WordBound B s) : ∃t u,
 t ≤ 44*rows.length ∧ BoundedRuns program n x B s t u ∧ Cursor p count count u ∧ u.pc=4 ∧
 u.natHeap=UniformCrossShearTableMachine.putRows (p.output+3*i) (rows.map (mappedRow p geo.capacity)) s.natHeap ∧ Frame s u := by
 induction rows generalizing i s with
 | nil =>
   have eqn:i=count:=by simpa using length
   subst i
   exact ⟨0,s,by simp,.refl bound,h,pc,rfl,frame_refl s⟩
 | cons row rows ih =>
   have hi:i < count:=by simp only [List.length_cons] at length;omega
   have fields:RowFields (p.logical+3*i) row s.natHeap:=table 0 (by simp)
   have dom:=domain row (by simp)
   obtain ⟨t,u,tb,run,cu,pcu,heap,frame⟩:=iteration (n:=n) (x:=x) geo h hi fields dom bank pc bound
   have tailLength:(i+1)+rows.length=count:=by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using length
   have tailTable:Table (p.logical+3*(i+1)) rows u:=by
    intro j hj
    have old:=table (j+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
    simp only [List.getElem_cons_succ] at old
    have le:p.logical+3*(i+1+j)+2 < p.output:=by
     have :=geo.inputFresh
     simp only [List.length_cons] at length
     omega
    have eq0:u.natHeap (p.logical+3*(i+1)+3*j)=s.natHeap (p.logical+3*(i+1)+3*j):=by
     rw [heap,UniformCrossShearTableMachine.putRow_outside _ _ _ _ (Or.inl (by omega))]
    have eq1:u.natHeap (p.logical+3*(i+1)+3*j+1)=s.natHeap (p.logical+3*(i+1)+3*j+1):=by
     rw [heap,UniformCrossShearTableMachine.putRow_outside _ _ _ _ (Or.inl (by omega))]
    have eq2:u.natHeap (p.logical+3*(i+1)+3*j+2)=s.natHeap (p.logical+3*(i+1)+3*j+2):=by
     rw [heap,UniformCrossShearTableMachine.putRow_outside _ _ _ _ (Or.inl (by omega))]
    unfold RowFields
    rw [eq0,eq1,eq2]
    simpa only [RowFields,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using old
   have tailBank:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) u:=by
    intro j hj
    rw [heap,UniformCrossShearTableMachine.putRow_outside _ _ _ _ (Or.inl (by have :=geo.borrowedFresh;omega))]
    exact bank j hj
   have tailDomain:RowsDomain p rows:=fun r hr=>domain r (by simp [hr])
   obtain ⟨t',w,tb',run',cw,pcw,heap',frame'⟩:=ih (i+1) u tailLength cu tailTable tailDomain tailBank pcu run.final_bound
   refine ⟨t+t',w,by simp only [List.length_cons];omega,run.trans run',cw,pcw,?_,frame_trans frame frame'⟩
   rw [heap',heap]
   simp only [List.map_cons,UniformCrossShearTableMachine.putRows]
   congr 1

theorem boot_spec {p : Parameters} {count : ℕ} {s : State} (h:Header p count s) : Cursor p count 0 (applyBlock boot s) := by
 refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
 · constructor
   all_goals simp [boot,applyBlock,Op.apply,writeNat,next,h.count,h.logical,h.output,h.inputs,h.gates,h.targets,h.source,h.target,h.borrowed]
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next]

/-- Complete fixed59 program: exactly three output fields for every actual
input row, with literal mapper calls and unchanged coefficient addresses. -/
theorem execution {p : Parameters} {B n : ℕ} {x : Fin n → ℂ} (rows : List Row) (s : State)
 (geo:Geometry p rows.length B) (h:Header p rows.length s) (table:Table p.logical rows s)
 (domain:RowsDomain p rows)
 (physical:∀j:Fin p.g,s.natHeap (p.borrowed+j.val)=some
  (UniformBorrowedCoordinateMachine.embedding p.v p.source p.e p.target p.a p.g geo.capacity j).val)
 (pc:s.pc=0) (bound:WordBound B s) : ∃t u,
 t ≤ 44*rows.length+6 ∧ BoundedExecution program n x B s t u ∧
 Table p.output (rows.map (mappedRow p geo.capacity)) u ∧ Header p rows.length u ∧
 Frame s u ∧ Outside p rows.length s u := by
 have b:=geo.code
 have bootRun:=block_runs boot program 0 n B x s boot_code pc bound (by change 0+4 ≤ B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let v:=applyBlock boot s
 have cv:=boot_spec h
 have pcv:v.pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have bank:UniformChunkPortMachine.Bank p.borrowed p.g (borrowed p geo.capacity) v:=
  UniformChunkPortMachine.bank_of_physical geo.capacity v physical
 obtain ⟨t,u,tb,run,cu,pcu,heap,frame⟩:=runRows (n:=n) (x:=x) geo rows 0 v (by simp) cv
  (by intro j hj;change RowFields _ _ s.natHeap;simpa only [Nat.mul_zero,Nat.add_zero] using table j hj) domain bank pcv bootRun.final_bound
 have endRun:BoundedRuns program n x B u 1 (setPC u 58):=pc_run n B x u 58 run.final_bound (by omega) (by
  simp [step,pcu,loop_branch,cu.index,cu.fixed.header.count,setPC])
 have halt:BoundedExecution program n x B (setPC u 58) 1 (setPC u 58):=
  .halt endRun.final_bound (by simp [step,final_halt,setPC])
 have total:=bootRun.trans (run.trans endRun) |>.executes halt
 refine ⟨4+t+1+1,setPC u 58,by omega,?_,?_,cu.fixed.header.withPC 58,
  (frame_trans (block_frame boot s (Or.inl rfl)) frame).withPC 58,?_⟩
 · convert total using 1
   simp only [boot_length]
   omega
 · intro j hj
   change RowFields _ _ u.natHeap
   rw [heap]
   simpa only [Nat.mul_zero,Nat.add_zero] using UniformCrossShearTableMachine.putRows_fields p.output
    (rows.map (mappedRow p geo.capacity)) v.natHeap j hj
 · intro q hq
   change u.natHeap q=s.natHeap q
   rw [heap]
   exact UniformCrossShearTableMachine.putRows_outside _ _ _ _ (by simpa only [Nat.mul_zero,Nat.add_zero,List.length_map] using hq)

theorem mappedRow_range {p : Parameters} {count B : ℕ} (geo:Geometry p count B) (row : Row)
 (domain:UniformChunkPortMachine.Domain p.e p.g p.a row.dst ∧ UniformChunkPortMachine.Domain p.e p.g p.a row.src) :
 (mappedRow p geo.capacity row).dst < p.v ∧ (mappedRow p geo.capacity row).src < p.v :=
 ⟨UniformChunkPortMachine.mapped_inRange _ _ _ _ _ _ _ geo.sourceRange geo.targetRange geo.separated geo.capacity domain.1,
 UniformChunkPortMachine.mapped_inRange _ _ _ _ _ _ _ geo.sourceRange geo.targetRange geo.separated geo.capacity domain.2⟩

theorem mappedRow_coefficient (p : Parameters) (fit:p.g+p.e+p.a ≤ p.v) (row : Row) :
 (mappedRow p fit row).coefficient=row.coefficient := rfl

variable {r : ℕ}

/-- The literal integer mapping is exactly the already verified chunk-word
placement applied to the dense no-hole port decoder. -/
theorem mapped_port {p : Parameters} {count B : ℕ} (geo:Geometry p count B) (he:0 < p.e)
 (q : ℕ) (hq:UniformChunkPortMachine.Domain p.e p.g p.a q) :
 UniformChunkPortMachine.mapped p.e p.g p.source p.target (borrowed p geo.capacity) q=
 ((UniformChunkPortMachine.placement p.v p.source p.e p.target p.a p.g
  geo.sourceRange geo.targetRange geo.separated geo.capacity).embedding
   (UniformToeplitzChunkWord.port (g:=p.g) (a:=p.a) he q)).val := by
 have hr: q∈Set.range (UniformToeplitzChunkWord.natPorts p.e p.g p.a):=
  (UniformChunkPortMachine.domain_range p.e p.g p.a q).mp hq
 have hn:=UniformToeplitzChunkWord.natPorts_port (g:=p.g) (a:=p.a) he q hr
 simpa only [borrowed,hn] using UniformChunkPortMachine.mapped_natPorts p.v p.source p.e p.target p.a p.g
  geo.sourceRange geo.targetRange geo.separated geo.capacity (UniformToeplitzChunkWord.port (g:=p.g) (a:=p.a) he q)

def packedRow {p : Parameters} {count B : ℕ} (geo:Geometry p count B) (he:0 < p.e)
 (locations:UniformInPlaceMachine.Locations r) (s:UniformReplayPrint.ShearCode ℕ r)
 (hs:UniformToeplitzChunkWord.Stored p.e p.g p.a s) : Row :=
 let c:=UniformDAGLayers.relabelCode
  (UniformChunkPortMachine.placement p.v p.source p.e p.target p.a p.g
   geo.sourceRange geo.targetRange geo.separated geo.capacity).embedding
  (UniformToeplitzChunkWord.packCode he s hs)
 ⟨c.dst.val,c.src.val,locations.address c.coefficient⟩

/-- Both endpoints and the unchanged coefficient address coincide with the
exact-width semantic chunk code. -/
theorem mapped_shiftedRow {p : Parameters} {count B : ℕ} (geo:Geometry p count B) (he:0 < p.e)
 (locations:UniformInPlaceMachine.Locations r) (s:UniformReplayPrint.ShearCode ℕ r)
 (hs:UniformToeplitzChunkWord.Stored p.e p.g p.a s) :
 mappedRow p geo.capacity (UniformCrossShearTableMachine.shiftedRow 0 locations s)=packedRow geo he locations s hs := by
 have hd:=mapped_port geo he s.dst ((UniformChunkPortMachine.domain_range _ _ _ _).mpr hs.1)
 have ht:=mapped_port geo he s.src ((UniformChunkPortMachine.domain_range _ _ _ _).mpr hs.2)
 change Row.mk _ _ _=Row.mk _ _ _
 congr 1
 · simpa only [UniformCrossShearTableMachine.shiftedRow,Nat.zero_add,UniformDAGLayers.relabelCode,UniformToeplitzChunkWord.packCode] using hd
 · simpa only [UniformCrossShearTableMachine.shiftedRow,Nat.zero_add,UniformDAGLayers.relabelCode,UniformToeplitzChunkWord.packCode] using ht

/-- Physical coordinate mapping preserves every matching inequality and all
indexed row occurrences. -/
def MatchingRows (rows : List Row) : Prop := rows.Pairwise (fun s t=>
 s.dst≠t.dst ∧ s.dst≠t.src ∧ s.src≠t.dst ∧ s.src≠t.src)

theorem mappedRows_matching {p : Parameters} {count B : ℕ} (geo:Geometry p count B)
 (rows : List Row) (domain:RowsDomain p rows) (hm:MatchingRows rows) :
 MatchingRows (rows.map (mappedRow p geo.capacity)) := by
 apply List.pairwise_map.mpr
 apply hm.imp_of_mem
 intro s t hs ht h
 have ds:=domain s hs
 have dt:=domain t ht
 have inj:=fun (u v : ℕ)=>UniformChunkPortMachine.mapped_injective p.v p.source p.e p.target p.a p.g
  geo.sourceRange geo.targetRange geo.separated geo.capacity (p:=u) (q:=v)
 exact ⟨fun eqn=>h.1 (inj _ _ ds.1 dt.1 eqn),fun eqn=>h.2.1 (inj _ _ ds.1 dt.2 eqn),
 fun eqn=>h.2.2.1 (inj _ _ ds.2 dt.1 eqn),fun eqn=>h.2.2.2 (inj _ _ ds.2 dt.2 eqn)⟩

/-- Actual forward sweep buckets omit the literal-zero hole in BOTH endpoints.
This statement covers the existing60/132 producer, without claiming an
inverse or broadcast producer. -/
theorem bucket_rows_domain {e g a : ℕ} (program:UniformReplayPrint.Program r e g)
 (enabled : Bool) (depth : ℕ) (locations:UniformInPlaceMachine.Locations r)
 (p : Parameters) (he:p.e=e) (hg:p.g=g) (ha:p.a=a) :
 RowsDomain p ((UniformCrossDepthReplayPreparation.bucket program enabled depth).map
  (UniformCrossShearTableMachine.shiftedRow 0 locations)) := by
 intro row hr
 obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hr
 have mem:= (List.mem_filter.mp hs).1
 have bounds:=UniformDAGLayers.natSweep_bounds program enabled s mem
 have nonzero:=UniformDAGLayers.natSweep_src_nonzero program enabled s mem
 change UniformChunkPortMachine.Domain p.e p.g p.a (0+s.dst) ∧ UniformChunkPortMachine.Domain p.e p.g p.a (0+s.src)
 simp only [Nat.zero_add,he,hg,ha,UniformChunkPortMachine.Domain]
 constructor <;> omega

theorem bucket_execution {p : Parameters} {B n r : ℕ} {x : Fin n → ℂ}
 (printed:UniformReplayPrint.Program r p.e p.g) (enabled:Bool) (depth:ℕ)
 (locations:UniformInPlaceMachine.Locations r) (s:State)
 (geo:Geometry p (UniformCrossDepthReplayPreparation.bucket printed enabled depth).length B)
 (h:Header p (UniformCrossDepthReplayPreparation.bucket printed enabled depth).length s)
 (table:Table p.logical ((UniformCrossDepthReplayPreparation.bucket printed enabled depth).map
  (UniformCrossShearTableMachine.shiftedRow 0 locations)) s)
 (physical:∀j:Fin p.g,s.natHeap (p.borrowed+j.val)=some
  (UniformBorrowedCoordinateMachine.embedding p.v p.source p.e p.target p.a p.g geo.capacity j).val)
 (pc:s.pc=0) (bound:WordBound B s) : ∃t u,
 t ≤ 44*(UniformCrossDepthReplayPreparation.bucket printed enabled depth).length+6 ∧
 BoundedExecution program n x B s t u ∧
 Table p.output (((UniformCrossDepthReplayPreparation.bucket printed enabled depth).map
  (UniformCrossShearTableMachine.shiftedRow 0 locations)).map (mappedRow p geo.capacity)) u ∧
 Header p (UniformCrossDepthReplayPreparation.bucket printed enabled depth).length u ∧ Frame s u ∧
 Outside p (UniformCrossDepthReplayPreparation.bucket printed enabled depth).length s u := by
 simpa only [List.length_map] using execution (n:=n) (x:=x)
  ((UniformCrossDepthReplayPreparation.bucket printed enabled depth).map (UniformCrossShearTableMachine.shiftedRow 0 locations))
  s (by simpa only [List.length_map] using geo) (by simpa only [List.length_map] using h) table (bucket_rows_domain printed enabled depth locations p rfl rfl rfl) physical pc bound

end
end ExactFourierCircuits.UniformChunkRowTableMachine