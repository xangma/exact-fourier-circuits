import UniformChunkRowTableMachine
import UniformColorLayerTableMachine
import UniformMatchingAxisTableMachine
import UniformCrossHeightPreparationMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformChunkMatchingPreparation
open UniformMachine UniformAssembly UniformColoring UniformReplayPrint
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInPlaceMachine (Row)
open UniformCrossShearTableMachine (Table RowFields)

/-- Actual caller1180..1192: tensor radix,source/target offsets,borrowed
coordinates,selected rows/ordinals,mapped rows,permutation,widths,markers,
axis row,depth,color. Original Height1050..1062 supplies K,a,e,J.
Scratch1193..1205 computes every other header from integer reads/operations. -/
def boot : List Op := [.literal 1193 0,.literal 1194 1,.literal 1195 2,
 .literal 1196 3,.literal 1197 6,.literal 1198 0,.literal 1199 1]
def power : List Op := [.mul 1199 1199 1195,.add 1198 1198 1194]
def size : List Op := [.mul 1200 1050 1199,.mul 1200 1200 1196,
 .mul 1201 1199 1195,.add 1200 1200 1201,.mul 1200 1200 1197,
 .mul 1201 1051 1195,.add 1200 1200 1201]
def directory : List Op := [.mul 1202 1191 1196,.add 1202 1059 1202,
 .getNat 1203 1202,.add 1202 1202 1194,.getNat 1204 1202,
 .add 1202 1202 1194,.getNat 1205 1202]
def borrowSetup : List Op := [.add 261 1181 1193,.add 262 1052 1193,
 .add 263 1182 1193,.add 264 1051 1193,.add 265 1200 1193,.add 266 1183 1193]
def colorSetup : List Op := [.add 880 1203 1193,.add 881 1204 1193,
 .add 882 1205 1193,.add 883 1192 1193,.add 884 1184 1193,.add 885 1185 1193]
def rowSetup : List Op := [.add 1080 894 1193,.add 1081 1184 1193,.add 1082 1186 1193,
 .add 1083 1052 1193,.add 1084 1200 1193,.add 1085 1051 1193,
 .add 1086 1181 1193,.add 1087 1182 1193,.add 1088 1183 1193]
def axisSetup : List Op := [.add 840 1180 1193,.add 841 894 1193,.add 842 1186 1193,
 .add 843 1187 1193,.add 844 1188 1193,.add 845 1189 1193,.add 846 1190 1193]
def entryCode : Program := boot.map Op.code ++ [.branchLT 1198 1050 8 11] ++ power.map Op.code ++
 [.jump 7] ++ size.map Op.code ++ directory.map Op.code ++ borrowSetup.map Op.code
def beforeColor : Program := entryCode ++ UniformBorrowedCoordinateMachine.program.map (relocate 31 48) ++ colorSetup.map Op.code
def beforeRow : Program := beforeColor ++ UniformColorLayerTableMachine.program.map (relocate 54 84) ++ rowSetup.map Op.code
def beforeAxis : Program := beforeRow ++ UniformChunkRowTableMachine.program.map (relocate 93 152) ++ axisSetup.map Op.code
def program : Program := beforeAxis ++ UniformMatchingAxisTableMachine.program.map (relocate 159 214) ++ [.halt]

theorem boot_length : boot.length=7:=rfl
theorem power_length : power.length=2:=rfl
theorem size_length : size.length=7:=rfl
theorem directory_length : directory.length=7:=rfl
theorem borrowSetup_length : borrowSetup.length=6:=rfl
theorem colorSetup_length : colorSetup.length=6:=rfl
theorem rowSetup_length : rowSetup.length=9:=rfl
theorem axisSetup_length : axisSetup.length=7:=rfl
theorem entryCode_length : entryCode.length=31:=by simp [entryCode,boot_length,power_length,size_length,directory_length,borrowSetup_length]
theorem beforeColor_length : beforeColor.length=54:=by simp [beforeColor,entryCode_length,UniformBorrowedCoordinateMachine.program_length,colorSetup_length]
theorem beforeRow_length : beforeRow.length=93:=by simp [beforeRow,beforeColor_length,UniformColorLayerTableMachine.program_length,rowSetup_length]
theorem beforeAxis_length : beforeAxis.length=159:=by simp [beforeAxis,beforeRow_length,UniformChunkRowTableMachine.program_length,axisSetup_length]
theorem program_length : program.length=215:=by simp [program,beforeAxis_length,UniformMatchingAxisTableMachine.program_length]

theorem boot_code : BlockAt boot program 0:=by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem power_code : BlockAt power program 8:=by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem size_code : BlockAt size program 11:=by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem directory_code : BlockAt directory program 18:=by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem borrowSetup_code : BlockAt borrowSetup program 25:=by intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem colorSetup_code : BlockAt colorSetup program 48:=by intro i hi;change i < 6 at hi;interval_cases i <;> rfl
theorem rowSetup_code : BlockAt rowSetup program 84:=by intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem axisSetup_code : BlockAt axisSetup program 152:=by intro i hi;change i < 7 at hi;interval_cases i <;> rfl

theorem borrow_code : CodeAt UniformBorrowedCoordinateMachine.program program 31 48:=by
 let after:=colorSetup.map Op.code ++ UniformColorLayerTableMachine.program.map (relocate 54 84) ++ rowSetup.map Op.code ++
  UniformChunkRowTableMachine.program.map (relocate 93 152) ++ axisSetup.map Op.code ++
  UniformMatchingAxisTableMachine.program.map (relocate 159 214) ++ [.halt]
 have eqn:program=entryCode ++ UniformBorrowedCoordinateMachine.program.map (relocate 31 48) ++ after:=by
  simp [program,beforeAxis,beforeRow,beforeColor,after,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code entryCode after _ 31 48 entryCode_length

theorem color_code : CodeAt UniformColorLayerTableMachine.program program 54 84:=by
 let after:=rowSetup.map Op.code ++ UniformChunkRowTableMachine.program.map (relocate 93 152) ++ axisSetup.map Op.code ++
  UniformMatchingAxisTableMachine.program.map (relocate 159 214) ++ [.halt]
 have eqn:program=beforeColor ++ UniformColorLayerTableMachine.program.map (relocate 54 84) ++ after:=by
  simp [program,beforeAxis,beforeRow,after,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code beforeColor after _ 54 84 beforeColor_length

theorem row_code : CodeAt UniformChunkRowTableMachine.program program 93 152:=by
 let after:=axisSetup.map Op.code ++ UniformMatchingAxisTableMachine.program.map (relocate 159 214) ++ [.halt]
 have eqn:program=beforeRow ++ UniformChunkRowTableMachine.program.map (relocate 93 152) ++ after:=by
  simp [program,beforeAxis,after,List.append_assoc]
 rw [eqn]
 exact UniformChunkRowTableMachine.segment_code beforeRow after _ 93 152 beforeRow_length

theorem axis_code : CodeAt UniformMatchingAxisTableMachine.program program 159 214:=by
 simpa only [program,List.append_assoc] using UniformChunkRowTableMachine.segment_code beforeAxis [.halt] _ 159 214 beforeAxis_length

theorem power_branch : program[7]?=some (.branchLT 1198 1050 8 11):=rfl
theorem power_jump : program[10]?=some (.jump 7):=rfl
theorem final_halt : program[214]?=some .halt:=rfl

structure Parameters where
 height : UniformCrossHeightPreparationMachine.Parameters
 radix : ℕ
 source : ℕ
 target : ℕ
 borrowed : ℕ
 selected : ℕ
 ordinals : ℕ
 mapped : ℕ
 permutation : ℕ
 widths : ℕ
 markers : ℕ
 axis : ℕ
 depth : ℕ
 color : ℕ

noncomputable section

structure Header (p : Parameters) (s : State) : Prop where
 height : UniformCrossHeightPreparationMachine.Header p.height s
 radix : s.natReg 1180=p.radix
 source : s.natReg 1181=p.source
 target : s.natReg 1182=p.target
 borrowed : s.natReg 1183=p.borrowed
 selected : s.natReg 1184=p.selected
 ordinals : s.natReg 1185=p.ordinals
 mapped : s.natReg 1186=p.mapped
 permutation : s.natReg 1187=p.permutation
 widths : s.natReg 1188=p.widths
 markers : s.natReg 1189=p.markers
 axis : s.natReg 1190=p.axis
 depth : s.natReg 1191=p.depth
 color : s.natReg 1192=p.color

structure Constants (s : State) : Prop where
 zero : s.natReg 1193=0
 one : s.natReg 1194=1
 two : s.natReg 1195=2
 three : s.natReg 1196=3
 six : s.natReg 1197=6
structure Sizing (p : Parameters) (i : ℕ) (s : State) : Prop where
 header : Header p s
 constants : Constants s
 index : s.natReg 1198=i
 width : s.natReg 1199=2^i
structure Sized (p : Parameters) (s : State) : Prop where
 header : Header p s
 constants : Constants s
 gates : s.natReg 1200=UniformCrossHeightPreparationMachine.gates p.height
structure Loaded (p : Parameters) (count : ℕ) (s : State) : Prop where
 sized : Sized p s
 count : s.natReg 1203=count
 rows : s.natReg 1204=UniformCrossHeightPreparationMachine.rowBase p.height p.depth
 colors : s.natReg 1205=UniformCrossHeightPreparationMachine.colorBase p.height p.depth

/-- Original geometry and fresh physical allocation only; no selected/mapped
rows, matching permutation, widths or ready axis enter. -/
structure Layout (p : Parameters) (B : ℕ) : Prop where
 code : 215 ≤ B
 radixPositive : 2 ≤ p.radix
 sourceRange : p.source+p.height.e ≤ p.radix
 targetRange : p.target+p.height.a ≤ p.radix
 separated : p.source+p.height.e ≤ p.target ∨ p.target+p.height.a ≤ p.source
 capacity : UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix
 oldRows : UniformCrossHeightPreparationMachine.rowBase p.height (UniformCrossHeightPreparationMachine.height p.height) ≤ p.borrowed
 oldColors : UniformCrossHeightPreparationMachine.colorBase p.height (UniformCrossHeightPreparationMachine.height p.height) ≤ p.borrowed
 oldDirectory : UniformCrossHeightPreparationMachine.recordBase p.height (UniformCrossHeightPreparationMachine.height p.height) ≤ p.borrowed
 borrowFresh : p.borrowed+UniformCrossHeightPreparationMachine.gates p.height ≤ p.selected
 selectedFresh : p.selected+6*UniformCrossHeightPreparationMachine.gates p.height ≤ p.ordinals
 ordinalFresh : p.ordinals+2*UniformCrossHeightPreparationMachine.gates p.height ≤ p.mapped
 mappedFresh : p.mapped+6*UniformCrossHeightPreparationMachine.gates p.height ≤ p.permutation
 permutationFresh : p.permutation+p.radix ≤ p.widths
 widthsFresh : p.widths+p.radix ≤ p.markers
 markersFresh : p.markers+p.radix ≤ p.axis
 finalBound : p.axis+4 ≤ B
 depthBound : p.depth < UniformCrossHeightPreparationMachine.height p.height
 colorBound : p.color < 11

/-- Caller/setup and helper scratch registers; all other Nat registers are retained. -/
def Protected (r : ℕ) := (r < 261 ∨ 273 ≤ r) ∧ (r < 840 ∨ 862 ≤ r) ∧
 (r < 880 ∨ 900 ≤ r) ∧ (r < 1020 ∨ 1035 ≤ r) ∧ (r < 1080 ∨ 1101 ≤ r) ∧ (r < 1193 ∨ 1206 ≤ r)
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ∀r,Protected r  →  u.natReg r=s.natReg r
def Outside (p : Parameters) (s u : State) : Prop :=
 ∀q,(q < p.borrowed ∨ p.axis+4 ≤ q) → u.natHeap q=s.natHeap q

theorem frame_refl (s : State) : Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (f:Frame s u) (g:Frame u v) : Frame s v:=
 ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,g.2.2.2.1.trans f.2.2.2.1,
 fun r hr=>(g.2.2.2.2 r hr).trans (f.2.2.2.2 r hr)⟩

def CallerBlock (b : List Op) : Prop := b=boot ∨ b=power ∨ b=size ∨ b=directory ∨
 b=borrowSetup ∨ b=colorSetup ∨ b=rowSetup ∨ b=axisSetup

theorem caller_frame (b : List Op) (s : State) (hb:CallerBlock b) : Frame s (applyBlock b s):=by
 rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
 all_goals intro r hr;unfold Protected at hr
 all_goals simp (disch:=omega) [boot,power,size,directory,borrowSetup,colorSetup,rowSetup,axisSetup,applyBlock,Op.apply,writeNat,next]

theorem caller_heap (b : List Op) (s : State) (hb:CallerBlock b) : (applyBlock b s).natHeap=s.natHeap:=by
 rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem Frame.withPC {s u : State} (f:Frame s u) (pc : ℕ) : Frame s (setPC u pc):=f

theorem Header.transport {p : Parameters} {s u : State} (h:Header p s) (f:Frame s u) : Header p u:=by
 refine ⟨h.height.transport_register (fun r lo hi=>f.2.2.2.2 r (by unfold Protected;omega)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.radix
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.source
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.target
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.borrowed
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.selected
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.ordinals
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.mapped
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.permutation
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.widths
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.markers
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.axis
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.depth
 | exact (f.2.2.2.2 _ (by unfold Protected;omega)).trans h.color

theorem Header.withPC {p : Parameters} {s : State} (h:Header p s) (pc : ℕ) : Header p (setPC s pc):=
 h.transport (u:=setPC s pc) (frame_refl s)

theorem Constants.transport {s u : State} (h:Constants s)
 (f:∀r,1193 ≤ r → r ≤ 1197 → u.natReg r=s.natReg r) : Constants u:=
 ⟨(f 1193 (by omega) (by omega)).trans h.zero,(f 1194 (by omega) (by omega)).trans h.one,
 (f 1195 (by omega) (by omega)).trans h.two,(f 1196 (by omega) (by omega)).trans h.three,
 (f 1197 (by omega) (by omega)).trans h.six⟩

theorem Constants.withPC {s : State} (h:Constants s) (pc : ℕ) : Constants (setPC s pc):=
 ⟨h.zero,h.one,h.two,h.three,h.six⟩

theorem constants_block {s : State} {b : List Op} (c:Constants s)
 (hb:b=power ∨ b=size ∨ b=directory ∨ b=borrowSetup ∨ b=colorSetup ∨ b=rowSetup ∨ b=axisSetup) : Constants (applyBlock b s):=by
 apply c.transport
 rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals intro r lo hi
 all_goals simp (disch:=omega) [power,size,directory,borrowSetup,colorSetup,rowSetup,axisSetup,applyBlock,Op.apply,writeNat,next]

theorem Sized.transport {p : Parameters} {s u : State} (h:Sized p s) (f:Frame s u)
 (regs:∀r,1193 ≤ r → r ≤ 1205 → u.natReg r=s.natReg r) : Sized p u:=
 ⟨h.header.transport f,h.constants.transport (fun r lo hi=>regs r lo (by omega)),
 (regs 1200 (by omega) (by omega)).trans h.gates⟩

theorem Loaded.transport {p : Parameters} {count : ℕ} {s u : State} (h:Loaded p count s) (f:Frame s u)
 (regs:∀r,1193 ≤ r → r ≤ 1205 → u.natReg r=s.natReg r) : Loaded p count u:=
 ⟨h.sized.transport f regs,(regs 1203 (by omega) (by omega)).trans h.count,
 (regs 1204 (by omega) (by omega)).trans h.rows,(regs 1205 (by omega) (by omega)).trans h.colors⟩

theorem Sizing.withPC {p : Parameters} {i : ℕ} {s : State} (h:Sizing p i s) (pc : ℕ) : Sizing p i (setPC s pc):=
 ⟨h.header.withPC pc,h.constants.withPC pc,h.index,h.width⟩
theorem Sized.withPC {p : Parameters} {s : State} (h:Sized p s) (pc : ℕ) : Sized p (setPC s pc):=
 ⟨h.header.withPC pc,h.constants.withPC pc,h.gates⟩
theorem Loaded.withPC {p : Parameters} {count : ℕ} {s : State} (h:Loaded p count s) (pc : ℕ) : Loaded p count (setPC s pc):=
 ⟨h.sized.withPC pc,h.count,h.rows,h.colors⟩

theorem setup_registers {b : List Op} {s : State} (hb:b=borrowSetup ∨ b=colorSetup ∨ b=rowSetup ∨ b=axisSetup) :
 ∀r,1193 ≤ r → r ≤ 1205 → (applyBlock b s).natReg r=s.natReg r:=by
 rcases hb with rfl|rfl|rfl|rfl
 all_goals intro r lo hi
 all_goals simp (disch:=omega) [borrowSetup,colorSetup,rowSetup,axisSetup,applyBlock,Op.apply,writeNat,next]

theorem borrow_frame {s u : State} (f:UniformBorrowedCoordinateMachine.Frame s u) : Frame s u:=
 ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,fun r hr=>f.2.2.2.2 r (by have :=hr.1;omega)⟩
theorem color_frame {s u : State} (f:UniformColorLayerTableMachine.Frame s u) : Frame s u:=
 ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,fun r hr=>f.2.2.2.2 r (by have :=hr.2.2.1;omega)⟩
theorem row_frame {s u : State} (f:UniformChunkRowTableMachine.Frame s u) : Frame s u:=
 ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,fun r hr=>f.2.2.2.2 r ⟨by have :=hr.2.2.2.1;omega,by have :=hr.2.2.2.2.1;omega⟩⟩
theorem axis_frame {s u : State} (f:UniformMatchingAxisTableMachine.Frame s u) : Frame s u:=
 ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,fun r hr=>f.2.2.2.2 r (by have :=hr.2.1;omega)⟩

theorem boot_spec {p : Parameters} {s : State} (h:Header p s) : Sizing p 0 (applyBlock boot s):=by
 refine ⟨h.transport (caller_frame boot s (Or.inl rfl)),⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next]

theorem power_spec {p : Parameters} {i : ℕ} {s : State} (h:Sizing p i s) : Sizing p (i+1) (applyBlock power s):=by
 refine ⟨h.header.transport (caller_frame power s (Or.inr (Or.inl rfl))),
 constants_block h.constants (Or.inl rfl),?_,?_⟩
 · simp [power,applyBlock,Op.apply,writeNat,next,h.index,h.constants.one]
 · simp [power,applyBlock,Op.apply,writeNat,next,h.width,h.constants.two,pow_succ]

theorem size_spec {p : Parameters} {s : State} (h:Sizing p p.height.K s) : Sized p (applyBlock size s):=by
 refine ⟨h.header.transport (caller_frame size s (Or.inr (Or.inr (Or.inl rfl)))),
 constants_block h.constants (Or.inr (Or.inl rfl)),?_⟩
 simp [size,applyBlock,Op.apply,writeNat,next,h.header.height.exponent,h.header.height.targets,
 h.constants.two,h.constants.three,h.constants.six,h.width,UniformCrossHeightPreparationMachine.gates,
 UniformCrossHeightPreparationMachine.widthOf,UniformRadixTwoDAG.width_eq]
 ring

theorem directory_spec {p : Parameters} {count : ℕ} {s : State} (h:Sized p s)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth count s) : Loaded p count (applyBlock directory s):=by
 refine ⟨⟨h.header.transport (caller_frame directory s (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
 constants_block h.constants (Or.inr (Or.inr (Or.inl rfl))),?_⟩,?_,?_,?_⟩
 · simp [directory,applyBlock,Op.apply,writeNat,next,h.gates]
 · have hd:=record.1
   have hs:=record.2.1
   have hc:=record.2.2
   simp only [UniformCrossHeightPreparationMachine.recordBase,Nat.mul_comm,Nat.add_assoc] at hd hs hc
   simp [directory,applyBlock,Op.apply,writeNat,next,h.header.height.directory,h.header.depth,
    h.constants.three,h.constants.one,Nat.add_assoc,hd]
 · have hs:=record.2.1
   simp only [UniformCrossHeightPreparationMachine.recordBase,Nat.mul_comm,Nat.add_assoc] at hs
   simp [directory,applyBlock,Op.apply,writeNat,next,h.header.height.directory,h.header.depth,
    h.constants.three,h.constants.one,Nat.add_assoc,hs]
 · have hc:=record.2.2
   simp only [UniformCrossHeightPreparationMachine.recordBase,Nat.mul_comm,Nat.add_assoc] at hc
   simp [directory,applyBlock,Op.apply,writeNat,next,h.header.height.directory,h.header.depth,
    h.constants.three,h.constants.one,Nat.add_assoc,hc]

/-- Charged dyadic sizing, with every iteration and exit branch included. -/
theorem sizing_loop {p : Parameters} {B n : ℕ} {x : Fin n  →  ℂ}
 (remaining i : ℕ) (s : State) (h:Sizing p i s) (length:i+remaining=p.height.K)
 (pc:s.pc=7) (bound:WordBound B s) (code:215 ≤ B) (hN:2^p.height.K ≤ B) : ∃u,
 BoundedRuns program n x B s (4*remaining+1) u ∧ Sizing p p.height.K u ∧ u.pc=11 ∧
 u.natHeap=s.natHeap ∧ Frame s u:=by
 induction remaining generalizing i s with
 | zero=>
   have eqn:i=p.height.K:=by omega
   subst i
   have run:=UniformRadixInstructionMachine.branch_runs program n B 1198 1050 8 11 x s bound (by omega) (by omega) (by rw [pc];exact power_branch)
   simp only [h.index,h.header.height.exponent,lt_self_iff_false,ite_false] at run
   exact ⟨setPC s 11,by simpa only [setPC] using run,h.withPC 11,rfl,rfl,frame_refl s⟩
 | succ rem ih=>
   have hi:i < p.height.K:=by omega
   have run:BoundedRuns program n x B s 1 (setPC s 8):=by
    have branch:=UniformRadixInstructionMachine.branch_runs program n B 1198 1050 8 11 x s bound (by omega) (by omega) (by rw [pc];exact power_branch)
    simpa only [h.index,h.header.height.exponent,hi,ite_true,setPC] using branch
   let v:=applyBlock power (setPC s 8)
   have nk:2^(i+1) ≤ B:=(Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega)).trans hN
   have kb:p.height.K ≤ B:=by simpa only [h.header.height.exponent] using bound.2.1 1050
   have safe:readable power (setPC s 8) ∧ peak power (setPC s 8) ≤ B:=by
    simp [readable,peak,power,Op.readable,Op.peak,Op.apply,writeNat,next,setPC,h.constants.two,h.constants.one,h.width,h.index]
    rw [pow_succ] at nk
    omega
   have body:=block_runs power program 8 n B x (setPC s 8) power_code rfl run.final_bound (by change 8+2 ≤ B;omega) safe.1 safe.2
   have hv:=power_spec (h.withPC 8)
   have pv:v.pc=10:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
   have jump:=UniformRadixInstructionMachine.jump_runs program n B 7 x v body.final_bound (by omega) (by rw [pv];exact power_jump)
   obtain ⟨u,tail,hu,pu,heap,frame⟩:=ih (i+1) (setPC v 7) (hv.withPC 7) (by omega) rfl jump.final_bound
   refine ⟨u,?_,hu,pu,heap,frame_trans (caller_frame power (setPC s 8) (Or.inr (Or.inl rfl))) frame⟩
   convert run.trans (body.trans (jump.trans tail)) using 1
   simp only [power_length]
   omega

theorem layout_bounds {p : Parameters} {B : ℕ} (l:Layout p B) :
 p.radix ≤ B ∧ UniformCrossHeightPreparationMachine.gates p.height ≤ B ∧ 2^p.height.K ≤ B:=by
 have r:p.radix ≤ B:=by have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;have :=l.finalBound;omega
 have g:UniformCrossHeightPreparationMachine.gates p.height ≤ B:=by have :=l.capacity;omega
 have ng:2^p.height.K ≤ UniformCrossHeightPreparationMachine.gates p.height:=by
  simp only [UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,UniformRadixTwoDAG.width_eq]
  omega
 exact ⟨r,g,ng.trans g⟩

theorem size_safe {p : Parameters} {s : State} {B : ℕ}
 (h:Sizing p p.height.K s) (l:Layout p B) : readable size s ∧ peak size s ≤ B:=by
 have g:6*(3*p.height.K*2^p.height.K+2*2^p.height.K)+2*p.height.a ≤ B:=by
  simpa only [UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,UniformRadixTwoDAG.width_eq] using (layout_bounds l).2.1
 simp [size,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.header.height.exponent,
 h.header.height.targets,h.constants.two,h.constants.three,h.constants.six,h.width]
 repeat' constructor
 all_goals nlinarith

theorem directory_safe {p : Parameters} {count : ℕ} {s : State} {B : ℕ}
 (h:Sized p s) (record:UniformCrossHeightPreparationMachine.Record p.height p.depth count s)
 (bound:WordBound B s) : readable directory s ∧ peak directory s ≤ B:=by
 rcases record with ⟨hd,hs,hc⟩
 have db:count ≤ B:=(bound.2.2.1 _ _ hd).2
 have rb:UniformCrossHeightPreparationMachine.rowBase p.height p.depth ≤ B:=(bound.2.2.1 _ _ hs).2
 have cb:UniformCrossHeightPreparationMachine.colorBase p.height p.depth ≤ B:=(bound.2.2.1 _ _ hc).2
 have ab:UniformCrossHeightPreparationMachine.recordBase p.height p.depth+2 ≤ B:=(bound.2.2.1 _ _ hc).1
 simp only [UniformCrossHeightPreparationMachine.recordBase,Nat.mul_comm,Nat.add_assoc] at hd hs hc
 simp [directory,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.header.depth,h.header.height.directory,
 h.constants.three,h.constants.one,Nat.add_assoc,hd,hs,hc]
 unfold UniformCrossHeightPreparationMachine.recordBase at ab
 omega

theorem setup_safe {s : State} {b : List Op} {B : ℕ} (c:Constants s) (bound:WordBound B s)
 (hb:b=borrowSetup ∨ b=colorSetup ∨ b=rowSetup ∨ b=axisSetup) : readable b s ∧ peak b s ≤ B:=by
 rcases hb with rfl|rfl|rfl|rfl
 all_goals simp [borrowSetup,colorSetup,rowSetup,axisSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,c.zero]
 all_goals repeat' constructor
 all_goals exact bound.2.1 _

theorem borrowSetup_spec {p : Parameters} {count : ℕ} {s : State} (h:Loaded p count s) :
 UniformBorrowedCoordinateMachine.Headers p.source p.height.e p.target p.height.a
  (UniformCrossHeightPreparationMachine.gates p.height) p.borrowed (applyBlock borrowSetup s):=by
 simp [UniformBorrowedCoordinateMachine.Headers,borrowSetup,applyBlock,Op.apply,writeNat,next,h.sized.header.source,
 h.sized.header.height.inputs,h.sized.header.target,h.sized.header.height.targets,h.sized.gates,
 h.sized.header.borrowed,h.sized.constants.zero]

theorem startup {p : Parameters} {count B n : ℕ} {x : Fin n → ℂ} (s : State)
 (l:Layout p B) (header:Header p s) (record:UniformCrossHeightPreparationMachine.Record p.height p.depth count s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedRuns program n x B s (4*p.height.K+28) u ∧ u.pc=31 ∧ Loaded p count u ∧
 UniformBorrowedCoordinateMachine.Headers p.source p.height.e p.target p.height.a
  (UniformCrossHeightPreparationMachine.gates p.height) p.borrowed u ∧ u.natHeap=s.natHeap ∧ Frame s u:=by
 have b:=l.code
 have start:=block_runs boot program 0 n B x s boot_code pc bound (by change 0+7 ≤ B;omega)
  (by simp [readable,boot,Op.readable]) (by simp [peak,boot,Op.peak];omega)
 let v:=applyBlock boot s
 have cv:=boot_spec header
 have pv:v.pc=7:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 obtain ⟨w,loop,cw,pw,heapW,frameW⟩:=sizing_loop (n:=n) (x:=x) p.height.K 0 v cv (by simp) pv start.final_bound b (layout_bounds l).2.2
 let a:=applyBlock size w
 have safeS:=size_safe cw l
 have runS:=block_runs size program 11 n B x w size_code pw loop.final_bound (by change 11+7 ≤ B;omega) safeS.1 safeS.2
 have ca:=size_spec cw
 have pa:a.pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pw];rfl
 have heapA:a.natHeap=s.natHeap:=heapW
 have recA:UniformCrossHeightPreparationMachine.Record p.height p.depth count a:=by
  simpa only [UniformCrossHeightPreparationMachine.Record,heapA] using record
 let q:=applyBlock directory a
 have safeD:=directory_safe ca recA runS.final_bound
 have runD:=block_runs directory program 18 n B x a directory_code pa runS.final_bound (by change 18+7 ≤ B;omega) safeD.1 safeD.2
 have cq:=directory_spec ca recA
 have pq:q.pc=25:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pa];rfl
 let z:=applyBlock borrowSetup q
 have safeB:=setup_safe cq.sized.constants runD.final_bound (Or.inl rfl)
 have runB:=block_runs borrowSetup program 25 n B x q borrowSetup_code pq runD.final_bound (by change 25+6 ≤ B;omega) safeB.1 safeB.2
 have cz:=cq.transport (caller_frame borrowSetup q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (setup_registers (Or.inl rfl))
 have pz:z.pc=31:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pq];rfl
 refine ⟨z,?_,pz,cz,borrowSetup_spec cq,heapA,?_⟩
 · convert start.trans (loop.trans (runS.trans (runD.trans runB))) using 1
   simp only [boot_length,size_length,directory_length,borrowSetup_length]
   omega
 · have f0:=caller_frame boot s (Or.inl rfl)
   have f1:=caller_frame size w (Or.inr (Or.inr (Or.inl rfl)))
   have f2:=caller_frame directory a (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
   have f3:=caller_frame borrowSetup q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
   exact frame_trans f0 (frame_trans frameW (frame_trans f1 (frame_trans f2 f3)))

theorem placed_zero (s : State) (base : ℕ) (pc:s.pc=base) : placed base (setPC s 0)=s:=by
 cases s;simp_all [placed,setPC]

def PhysicalBorrowed (p : Parameters) (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix) (s : State) : Prop :=
 ∀j:Fin (UniformCrossHeightPreparationMachine.gates p.height),s.natHeap (p.borrowed+j.val)=some
  (UniformBorrowedCoordinateMachine.embedding p.radix p.source p.height.e p.target p.height.a
   (UniformCrossHeightPreparationMachine.gates p.height) fit j).val

theorem borrowed_stage {p : Parameters} {M B n : ℕ} {x : Fin n → ℂ} (s : State)
 (l:Layout p B) (h:Loaded p M s)
 (headers:UniformBorrowedCoordinateMachine.Headers p.source p.height.e p.target p.height.a
  (UniformCrossHeightPreparationMachine.gates p.height) p.borrowed s)
 (pc:s.pc=31) (bound:WordBound B s) : ∃t u,
 t ≤ 11*p.radix+7 ∧ BoundedRuns program n x B s t u ∧ u.pc=48 ∧ Loaded p M u ∧
 PhysicalBorrowed p l.capacity u ∧ Outside p s u ∧ Frame s u:=by
 have b:=l.code
 have vals:=layout_bounds l
 have output:p.borrowed+UniformCrossHeightPreparationMachine.gates p.height ≤ B:=by
  have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh
  have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;have :=l.finalBound;omega
 obtain ⟨t,u,run,cost,bank,frame,outside⟩:=UniformBorrowedCoordinateMachine.physical_embedding n x
  p.radix p.source p.height.e p.target p.height.a (UniformCrossHeightPreparationMachine.gates p.height) p.borrowed B
  (setPC s 0) headers rfl (changePC_bound B s 0 bound (by omega)) (by omega) vals.1
  (l.sourceRange.trans vals.1) (l.targetRange.trans vals.1) output l.capacity
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed borrow_code (by rw [UniformBorrowedCoordinateMachine.program_length];omega) (by omega) run
 rw [placed_zero s 31 pc] at placedRun
 have f:Frame s (setPC u 48):=borrow_frame frame
 have regs:∀r,1193 ≤ r → r ≤ 1205 → (setPC u 48).natReg r=s.natReg r:=fun r lo _=>frame.2.2.2.2 r (by omega)
 refine ⟨t,setPC u 48,cost,placedRun,rfl,h.transport f regs,bank,?_,f⟩
 intro q hq
 exact outside q (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;omega)

theorem colorSetup_spec {p : Parameters} {M : ℕ} {s : State} (h:Loaded p M s) :
 UniformColorLayerTableMachine.Header M (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (UniformCrossHeightPreparationMachine.colorBase p.height p.depth) p.color p.selected p.ordinals
   (applyBlock colorSetup s):=by
 constructor
 all_goals simp [colorSetup,applyBlock,Op.apply,writeNat,next,h.count,h.rows,h.colors,h.sized.constants.zero,
 h.sized.header.color,h.sized.header.selected,h.sized.header.ordinals]

def rowParameters (p : Parameters) : UniformChunkRowTableMachine.Parameters:=
 ⟨p.radix,p.height.e,UniformCrossHeightPreparationMachine.gates p.height,p.height.a,p.source,p.target,p.borrowed,p.selected,p.mapped⟩

theorem row_geometry {p : Parameters} {M B : ℕ} (l:Layout p B) (hm:M ≤ 2*UniformCrossHeightPreparationMachine.gates p.height) :
 UniformChunkRowTableMachine.Geometry (rowParameters p) M B:=by
 constructor
 · have :=l.code;omega
 · exact (layout_bounds l).1
 · exact l.sourceRange
 · exact l.targetRange
 · exact l.separated
 · exact l.capacity
 · change p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height ≤ B
   have :=l.capacity;have :=l.markersFresh;have :=l.finalBound;omega
 · change p.selected+3*M ≤ p.mapped
   have :=l.selectedFresh;have :=l.ordinalFresh;omega
 · change p.borrowed+UniformCrossHeightPreparationMachine.gates p.height ≤ p.mapped
   have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;omega
 · change p.mapped+3*M ≤ B
   have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;have :=l.finalBound;omega

theorem rowSetup_spec {p : Parameters} {M k : ℕ} {s : State} (h:Loaded p M s) (count:s.natReg 894=k) :
 UniformChunkRowTableMachine.Header (rowParameters p) k (applyBlock rowSetup s):=by
 constructor
 all_goals simp [rowSetup,applyBlock,Op.apply,writeNat,next,h.sized.constants.zero,count,rowParameters,
 h.sized.header.selected,h.sized.header.mapped,h.sized.header.height.inputs,h.sized.gates,h.sized.header.height.targets,
 h.sized.header.source,h.sized.header.target,h.sized.header.borrowed]

theorem axisSetup_spec {p : Parameters} {M k : ℕ} {s : State} (h:Loaded p M s) (count:s.natReg 894=k) :
 UniformMatchingAxisTableMachine.Header p.radix k p.mapped p.permutation p.widths p.markers p.axis (applyBlock axisSetup s):=by
 constructor
 all_goals simp [axisSetup,applyBlock,Op.apply,writeNat,next,h.sized.constants.zero,count,h.sized.header.radix,
 h.sized.header.mapped,h.sized.header.permutation,h.sized.header.widths,h.sized.header.markers,h.sized.header.axis]

theorem Outside.trans {p : Parameters} {s u v : State} (f:Outside p s u) (g:Outside p u v) : Outside p s v:=
 fun q hq=>(g q hq).trans (f q hq)

variable {r : ℕ}

def rowFunction (W : List (ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r) (i : ℕ) : Row:=
 if hi:i < W.length then UniformCrossShearTableMachine.shiftedRow 0 loc (W[i]'hi) else ⟨0,0,0⟩
def edges (W : List (ShearCode ℕ r)) := UniformCrossDepthReplayPreparation.shiftedEdges 0 W
def colors (W : List (ShearCode ℕ r)) := greedy (edges W) 11 W.length
def indices (p : Parameters) (W : List (ShearCode ℕ r)) := UniformColorLayerTableMachine.selected W.length p.color (colors W)
def selectedRows (p : Parameters) (W : List (ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r) : List Row:=
 (indices p W).map (rowFunction W loc)
def selectedEdges (p : Parameters) (W : List (ShearCode ℕ r)) := UniformColorLayerTableMachine.selectedEdges (edges W) p.color (colors W)
def CodesDomain (p : Parameters) (W : List (ShearCode ℕ r)) : Prop:=∀s∈W,
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a s.dst ∧
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a s.src

theorem selected_count (p : Parameters) (W : List (ShearCode ℕ r)) : (indices p W).length ≤ W.length:=
 UniformColorLayerTableMachine.selected_length _ _ _

theorem selected_rows_table {p : Parameters} {W : List (ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r} {s : State}
 (h:UniformColorLayerTableMachine.OutputRows p.selected (indices p W) (rowFunction W loc) s) : Table p.selected (selectedRows p W loc) s:=by
 intro j hj
 simpa only [selectedRows,List.length_map,List.getElem_map,RowFields] using h j (by simpa only [selectedRows,List.length_map] using hj)

theorem codes_domain_edges {p : Parameters} {W : List (ShearCode ℕ r)} (dom:CodesDomain p W) (i : Fin W.length) :
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (edges W i).left ∧
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (edges W i).right:=by
 simpa only [edges,UniformCrossDepthReplayPreparation.shiftedEdges,Nat.zero_add,List.get_eq_getElem] using dom (W[i.val]'i.isLt) (List.getElem_mem i.isLt)

theorem selected_rows_domain {p : Parameters} {W : List (ShearCode ℕ r)} (loc:UniformInPlaceMachine.Locations r) (dom:CodesDomain p W) :
 UniformChunkRowTableMachine.RowsDomain (rowParameters p) (selectedRows p W loc):=by
 intro row hr
 obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hr
 have jr:j < W.length:=(UniformColorLayerTableMachine.selected_mem _ _ _ _).mp hj |>.1
 simpa only [rowFunction,dite_eq_left jr,rowParameters,UniformCrossShearTableMachine.shiftedRow,Nat.zero_add] using dom (W[j]'jr) (List.getElem_mem jr)

theorem selected_edge_domain {p : Parameters} {W : List (ShearCode ℕ r)} (dom:CodesDomain p W) (i : Fin (indices p W).length) :
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (selectedEdges p W i).left ∧
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (selectedEdges p W i).right:=
 codes_domain_edges dom (UniformColorLayerTableMachine.selectionIndex W.length p.color (colors W) i)

def coordinate (p : Parameters) (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix) : ℕ → ℕ:=
 UniformChunkPortMachine.mapped p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.source p.target
  (UniformChunkPortMachine.borrowedCoordinate p.radix p.source p.height.e p.target p.height.a
   (UniformCrossHeightPreparationMachine.gates p.height) fit)

def physicalEdges {p : Parameters} {B : ℕ} (l:Layout p B) (W : List (ShearCode ℕ r)) (dom:CodesDomain p W) : Fin (indices p W).length → Edge:=fun i=>
 ⟨coordinate p l.capacity (selectedEdges p W i).left,coordinate p l.capacity (selectedEdges p W i).right,
  fun eqn=>(selectedEdges p W i).different (UniformChunkPortMachine.mapped_injective p.radix p.source p.height.e p.target p.height.a
   (UniformCrossHeightPreparationMachine.gates p.height) l.sourceRange l.targetRange l.separated l.capacity
   (selected_edge_domain dom i).1 (selected_edge_domain dom i).2 eqn)⟩

theorem physical_matching {p : Parameters} {B : ℕ} {W : List (ShearCode ℕ r)} (l:Layout p B) (dom:CodesDomain p W)
 (degree:DegreeBound (edges W) 6) : UniformMatchingAxisTableMachine.Matching (physicalEdges l W dom):=by
 have logical:=UniformColorLayerTableMachine.selected_matching (edges W) p.color (colors W) degree (fun _=>rfl)
 intro i j ne conflict
 have di:=selected_edge_domain dom i
 have dj:=selected_edge_domain dom j
 have inj:=fun (u v : ℕ)=>UniformChunkPortMachine.mapped_injective p.radix p.source p.height.e p.target p.height.a
  (UniformCrossHeightPreparationMachine.gates p.height) l.sourceRange l.targetRange l.separated l.capacity (p:=u) (q:=v)
 apply logical i j ne
 unfold Conflict Incident at conflict ⊢
 simp only [physicalEdges] at conflict
 rcases conflict with (h|h)|(h|h)
 · exact Or.inl (Or.inl (inj _ _ dj.1 di.1 h))
 · exact Or.inl (Or.inr (inj _ _ dj.2 di.1 h))
 · exact Or.inr (Or.inl (inj _ _ dj.1 di.2 h))
 · exact Or.inr (Or.inr (inj _ _ dj.2 di.2 h))

theorem physical_range {p : Parameters} {B : ℕ} {W : List (ShearCode ℕ r)} (l:Layout p B) (dom:CodesDomain p W) :
 UniformMatchingAxisTableMachine.InRange p.radix (physicalEdges l W dom):=by
 intro i
 exact ⟨UniformChunkPortMachine.mapped_inRange _ _ _ _ _ _ _ l.sourceRange l.targetRange l.separated l.capacity (selected_edge_domain dom i).1,
 UniformChunkPortMachine.mapped_inRange _ _ _ _ _ _ _ l.sourceRange l.targetRange l.separated l.capacity (selected_edge_domain dom i).2⟩

theorem selected_align (p : Parameters) (W : List (ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r) (i : Fin (indices p W).length) :
 ((selectedRows p W loc)[i.val]'(by simpa only [selectedRows,List.length_map] using i.isLt)).dst=(selectedEdges p W i).left ∧
 ((selectedRows p W loc)[i.val]'(by simpa only [selectedRows,List.length_map] using i.isLt)).src=(selectedEdges p W i).right:=by
 have hi:(indices p W)[i.val]'i.isLt < W.length:=
  ((UniformColorLayerTableMachine.selected_mem _ _ _ _).mp (List.getElem_mem i.isLt)).1
 simp only [selectedRows,List.getElem_map,rowFunction,dite_eq_left hi,selectedEdges,
  UniformColorLayerTableMachine.selectedEdges,UniformColorLayerTableMachine.selectionIndex,edges,
  UniformCrossDepthReplayPreparation.shiftedEdges,UniformCrossShearTableMachine.shiftedRow]
 exact ⟨rfl,rfl⟩

theorem mapped_edges {p : Parameters} {B : ℕ} {W : List (ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r} {s : State}
 (l:Layout p B) (dom:CodesDomain p W) (geo:UniformChunkRowTableMachine.Geometry (rowParameters p) (selectedRows p W loc).length B)
 (table:Table p.mapped ((selectedRows p W loc).map (UniformChunkRowTableMachine.mappedRow (rowParameters p) geo.capacity)) s) :
 UniformMatchingAxisTableMachine.Edges (physicalEdges l W dom) p.mapped s:=by
 intro i
 have tab:=table i.val (by simpa only [List.length_map,selectedRows] using i.isLt)
 have align:=selected_align p W loc i
 simp only [List.getElem_map] at tab
 refine ⟨?_,?_⟩
 · exact tab.1.trans (congrArg some (congrArg (coordinate p l.capacity) align.1))
 · exact tab.2.1.trans (congrArg some (congrArg (coordinate p l.capacity) align.2))

theorem source_rows {W : List (ShearCode ℕ r)} {loc:UniformInPlaceMachine.Locations r} {T : ℕ} {s : State}
 (h:Table T (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) s) :
 UniformColorLayerTableMachine.Rows T W.length (rowFunction W loc) s:=by
 intro i hi
 have t:=h i (by simpa only [List.length_map] using hi)
 rw [List.getElem_map] at t
 simpa only [RowFields,rowFunction,dite_eq_left hi] using t

theorem color_stage {p : Parameters} {B n : ℕ} {x : Fin n → ℂ} (W : List (ShearCode ℕ r))
 (loc:UniformInPlaceMachine.Locations r) (s : State) (l:Layout p B)
 (size:W.length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height) (loaded:Loaded p W.length s)
 (table:Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth) (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) s)
 (col:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=some (colors W i.val))
 (bank:PhysicalBorrowed p l.capacity s) (pc:s.pc=48) (bound:WordBound B s) : ∃t u,
 t ≤ 24*W.length+13 ∧ BoundedRuns program n x B s t u ∧ u.pc=84 ∧ Loaded p W.length u ∧
 u.natReg 894=(indices p W).length ∧ Table p.selected (selectedRows p W loc) u ∧
 UniformColorLayerTableMachine.Ordinals p.ordinals (indices p W) u ∧ PhysicalBorrowed p l.capacity u ∧
 Outside p s u ∧ Frame s u:=by
 have b:=l.code
 have safe:=setup_safe loaded.sized.constants bound (Or.inr (Or.inl rfl))
 have rs:=block_runs colorSetup program 48 n B x s colorSetup_code pc bound (by change 48+6 ≤ B;omega) safe.1 safe.2
 let z:=applyBlock colorSetup s
 have zpc:z.pc=54:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have oldRows:=l.oldRows
 have oldColors:=l.oldColors
 have oldDir:=l.oldDirectory
 have hrow:UniformCrossHeightPreparationMachine.rowBase p.height p.depth+3*W.length ≤ p.selected:=by
  simp only [UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.height] at oldRows ⊢
  have db:=l.depthBound
  unfold UniformCrossHeightPreparationMachine.height at db
  have bf:=l.borrowFresh
  nlinarith
 have hcolor:UniformCrossHeightPreparationMachine.colorBase p.height p.depth+W.length ≤ p.selected:=by
  simp only [UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.height] at oldColors ⊢
  have db:=l.depthBound
  unfold UniformCrossHeightPreparationMachine.height at db
  have bf:=l.borrowFresh
  nlinarith
 have out1:p.selected+3*W.length ≤ p.ordinals:=by have :=l.selectedFresh;omega
 have out2:p.ordinals+W.length ≤ B:=by
  have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;have :=l.finalBound;omega
 have zr:=source_rows table
 have zc:UniformColorLayerTableMachine.Colors (UniformCrossHeightPreparationMachine.colorBase p.height p.depth) W.length (colors W) (setPC z 0):=
  fun i hi=>col ⟨i,hi⟩
 obtain ⟨u,run,cost,upc,uh,count,rows,ord,src,cols,out,f⟩:=UniformColorLayerTableMachine.execution W.length
  (UniformCrossHeightPreparationMachine.rowBase p.height p.depth) (UniformCrossHeightPreparationMachine.colorBase p.height p.depth)
  p.color p.selected p.ordinals B n x (rowFunction W loc) (colors W) (setPC z 0)
  (by have h:=colorSetup_spec loaded;exact ⟨h.count,h.source,h.colors,h.selectedColor,h.output,h.ordinals⟩) rfl zr zc hrow hcolor out1 out2 (by omega) (changePC_bound B z 0 rs.final_bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed color_code (by rw [UniformColorLayerTableMachine.program_length];omega) (by omega) run
 rw [placed_zero z 54 zpc] at placedRun
 have f0:=caller_frame colorSetup s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
 have f1:=color_frame f
 have cl:=loaded.transport f0 (setup_registers (Or.inr (Or.inl rfl)))
 have regs:∀r,1193 ≤ r → r ≤ 1205 → (setPC u 84).natReg r=z.natReg r:=fun r lo _=>f.2.2.2.2 r (by omega)
 refine ⟨6+(UniformColorLayerTableMachine.scanCost p.color (colors W) 0 W.length+7),setPC u 84,?_,?_,rfl,cl.transport f1 regs,count,selected_rows_table rows,ord,?_,?_,frame_trans f0 f1⟩
 · change UniformColorLayerTableMachine.scanCost p.color (colors W) 0 W.length+7 ≤ 24*W.length+7 at cost
   omega
 · convert rs.trans placedRun using 1 <;> simp only [colorSetup_length,setPC]
 · intro j
   change u.natHeap _=_
   rw [out (p.borrowed+j.val) (by have :=l.borrowFresh;omega) (by have :=l.borrowFresh;have :=l.selectedFresh;omega)]
   exact bank j
 · intro q hq
   exact out q (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;omega)
    (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;omega)

def mappedRows (p : Parameters) (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix)
 (W : List (ShearCode ℕ r)) (loc:UniformInPlaceMachine.Locations r) : List Row:=
 (selectedRows p W loc).map (UniformChunkRowTableMachine.mappedRow (rowParameters p) fit)

theorem row_stage {p : Parameters} {B n : ℕ} {x : Fin n → ℂ} (W : List (ShearCode ℕ r))
 (loc:UniformInPlaceMachine.Locations r) (s : State) (l:Layout p B)
 (size:W.length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height) (loaded:Loaded p W.length s)
 (count:s.natReg 894=(indices p W).length) (table:Table p.selected (selectedRows p W loc) s)
 (dom:CodesDomain p W) (bank:PhysicalBorrowed p l.capacity s) (pc:s.pc=84) (bound:WordBound B s) : ∃t u,
 t ≤ 44*(indices p W).length+15 ∧ BoundedRuns program n x B s t u ∧ u.pc=152 ∧ Loaded p W.length u ∧
 u.natReg 894=(indices p W).length ∧ Table p.mapped (mappedRows p l.capacity W loc) u ∧ Outside p s u ∧ Frame s u:=by
 have b:=l.code
 have al0:=l.borrowFresh
 have al1:=l.selectedFresh
 have al2:=l.ordinalFresh
 have al3:=l.mappedFresh
 have al4:=l.permutationFresh
 have al5:=l.widthsFresh
 have al6:=l.markersFresh
 have al7:=l.finalBound
 have small: (selectedRows p W loc).length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [selectedRows,List.length_map] using (selected_count p W).trans size
 have geo:=row_geometry l small
 have safe:=setup_safe loaded.sized.constants bound (Or.inr (Or.inr (Or.inl rfl)))
 have rs:=block_runs rowSetup program 84 n B x s rowSetup_code pc bound (by change 84+9 ≤ B;omega) safe.1 safe.2
 let z:=applyBlock rowSetup s
 have zpc:z.pc=93:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have zh:=rowSetup_spec loaded count
 have header:UniformChunkRowTableMachine.Header (rowParameters p) (selectedRows p W loc).length (setPC z 0):=by
  simpa only [selectedRows,List.length_map] using zh.withPC 0
 obtain ⟨t,u,cost,run,rows,head,f,out⟩:=UniformChunkRowTableMachine.execution (selectedRows p W loc) (setPC z 0)
  geo header table (selected_rows_domain loc dom) bank rfl (changePC_bound B z 0 rs.final_bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed row_code (by rw [UniformChunkRowTableMachine.program_length];omega) (by omega) run
 rw [placed_zero z 93 zpc] at placedRun
 have f0:=caller_frame rowSetup s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
 have f1:=row_frame f
 have cl:=loaded.transport f0 (setup_registers (Or.inr (Or.inr (Or.inl rfl))))
 have regs:∀r,1193 ≤ r → r ≤ 1205 → (setPC u 152).natReg r=z.natReg r:=fun r lo _=>f.2.2.2.2 r ⟨by omega,by omega⟩
 refine ⟨9+t,setPC u 152,?_,?_,rfl,cl.transport f1 regs,?_,rows,?_,frame_trans f0 f1⟩
 · simp only [selectedRows,List.length_map] at cost;omega
 · convert rs.trans placedRun using 1 <;> simp only [rowSetup_length,setPC]
 · change u.natReg 894=_
   rw [f.2.2.2.2 894 ⟨by omega,by omega⟩]
   simpa [setPC,z,rowSetup,applyBlock,Op.apply,writeNat,next] using count
 · intro q hq
   apply out q
   change q < p.mapped ∨ p.mapped+3*(selectedRows p W loc).length ≤ q
   have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh
   have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;omega

def axis {p : Parameters} {B : ℕ} (l:Layout p B) (W : List (ShearCode ℕ r)) (dom:CodesDomain p W)
 (degree:DegreeBound (edges W) 6) : UniformSectorPackingMachine.PhysicalAxis:=
 UniformMatchingAxisTableMachine.physicalAxis p.radix p.widths p.permutation (physicalEdges l W dom)
  (physical_matching l dom degree) (physical_range l dom) l.radixPositive

theorem axis_stage {p : Parameters} {B n : ℕ} {x : Fin n → ℂ} (W : List (ShearCode ℕ r))
 (loc:UniformInPlaceMachine.Locations r) (s : State) (l:Layout p B)
 (size:W.length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height) (loaded:Loaded p W.length s)
 (count:s.natReg 894=(indices p W).length) (table:Table p.mapped (mappedRows p l.capacity W loc) s)
 (dom:CodesDomain p W) (degree:DegreeBound (edges W) 6) (pc:s.pc=152) (bound:WordBound B s) : ∃t u,
 t ≤ 21*p.radix+28 ∧ BoundedRuns program n x B s t u ∧ u.pc=214 ∧ Loaded p W.length u ∧
 u.natReg 894=(indices p W).length ∧ UniformSectorPackingMachine.Rows [axis l W dom degree] 0 p.axis u ∧
 UniformSectorPackingMachine.Widths [axis l W dom degree] u ∧
 UniformSectorPackingMachine.Permutations [axis l W dom degree] u ∧
 Table p.mapped (mappedRows p l.capacity W loc) u ∧ Outside p s u ∧ Frame s u:=by
 have b:=l.code
 have al0:=l.borrowFresh
 have al1:=l.selectedFresh
 have al2:=l.ordinalFresh
 have al3:=l.mappedFresh
 have al4:=l.permutationFresh
 have al5:=l.widthsFresh
 have al6:=l.markersFresh
 have al7:=l.finalBound
 have small: (selectedRows p W loc).length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [selectedRows,List.length_map] using (selected_count p W).trans size
 have geo:=row_geometry l small
 have safe:=setup_safe loaded.sized.constants bound (Or.inr (Or.inr (Or.inr rfl)))
 have rs:=block_runs axisSetup program 152 n B x s axisSetup_code pc bound (by change 152+7 ≤ B;omega) safe.1 safe.2
 let z:=applyBlock axisSetup s
 have zpc:z.pc=159:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have zh:=axisSetup_spec loaded count
 have header:UniformMatchingAxisTableMachine.Header p.radix (indices p W).length p.mapped p.permutation p.widths p.markers p.axis (setPC z 0):=
  ⟨zh.radix,zh.count,zh.source,zh.permutation,zh.widths,zh.markers,zh.row⟩
 have hT:p.mapped+3*(indices p W).length ≤ p.permutation:=by
  have :=(selected_count p W).trans size;have :=l.mappedFresh;omega
 have src:=mapped_edges l dom geo table
 obtain ⟨u,run,cost,upc,rows,widths,perms,head,src',out,f⟩:=UniformMatchingAxisTableMachine.execution_axis
  p.radix (indices p W).length p.mapped p.permutation p.widths p.markers p.axis B n x
  (physicalEdges l W dom) (setPC z 0) header rfl src (physical_matching l dom degree) (physical_range l dom)
  l.radixPositive hT l.permutationFresh l.widthsFresh l.markersFresh l.finalBound (by omega)
  (changePC_bound B z 0 rs.final_bound (by omega))
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed axis_code (by rw [UniformMatchingAxisTableMachine.program_length];omega) (by omega) run
 rw [placed_zero z 159 zpc] at placedRun
 have f0:=caller_frame axisSetup s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
 have f1:=axis_frame f
 have cl:=loaded.transport f0 (setup_registers (Or.inr (Or.inr (Or.inr rfl))))
 have regs:∀r,1193 ≤ r → r ≤ 1205 → (setPC u 214).natReg r=z.natReg r:=fun r lo _=>f.2.2.2.2 r (by omega)
 refine ⟨7+UniformMatchingAxisTableMachine.runtime p.radix (indices p W).length,setPC u 214,by omega,?_,rfl,cl.transport f1 regs,?_,rows,widths,perms,?_,?_,frame_trans f0 f1⟩
 · convert rs.trans placedRun using 1 <;> simp only [axisSetup_length,setPC]
 · change u.natReg 894=_
   rw [f.2.2.2.2 894 (Or.inr (by omega))]
   simpa [setPC,z,axisSetup,applyBlock,Op.apply,writeNat,next] using count
 · intro i hi
   have len:(mappedRows p l.capacity W loc).length=(indices p W).length:=by simp only [mappedRows,selectedRows,List.length_map]
   rw [len] at hi
   change RowFields _ _ u.natHeap
   unfold RowFields
   rw [out (p.mapped+3*i) (by omega) (by have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;have :=l.permutationFresh;omega),
    out (p.mapped+3*i+1) (by omega) (by have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;have :=l.permutationFresh;omega),
    out (p.mapped+3*i+2) (by omega) (by have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;omega) (by have :=l.markersFresh;have :=l.widthsFresh;have :=l.permutationFresh;omega)]
   exact table i (by simpa only [len] using hi)
 · intro q hq
   exact out q (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;omega)
    (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;omega)
    (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;omega)
    (by have :=l.borrowFresh;have :=l.selectedFresh;have :=l.ordinalFresh;have :=l.mappedFresh;have :=l.permutationFresh;have :=l.widthsFresh;have :=l.markersFresh;omega)

theorem old_ranges {p : Parameters} {M B : ℕ} (l:Layout p B)
 (hm:M ≤ 2*UniformCrossHeightPreparationMachine.gates p.height) :
 UniformCrossHeightPreparationMachine.rowBase p.height p.depth+3*M ≤ p.borrowed ∧
 UniformCrossHeightPreparationMachine.colorBase p.height p.depth+M ≤ p.borrowed ∧
 UniformCrossHeightPreparationMachine.recordBase p.height p.depth+3 ≤ p.borrowed:=by
 have r:=l.oldRows;have c:=l.oldColors;have d:=l.oldDirectory;have db:=l.depthBound
 simp only [UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.colorBase,
  UniformCrossHeightPreparationMachine.recordBase] at r c d ⊢
 exact ⟨by nlinarith,by nlinarith,by omega⟩

theorem table_transport {rows : List Row} {D : ℕ} {s u : State} (table:Table D rows s)
 (heap:∀q,D ≤ q → q < D+3*rows.length → u.natHeap q=s.natHeap q) : Table D rows u:=by
 intro i hi
 unfold RowFields
 rw [heap (D+3*i) (by omega) (by omega),heap (D+3*i+1) (by omega) (by omega),heap (D+3*i+2) (by omega) (by omega)]
 exact table i hi

theorem execution {p : Parameters} {B n : ℕ} {x : Fin n → ℂ} (W : List (ShearCode ℕ r))
 (loc:UniformInPlaceMachine.Locations r) (s : State) (l:Layout p B)
 (header:Header p s) (size:W.length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth) (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) s)
 (col:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=some (colors W i.val))
 (dom:CodesDomain p W) (degree:DegreeBound (edges W) 6) (pc:s.pc=0) (bound:WordBound B s) : ∃t u,
 t ≤ 4*p.height.K+180*p.radix+92 ∧ BoundedExecution program n x B s t u ∧ Header p u ∧ u.natReg 894=(indices p W).length ∧
 UniformSectorPackingMachine.Rows [axis l W dom degree] 0 p.axis u ∧
 UniformSectorPackingMachine.Widths [axis l W dom degree] u ∧
 UniformSectorPackingMachine.Permutations [axis l W dom degree] u ∧
 Table p.mapped (mappedRows p l.capacity W loc) u ∧ Outside p s u ∧ Frame s u:=by
 obtain ⟨v,r0,p0,h0,bh,heap0,f0⟩:=startup (n:=n) (x:=x) s l header record pc bound
 obtain ⟨tb,w,cb,r1,p1,h1,borrow,o1,f1⟩:=borrowed_stage (n:=n) (x:=x) v l h0 bh p0 r0.final_bound
 have ranges:=old_ranges l size
 have wtable:Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth) (W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)) w:=by
  apply table_transport table
  intro q lo hi
  simp only [List.length_map] at hi
  have hi':q < p.borrowed:=lt_of_lt_of_le hi ranges.1
  rw [o1 q (Or.inl hi'),heap0]
 have wcol:∀i:Fin W.length,w.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=some (colors W i.val):=by
  intro i
  rw [o1 _ (Or.inl (by have :=i.isLt;omega)),heap0]
  exact col i
 obtain ⟨tc,z,cc,r2,p2,h2,count2,rows2,ord2,bank2,o2,f2⟩:=color_stage (n:=n) (x:=x) W loc w l size h1 wtable wcol borrow p1 r1.final_bound
 obtain ⟨tr,a,cr,r3,p3,h3,count3,rows3,o3,f3⟩:=row_stage (n:=n) (x:=x) W loc z l size h2 count2 rows2 dom bank2 p2 r2.final_bound
 obtain ⟨ta,u,ca,r4,p4,h4,count4,axisRows,axisWidths,axisPerms,rows4,o4,f4⟩:=axis_stage (n:=n) (x:=x) W loc a l size h3 count3 rows3 dom degree p3 r3.final_bound
 have halt:BoundedExecution program n x B u 1 u:=.halt r4.final_bound (by simp [step,p4,final_halt])
 have small: (indices p W).length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height:=(selected_count p W).trans size
 have cap:=l.capacity
 refine ⟨4*p.height.K+28+tb+tc+tr+ta+1,u,by omega,?_,h4.sized.header,count4,axisRows,axisWidths,axisPerms,rows4,?_,?_⟩
 · convert r0.trans (r1.trans (r2.trans (r3.trans r4))) |>.executes halt using 1
   omega
 · intro q hq
   rw [o4 q hq,o3 q hq,o2 q hq,o1 q hq,heap0]
 · exact frame_trans f0 (frame_trans f1 (frame_trans f2 (frame_trans f3 f4)))

open UniformToeplitzCrossDAG (crossDAG bankSize)
def crossWord (p : Parameters) (ha:p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height) :=
 UniformCrossDepthReplayPreparation.bucket (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled p.depth

def crossLocations (p : Parameters) (Z : ℕ) :=UniformCrossShearTableMachine.locations (bankSize p.height.K) p.height.C Z p.height.P

theorem cross_domain (p : Parameters) (ha:p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height) : CodesDomain p (crossWord p ha he):=by
 intro s hs
 have mem: s∈UniformDAGLayers.natSweep (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled:=
  (List.mem_filter.mp hs).1
 have b:=UniformDAGLayers.natSweep_bounds (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled s mem
 have nz:=UniformDAGLayers.natSweep_src_nonzero (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled s mem
 rw [UniformCrossHeightPreparationMachine.cross_size p.height ha he] at b
 simp only [UniformChunkPortMachine.Domain]
 constructor <;> omega

theorem cross_degree (p : Parameters) (ha:p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height) : DegreeBound (edges (crossWord p ha he)) 6:=
 UniformCrossDepthReplayPreparation.shiftedEdges_degree 0 6 _
  (UniformCrossDepthReplayPreparation.cross_bucket_degree p.height.K p.height.a p.height.e p.depth ha he p.height.enabled)

theorem processed_transport {p : Parameters} {B Z G : ℕ} {printed:UniformReplayPrint.Program (bankSize p.height.K) p.height.e G}
 {s u : State} (l:Layout p B) (size:G=UniformCrossHeightPreparationMachine.gates p.height)
 (h:UniformCrossHeightPreparationMachine.Processed p.height Z printed (UniformCrossHeightPreparationMachine.height p.height) s)
 (out:Outside p s u) :
 UniformCrossHeightPreparationMachine.Processed p.height Z printed (UniformCrossHeightPreparationMachine.height p.height) u:=by
 intro d hd
 obtain ⟨table,col,rec⟩:=h d hd
 have len:=UniformCrossHeightPreparationMachine.bucket_length printed p.height.enabled d
 have len':(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height:=len.trans (by rw [size])
 have rr:=l.oldRows
 have cc:=l.oldColors
 have dd:=l.oldDirectory
 have rh:UniformCrossHeightPreparationMachine.rowBase p.height d+3*(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length ≤ p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.rowBase] at rr ⊢;nlinarith [len']
 have ch:UniformCrossHeightPreparationMachine.colorBase p.height d+(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length ≤ p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.colorBase] at cc ⊢;nlinarith [len']
 have dh:UniformCrossHeightPreparationMachine.recordBase p.height d+3 ≤ p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.recordBase] at dd ⊢;omega
 refine ⟨?_,?_,?_⟩
 · apply table_transport table
   intro q lo hi
   simp only [List.length_map] at hi
   exact out q (Or.inl (lt_of_lt_of_le hi rh))
 · intro i
   rw [out _ (Or.inl (by have :=i.isLt;omega))]
   exact col i
 · unfold UniformCrossHeightPreparationMachine.Record
   rw [out _ (Or.inl (by omega)),out _ (Or.inl (by omega)),out _ (Or.inl (by omega))]
   exact rec

/-- One actual color of one actual Height186 forward layer, lowered to a
physical tensor axis. Original Height output is an honest prior producer
contract; selected rows, borrowed coordinates and axis banks are all computed. -/
theorem cross_execution (p : Parameters) (Z B n : ℕ) (x : Fin n → ℂ) (s : State)
 (ha:p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (l:Layout p B) (header:Header p s)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height Z
  (crossDAG p.height.K p.height.a p.height.e ha he).program (UniformCrossHeightPreparationMachine.height p.height) s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃t u,
 t ≤ 4*p.height.K+180*p.radix+92 ∧ BoundedExecution program n x B s t u ∧ Header p u ∧ u.natReg 894=(indices p (crossWord p ha he)).length ∧
 UniformSectorPackingMachine.Rows [axis l (crossWord p ha he) (cross_domain p ha he) (cross_degree p ha he)] 0 p.axis u ∧
 UniformSectorPackingMachine.Widths [axis l (crossWord p ha he) (cross_domain p ha he) (cross_degree p ha he)] u ∧
 UniformSectorPackingMachine.Permutations [axis l (crossWord p ha he) (cross_domain p ha he) (cross_degree p ha he)] u ∧
 Table p.mapped (mappedRows p l.capacity (crossWord p ha he) (crossLocations p Z)) u ∧
 UniformCrossHeightPreparationMachine.Processed p.height Z
  (crossDAG p.height.K p.height.a p.height.e ha he).program (UniformCrossHeightPreparationMachine.height p.height) u ∧
 Outside p s u ∧ Frame s u:=by
 obtain ⟨table,col,record⟩:=processed p.depth l.depthBound
 have size:(crossWord p ha he).length ≤ 2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [crossWord,UniformCrossHeightPreparationMachine.cross_size p.height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled p.depth
 have cols:∀i:Fin (crossWord p ha he).length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=some (colors (crossWord p ha he) i.val):=
  fun i=>col i
 obtain ⟨t,u,cost,run,head,count,rows,widths,perms,mapped,out,frame⟩:=execution (n:=n) (x:=x) (crossWord p ha he) (crossLocations p Z) s l header size record table cols
  (cross_domain p ha he) (cross_degree p ha he) pc bound
 exact ⟨t,u,cost,run,head,count,rows,widths,perms,mapped,processed_transport l (UniformCrossHeightPreparationMachine.cross_size p.height ha he) processed out,out,frame⟩

/-- In particular the saved global metadata is unchanged, independent of the
arbitrary scalar values/tags in unrelated dirty cells. -/
theorem saved_metadata_frame {s u : State} (f:Frame s u) (r : ℕ) (lo:100 ≤ r) (hi:r ≤ 106) : u.natReg r=s.natReg r:=
 f.2.2.2.2 r (by unfold Protected;omega)

end
end ExactFourierCircuits.UniformChunkMatchingPreparation
