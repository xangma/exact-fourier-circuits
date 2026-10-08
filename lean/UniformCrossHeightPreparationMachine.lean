import UniformCrossDepthReplayPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCrossHeightPreparationMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformRadixTwoDAG (width)
open UniformToeplitzCrossDAG (crossDAG bankSize)

/-- Readonly caller registers1050..1062. Scratch1063..1079 is local. -/
structure Parameters where
  K : ℕ
  a : ℕ
  e : ℕ
  T : ℕ
  Q : ℕ
  R : ℕ
  D : ℕ
  F : ℕ
  U : ℕ
  J : ℕ
  C : ℕ
  P : ℕ
  enabled : Bool
  deriving DecidableEq

def widthOf (v : Parameters) := width v.K
def gates (v : Parameters) := 6*(3*v.K*widthOf v+2*widthOf v)+2*v.a
def height (v : Parameters) := 8*v.K+7
def rowBase (v : Parameters) (d : ℕ) := v.D+6*gates v*d
def colorBase (v : Parameters) (d : ℕ) := v.F+2*gates v*d
def recordBase (v : Parameters) (d : ℕ) := v.J+3*d

def bootOps : List Op := [.literal 1063 0,.literal 1064 1,.literal 1065 2,
  .literal 1066 3,.literal 1067 6,.literal 1068 8,.literal 1069 7,
  .literal 1070 0,.literal 1071 1]
def powerOps : List Op := [.mul 1071 1071 1065,.add 1070 1070 1064]
def sizeOps : List Op := [.mul 1072 1050 1071,.mul 1072 1072 1066,
  .mul 1073 1071 1065,.add 1072 1072 1073,.mul 1072 1072 1067,
  .mul 1073 1051 1065,.add 1072 1072 1073,.mul 1073 1050 1068,
  .add 1073 1073 1069,.literal 1074 0,.add 1075 1056 1063,
  .add 1076 1057 1063,.add 1077 1059 1063,.mul 1078 1072 1067,.mul 1079 1072 1065]
def headerOps : List Op := [.add 900 1072 1063,.add 901 1074 1063,
  .add 902 1053 1063,.add 903 1054 1063,.add 904 1055 1063,
  .add 905 1075 1063,.literal 906 0,.add 907 1060 1063,
  .add 908 1062 1063,.add 909 1052 1063,.add 911 1071 1063,
  .add 912 1061 1063,.add 913 1076 1063,.add 914 1058 1063]
def tailOps : List Op := [.putNat 1077 800,.add 1077 1077 1064,
  .putNat 1077 1075,.add 1077 1077 1064,.putNat 1077 1076,
  .add 1077 1077 1064,.add 1075 1075 1078,.add 1076 1076 1079,.add 1074 1074 1064]

/-- One literal186-instruction machine. The local132 helper's halt is patched
    to a charged continuation jump; every sizing and directory instruction is charged. -/
def program : UniformMachine.Program := bootOps.map Op.code ++ [.branchLT 1070 1050 10 13] ++
  powerOps.map Op.code ++ [.jump 9] ++ sizeOps.map Op.code ++ [.branchLT 1074 1073 29 185] ++
  headerOps.map Op.code ++ UniformCrossDepthReplayPreparation.program.map (relocate 43 175) ++
  tailOps.map Op.code ++ [.jump 28,.halt]
lemma program_length : program.length=186 := by
  simp only [program,List.length_append,List.length_map,UniformCrossDepthReplayPreparation.program_length]
  rfl
lemma boot_code : BlockAt bootOps program 0 := by intro i hi;change i<9 at hi;interval_cases i <;> rfl
lemma power_code : BlockAt powerOps program 10 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma size_code : BlockAt sizeOps program 13 := by intro i hi;change i<15 at hi;interval_cases i <;> rfl
lemma header_code : BlockAt headerOps program 29 := by intro i hi;change i<14 at hi;interval_cases i <;> rfl
lemma bucket_code : CodeAt UniformCrossDepthReplayPreparation.program program 43 175 := by
  intro i hi;rw [UniformCrossDepthReplayPreparation.program_length] at hi
  interval_cases i <;> rfl
lemma tail_code : BlockAt tailOps program 175 := by intro i hi;change i<9 at hi;interval_cases i <;> rfl
lemma power_branch : program[9]?=some (.branchLT 1070 1050 10 13) := rfl
lemma power_jump : program[12]?=some (.jump 9) := rfl
lemma depth_branch : program[28]?=some (.branchLT 1074 1073 29 185) := rfl
lemma depth_jump : program[184]?=some (.jump 28) := rfl
lemma halt_at : program[185]?=some .halt := rfl

noncomputable section

structure Header (v : Parameters) (s : State) : Prop where
  exponent : s.natReg 1050=v.K
  targets : s.natReg 1051=v.a
  inputs : s.natReg 1052=v.e
  tape : s.natReg 1053=v.T
  order : s.natReg 1054=v.Q
  sourceDirectory : s.natReg 1055=v.R
  rows : s.natReg 1056=v.D
  colors : s.natReg 1057=v.F
  palette : s.natReg 1058=v.U
  directory : s.natReg 1059=v.J
  coefficients : s.natReg 1060=v.C
  enabled : s.natReg 1061=if v.enabled then 1 else 0
  constants : s.natReg 1062=v.P

structure Constants (s : State) : Prop where
  zero : s.natReg 1063=0
  one : s.natReg 1064=1
  two : s.natReg 1065=2
  three : s.natReg 1066=3
  six : s.natReg 1067=6
  eight : s.natReg 1068=8
  seven : s.natReg 1069=7

structure Initializing (v : Parameters) (i : ℕ) (s : State) : Prop where
  header : Header v s
  constants : Constants s
  index : s.natReg 1070=i
  width : s.natReg 1071=width i

structure Cursor (v : Parameters) (d : ℕ) (s : State) : Prop where
  header : Header v s
  constants : Constants s
  width : s.natReg 1071=widthOf v
  gateCount : s.natReg 1072=gates v
  heightCount : s.natReg 1073=height v
  depth : s.natReg 1074=d
  rows : s.natReg 1075=rowBase v d
  colors : s.natReg 1076=colorBase v d
  directory : s.natReg 1077=recordBase v d
  rowStride : s.natReg 1078=6*gates v
  colorStride : s.natReg 1079=2*gates v

def Protected (j : ℕ) : Prop := UniformCrossDepthReplayPreparation.Protected j ∧
  (j<900 ∨ 915≤j) ∧ (j<1063 ∨ 1080≤j)
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ∀j,Protected j→u.natReg j=s.natReg j
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u t : State} (h : Frame s u) (h' : Frame u t) : Frame s t :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun j hj=>(h'.2.2.2.2 j hj).trans (h.2.2.2.2 j hj)⟩
lemma Frame.withPC {s u : State} (h : Frame s u) (pc : ℕ) : Frame s {u with pc:=pc} := h
lemma Header.transport {v : Parameters} {s u : State} (h : Header v s) (hf : Frame s u) : Header v u := by
  constructor
  · exact (hf.2.2.2.2 1050 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.exponent
  · exact (hf.2.2.2.2 1051 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.targets
  · exact (hf.2.2.2.2 1052 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.inputs
  · exact (hf.2.2.2.2 1053 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.tape
  · exact (hf.2.2.2.2 1054 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.order
  · exact (hf.2.2.2.2 1055 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.sourceDirectory
  · exact (hf.2.2.2.2 1056 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.rows
  · exact (hf.2.2.2.2 1057 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.colors
  · exact (hf.2.2.2.2 1058 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.palette
  · exact (hf.2.2.2.2 1059 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.directory
  · exact (hf.2.2.2.2 1060 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.coefficients
  · exact (hf.2.2.2.2 1061 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.enabled
  · exact (hf.2.2.2.2 1062 (by simp [Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.constants

lemma Header.withPC {v : Parameters} {s : State} (h : Header v s) (pc : ℕ) : Header v {s with pc:=pc} := by cases h;constructor <;> assumption
lemma Constants.withPC {s : State} (h : Constants s) (pc : ℕ) : Constants {s with pc:=pc} := by cases h;constructor <;> assumption
lemma Initializing.withPC {v : Parameters} {i pc : ℕ} {s : State} (h : Initializing v i s) : Initializing v i {s with pc:=pc} := ⟨h.header.withPC _,h.constants.withPC _,h.index,h.width⟩
lemma Cursor.withPC {v : Parameters} {i pc : ℕ} {s : State} (h : Cursor v i s) : Cursor v i {s with pc:=pc} := ⟨h.header.withPC _,h.constants.withPC _,h.width,h.gateCount,h.heightCount,h.depth,h.rows,h.colors,h.directory,h.rowStride,h.colorStride⟩

def natOnly : Op→Prop
 | .literal _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .putNat _ _=>True
 | _=>False
def writes (o : Op) (j : ℕ) : Prop := match o with
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _=>d=j
 | _=>False
lemma natOp_frame (o : Op) (s : State) (hn : natOnly o)
    (hw : ∀j,Protected j→¬writes o j) : Frame s (o.apply s) := by
  cases o <;> simp only [natOnly] at hn
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro j hj
  all_goals first
  | exact Function.update_of_ne (by intro he;exact hw j hj (by simpa [writes] using he.symm)) _ _
  | rfl
lemma natBlock_frame (b : List Op) (s : State)
    (hn : ∀o∈b,natOnly o) (hw : ∀o∈b,∀j,Protected j→¬writes o j) : Frame s (applyBlock b s) := by
  induction b generalizing s with
  | nil=>exact Frame.refl s
  | cons o b ih=>
    exact (natOp_frame o s (hn o (by simp)) (hw o (by simp))).trans
      (ih _ (fun v hv=>hn v (by simp [hv])) (fun v hv=>hw v (by simp [hv])))
lemma natBlock_heap (b : List Op) (s : State)
    (hn : ∀o∈b,natOnly o) (hp : ∀a r,Op.putNat a r∉b) : (applyBlock b s).natHeap=s.natHeap := by
  induction b generalizing s with
  | nil=>rfl
  | cons o b ih=>
    rw [applyBlock,ih _ (fun v hv=>hn v (by simp [hv])) (fun a r h=>hp a r (by simp [h]))]
    have h:=hn o (by simp)
    cases o with
    | putNat a r=>exact False.elim (hp a r (by simp))
    | _=>simp only [natOnly] at h <;> rfl

lemma boot_frame (s : State) : Frame s (applyBlock bootOps s) := by
  apply natBlock_frame
  · simp [bootOps,natOnly]
  · intro o ho j hj
    simp only [bootOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h
    all_goals subst o; simp only [writes];unfold Protected at hj;omega
lemma power_frame (s : State) : Frame s (applyBlock powerOps s) := by
  apply natBlock_frame
  · simp [powerOps,natOnly]
  · intro o ho j hj
    simp only [powerOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h
    all_goals subst o; simp only [writes];unfold Protected at hj;omega
lemma size_frame (s : State) : Frame s (applyBlock sizeOps s) := by
  apply natBlock_frame
  · simp [sizeOps,natOnly]
  · intro o ho j hj
    simp only [sizeOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals subst o; simp only [writes];unfold Protected at hj;omega
lemma header_frame (s : State) : Frame s (applyBlock headerOps s) := by
  apply natBlock_frame
  · simp [headerOps,natOnly]
  · intro o ho j hj
    simp only [headerOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals subst o; simp only [writes];unfold Protected at hj;omega
lemma tail_frame (s : State) : Frame s (applyBlock tailOps s) := by
  apply natBlock_frame
  · simp [tailOps,natOnly]
  · intro o ho j hj
    simp only [tailOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h
    all_goals subst o; simp [writes] <;> unfold Protected at hj <;> omega
lemma boot_heap (s : State) : (applyBlock bootOps s).natHeap=s.natHeap := by
  apply natBlock_heap <;> simp [bootOps,natOnly]
lemma power_heap (s : State) : (applyBlock powerOps s).natHeap=s.natHeap := by
  apply natBlock_heap <;> simp [powerOps,natOnly]
lemma size_heap (s : State) : (applyBlock sizeOps s).natHeap=s.natHeap := by
  apply natBlock_heap <;> simp [sizeOps,natOnly]
lemma header_heap (s : State) : (applyBlock headerOps s).natHeap=s.natHeap := by
  apply natBlock_heap <;> simp [headerOps,natOnly]

lemma boot_spec (v : Parameters) (s : State) (h : Header v s) : Initializing v 0 (applyBlock bootOps s) := by
  refine ⟨h.transport (boot_frame s),?_,?_,?_⟩
  · constructor <;> simp [bootOps,applyBlock,Op.apply,writeNat,next]
  · simp [bootOps,applyBlock,Op.apply,writeNat,next]
  · simp [bootOps,applyBlock,Op.apply,writeNat,next,width]
lemma power_spec (v : Parameters) (i : ℕ) (s : State) (h : Initializing v i s) : Initializing v (i+1) (applyBlock powerOps s) := by
  refine ⟨h.header.transport (power_frame s),?_,?_,?_⟩
  · constructor <;> simp [powerOps,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one,h.constants.two,h.constants.three,h.constants.six,h.constants.eight,h.constants.seven]
  · simp [powerOps,applyBlock,Op.apply,writeNat,next,h.index,h.constants.one]
  · simp [powerOps,applyBlock,Op.apply,writeNat,next,h.width,h.constants.two,width,Nat.mul_comm,Nat.two_mul]
lemma size_spec (v : Parameters) (s : State) (h : Initializing v v.K s) : Cursor v 0 (applyBlock sizeOps s) := by
  refine ⟨h.header.transport (size_frame s),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
  | constructor <;> simp [sizeOps,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one,h.constants.two,h.constants.three,h.constants.six,h.constants.eight,h.constants.seven]
  | simp [sizeOps,applyBlock,Op.apply,writeNat,next,h.header.exponent,h.header.targets,h.header.rows,h.header.colors,h.header.directory,h.width,h.constants.zero,h.constants.two,h.constants.three,h.constants.six,h.constants.eight,h.constants.seven,gates,height,widthOf,rowBase,colorBase,recordBase,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
lemma header_spec (v : Parameters) (d : ℕ) (s : State) (h : Cursor v d s) :
    UniformCrossDepthReplayPreparation.Header (gates v) d v.T v.Q v.R (rowBase v d) 0 v.C v.P v.e (widthOf v) (colorBase v d) v.U v.enabled (applyBlock headerOps s) := by
  constructor <;> simp [headerOps,applyBlock,Op.apply,writeNat,next,h.gateCount,h.depth,h.rows,h.colors,h.width,h.constants.zero,h.header.tape,h.header.order,h.header.sourceDirectory,h.header.coefficients,h.header.constants,h.header.inputs,h.header.enabled,h.header.palette]

lemma branch_runs (B m pc l r yes no : ℕ) (x : Fin m→ℂ) (s : State)
    (hpc : s.pc=pc) (hcode : program[pc]?=some (.branchLT l r yes no))
    (hs : WordBound B s) (hy : yes≤B) (hn : no≤B) :
    BoundedRuns program m x B s 1 (setPC s (if s.natReg l<s.natReg r then yes else no)) := by
  refine .next hs ?_ (.refl (changePC_bound B s _ hs (by split_ifs <;> assumption)))
  simp [UniformMachine.step,hpc,hcode,setPC]
lemma jump_runs (B m pc target : ℕ) (x : Fin m→ℂ) (s : State)
    (hpc : s.pc=pc) (hcode : program[pc]?=some (.jump target))
    (hs : WordBound B s) (ht : target≤B) :
    BoundedRuns program m x B s 1 (setPC s target) := by
  exact .next hs (by simp [UniformMachine.step,hpc,hcode,setPC]) (.refl (changePC_bound B s target hs ht))

lemma natBlock_register (b : List Op) (s : State) (j : ℕ)
    (hn : ∀o∈b,natOnly o) (hw : ∀o∈b,¬writes o j) : (applyBlock b s).natReg j=s.natReg j := by
  induction b generalizing s with
  | nil=>rfl
  | cons o b ih=>
    rw [applyBlock,ih _ (fun v hv=>hn v (by simp [hv])) (fun v hv=>hw v (by simp [hv]))]
    have hp:=hw o (by simp)
    have h:=hn o (by simp)
    cases o <;> simp only [natOnly] at h
    all_goals first
    | exact Function.update_of_ne (by intro he;exact hp (by simpa [writes] using he.symm)) _ _
    | rfl

lemma Header.transport_register {v : Parameters} {s u : State} (h : Header v s)
    (he : ∀j,1050≤j→j≤1079→u.natReg j=s.natReg j) : Header v u := by
  constructor
  · exact (he 1050 (by omega) (by omega)).trans h.exponent
  · exact (he 1051 (by omega) (by omega)).trans h.targets
  · exact (he 1052 (by omega) (by omega)).trans h.inputs
  · exact (he 1053 (by omega) (by omega)).trans h.tape
  · exact (he 1054 (by omega) (by omega)).trans h.order
  · exact (he 1055 (by omega) (by omega)).trans h.sourceDirectory
  · exact (he 1056 (by omega) (by omega)).trans h.rows
  · exact (he 1057 (by omega) (by omega)).trans h.colors
  · exact (he 1058 (by omega) (by omega)).trans h.palette
  · exact (he 1059 (by omega) (by omega)).trans h.directory
  · exact (he 1060 (by omega) (by omega)).trans h.coefficients
  · exact (he 1061 (by omega) (by omega)).trans h.enabled
  · exact (he 1062 (by omega) (by omega)).trans h.constants

lemma Constants.transport_register {s u : State} (h : Constants s)
    (he : ∀j,1050≤j→j≤1079→u.natReg j=s.natReg j) : Constants u := by
  constructor
  · exact (he 1063 (by omega) (by omega)).trans h.zero
  · exact (he 1064 (by omega) (by omega)).trans h.one
  · exact (he 1065 (by omega) (by omega)).trans h.two
  · exact (he 1066 (by omega) (by omega)).trans h.three
  · exact (he 1067 (by omega) (by omega)).trans h.six
  · exact (he 1068 (by omega) (by omega)).trans h.eight
  · exact (he 1069 (by omega) (by omega)).trans h.seven

lemma Cursor.transport_register {v : Parameters} {d : ℕ} {s u : State} (h : Cursor v d s)
    (he : ∀j,1050≤j→j≤1079→u.natReg j=s.natReg j) : Cursor v d u := by
  refine ⟨h.header.transport_register he,h.constants.transport_register he,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (he 1071 (by omega) (by omega)).trans h.width
  · exact (he 1072 (by omega) (by omega)).trans h.gateCount
  · exact (he 1073 (by omega) (by omega)).trans h.heightCount
  · exact (he 1074 (by omega) (by omega)).trans h.depth
  · exact (he 1075 (by omega) (by omega)).trans h.rows
  · exact (he 1076 (by omega) (by omega)).trans h.colors
  · exact (he 1077 (by omega) (by omega)).trans h.directory
  · exact (he 1078 (by omega) (by omega)).trans h.rowStride
  · exact (he 1079 (by omega) (by omega)).trans h.colorStride

lemma header_cursor {v : Parameters} {d : ℕ} {s : State} (h : Cursor v d s) : Cursor v d (applyBlock headerOps s) := by
  apply h.transport_register
  intro j hj hj'
  apply natBlock_register
  · simp [headerOps,natOnly]
  · intro o ho
    simp only [headerOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h|h|h|h|h|h|h|h|h|h|h|h
    all_goals subst o;simp only [writes];omega

lemma bucket_cursor {v : Parameters} {d : ℕ} {s u : State} (h : Cursor v d s)
    (hf : UniformCrossDepthReplayPreparation.Frame s u) : Cursor v d u := by
  apply h.transport_register
  intro j hj _
  exact hf.2.2.2.2 j (by unfold UniformCrossDepthReplayPreparation.Protected;omega)
lemma bucket_frame {s u : State} (hf : UniformCrossDepthReplayPreparation.Frame s u) : Frame s u :=
  ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,fun j hj=>hf.2.2.2.2 j hj.1⟩

/-- Ordinary word/address envelope. Arena capacity is charged through values,
    not through an assumed initialized table. -/
def wordBudget (v : Parameters) : ℕ := 186+v.K+widthOf v+gates v+height v+
  v.T+v.Q+v.R+v.C+v.P+v.e+v.U+rowBase v (height v)+colorBase v (height v)+recordBase v (height v)+
  UniformCrossDepthReplayPreparation.wordBudget (gates v) v.T v.Q v.R (rowBase v (height v)) 0 v.C v.P v.e
    (widthOf v) (colorBase v (height v)) v.U

structure Layout (v : Parameters) : Prop where
  tape : v.T+5*gates v≤v.D
  order : v.Q+gates v≤v.D
  directory : v.R+gates v+2≤v.D
  rows : rowBase v (height v)≤v.F
  colors : colorBase v (height v)≤v.U
  palette : v.U+12≤v.J

lemma height_positive (v : Parameters) : 0<height v := by simp [height]
lemma rowBase_mono (v : Parameters) {a b : ℕ} (h : a≤b) : rowBase v a≤rowBase v b :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
lemma colorBase_mono (v : Parameters) {a b : ℕ} (h : a≤b) : colorBase v a≤colorBase v b :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
lemma recordBase_mono (v : Parameters) {a b : ℕ} (h : a≤b) : recordBase v a≤recordBase v b :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
lemma rowBase_succ (v : Parameters) (d : ℕ) : rowBase v (d+1)=rowBase v d+6*gates v := by simp [rowBase,Nat.mul_add];omega
lemma colorBase_succ (v : Parameters) (d : ℕ) : colorBase v (d+1)=colorBase v d+2*gates v := by simp [colorBase,Nat.mul_add];omega
lemma recordBase_succ (v : Parameters) (d : ℕ) : recordBase v (d+1)=recordBase v d+3 := by simp [recordBase,Nat.mul_add];omega

lemma cross_size (v : Parameters) (ha : v.a≤widthOf v) (he : v.e≤widthOf v) :
    (crossDAG v.K v.a v.e ha he).size=gates v := by
  simpa only [gates,widthOf,UniformRadixTwoDAG.width_eq] using UniformToeplitzCrossDAG.crossDAG_size v.K v.a v.e ha he

lemma initialize_loop (m i f B : ℕ) (v : Parameters) (x : Fin m→ℂ) (s : State)
    (h : Initializing v i s) (hf : i+f=v.K) (hp : s.pc=9)
    (hb : wordBudget v≤B) (hs : WordBound B s) :
    ∃u,BoundedRuns program m x B s (4*f+1) u ∧ Initializing v v.K u ∧ u.pc=13 ∧
      u.natHeap=s.natHeap ∧ Frame s u := by
  have hc : 186≤B := by unfold wordBudget at hb;omega
  have hN : widthOf v≤B := by unfold wordBudget at hb;omega
  have hK : v.K≤B := by unfold wordBudget at hb;omega
  induction f generalizing i s with
  | zero=>
    have hi : i=v.K := by omega
    subst i
    have r:=branch_runs B m 9 1070 1050 10 13 x s hp power_branch hs (by omega) (by omega)
    simpa [h.index,h.header.exponent,setPC] using
      (show ∃u,BoundedRuns program m x B s 1 u ∧ Initializing v v.K u ∧ u.pc=13 ∧
        u.natHeap=s.natHeap ∧ Frame s u from
        ⟨setPC s 13,by simpa [h.index,h.header.exponent] using r,h.withPC,rfl,rfl,Frame.refl s⟩)
  | succ f ih=>
    have hi : i<v.K := by omega
    let e : State:=setPC s 10
    have first : BoundedRuns program m x B s 1 e := by
      simpa [e,h.index,h.header.exponent,hi] using
        branch_runs B m 9 1070 1050 10 13 x s hp power_branch hs (by omega) (by omega)
    have hn : width (i+1)≤widthOf v := UniformRadixInstructionMachine.width_mono (by omega)
    have peakBound : peak powerOps e≤B := by
      simp [peak,powerOps,Op.peak,Op.apply,writeNat,next,e,setPC,h.width,h.index,h.constants.two,h.constants.one]
      constructor
      · simpa only [width,Nat.mul_comm,Nat.two_mul] using hn.trans hN
      · omega
    have middle:=block_runs powerOps program 10 m B x e power_code rfl first.final_bound
      (by change 10+2≤B;omega) (by simp [readable,powerOps,Op.readable]) peakBound
    have epc : (applyBlock powerOps e).pc=12 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have last:=jump_runs B m 12 9 x (applyBlock powerOps e) epc power_jump middle.final_bound (by omega)
    let u:=setPC (applyBlock powerOps e) 9
    have hu : Initializing v (i+1) u := (power_spec v i e h.withPC).withPC
    obtain ⟨t,run,ht,pc,heap,frame⟩:=ih (i+1) u hu (by omega) rfl last.final_bound
    refine ⟨t,?_,ht,pc,heap.trans (power_heap e),(power_frame e).trans frame⟩
    have all:=first.trans (middle.trans (last.trans run))
    convert all using 1
    simp only [show powerOps.length=2 by rfl]
    omega

lemma boot_readable (s : State) : readable bootOps s := by simp [readable,bootOps,Op.readable]
lemma size_readable (s : State) : readable sizeOps s := by simp [readable,sizeOps,Op.readable]
lemma header_readable (s : State) : readable headerOps s := by simp [readable,headerOps,Op.readable]
lemma tail_readable (s : State) : readable tailOps s := by simp [readable,tailOps,Op.readable]

lemma size_peak (v : Parameters) (s : State) (h : Initializing v v.K s) (B : ℕ)
    (hb : wordBudget v≤B) : peak sizeOps s≤B := by
  have hG : gates v≤B := by unfold wordBudget at hb;omega
  have hH : height v≤B := by unfold wordBudget at hb;omega
  have hD : v.D≤B := by unfold wordBudget rowBase at hb;omega
  have hF : v.F≤B := by unfold wordBudget colorBase at hb;omega
  have hJ : v.J≤B := by unfold wordBudget recordBase at hb;omega
  have hR : 6*gates v≤B := by
    have hm : 6*gates v≤6*gates v*height v := Nat.le_mul_of_pos_right _ (height_positive v)
    unfold wordBudget rowBase at hb;omega
  have hC : 2*gates v≤B := by
    have hm : 2*gates v≤2*gates v*height v := Nat.le_mul_of_pos_right _ (height_positive v)
    unfold wordBudget colorBase at hb;omega
  simp [peak,sizeOps,Op.peak,Op.apply,writeNat,next,h.header.exponent,h.header.targets,h.header.rows,h.header.colors,h.header.directory,h.width,h.constants.zero,h.constants.two,h.constants.three,h.constants.six,h.constants.eight,h.constants.seven,Nat.mul_comm,Nat.mul_left_comm]
  have hKN : v.K*width v.K≤B := by unfold gates widthOf at hG;nlinarith
  unfold gates widthOf at hG hR hC
  unfold height at hH
  refine ⟨hKN,?_,?_,?_,hD,hF,hJ,?_⟩ <;> nlinarith

lemma header_peak (v : Parameters) (d B : ℕ) (s : State) (h : Cursor v d s)
    (hd : d≤height v) (hb : wordBudget v≤B) : peak headerOps s≤B := by
  have hD:=rowBase_mono v hd
  have hF:=colorBase_mono v hd
  have hen : (if v.enabled then 1 else 0)≤1 := by split_ifs <;> omega
  simp [peak,headerOps,Op.peak,Op.apply,writeNat,next,h.gateCount,h.depth,h.rows,h.colors,h.width,h.constants.zero,h.header.tape,h.header.order,h.header.sourceDirectory,h.header.coefficients,h.header.constants,h.header.inputs,h.header.enabled,h.header.palette]
  unfold wordBudget at hb
  omega

lemma tail_spec (v : Parameters) (d count : ℕ) (s : State) (h : Cursor v d s)
    (hc : s.natReg 800=count) :
    Cursor v (d+1) (applyBlock tailOps s) ∧
    (applyBlock tailOps s).natHeap (recordBase v d)=some count ∧
    (applyBlock tailOps s).natHeap (recordBase v d+1)=some (rowBase v d) ∧
    (applyBlock tailOps s).natHeap (recordBase v d+2)=some (colorBase v d) := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨h.header.transport (tail_frame s),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first
    | constructor <;> simp [tailOps,applyBlock,Op.apply,writeNat,next,h.constants.zero,h.constants.one,h.constants.two,h.constants.three,h.constants.six,h.constants.eight,h.constants.seven]
    | simp [tailOps,applyBlock,Op.apply,writeNat,next,h.width,h.gateCount,h.heightCount,h.depth,h.rows,h.colors,h.directory,h.rowStride,h.colorStride,h.constants.one,rowBase_succ,colorBase_succ,recordBase_succ]
  all_goals simp (disch:=omega) [tailOps,applyBlock,Op.apply,writeNat,next,h.directory,h.constants.one,h.rows,h.colors,hc]

lemma tail_heap_outside (v : Parameters) (d : ℕ) (s : State) (h : Cursor v d s) :
    ∀j,(j<recordBase v d ∨ recordBase v (d+1)≤j)→(applyBlock tailOps s).natHeap j=s.natHeap j := by
  intro j hj
  rw [recordBase_succ] at hj
  simp (disch:=omega) [tailOps,applyBlock,Op.apply,writeNat,next,h.directory,h.constants.one]

lemma tail_peak (v : Parameters) (d count B : ℕ) (s : State) (h : Cursor v d s)
    (hd : d<height v) (hc : s.natReg 800=count) (hcount : count≤2*gates v)
    (hb : wordBudget v≤B) : peak tailOps s≤B := by
  have hD:=rowBase_mono v (show d+1≤height v by omega)
  have hF:=colorBase_mono v (show d+1≤height v by omega)
  have hJ:=recordBase_mono v (show d+1≤height v by omega)
  rw [rowBase_succ] at hD
  rw [colorBase_succ] at hF
  rw [recordBase_succ] at hJ
  have hm : 2*gates v≤2*gates v*height v := Nat.le_mul_of_pos_right _ (height_positive v)
  have hcb : colorBase v (height v)≤B := by unfold wordBudget at hb;omega
  have hrb : rowBase v (height v)≤B := by unfold wordBudget at hb;omega
  have hjb : recordBase v (height v)≤B := by unfold wordBudget at hb;omega
  simp [peak,tailOps,Op.peak,Op.apply,writeNat,next,h.directory,h.rows,h.colors,h.depth,h.constants.one,h.rowStride,h.colorStride,hc]
  unfold wordBudget colorBase at hb
  omega

open UniformDAGLayers UniformReplayPrint UniformColoring

lemma bucket_length {r n G : ℕ} (p : UniformReplayPrint.Program r n G) (enabled : Bool) (d : ℕ) :
    (UniformCrossDepthReplayPreparation.bucket p enabled d).length≤2*G := by
  apply (List.length_filter_le _ _).trans
  exact p.sweep_length enabled _ _ _ _

/-- Only actual input tape/order/directory banks occur in this entry contract. -/
structure Source {G : ℕ} (v : Parameters) (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (s : State) : Prop where
  bank : UniformDAGBucketMachine.Bank v.Q (UniformDAGBucketMachine.order G (UniformDAGBucketMachine.typedDepth p)) s
  directory : UniformDAGBucketMachine.Directory v.R G (G+2) (UniformDAGBucketMachine.typedDepth p) s
  tape : UniformToeplitzCrossTopologyMachine.RowTable
    ((UniformToeplitzCrossDAG.programRecords p).map UniformConvolutionTopologyMachine.encode) v.T s

lemma Source.withPC {G pc : ℕ} {v : Parameters} {p : UniformReplayPrint.Program (bankSize v.K) v.e G} {s : State}
    (h : Source v p s) : Source v p {s with pc:=pc} := by cases h;constructor <;> assumption
lemma Source.transport {G : ℕ} {v : Parameters} {p : UniformReplayPrint.Program (bankSize v.K) v.e G} {s u : State}
    (h : Source v p s) (hG : G=gates v) (hl : Layout v)
    (eq : ∀j,j<v.D→u.natHeap j=s.natHeap j) : Source v p u := by
  constructor
  · intro i hi
    have hr:=h.bank i hi
    have len:=UniformDAGBucketMachine.order_length G (UniformDAGBucketMachine.typedDepth p) (UniformDAGBucketMachine.typedDepth_bound p)
    rw [len] at hi
    rw [eq _ (by have hb:=hl.order;omega)]
    exact hr
  · intro i hi
    rw [eq _ (by have hb:=hl.directory;omega)]
    exact h.directory i hi
  · intro i row hi
    have hlen : i<G := by
      have ht: i<((UniformToeplitzCrossDAG.programRecords p).map UniformConvolutionTopologyMachine.encode).length :=
        (List.getElem?_eq_some_iff.mp hi).choose
      simpa [UniformToeplitzCrossDAG.programRecords_length] using ht
    have ht:=h.tape i row hi
    unfold UniformToeplitzCrossTopologyMachine.HeapFields at ht ⊢
    have hb:=hl.tape
    rw [eq _ (by omega),eq _ (by omega),eq _ (by omega),eq _ (by omega),eq _ (by omega)]
    exact ht

/-- The directory stores genuine returned counts and physical row/color bases. -/
def Record (v : Parameters) (d count : ℕ) (s : State) : Prop :=
  s.natHeap (recordBase v d)=some count ∧
  s.natHeap (recordBase v d+1)=some (rowBase v d) ∧
  s.natHeap (recordBase v d+2)=some (colorBase v d)

def Slice {G : ℕ} (v : Parameters) (Z : ℕ) (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (d : ℕ) (s : State) : Prop :=
  let W:=UniformCrossDepthReplayPreparation.bucket p v.enabled d
  UniformCrossShearTableMachine.Table (rowBase v d)
    (W.map (UniformCrossShearTableMachine.shiftedRow 0
      (UniformCrossShearTableMachine.locations (bankSize v.K) v.C Z v.P))) s ∧
  (∀i:Fin W.length,s.natHeap (colorBase v d+i.val)=some
    (coloring (UniformCrossDepthReplayPreparation.shiftedEdges 0 W) 6 i)) ∧
  Record v d W.length s

def Processed {G : ℕ} (v : Parameters) (Z : ℕ) (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (d : ℕ) (s : State) : Prop :=
  ∀i,i<d→Slice v Z p i s

/-- Per-step physical footprint, including the shared twelve-cell palette. -/
def StepOutside (v : Parameters) (d : ℕ) (s u : State) : Prop :=
  ∀j,(j<rowBase v d ∨ rowBase v (d+1)≤j)→
    (j<colorBase v d ∨ colorBase v (d+1)≤j)→
    (j<v.U ∨ v.U+12≤j)→
    (j<recordBase v d ∨ recordBase v (d+1)≤j)→u.natHeap j=s.natHeap j

def Outside (v : Parameters) (s u : State) : Prop :=
  ∀j,(j<v.D ∨ rowBase v (height v)≤j)→
    (j<v.F ∨ colorBase v (height v)≤j)→
    (j<v.U ∨ v.U+12≤j)→
    (j<v.J ∨ recordBase v (height v)≤j)→u.natHeap j=s.natHeap j
lemma Outside.refl (v : Parameters) (s : State) : Outside v s s := fun _ _ _ _ _=>rfl
lemma Outside.trans {v : Parameters} {s u t : State} (h : Outside v s u) (h' : Outside v u t) : Outside v s t :=
  fun j hj hf hu hh=>(h' j hj hf hu hh).trans (h j hj hf hu hh)
lemma StepOutside.global {v : Parameters} {d : ℕ} {s u : State} (h : StepOutside v d s u)
    (hd : d<height v) : Outside v s u := by
  intro j hj hf hu hh
  have hr:=rowBase_mono v (show d+1≤height v by omega)
  have hc:=colorBase_mono v (show d+1≤height v by omega)
  have ht:=recordBase_mono v (show d+1≤height v by omega)
  exact h j (by unfold rowBase at *;omega) (by unfold colorBase at *;omega) hu (by unfold recordBase at *;omega)
lemma StepOutside.source {G : ℕ} {v : Parameters} {p : UniformReplayPrint.Program (bankSize v.K) v.e G} {d : ℕ} {s u : State}
    (h : Source v p s) (hG : G=gates v) (hl : Layout v) (_hd : d<height v)
    (he : StepOutside v d s u) : Source v p u := by
  apply h.transport hG hl
  intro j hj
  have hDF : v.D≤v.F := (by unfold rowBase;omega : v.D≤rowBase v (height v)).trans hl.rows
  have hFU : v.F≤v.U := (by unfold colorBase;omega : v.F≤colorBase v (height v)).trans hl.colors
  have hUJ : v.U≤v.J := by have :=hl.palette;omega
  exact he j (Or.inl (by unfold rowBase;omega)) (Or.inl (by unfold colorBase;omega)) (Or.inl (by omega)) (Or.inl (by unfold recordBase;omega))

lemma Slice.transport {G : ℕ} {v : Parameters} {Z i d : ℕ} {p : UniformReplayPrint.Program (bankSize v.K) v.e G} {s u : State}
    (h : Slice v Z p i s) (hG : G=gates v) (hl : Layout v) (hi : i<d) (hd : d<height v)
    (out : StepOutside v d s u) : Slice v Z p i u := by
  have hlen:=bucket_length p v.enabled i
  have hir:=rowBase_mono v (show i+1≤d by omega)
  have hic:=colorBase_mono v (show i+1≤d by omega)
  have hit:=recordBase_mono v (show i+1≤d by omega)
  have hdr:=rowBase_mono v (show d+1≤height v by omega)
  have hdc:=colorBase_mono v (show d+1≤height v by omega)
  have hdt:=recordBase_mono v (show d+1≤height v by omega)
  rw [rowBase_succ] at hir
  rw [colorBase_succ] at hic
  rw [recordBase_succ] at hit
  have hp:=hl.palette
  have hrf:=hl.rows
  have hcu:=hl.colors
  have rf : rowBase v (d+1)≤v.F := hdr.trans hrf
  have cu : colorBase v (d+1)≤v.U := hdc.trans hcu
  have fc : v.F≤colorBase v d := by unfold colorBase;omega
  have jj : v.J≤recordBase v d := by unfold recordBase;omega
  have jj' : v.J≤recordBase v i := by unfold recordBase;omega
  have cc : colorBase v d≤colorBase v (d+1) := colorBase_mono v (by omega)
  have rr : rowBase v d≤rowBase v (d+1) := rowBase_mono v (by omega)
  have retainRow (z : ℕ) (hz : z<rowBase v d) : u.natHeap z=s.natHeap z :=
    out z (Or.inl hz) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have retainColor (z : ℕ) (hz : v.F≤z) (hz' : z<colorBase v d) : u.natHeap z=s.natHeap z :=
    out z (Or.inr (by omega)) (Or.inl hz') (Or.inl (by omega)) (Or.inl (by omega))
  have retainRecord (z : ℕ) (hz : v.J≤z) (hz' : z<recordBase v d) : u.natHeap z=s.natHeap z :=
    out z (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hz')
  dsimp only [Slice] at h ⊢
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hrow:=h.1 j hj
    have hj':j<(UniformCrossDepthReplayPreparation.bucket p v.enabled i).length := by simpa only [List.length_map] using hj
    unfold UniformCrossShearTableMachine.RowFields at hrow ⊢
    rw [retainRow (rowBase v i+3*j) (by omega),
      retainRow (rowBase v i+3*j+1) (by omega),
      retainRow (rowBase v i+3*j+2) (by omega)]
    exact hrow
  · intro j
    rw [retainColor (colorBase v i+j.val) (by unfold colorBase;omega) (by have :=j.isLt;omega)]
    exact h.2.1 j
  · unfold Record at h ⊢
    rw [retainRecord (recordBase v i) jj' (by omega),
      retainRecord (recordBase v i+1) (by omega) (by omega),
      retainRecord (recordBase v i+2) (by omega) (by omega)]
    exact h.2.2

lemma call_budget (v : Parameters) (d G B : ℕ) (hG : G=gates v) (hd : d<height v)
    (hb : wordBudget v≤B) :
    UniformCrossDepthReplayPreparation.wordBudget G v.T v.Q v.R (rowBase v d) 0 v.C v.P v.e
      (widthOf v) (colorBase v d) v.U≤B := by
  have hr:=rowBase_mono v (show d≤height v by omega)
  have hc:=colorBase_mono v (show d≤height v by omega)
  have hm : UniformCrossDepthReplayPreparation.wordBudget G v.T v.Q v.R (rowBase v d) 0 v.C v.P v.e
      (widthOf v) (colorBase v d) v.U≤
      UniformCrossDepthReplayPreparation.wordBudget G v.T v.Q v.R (rowBase v (height v)) 0 v.C v.P v.e
        (widthOf v) (colorBase v (height v)) v.U := by
    unfold UniformCrossDepthReplayPreparation.wordBudget
    gcongr
  apply hm.trans
  rw [hG]
  unfold wordBudget at hb
  omega

def iterationBudget (v : Parameters) := 64*gates v+200*(2*gates v+1)^2+56

/-- A complete physical iteration consumes the original typed tape and real
    Bucket24 banks. The only generic premises are syntactic coefficient/depth
    bounds, discharged by the Cross271 wrapper below. -/
theorem iteration {G : ℕ} (v : Parameters) (Z d B m : ℕ)
    (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (x : Fin m→ℂ) (s : State)
    (hG : G=gates v) (hl : Layout v)
    (good : ∀g∈UniformToeplitzCrossDAG.programRecords p,
      UniformCrossShearTableMachine.GoodExpr (widthOf v) g)
    (degree : DegreeBound (printedEdges (UniformCrossDepthReplayPreparation.bucket p v.enabled d)) 6)
    (hheight : height v-1≤G) (hd : d<height v)
    (cursor : Cursor v d s) (source : Source v p s) (pc : s.pc=28)
    (hs : WordBound B s) (hb : wordBudget v≤B) :
    ∃u ticks,BoundedRuns program m x B s ticks u ∧ ticks≤ iterationBudget v ∧ u.pc=28 ∧
      Cursor v (d+1) u ∧ Source v p u ∧ Slice v Z p d u ∧ StepOutside v d s u ∧ Frame s u := by
  have hc : 186≤B := by unfold wordBudget at hb;omega
  have hrow:=rowBase_mono v (show d+1≤height v by omega)
  have hcolor:=colorBase_mono v (show d+1≤height v by omega)
  have hrecord:=recordBase_mono v (show d+1≤height v by omega)
  have hFbase : v.F≤colorBase v d := by unfold colorBase;omega
  have hJbase : v.J≤recordBase v d := by unfold recordBase;omega
  have hRF : rowBase v (d+1)≤v.F := hrow.trans hl.rows
  have hCU : colorBase v (d+1)≤v.U := hcolor.trans hl.colors
  have hPJ :=hl.palette
  have hFU : v.F≤v.U := (show v.F≤colorBase v (height v) by unfold colorBase;omega).trans hl.colors
  let e : State:=setPC s 29
  have first : BoundedRuns program m x B s 1 e := by
    simpa [e,cursor.depth,cursor.heightCount,hd] using
      branch_runs B m 28 1074 1073 29 185 x s pc depth_branch hs (by omega) (by omega)
  have boot:=block_runs headerOps program 29 m B x e header_code rfl first.final_bound
    (by change 29+14≤B;omega) (header_readable e)
    (header_peak v d B e cursor.withPC (by omega) hb)
  let b:=applyBlock headerOps e
  have bpc : b.pc=43 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have bcur : Cursor v d b := header_cursor cursor.withPC
  have bheader : UniformCrossDepthReplayPreparation.Header G d v.T v.Q v.R (rowBase v d) 0 v.C v.P v.e (width v.K) (colorBase v d) v.U v.enabled {b with pc:=0} := by
    have h:=header_spec v d e cursor.withPC
    rw [←hG] at h
    exact UniformCrossDepthReplayPreparation.Header.transport h
      (show UniformCrossDepthReplayPreparation.Frame b {b with pc:=0} from ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩)
  have bsource : Source v p {b with pc:=0} := source.transport hG hl
    (fun j _=>congrFun (header_heap e) j)
  obtain ⟨t,ticks,run,cost,tpc,rows,count,colors,colorbound,matching,outside,_,frame,_⟩ :=
    UniformCrossDepthReplayPreparation.bucket_execution v.K d v.T v.Q v.R (rowBase v d) 0 v.C Z v.P (colorBase v d) v.U B m
      p x v.enabled {b with pc:=0} good degree bheader rfl
      (changePC_bound B b 0 boot.final_bound (by omega)) (by omega)
      bsource.bank bsource.directory bsource.tape
      (by have :=hl.tape;unfold rowBase;omega)
      (by have :=hl.order;unfold rowBase;omega)
      (by have :=hl.directory;unfold rowBase;omega)
      (by rw [hG,←rowBase_succ];omega) (by rw [hG,←colorBase_succ];exact hCU)
      (call_budget v d G B hG hd hb)
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed bucket_code
    (by rw [UniformCrossDepthReplayPreparation.program_length];omega) (by omega) run
  rw [UniformCrossDepthReplayPreparation.reset_placed 43 b bpc] at placedRun
  let c : State:={t with pc:=175}
  have ccur : Cursor v d c := (bucket_cursor bcur.withPC frame).withPC
  have ccount : c.natReg 800=(UniformCrossDepthReplayPreparation.bucket p v.enabled d).length := count
  have countBound : (UniformCrossDepthReplayPreparation.bucket p v.enabled d).length≤2*gates v := by
    simpa [hG] using bucket_length p v.enabled d
  have tail:=block_runs tailOps program 175 m B x c tail_code rfl placedRun.final_bound
    (by change 175+9≤B;omega) (tail_readable c)
    (tail_peak v d _ B c ccur hd ccount countBound hb)
  let f:=applyBlock tailOps c
  have fpc : f.pc=184 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have finish:=jump_runs B m 184 28 x f fpc depth_jump tail.final_bound (by omega)
  let u:=setPC f 28
  obtain ⟨fcur,rec0,rec1,rec2⟩:=tail_spec v d _ c ccur ccount
  have stepOutside : StepOutside v d s u := by
    intro j hj hf hu hh
    change f.natHeap j=s.natHeap j
    rw [tail_heap_outside v d c ccur j hh]
    change t.natHeap j=s.natHeap j
    rw [outside j (by simpa [rowBase_succ,hG] using hj) (by simpa [colorBase_succ,hG] using hf) hu]
    exact congrFun (header_heap e) j
  have table : UniformCrossShearTableMachine.Table (rowBase v d)
      ((UniformCrossDepthReplayPreparation.bucket p v.enabled d).map
        (UniformCrossShearTableMachine.shiftedRow 0
          (UniformCrossShearTableMachine.locations (bankSize v.K) v.C Z v.P))) u := by
    intro j hj
    have r:=rows j hj
    have hj' : j<(UniformCrossDepthReplayPreparation.bucket p v.enabled d).length := by simpa only [List.length_map] using hj
    have small : rowBase v d+3*j+2<recordBase v d := by
      have := countBound
      rw [rowBase_succ] at hRF
      omega
    unfold UniformCrossShearTableMachine.RowFields at r ⊢
    change (applyBlock tailOps c).natHeap _=_ ∧ (applyBlock tailOps c).natHeap _=_ ∧ (applyBlock tailOps c).natHeap _=_
    rw [tail_heap_outside v d c ccur (rowBase v d+3*j) (Or.inl (by omega)),
      tail_heap_outside v d c ccur (rowBase v d+3*j+1) (Or.inl (by omega)),
      tail_heap_outside v d c ccur (rowBase v d+3*j+2) (Or.inl small)]
    exact r
  have color : ∀i:Fin (UniformCrossDepthReplayPreparation.bucket p v.enabled d).length,
      u.natHeap (colorBase v d+i.val)=some
        (coloring (UniformCrossDepthReplayPreparation.shiftedEdges 0 (UniformCrossDepthReplayPreparation.bucket p v.enabled d)) 6 i) := by
    intro i
    have small : colorBase v d+i.val<recordBase v d := by
      have :=i.isLt
      rw [colorBase_succ] at hCU
      omega
    change (applyBlock tailOps c).natHeap _=_
    rw [tail_heap_outside v d c ccur (colorBase v d+i.val) (Or.inl small)]
    exact colors i
  have all:=first.trans (boot.trans (placedRun.trans (tail.trans finish)))
  have total : ticks+(1+14+9+1)≤ iterationBudget v := by
    unfold iterationBudget
    rw [hG] at cost
    omega
  refine ⟨u,1+14+ticks+9+1,?_,by omega,rfl,fcur.withPC,
    stepOutside.source source hG hl hd,⟨table,color,rec0,rec1,rec2⟩,stepOutside,
    (header_frame e).trans ((bucket_frame frame).trans (tail_frame c))⟩
  convert all using 1
  simp only [show headerOps.length=14 by rfl,show tailOps.length=9 by rfl]
  omega

/-- The finite loop visits exactly the constructor height, including empty
    buckets. Earlier physical rows/colors/records remain present. -/
theorem height_loop {G : ℕ} (v : Parameters) (Z d f B m : ℕ)
    (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (x : Fin m→ℂ) (s : State)
    (hG : G=gates v) (hl : Layout v)
    (good : ∀g∈UniformToeplitzCrossDAG.programRecords p,UniformCrossShearTableMachine.GoodExpr (widthOf v) g)
    (degree : ∀i,i<height v→DegreeBound (printedEdges (UniformCrossDepthReplayPreparation.bucket p v.enabled i)) 6)
    (hheight : height v-1≤G) (hf : d+f=height v)
    (cursor : Cursor v d s) (source : Source v p s) (done : Processed v Z p d s)
    (pc : s.pc=28) (hs : WordBound B s) (hb : wordBudget v≤B) :
    ∃u ticks,BoundedRuns program m x B s ticks u ∧ ticks≤f*iterationBudget v+1 ∧
      u.pc=185 ∧ Cursor v (height v) u ∧ Source v p u ∧ Processed v Z p (height v) u ∧
      Outside v s u ∧ Frame s u := by
  have hc : 186≤B := by unfold wordBudget at hb;omega
  induction f generalizing d s with
  | zero=>
    have hd : d=height v := by omega
    subst d
    let u:=setPC s 185
    have r:=branch_runs B m 28 1074 1073 29 185 x s pc depth_branch hs (by omega) (by omega)
    have run : BoundedRuns program m x B s 1 u := by
      simpa [u,cursor.depth,cursor.heightCount] using r
    exact ⟨u,1,run,by simp,rfl,cursor.withPC,source.withPC,done,Outside.refl v s,Frame.refl s⟩
  | succ f ih=>
    have hd : d<height v := by omega
    obtain ⟨u,ticks,run,cost,pc',cur',source',slice,out,frame⟩:=
      iteration v Z d B m p x s hG hl good (degree d hd) hheight hd cursor source pc hs hb
    have done' : Processed v Z p (d+1) u := by
      intro i hi
      by_cases he : i=d
      · subst i;exact slice
      · exact (done i (by omega)).transport hG hl (by omega) hd out
    obtain ⟨t,steps,tail,tailcost,tpc,tcur,tsource,tdone,tout,tframe⟩:=
      ih (d+1) u (by omega) cur' source' done' pc' run.final_bound
    refine ⟨t,ticks+steps,run.trans tail,?_,tpc,tcur,tsource,tdone,(out.global hd).trans tout,frame.trans tframe⟩
    rw [Nat.succ_mul]
    omega

/-- Actual input banks plus syntactic bounds suffice for this literal driver;
    no preprinted per-depth rows, colors, counts or action is an input. -/
theorem execution {G : ℕ} (v : Parameters) (Z B m : ℕ)
    (p : UniformReplayPrint.Program (bankSize v.K) v.e G) (x : Fin m→ℂ) (s : State)
    (hG : G=gates v) (hl : Layout v)
    (good : ∀g∈UniformToeplitzCrossDAG.programRecords p,UniformCrossShearTableMachine.GoodExpr (widthOf v) g)
    (degree : ∀i,i<height v→DegreeBound (printedEdges (UniformCrossDepthReplayPreparation.bucket p v.enabled i)) 6)
    (hheight : height v-1≤G) (header : Header v s) (source : Source v p s)
    (pc : s.pc=0) (hs : WordBound B s) (hb : wordBudget v≤B) :
    ∃u ticks,BoundedExecution program m x B s ticks u ∧
      ticks≤4*v.K+27+height v*iterationBudget v ∧ u.pc=185 ∧
      Cursor v (height v) u ∧ Source v p u ∧ Processed v Z p (height v) u ∧
      Outside v s u ∧ Frame s u := by
  have hc : 186≤B := by unfold wordBudget at hb;omega
  have boot:=block_runs bootOps program 0 m B x s boot_code pc hs
    (by change 0+9≤B;omega) (boot_readable s) (by simp [peak,bootOps,Op.peak];omega)
  let b:=applyBlock bootOps s
  have bcur : Initializing v 0 b := boot_spec v s header
  have bpc : b.pc=9 := by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
  obtain ⟨c,init,cur,cpc,cheap,cframe⟩:=initialize_loop m 0 v.K B v x b bcur (by omega) bpc hb boot.final_bound
  have size:=block_runs sizeOps program 13 m B x c size_code cpc init.final_bound
    (by change 13+15≤B;omega) (size_readable c) (size_peak v c cur B hb)
  let d:=applyBlock sizeOps c
  have dcur : Cursor v 0 d := size_spec v c cur
  have dpc : d.pc=28 := by rw [UniformTensorMonomialMachine.applyBlock_pc,cpc];rfl
  have dheap : d.natHeap=s.natHeap := (size_heap c).trans (cheap.trans (boot_heap s))
  have dsource : Source v p d := source.transport hG hl (fun j _=>congrFun dheap j)
  obtain ⟨u,ticks,loop,cost,upc,ucur,usource,done,outside,frame⟩:=height_loop v Z 0 (height v) B m p x d hG hl good degree hheight
    (by omega) dcur dsource (by intro i hi;omega) dpc size.final_bound hb
  have stop : BoundedExecution program m x B u 1 u := .halt loop.final_bound (by simp [step,upc,halt_at])
  have all:=(boot.trans (init.trans (size.trans loop))).executes stop
  refine ⟨u,9+(4*v.K+1)+15+ticks+1,?_,by omega,upc,ucur,usource,done,?_,
    (boot_frame s).trans (cframe.trans ((size_frame c).trans frame))⟩
  · convert all using 1
    simp only [show bootOps.length=9 by rfl,show sizeOps.length=15 by rfl]
    omega
  · intro j hj hf hu hh
    exact (outside j hj hf hu hh).trans (congrFun dheap j)

/-- Closed Cross271 specialization: the actual constructor discharges every
    coefficient/depth/degree/size bound of the generic machine. The tape and
    Bucket24 output are honest earlier physical producer outputs. -/
theorem cross_execution (v : Parameters) (Z B m : ℕ)
    (ha : v.a≤widthOf v) (he : v.e≤widthOf v) (x : Fin m→ℂ) (s : State)
    (header : Header v s) (pc : s.pc=0) (hs : WordBound B s) (hl : Layout v) (hb : wordBudget v≤B)
    (bank : UniformDAGBucketMachine.Bank v.Q
      (UniformDAGBucketMachine.order (crossDAG v.K v.a v.e ha he).size
        (UniformDAGBucketMachine.typedDepth (crossDAG v.K v.a v.e ha he).program)) s)
    (directory : UniformDAGBucketMachine.Directory v.R (crossDAG v.K v.a v.e ha he).size
      ((crossDAG v.K v.a v.e ha he).size+2)
      (UniformDAGBucketMachine.typedDepth (crossDAG v.K v.a v.e ha he).program) s)
    (tape : UniformToeplitzCrossTopologyMachine.RowTable (UniformToeplitzCrossTopologyMachine.crossRows v.K v.a v.e) v.T s) :
    ∃u ticks,BoundedExecution program m x B s ticks u ∧
      ticks≤4*v.K+27+(8*v.K+7)*(64*gates v+200*(2*gates v+1)^2+56) ∧ u.pc=185 ∧
      Cursor v (height v) u ∧ Source v (crossDAG v.K v.a v.e ha he).program u ∧
      Processed v Z (crossDAG v.K v.a v.e ha he).program (8*v.K+7) u ∧ Outside v s u ∧ Frame s u := by
  have hsource : Source v (crossDAG v.K v.a v.e ha he).program s := by
    refine ⟨bank,directory,?_⟩
    rw [←UniformToeplitzCrossTopologyMachine.crossRows_typed v.K v.a v.e ha he]
    exact tape
  have hheight : height v-1≤(crossDAG v.K v.a v.e ha he).size := by
    have h:=UniformCrossDepthReplayPreparation.cross_height_le_size v.K v.a v.e ha he
    unfold height;omega
  simpa only [height,iterationBudget] using execution v Z B m (crossDAG v.K v.a v.e ha he).program x s
    (cross_size v ha he) hl (UniformCrossShearTableMachine.cross_good v.K v.a v.e ha he)
    (fun d hd=>UniformCrossDepthReplayPreparation.cross_bucket_degree v.K v.a v.e d ha he v.enabled)
    hheight header hsource pc hs hb

lemma saved_headers {s u : State} (frame : Frame s u) (j : ℕ) (h : 100≤j ∧ j≤106) : u.natReg j=s.natReg j :=
  frame.2.2.2.2 j (by unfold Protected UniformCrossDepthReplayPreparation.Protected;omega)
lemma master_retained {s u : State} (frame : Frame s u) : u.scalarHeap 0=s.scalarHeap 0 := congrFun frame.1 0


/-- A concrete polynomial envelope for ordinary caller placements. Consequently
    every address remains an O(log W)-bit word when the ambient B is this
    polynomial. This does not bound the global algorithm's running time. -/
lemma wordBudget_polynomial (v : Parameters) (W : ℕ)
    (hN : widthOf v≤W) (ha : v.a≤W) (he : v.e≤W)
    (hT : v.T≤W) (hQ : v.Q≤W) (hR : v.R≤W) (hD : v.D≤W)
    (hF : v.F≤W) (hU : v.U≤W) (hJ : v.J≤W) (hC : v.C≤W) (hP : v.P≤W) :
    wordBudget v≤10000*(W+1)^3 := by
  have hk : v.K≤W := by
    have hp:=UniformCrossDepthReplayPreparation.power_ge_successor v.K
    rw [←UniformRadixTwoDAG.width_eq] at hp
    unfold widthOf at hN
    omega
  have hkn : v.K*widthOf v≤W*W := Nat.mul_le_mul hk hN
  have hg : gates v≤32*(W+1)^2 := by unfold gates;nlinarith
  have hh : height v≤15*(W+1) := by unfold height;omega
  have hgh : gates v*height v≤480*(W+1)^3 := by
    have h:=Nat.mul_le_mul hg hh
    convert h using 1
    ring
  unfold wordBudget UniformCrossDepthReplayPreparation.wordBudget rowBase colorBase recordBase
  nlinarith

lemma constructor_height (v : Parameters) : height v=8*v.K+7 := rfl
lemma stored_layer_count (v : Parameters) (Z : ℕ)
    (ha : v.a≤widthOf v) (he : v.e≤widthOf v) (u : State)
    (result : Processed v Z (crossDAG v.K v.a v.e ha he).program (height v) u)
    (d : Fin (height v)) :
    u.natHeap (v.J+3*d.val)=some
      (UniformCrossDepthReplayPreparation.bucket (crossDAG v.K v.a v.e ha he).program v.enabled d.val).length :=
  (result d.val d.isLt).2.2.1

end
end ExactFourierCircuits.UniformCrossHeightPreparationMachine
