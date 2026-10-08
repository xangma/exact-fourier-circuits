import UniformToeplitzCrossTopologyMachine
import UniformDAGLayers
import UniformDAGBucketMachine
import UniformTensorMonomialMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformCrossShearTableMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformConvolutionTopologyMachine (Row)

/-- Literal-zero port n is always omitted. Inputs are omitted only in a
disabled sweep. No coefficient or data value participates in this decision. -/
def visible (n : ℕ) (enabled : Bool) (a : ℕ) : Bool :=
 if a < n then enabled else decide (n < a)

def coefficientAddress (C P : ℕ) (row : Row) : ℕ :=
 if row.kind=1 then C+row.payload else if row.payload < 2 then P else P+2

def emit (n A dst src coefficient : ℕ) (enabled : Bool) : List UniformInPlaceMachine.Row :=
 if visible n enabled src then [⟨A+dst,A+src,coefficient⟩] else []

def expansion (n A C P ordinal : ℕ) (enabled : Bool) (row : Row) :
 List UniformInPlaceMachine.Row :=
 let dst:=n+1+ordinal
 if row.opcode < 2 then
   emit n A dst row.left P enabled ++ emit n A dst row.right (P+row.opcode) enabled
 else emit n A dst row.left (coefficientAddress C P row) enabled

theorem emit_length (n A dst src coefficient : ℕ) (enabled : Bool) :
 (emit n A dst src coefficient enabled).length ≤ 1 := by
 unfold emit;split <;> simp

theorem expansion_length (n A C P ordinal : ℕ) (enabled : Bool) (row : Row) :
 (expansion n A C P ordinal enabled row).length ≤ 2 := by
 unfold expansion;split
 · simpa only [List.length_append] using Nat.add_le_add
     (emit_length n A _ _ _ enabled) (emit_length n A _ _ _ enabled)
 · exact (emit_length n A _ _ _ enabled).trans (by decide)

/-- Read-only caller720..729: gate count, five-field tape, stable gate order,
fresh triple output, data base, positive coefficient base, six-constant base,
enabled0/1, input count and dyadic width. Scratch730..749; no scalar accesses. -/
def boot : List Op := [.literal 730 0,.literal 731 1,.literal 732 2,
 .literal 733 3,.literal 734 5,.literal 735 0,.literal 736 0,.add 749 728 731]
def reads : List Op := [.add 737 722 735,.getNat 738 737,
 .mul 737 738 734,.add 737 721 737,.getNat 739 737,
 .add 737 737 731,.getNat 740 737,.add 737 737 731,.getNat 741 737,
 .add 737 737 731,.getNat 742 737,.add 737 737 731,.getNat 743 737,
 .add 744 724 728,.add 744 744 731,.add 744 744 738,.literal 747 0]
def left : List Op := [.add 746 740 730]
def positive : List Op := [.add 745 726 730]
def reciprocal : List Op := [.add 745 726 732]
def prepared : List Op := [.add 745 725 743]
def right : List Op := [.add 746 741 730,.add 745 726 739]
def stores : List Op := [.add 746 724 746,.mul 737 733 736,.add 737 723 737,
 .putNat 737 744,.add 737 737 731,.putNat 737 746,
 .add 737 737 731,.putNat 737 745,.add 736 736 731]
def tick : List Op := [.add 747 747 731]
def advance : List Op := [.add 735 735 731]
def program : Program := boot.map Op.code ++ [.branchLT 735 720 9 59] ++ reads.map Op.code ++
 [.branchLT 747 732 27 57,.branchLT 747 731 28 40] ++ left.map Op.code ++
 [.branchLT 739 732 30 32] ++ positive.map Op.code ++ [.jump 43,.branchLT 742 731 33 38,
 .branchLT 743 732 34 36] ++ positive.map Op.code ++ [.jump 43] ++ reciprocal.map Op.code ++
 [.jump 43] ++ prepared.map Op.code ++ [.jump 43,.branchLT 739 732 41 55] ++ right.map Op.code ++
 [.branchLT 746 728 44 45,.branchLT 730 727 46 55,.branchLT 746 749 55 46] ++
 stores.map Op.code ++ tick.map Op.code ++ [.jump 26] ++ advance.map Op.code ++ [.jump 8,.halt]
theorem program_length : program.length=60 := rfl

theorem boot_code : BlockAt boot program 0 := by intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem reads_code : BlockAt reads program 9 := by intro i hi;change i < 17 at hi;interval_cases i <;> rfl
theorem left_code : BlockAt left program 28 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem positive_code : BlockAt positive program 30 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem positive_again_code : BlockAt positive program 34 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem reciprocal_code : BlockAt reciprocal program 36 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem prepared_code : BlockAt prepared program 38 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem right_code : BlockAt right program 41 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem stores_code : BlockAt stores program 46 := by intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem tick_code : BlockAt tick program 55 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem advance_code : BlockAt advance program 57 := by intro i hi;change i < 1 at hi;interval_cases i;rfl

noncomputable section
structure Header (M T Q D A C P n N : ℕ) (enabled : Bool) (s : State) : Prop where
 count : s.natReg 720=M
 tape : s.natReg 721=T
 order : s.natReg 722=Q
 output : s.natReg 723=D
 dataBase : s.natReg 724=A
 coefficients : s.natReg 725=C
 constants : s.natReg 726=P
 enabled : s.natReg 727=if enabled then 1 else 0
 inputs : s.natReg 728=n
 width : s.natReg 729=N
structure Fixed (M T Q D A C P n N : ℕ) (enabled : Bool) (s : State) : Prop where
 header : Header M T Q D A C P n N enabled s
 zero : s.natReg 730=0
 one : s.natReg 731=1
 two : s.natReg 732=2
 three : s.natReg 733=3
 five : s.natReg 734=5
 inputsSucc : s.natReg 749=n+1

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,j < 730 ∨ 750 ≤ j → u.natReg j=s.natReg j)

theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
 h'.2.2.2.1.trans h.2.2.2.1,fun j hj=>(h'.2.2.2.2 j hj).trans (h.2.2.2.2 j hj)⟩

def natScratch (o:Op) : Prop := match o with
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _=>730 ≤ d ∧ d < 750
 | .putNat _ _=>True
 | _=>False

theorem block_frame (os:List Op) (s:State) (h:∀o∈os,natScratch o):Frame s (applyBlock os s):=by
 induction os generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | cons o os ih=>
   have ho:=h o (by simp)
   have ht:=ih (o.apply s) (fun t ht=>h t (by simp[ht]))
   apply frame_trans (u:=o.apply s) ?_ ht
   cases o <;> simp only[natScratch] at ho
   all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
   all_goals intro j hj
   all_goals simp (disch:=omega) [Op.apply,writeNat,next]

theorem Header.transport {M T Q D A C P n N:ℕ} {enabled:Bool} {s u:State}
 (h:Header M T Q D A C P n N enabled s) (f:Frame s u):Header M T Q D A C P n N enabled u:=
 ⟨(f.2.2.2.2 720 (by omega)).trans h.count,(f.2.2.2.2 721 (by omega)).trans h.tape,
 (f.2.2.2.2 722 (by omega)).trans h.order,(f.2.2.2.2 723 (by omega)).trans h.output,
 (f.2.2.2.2 724 (by omega)).trans h.dataBase,(f.2.2.2.2 725 (by omega)).trans h.coefficients,
 (f.2.2.2.2 726 (by omega)).trans h.constants,(f.2.2.2.2 727 (by omega)).trans h.enabled,
 (f.2.2.2.2 728 (by omega)).trans h.inputs,(f.2.2.2.2 729 (by omega)).trans h.width⟩

def coreScratch (o:Op):Prop:=match o with
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _=>735 ≤ d ∧ d < 749
 | .putNat _ _=>True
 | _=>False

theorem core_registers (os:List Op) (s:State) (h:∀o∈os,coreScratch o):
 ∀j,j < 735 ∨ 749 ≤ j → (applyBlock os s).natReg j=s.natReg j:=by
 induction os generalizing s with
 | nil=>intro _ _;rfl
 | cons o os ih=>
   intro j hj
   change (applyBlock os (o.apply s)).natReg j=s.natReg j
   rw[ih (o.apply s) (fun t ht=>h t (by simp[ht])) j hj]
   have ho:=h o (by simp)
   cases o <;> simp only[coreScratch] at ho
   all_goals simp (disch:=omega) [Op.apply,writeNat,next]

theorem Fixed.transport {M T Q D A C P n N:ℕ} {enabled:Bool} {s u:State}
 (h:Fixed M T Q D A C P n N enabled s)
 (f:∀j,j < 735 ∨ 749 ≤ j → u.natReg j=s.natReg j):Fixed M T Q D A C P n N enabled u:=
 ⟨⟨(f 720 (by omega)).trans h.header.count,(f 721 (by omega)).trans h.header.tape,
 (f 722 (by omega)).trans h.header.order,(f 723 (by omega)).trans h.header.output,
 (f 724 (by omega)).trans h.header.dataBase,(f 725 (by omega)).trans h.header.coefficients,
 (f 726 (by omega)).trans h.header.constants,(f 727 (by omega)).trans h.header.enabled,
 (f 728 (by omega)).trans h.header.inputs,(f 729 (by omega)).trans h.header.width⟩,
 (f 730 (by omega)).trans h.zero,(f 731 (by omega)).trans h.one,
 (f 732 (by omega)).trans h.two,(f 733 (by omega)).trans h.three,
 (f 734 (by omega)).trans h.five,(f 749 (by omega)).trans h.inputsSucc⟩

def started (s:State):State:=applyBlock boot s
theorem started_spec {M T Q D A C P n N:ℕ} {enabled:Bool} (s:State)
 (h:Header M T Q D A C P n N enabled s) (hpc:s.pc=0):
 Fixed M T Q D A C P n N enabled (started s) ∧
 (started s).natReg 735=0 ∧ (started s).natReg 736=0 ∧ (started s).pc=8:=by
 refine ⟨⟨h.transport (block_frame boot s (by simp[boot,natScratch])),?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
 all_goals simp[started,boot,applyBlock,Op.apply,writeNat,next,h.inputs,hpc]

def loaded (s:State):State:=applyBlock reads (setPC s 9)
structure Cache (A n ordinal:ℕ) (row:Row) (s:State):Prop where
 gateIndex:s.natReg 738=ordinal
 opcode:s.natReg 739=row.opcode
 left:s.natReg 740=row.left
 right:s.natReg 741=row.right
 kind:s.natReg 742=row.kind
 payload:s.natReg 743=row.payload
 destination:s.natReg 744=A+n+1+ordinal

def Fields (T ordinal:ℕ) (row:Row) (s:State):Prop:=
 s.natHeap (T+5*ordinal)=some row.opcode ∧ s.natHeap (T+5*ordinal+1)=some row.left ∧
 s.natHeap (T+5*ordinal+2)=some row.right ∧ s.natHeap (T+5*ordinal+3)=some row.kind ∧
 s.natHeap (T+5*ordinal+4)=some row.payload

theorem loaded_spec {M T Q D A C P n N i ordinal:ℕ} {enabled:Bool}
 (s:State) (row:Row) (h:Fixed M T Q D A C P n N enabled s)
 (hi:s.natReg 735=i) (ho:s.natHeap (Q+i)=some ordinal) (hf:Fields T ordinal row s):
 Cache A n ordinal row (loaded s) ∧ (loaded s).natReg 747=0 ∧ (loaded s).pc=26 ∧
 Fixed M T Q D A C P n N enabled (loaded s) ∧ Frame s (loaded s) ∧
 (loaded s).natHeap=s.natHeap ∧ (loaded s).natReg 735=s.natReg 735 ∧
 (loaded s).natReg 736=s.natReg 736:=by
 have fixed:=h.transport (core_registers reads (setPC s 9) (by simp[reads,coreScratch]))
 have frame:=block_frame reads (setPC s 9) (by simp[reads,natScratch])
 unfold Fields at hf
 simp only[Nat.mul_comm,Nat.add_assoc] at hf
 refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,fixed,frame,?_,?_,?_⟩
 all_goals simp[loaded,reads,applyBlock,Op.apply,setPC,writeNat,next,h.header.order,h.header.tape,
   h.header.dataBase,h.header.inputs,h.one,h.five,hi,ho,hf.1,hf.2.1,hf.2.2.1,
   hf.2.2.2.1,hf.2.2.2.2,Nat.add_assoc]

theorem branch_runs (B m pc l r yes no:ℕ) (x:Fin m→ℂ) (s:State)
 (hpc:s.pc=pc) (hcode:program[pc]?=some (.branchLT l r yes no))
 (hs:WordBound B s) (hy:yes ≤ B) (hn:no ≤ B):
 BoundedRuns program m x B s 1 (setPC s (if s.natReg l < s.natReg r then yes else no)):=by
 refine .next hs ?_ (.refl (changePC_bound B s _ hs (by split_ifs <;> assumption)))
 simp[UniformMachine.step,hpc,hcode,setPC]

theorem jump_runs (B m pc target:ℕ) (x:Fin m→ℂ) (s:State)
 (hpc:s.pc=pc) (hcode:program[pc]?=some (.jump target))
 (hs:WordBound B s) (ht:target ≤ B):
 BoundedRuns program m x B s 1 (setPC s target):=by
 refine .next hs ?_ (.refl (changePC_bound B s _ hs ht))
 simp[UniformMachine.step,hpc,hcode,setPC]

theorem startup_bounded {M T Q D A C P n N:ℕ} {enabled:Bool} (B m:ℕ) (x:Fin m→ℂ)
 (s:State) (h:Header M T Q D A C P n N enabled s) (hpc:s.pc=0)
 (hs:WordBound B s) (hb:60 ≤ B) (hn:n+1 ≤ B):
 BoundedRuns program m x B s 8 (started s):=by
 exact block_runs boot program 0 m B x s boot_code hpc hs (by change 0+8 ≤ B;omega)
   (by simp[readable,boot,Op.readable])
   (by simp[peak,boot,Op.peak,Op.apply,writeNat,next,h.inputs];omega)

theorem loaded_bounded {M T Q D A C P n N i ordinal G:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (s:State) (row:Row) (h:Fixed M T Q D A C P n N enabled s)
 (hi:s.natReg 735=i) (hlt:i < M) (ho:s.natHeap (Q+i)=some ordinal) (hord:ordinal < G)
 (hf:Fields T ordinal row s) (hpc:s.pc=8) (hs:WordBound B s) (hb:60 ≤ B)
 (ht:T+5*G ≤ B) (hq:Q+M ≤ B) (ha:A+n+1+G ≤ B):
 BoundedRuns program m x B s 18 (loaded s):=by
 have first:=branch_runs B m 8 735 720 9 59 x s hpc rfl hs (by omega) (by omega)
 have take:s.natReg 735 < s.natReg 720:=by rw[hi,h.header.count];exact hlt
 rw[ite_eq_left take] at first
 have values:row.opcode ≤ B ∧ row.left ≤ B ∧ row.right ≤ B ∧ row.kind ≤ B ∧ row.payload ≤ B:=
   ⟨(hs.2.2.1 _ _ hf.1).2,(hs.2.2.1 _ _ hf.2.1).2,(hs.2.2.1 _ _ hf.2.2.1).2,
   (hs.2.2.1 _ _ hf.2.2.2.1).2,(hs.2.2.1 _ _ hf.2.2.2.2).2⟩
 unfold Fields at hf
 simp only[Nat.mul_comm,Nat.add_assoc] at hf
 have block:=block_runs reads program 9 m B x (setPC s 9) reads_code rfl first.final_bound
   (by change 9+17 ≤ B;omega)
   (by simp[readable,reads,Op.readable,Op.apply,setPC,writeNat,next,h.header.order,
     h.header.tape,h.one,h.five,hi,ho,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,
     Nat.add_assoc])
   (by simp[peak,reads,Op.peak,Op.apply,setPC,writeNat,next,h.header.order,h.header.tape,
     h.header.dataBase,h.header.inputs,h.one,h.five,hi,ho,hf.1,hf.2.1,hf.2.2.1,
     hf.2.2.2.1,hf.2.2.2.2,Nat.add_assoc];omega)
 exact first.trans block

def GoodCoefficient (N:ℕ) {r:ℕ} (c:UniformReplayPrint.Coefficient r):Prop:=
 c=.rational ((N:ℚ)⁻¹) ∨ ∃i,c=.prepared i false
def GoodExpr (N:ℕ) {r:ℕ} {α:Type} (g:UniformConvolutionDAG.Expr r α):Prop:=match g with
 | .add _ _ | .sub _ _=>True
 | .scale c _=>GoodCoefficient N c
theorem goodExpr_map {N r:ℕ} {α β:Type} (f:α→β) (g:UniformConvolutionDAG.Expr r α)
 (h:GoodExpr N g):GoodExpr N (g.map f):=by cases g <;> exact h

theorem convolution_gate_good (K:ℕ) (j:UniformConvolutionDAG.Node K):
 GoodExpr (UniformRadixTwoDAG.width K) (UniformConvolutionDAG.gate j):=by
 cases j with
 | forward j | backward j=>
   apply goodExpr_map
   cases hg:UniformRadixTwoDAG.gate j with
   | add a b | sub a b=>trivial
   | scale c a=>
     have hc:=UniformRadixTwoDAG.gate_scalar_bound j c (by simp[hg,UniformRadixTwoDAG.Op.scalars])
     simp only[UniformConvolutionDAG.prepareOp,GoodExpr,GoodCoefficient]
     right
     simp[UniformConvolutionDAG.powerCoefficient,hc]
 | diagonal i=>exact Or.inr ⟨_,rfl⟩
 | normalize i=>exact Or.inl rfl

theorem convolution_instruction_good (K:ℕ) (j:Fin (UniformConvolutionDAG.total K)):
 GoodExpr (UniformRadixTwoDAG.width K) (UniformConvolutionDAG.instruction K j):=
 goodExpr_map _ _ (convolution_gate_good K _)

theorem goodExpr_remap (K e:ℕ) (slot:Fin 6)
 (g:UniformConvolutionDAG.Expr (UniformRadixTwoDAG.width K+UniformRadixTwoDAG.width K) ℕ)
 (h:GoodExpr (UniformRadixTwoDAG.width K) g):
 GoodExpr (UniformRadixTwoDAG.width K) (UniformToeplitzCrossTopologyMachine.remapExpr K e slot g):=by
 cases g with
 | add a b | sub a b=>trivial
 | scale c a=>
   rcases h with rfl|⟨i,rfl⟩
   · exact Or.inl rfl
   · exact Or.inr ⟨_,rfl⟩

theorem slot_rows_good (K e:ℕ) (slot:Fin 6) (row:Row)
 (hr:row ∈ UniformToeplitzCrossTopologyMachine.slotRows K e slot.val):
 GoodExpr (UniformRadixTwoDAG.width K) (UniformToeplitzCrossTopologyMachine.decodeCrossRow K row):=by
 have hm:UniformToeplitzCrossTopologyMachine.decodeCrossRow K row ∈
   (UniformToeplitzCrossTopologyMachine.slotRows K e slot.val).map
     (UniformToeplitzCrossTopologyMachine.decodeCrossRow K):=List.mem_map.mpr ⟨row,hr,rfl⟩
 rw[UniformToeplitzCrossTopologyMachine.slot_encoding_lossless] at hm
 obtain ⟨g,hg,heq⟩:=List.mem_map.mp hm
 rw[←heq]
 obtain ⟨j,_,rfl⟩:=List.mem_map.mp hg
 exact goodExpr_remap K e slot _ (convolution_instruction_good K j)

theorem cross_records_good (K a e:ℕ) (ha:a ≤ UniformRadixTwoDAG.width K)
 (he:e ≤ UniformRadixTwoDAG.width K) (g:UniformConvolutionDAG.Expr (UniformToeplitzCrossDAG.bankSize K) ℕ)
 (hg:g ∈ UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG K a e ha he).program):
 GoodExpr (UniformRadixTwoDAG.width K) g:=by
 rw[←UniformToeplitzCrossTopologyMachine.cross_encoding_lossless K a e ha he] at hg
 obtain ⟨row,hr,rfl⟩:=List.mem_map.mp hg
 simp only[UniformToeplitzCrossTopologyMachine.crossRows,List.mem_append] at hr
 rcases hr with (hs|hf)|hs
 · obtain ⟨slot,hslot,hrow⟩:=List.mem_flatMap.mp hs
   exact slot_rows_good K e ⟨slot,List.mem_range.mp hslot⟩ row hrow
 · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
   trivial
 · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hs
   trivial

def locations (r C Z P:ℕ):UniformInPlaceMachine.Locations r where
 rational:=fun q=>if q=1 then P else if q=(-1) then P+1 else P+2
 positive:=fun i=>C+i.val
 negative:=fun i=>Z+i.val

theorem reciprocal_eq_one (N:ℕ) (hN:0 < N):((N:ℚ)⁻¹=1 ↔ N=1):=by
 have hn:(N:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hN)
 constructor
 · intro h
   have hh:=congrArg (fun q:ℚ=>q*(N:ℚ)) h
   simp only[inv_mul_cancel₀ hn,one_mul] at hh
   exact_mod_cast hh.symm
 · intro h;subst N;norm_num

/-- Width1 consistently aliases the reciprocal leaf to the rational-one
slot. The printer and rowOf use the same numerical address policy. -/
theorem reciprocal_location (r C Z P N:ℕ) (hN:0 < N):
 (locations r C Z P).address (.rational ((N:ℚ)⁻¹))=if N < 2 then P else P+2:=by
 have pos:0 < (N:ℚ)⁻¹:=inv_pos.mpr (by exact_mod_cast hN)
 have neg:(N:ℚ)⁻¹ ≠ (-1):=by linarith
 simp only[UniformInPlaceMachine.Locations.address,locations,reciprocal_eq_one N hN,
   ite_eq_right neg]
 split_ifs <;> omega

def sourceRef (n:ℕ) (enabled:Bool) (a:ℕ):Option ℕ:=if visible n enabled a then some a else none

theorem referenceMap_sourceRef {n k:ℕ} (enabled:Bool) (a:Fin (n+1+k)):
 OAI.ExactFourier.referenceMap enabled (fun i:Fin n=>i.val) (fun j:Fin k=>n+1+j.val) a=
 sourceRef n enabled a.val:=by
 refine Fin.addCases (fun i=>?_) (fun j=>?_) a
 · refine Fin.lastCases ?_ (fun i=>?_) i
   · simp[OAI.ExactFourier.referenceMap,sourceRef,visible]
   · cases enabled <;> simp[OAI.ExactFourier.referenceMap,sourceRef,visible,i.isLt]
 · have low:¬ n+1+j.val < n:=by omega
   have high:n < n+1+j.val:=by omega
   simp[OAI.ExactFourier.referenceMap,sourceRef,visible,low,high]

def shiftedRow {r:ℕ} (A:ℕ) (p:UniformInPlaceMachine.Locations r)
 (s:UniformReplayPrint.ShearCode ℕ r):UniformInPlaceMachine.Row:=
 ⟨A+s.dst,A+s.src,p.address s.coefficient⟩

theorem reference_rows {r:ℕ} (n A dst src:ℕ) (enabled:Bool)
 (p:UniformInPlaceMachine.Locations r) (c:UniformReplayPrint.Coefficient r)
 (h:∀i,sourceRef n enabled src=some i → dst≠i):
 (UniformReplayPrint.reference dst (sourceRef n enabled src) c h).map (shiftedRow A p)=
 emit n A dst src (p.address c) enabled:=by
 unfold sourceRef emit
 split <;> simp[UniformReplayPrint.reference,shiftedRow]

def directRows {r:ℕ} (n A:ℕ) (p:UniformInPlaceMachine.Locations r) (j:ℕ)
 (enabled:Bool):UniformConvolutionDAG.Expr r ℕ→List UniformInPlaceMachine.Row
 | .add a b=>emit n A (n+1+j) a (p.address (.rational 1)) enabled ++
   emit n A (n+1+j) b (p.address (.rational 1)) enabled
 | .sub a b=>emit n A (n+1+j) a (p.address (.rational 1)) enabled ++
   emit n A (n+1+j) b (p.address (.rational (-1))) enabled
 | .scale c a=>emit n A (n+1+j) a (p.address c) enabled

theorem expansion_typed (K n A C Z P j:ℕ) (enabled:Bool)
 (g:UniformConvolutionDAG.Expr (UniformToeplitzCrossDAG.bankSize K) ℕ)
 (h:GoodExpr (UniformRadixTwoDAG.width K) g):
 expansion n A C P j enabled (UniformConvolutionTopologyMachine.encode g)=
 directRows n A (locations (UniformToeplitzCrossDAG.bankSize K) C Z P) j enabled g:=by
 cases g with
 | add a b=>simp[expansion,directRows,UniformConvolutionTopologyMachine.encode,
   locations,UniformInPlaceMachine.Locations.address]
 | sub a b=>norm_num[expansion,directRows,UniformConvolutionTopologyMachine.encode,
   locations,UniformInPlaceMachine.Locations.address]
 | scale c a=>
   rcases h with rfl|⟨i,rfl⟩
   · simp only[expansion,directRows,UniformConvolutionTopologyMachine.encode,
       UniformConvolutionTopologyMachine.reciprocal_den,show ¬ 2 < 2 by decide,ite_false,
       coefficientAddress,show (0:ℕ)≠1 by decide]
     rw[reciprocal_location _ C Z P _ (UniformRadixTwoDAG.width_pos K)]
   · rfl

theorem Fixed.setPC {M T Q D A C P n N:ℕ} {enabled:Bool} {s:State}
 (h:Fixed M T Q D A C P n N enabled s) (pc:ℕ):
 Fixed M T Q D A C P n N enabled (setPC s pc):=h.transport (fun _ _=>rfl)

theorem Fixed.writeNat {M T Q D A C P n N:ℕ} {enabled:Bool} {s:State}
 (h:Fixed M T Q D A C P n N enabled s) (d v:ℕ) (hd:735 ≤ d ∧ d < 749):
 Fixed M T Q D A C P n N enabled (writeNat s d v):=by
 apply h.transport
 intro j hj
 exact Function.update_of_ne (show j≠d by omega) v s.natReg

theorem Cache.setPC {A n j:ℕ} {row:Row} {s:State} (h:Cache A n j row s) (pc:ℕ):
 Cache A n j row (setPC s pc):=
 ⟨h.gateIndex,h.opcode,h.left,h.right,h.kind,h.payload,h.destination⟩

theorem Cache.writeNat {A n j:ℕ} {row:Row} {s:State} (h:Cache A n j row s)
 (d v:ℕ) (hd:d < 738 ∨ 744 < d):Cache A n j row (writeNat s d v):=by
 have regs:∀i,i≠d → (UniformMachine.writeNat s d v).natReg i=s.natReg i:=by
   intro i hi;exact Function.update_of_ne hi v s.natReg
 exact ⟨(regs 738 (by omega)).trans h.gateIndex,(regs 739 (by omega)).trans h.opcode,
   (regs 740 (by omega)).trans h.left,(regs 741 (by omega)).trans h.right,
   (regs 742 (by omega)).trans h.kind,(regs 743 (by omega)).trans h.payload,
   (regs 744 (by omega)).trans h.destination⟩

theorem add_runs (B m pc d l r value:ℕ) (x:Fin m→ℂ) (s:State)
 (hpc:s.pc=pc) (hcode:program[pc]?=some (.natBinary .add d l r)) (hs:WordBound B s)
 (hb:pc+1 ≤ B) (hv:s.natReg l+s.natReg r=value) (hvalue:value ≤ B):
 BoundedRuns program m x B s 1 (writeNat s d value):=by
 refine .next hs ?_ (.refl (writeNat_bound B s d value hs (by rw[hpc];exact hb) hvalue))
 simp[UniformMachine.step,hpc,hcode,evalNat,hv]

def selected (C P:ℕ) (row:Row) (phase:ℕ) (s:State):State:=
 if phase=0 then
   setPC (writeNat (writeNat (setPC s 28) 746 row.left) 745
     (if row.opcode < 2 then P else coefficientAddress C P row)) 43
 else if row.opcode < 2 then
   setPC (writeNat (writeNat (setPC s 41) 746 row.right) 745 (P+row.opcode)) 43
 else setPC s 55

def slotActive (row:Row) (phase:ℕ):Bool:=decide (phase=0 ∨ row.opcode < 2)
def slotSource (row:Row) (phase:ℕ):ℕ:=if phase=0 then row.left else row.right
def slotCoefficient (C P:ℕ) (row:Row) (phase:ℕ):ℕ:=
 if phase=0 then if row.opcode < 2 then P else coefficientAddress C P row else P+row.opcode

theorem selected_spec {M T Q D A C P n N ordinal phase:ℕ} {enabled:Bool} (row:Row) (s:State)
 (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s):
 Fixed M T Q D A C P n N enabled (selected C P row phase s) ∧
 Cache A n ordinal row (selected C P row phase s) ∧ Frame s (selected C P row phase s) ∧
 (selected C P row phase s).natHeap=s.natHeap ∧
 (selected C P row phase s).natReg 735=s.natReg 735 ∧
 (selected C P row phase s).natReg 736=s.natReg 736 ∧
 (selected C P row phase s).natReg 747=s.natReg 747 ∧
 (selected C P row phase s).pc=(if slotActive row phase then 43 else 55) ∧
 (slotActive row phase=true → (selected C P row phase s).natReg 746=slotSource row phase ∧
   (selected C P row phase s).natReg 745=slotCoefficient C P row phase):=by
 by_cases hp:phase=0
 · simp only[selected,ite_eq_left hp]
   have fixed:=(((h.setPC 28).writeNat 746 row.left (by omega)).writeNat 745
     (if row.opcode < 2 then P else coefficientAddress C P row) (by omega)).setPC 43
   have cached:=(((cache.setPC 28).writeNat 746 row.left (by omega)).writeNat 745
     (if row.opcode < 2 then P else coefficientAddress C P row) (by omega)).setPC 43
   refine ⟨fixed,cached,?_,rfl,?_,?_,?_,?_,?_⟩
   · refine ⟨rfl,rfl,rfl,rfl,?_ ⟩
     intro j hj;simp (disch:=omega) [writeNat,next,setPC]
   all_goals simp [writeNat,next,setPC,slotActive,slotSource,slotCoefficient,hp]
 · by_cases hop:row.opcode < 2
   · simp only[selected,ite_eq_right hp,ite_eq_left hop]
     have fixed:=(((h.setPC 41).writeNat 746 row.right (by omega)).writeNat 745 (P+row.opcode) (by omega)).setPC 43
     have cached:=(((cache.setPC 41).writeNat 746 row.right (by omega)).writeNat 745 (P+row.opcode) (by omega)).setPC 43
     refine ⟨fixed,cached,?_,rfl,?_,?_,?_,?_,?_⟩
     · refine ⟨rfl,rfl,rfl,rfl,?_ ⟩
       intro j hj;simp (disch:=omega) [writeNat,next,setPC]
     all_goals simp [writeNat,next,setPC,slotActive,slotSource,slotCoefficient,hp,hop]
   · simp only[selected,ite_eq_right hp,ite_eq_right hop]
     exact ⟨h.setPC 55,cache.setPC 55,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩,rfl,rfl,rfl,rfl,
       by simp[slotActive,hp,hop,setPC],by simp[slotActive,hp,hop]⟩

theorem selected_bounded {M T Q D A C P n N ordinal phase:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (row:Row) (s:State)
 (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hp:s.natReg 747=phase) (phaseBound:phase < 2) (hpc:s.pc=27) (hs:WordBound B s)
 (hb:60 ≤ B) (hP:P+2 ≤ B) (hC:C+row.payload ≤ B) (kind:row.kind ≤ 1):
 ∃ticks,ticks ≤ 7 ∧ BoundedRuns program m x B s ticks (selected C P row phase s):=by
 have choose:=branch_runs B m 27 747 731 28 40 x s hpc rfl hs (by omega) (by omega)
 by_cases hz:phase=0
 · have test:s.natReg 747 < s.natReg 731:=by rw[hp,h.one,hz];omega
   rw[ite_eq_left test] at choose
   let a:=writeNat (setPC s 28) 746 row.left
   have leftRun:=add_runs B m 28 746 740 730 row.left x (setPC s 28) rfl rfl choose.final_bound
     (by omega) (by dsimp only[setPC];rw[cache.left,h.zero];omega) (by rw[←cache.left];exact hs.2.1 740)
   have af:Fixed M T Q D A C P n N enabled a:=(h.setPC 28).writeNat 746 row.left (by omega)
   have ac:Cache A n ordinal row a:=(cache.setPC 28).writeNat 746 row.left (by omega)
   have apc:a.pc=29:=rfl
   have opRun:=branch_runs B m 29 739 732 30 32 x a apc rfl leftRun.final_bound (by omega) (by omega)
   by_cases binary:row.opcode < 2
   · have test:a.natReg 739 < a.natReg 732:=by rw[ac.opcode,af.two];exact binary
     rw[ite_eq_left test] at opRun
     have value:=add_runs B m 30 745 726 730 P x (setPC a 30) rfl rfl opRun.final_bound
       (by omega) (by dsimp only[setPC];rw[af.header.constants,af.zero];omega) (by omega)
     have jump:=jump_runs B m 31 43 x (writeNat (setPC a 30) 745 P) rfl rfl value.final_bound (by omega)
     refine ⟨5,by omega,?_⟩
     convert choose.trans (leftRun.trans (opRun.trans (value.trans jump))) using 1
     simp[selected,hz,binary,a,writeNat,next,setPC]
   · have test:¬ a.natReg 739 < a.natReg 732:=by rw[ac.opcode,af.two];exact binary
     rw[ite_eq_right test] at opRun
     have kindRun:=branch_runs B m 32 742 731 33 38 x (setPC a 32) rfl rfl opRun.final_bound (by omega) (by omega)
     by_cases hk:row.kind=0
     · have test:(setPC a 32).natReg 742 < (setPC a 32).natReg 731:=by dsimp only[setPC];rw[ac.kind,af.one,hk];omega
       rw[ite_eq_left test] at kindRun
       have payloadRun:=branch_runs B m 33 743 732 34 36 x (setPC (setPC a 32) 33) rfl rfl
         kindRun.final_bound (by omega) (by omega)
       by_cases small:row.payload < 2
       · have test:(setPC (setPC a 32) 33).natReg 743 < (setPC (setPC a 32) 33).natReg 732:=by
           dsimp only[setPC];rw[ac.payload,af.two];exact small
         rw[ite_eq_left test] at payloadRun
         have value:=add_runs B m 34 745 726 730 P x (setPC (setPC (setPC a 32) 33) 34) rfl rfl
           payloadRun.final_bound (by omega) (by dsimp only[setPC];rw[af.header.constants,af.zero];omega) (by omega)
         have jump:=jump_runs B m 35 43 x (writeNat _ 745 P) rfl rfl value.final_bound (by omega)
         refine ⟨7,by omega,?_⟩
         convert choose.trans (leftRun.trans (opRun.trans (kindRun.trans (payloadRun.trans (value.trans jump))))) using 1
         simp[selected,hz,binary,coefficientAddress,hk,small,a,writeNat,next,setPC]
       · have test:¬ (setPC (setPC a 32) 33).natReg 743 < (setPC (setPC a 32) 33).natReg 732:=by
           dsimp only[setPC];rw[ac.payload,af.two];exact small
         rw[ite_eq_right test] at payloadRun
         have value:=add_runs B m 36 745 726 732 (P+2) x (setPC (setPC (setPC a 32) 33) 36) rfl rfl
           payloadRun.final_bound (by omega) (by dsimp only[setPC];rw[af.header.constants,af.two]) hP
         have jump:=jump_runs B m 37 43 x (writeNat _ 745 (P+2)) rfl rfl value.final_bound (by omega)
         refine ⟨7,by omega,?_⟩
         convert choose.trans (leftRun.trans (opRun.trans (kindRun.trans (payloadRun.trans (value.trans jump))))) using 1
         simp[selected,hz,binary,coefficientAddress,hk,small,a,writeNat,next,setPC]
     · have hk1:row.kind=1:=by omega
       have test:¬ (setPC a 32).natReg 742 < (setPC a 32).natReg 731:=by dsimp only[setPC];rw[ac.kind,af.one,hk1];omega
       rw[ite_eq_right test] at kindRun
       have value:=add_runs B m 38 745 725 743 (C+row.payload) x (setPC (setPC a 32) 38) rfl rfl
         kindRun.final_bound (by omega) (by dsimp only[setPC];rw[af.header.coefficients,ac.payload]) hC
       have jump:=jump_runs B m 39 43 x (writeNat _ 745 (C+row.payload)) rfl rfl value.final_bound (by omega)
       refine ⟨6,by omega,?_⟩
       convert choose.trans (leftRun.trans (opRun.trans (kindRun.trans (value.trans jump)))) using 1
       simp[selected,hz,binary,coefficientAddress,hk1,a,writeNat,next,setPC]
 · have test:¬ s.natReg 747 < s.natReg 731:=by rw[hp,h.one];omega
   rw[ite_eq_right test] at choose
   have opRun:=branch_runs B m 40 739 732 41 55 x (setPC s 40) rfl rfl choose.final_bound (by omega) (by omega)
   by_cases binary:row.opcode < 2
   · have test:(setPC s 40).natReg 739 < (setPC s 40).natReg 732:=by dsimp only[setPC];rw[cache.opcode,h.two];exact binary
     rw[ite_eq_left test] at opRun
     have block:=block_runs right program 41 m B x (setPC (setPC s 40) 41) right_code rfl
       opRun.final_bound (by change 41+2 ≤ B;omega)
       (by simp[readable,right,Op.readable])
       (by simp[peak,right,Op.peak,Op.apply,setPC,writeNat,next,cache.right,cache.opcode,h.zero,h.header.constants]
           have hr:=hs.2.1 741;rw[cache.right] at hr;omega)
     refine ⟨4,by omega,?_⟩
     convert choose.trans (opRun.trans block) using 1
     all_goals simp[selected,hz,binary,right,applyBlock,Op.apply,writeNat,next,setPC,cache.right,cache.opcode,h.zero,h.header.constants]
   · have test:¬ (setPC s 40).natReg 739 < (setPC s 40).natReg 732:=by dsimp only[setPC];rw[cache.opcode,h.two];exact binary
     rw[ite_eq_right test] at opRun
     refine ⟨2,by omega,?_⟩
     convert choose.trans opRun using 1
     simp[selected,hz,binary,setPC]


def emitted (n:ℕ) (enabled:Bool) (s:State):State:=
 if visible n enabled (s.natReg 746) then applyBlock stores (setPC s 46) else setPC s 55

def putRow (D:ℕ) (row:UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ):ℕ→Option ℕ:=
 Function.update (Function.update (Function.update heap D (some row.dst)) (D+1) (some row.src))
   (D+2) (some row.coefficient)

def putRows (D:ℕ) : List UniformInPlaceMachine.Row → (ℕ→Option ℕ) → (ℕ→Option ℕ)
 | [],heap=>heap
 | row::rows,heap=>putRows (D+3) rows (putRow D row heap)

theorem putRows_append (D:ℕ) (xs ys:List UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ):
 putRows D (xs++ys) heap=putRows (D+3*xs.length) ys (putRows D xs heap):=by
 induction xs generalizing D heap with
 | nil=>simp[putRows]
 | cons row xs ih=>
   simp only[List.cons_append,putRows,List.length_cons]
   rw[ih];congr 1;omega

theorem putRow_outside (D j:ℕ) (row:UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ)
 (h:j<D ∨ D+3≤j):putRow D row heap j=heap j:=by
 simp (disch:=omega) [putRow]

theorem putRows_outside (D j:ℕ) (rows:List UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ)
 (h:j<D ∨ D+3*rows.length≤j):putRows D rows heap j=heap j:=by
 induction rows generalizing D heap with
 | nil=>rfl
 | cons row rows ih=>
   simp only[putRows,List.length_cons] at *
   rw[ih (D+3) (putRow D row heap) (by omega)]
   exact putRow_outside D j row heap (by omega)

def RowFields (D:ℕ) (row:UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ):Prop:=
 heap D=some row.dst ∧ heap (D+1)=some row.src ∧ heap (D+2)=some row.coefficient

def Table (D:ℕ) (rows:List UniformInPlaceMachine.Row) (s:State):Prop:=
 ∀i,(hi:i<rows.length)→RowFields (D+3*i) (rows[i]'hi) s.natHeap

theorem putRows_fields (D:ℕ) (rows:List UniformInPlaceMachine.Row) (heap:ℕ→Option ℕ):
 ∀i,(hi:i<rows.length)→RowFields (D+3*i) (rows[i]'hi) (putRows D rows heap):=by
 induction rows generalizing D heap with
 | nil=>simp
 | cons row rows ih=>
   intro i hi
   cases i with
   | zero=>
     have h0:=putRows_outside (D+3) D rows (putRow D row heap) (by omega)
     have h1:=putRows_outside (D+3) (D+1) rows (putRow D row heap) (by omega)
     have h2:=putRows_outside (D+3) (D+2) rows (putRow D row heap) (by omega)
     simp only[putRows,List.getElem_cons_zero,Nat.mul_zero,Nat.add_zero,RowFields]
     rw[h0,h1,h2]
     simp[putRow]
   | succ i=>
     have h:=ih (D+3) (putRow D row heap) i (by simpa using hi)
     simpa only[putRows,List.getElem_cons_succ,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem stored_spec {M T Q D A C P n N ordinal count raw coefficient:ℕ} {enabled:Bool}
 (row:Row) (s:State) (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hc:s.natReg 736=count) (hr:s.natReg 746=raw) (hcoef:s.natReg 745=coefficient):
 let u:=applyBlock stores (setPC s 46)
 Fixed M T Q D A C P n N enabled u ∧ Cache A n ordinal row u ∧ Frame s u ∧
 u.natHeap=putRow (D+3*count) ⟨A+n+1+ordinal,A+raw,coefficient⟩ s.natHeap ∧
 u.natReg 735=s.natReg 735 ∧ u.natReg 736=count+1 ∧ u.natReg 747=s.natReg 747 ∧ u.pc=55:=by
 dsimp only
 have fixed:=h.transport (core_registers stores (setPC s 46) (by simp[stores,coreScratch]))
 have frame:=block_frame stores (setPC s 46) (by simp[stores,natScratch])
 refine ⟨fixed,?_,frame,?_,?_,?_,?_,?_⟩
 · constructor <;> simp[stores,applyBlock,Op.apply,setPC,writeNat,next,cache.gateIndex,cache.opcode,
     cache.left,cache.right,cache.kind,cache.payload,cache.destination]
 all_goals simp[stores,applyBlock,Op.apply,setPC,writeNat,next,h.header.dataBase,h.header.output,
   h.one,h.three,hc,hr,hcoef,cache.destination,putRow,Nat.add_assoc,Nat.mul_comm]

theorem stored_bounded {M T Q D A C P n N ordinal count raw coefficient:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (row:Row) (s:State) (h:Fixed M T Q D A C P n N enabled s)
 (cache:Cache A n ordinal row s) (hc:s.natReg 736=count) (hr:s.natReg 746=raw)
 (hcoef:s.natReg 745=coefficient) (hpc:s.pc=46) (hs:WordBound B s)
 (hcode:60≤B) (hout:D+3*(count+1)≤B) (hraw:A+raw≤B) (hdst:A+n+1+ordinal≤B)
 (hcoeff:coefficient≤B) (hcount:count+1≤B):
 BoundedRuns program m x B s 9 (applyBlock stores s):=by
 apply block_runs stores program 46 m B x s stores_code hpc hs (by change 46+9≤B;omega)
 · simp[stores,readable,Op.readable]
 · simp[stores,peak,Op.peak,Op.apply,writeNat,next,h.header.dataBase,h.header.output,
      h.one,h.three,hc,hr,hcoef,cache.destination]
   omega


theorem visibility_bounded {M T Q D A C P n N raw:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (s:State) (h:Fixed M T Q D A C P n N enabled s)
 (hr:s.natReg 746=raw) (hpc:s.pc=43) (hs:WordBound B s) (hb:60≤B):
 BoundedRuns program m x B s 2 (setPC s (if visible n enabled raw then 46 else 55)):=by
 have first:=branch_runs B m 43 746 728 44 45 x s hpc rfl hs (by omega) (by omega)
 by_cases hin:raw<n
 · have test:s.natReg 746<s.natReg 728:=by rw[hr,h.header.inputs];exact hin
   rw[ite_eq_left test] at first
   have second:=branch_runs B m 44 730 727 46 55 x (setPC s 44) rfl rfl first.final_bound (by omega) (by omega)
   convert first.trans second using 1
   cases enabled <;> simp[visible,hin,setPC,h.zero,h.header.enabled]
 · have test:¬s.natReg 746<s.natReg 728:=by rw[hr,h.header.inputs];exact hin
   rw[ite_eq_right test] at first
   have second:=branch_runs B m 45 746 749 55 46 x (setPC s 45) rfl rfl first.final_bound (by omega) (by omega)
   convert first.trans second using 1
   by_cases heq:raw=n
   · simp[visible,heq,setPC,hr,h.inputsSucc]
   · have hgt:n<raw:=by omega
     have hh:¬raw<n+1:=by omega
     simp[visible,hin,hgt,setPC,hr,h.inputsSucc,hh]

def slotRows (n A C P ordinal:ℕ) (enabled:Bool) (row:Row) (phase:ℕ):List UniformInPlaceMachine.Row:=
 if slotActive row phase then emit n A (n+1+ordinal) (slotSource row phase)
   (slotCoefficient C P row phase) enabled else []

def slotEnd (n C P:ℕ) (enabled:Bool) (row:Row) (phase:ℕ) (s:State):State:=
 let a:=selected C P row phase (setPC s 27)
 let b:=if slotActive row phase then emitted n enabled a else a
 setPC (applyBlock tick (setPC b 55)) 26

theorem tick_spec {M T Q D A C P n N ordinal phase:ℕ} {enabled:Bool}
 (row:Row) (s:State) (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hp:s.natReg 747=phase):
 let u:=setPC (applyBlock tick (setPC s 55)) 26
 Fixed M T Q D A C P n N enabled u ∧ Cache A n ordinal row u ∧ Frame s u ∧
 u.natHeap=s.natHeap ∧ u.natReg 735=s.natReg 735 ∧ u.natReg 736=s.natReg 736 ∧
 u.natReg 747=phase+1 ∧ u.pc=26:=by
 dsimp only
 have ff:=h.transport (core_registers tick (setPC s 55) (by simp[tick,coreScratch]))
 have ca:Cache A n ordinal row (applyBlock tick (setPC s 55)):=by
   constructor <;> simp[tick,applyBlock,Op.apply,writeNat,next,setPC,cache.gateIndex,
     cache.opcode,cache.left,cache.right,cache.kind,cache.payload,cache.destination]
 refine ⟨ff.setPC 26,ca.setPC 26,block_frame tick (setPC s 55) (by simp[tick,natScratch]),?_,?_,?_,?_,rfl⟩
 all_goals simp[tick,applyBlock,Op.apply,writeNat,next,setPC,hp,h.one]

theorem slot_spec {M T Q D A C P n N ordinal count phase:ℕ} {enabled:Bool}
 (row:Row) (s:State) (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hc:s.natReg 736=count) (hp:s.natReg 747=phase):
 let u:=slotEnd n C P enabled row phase s
 Fixed M T Q D A C P n N enabled u ∧ Cache A n ordinal row u ∧ Frame s u ∧
 u.natHeap=putRows (D+3*count) (slotRows n A C P ordinal enabled row phase) s.natHeap ∧
 u.natReg 735=s.natReg 735 ∧ u.natReg 736=count+(slotRows n A C P ordinal enabled row phase).length ∧
 u.natReg 747=phase+1 ∧ u.pc=26:=by
 dsimp only
 let a:=selected C P row phase (setPC s 27)
 obtain ⟨ha,ca,fa,hea,hia,hca,hpa,pca,ra⟩:=selected_spec (phase:=phase) row (setPC s 27) (h.setPC 27) (cache.setPC 27)
 change Fixed M T Q D A C P n N enabled a at ha
 change Cache A n ordinal row a at ca
 change Frame s a at fa
 change a.natHeap=s.natHeap at hea
 change a.natReg 735=s.natReg 735 at hia
 change a.natReg 736=s.natReg 736 at hca
 change a.natReg 747=s.natReg 747 at hpa
 change slotActive row phase=true → a.natReg 746=slotSource row phase ∧ a.natReg 745=slotCoefficient C P row phase at ra
 by_cases active:slotActive row phase=true
 · obtain ⟨raw,coef⟩:=ra active
   by_cases hv:visible n enabled (slotSource row phase)=true
   · let b:=applyBlock stores (setPC a 46)
     obtain ⟨hb,cb,fb,heb,hib,hcb,hpb,pcb⟩:=stored_spec row a ha ca (hca.trans hc) raw coef
     change Fixed M T Q D A C P n N enabled b at hb
     change Cache A n ordinal row b at cb
     change Frame a b at fb
     change b.natHeap=putRow (D+3*count) ⟨A+n+1+ordinal,A+slotSource row phase,slotCoefficient C P row phase⟩ a.natHeap at heb
     change b.natReg 735=a.natReg 735 at hib
     change b.natReg 736=count+1 at hcb
     change b.natReg 747=a.natReg 747 at hpb
     have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick (setPC b 55)) 26:=by
       change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
       rw[ite_eq_left active]
       have vv:visible n enabled (a.natReg 746)=true:=by rw[raw];exact hv
       simp only[emitted,ite_eq_left vv];rfl
     rw[endeq]
     obtain ⟨ht,ct,ft,het,hit,hct,hpt,pct⟩:=tick_spec row b hb cb (hpb.trans (hpa.trans hp))
     refine ⟨ht,ct,frame_trans fa (frame_trans fb ft),?_,hit.trans (hib.trans hia),?_,hpt,pct⟩
     · rw[het,heb,hea];simp[slotRows,active,emit,hv,putRows,Nat.add_assoc]
     · rw[hct,hcb];simp[slotRows,active,emit,hv]
   · have hv':visible n enabled (a.natReg 746)=false:=by rw[raw];exact Bool.eq_false_iff.mpr hv
     have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick (setPC a 55)) 26:=by
       change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
       simp only[ite_eq_left active,emitted,hv',Bool.false_eq_true,ite_false];rfl
     rw[endeq]
     obtain ⟨ht,ct,ft,het,hit,hct,hpt,pct⟩:=tick_spec row a ha ca (hpa.trans hp)
     refine ⟨ht,ct,frame_trans fa ft,?_,hit.trans hia,?_,hpt,pct⟩
     · rw[het,hea];simp[slotRows,active,emit,hv,putRows]
     · rw[hct,hca,hc];simp[slotRows,active,emit,hv]
 · have act:slotActive row phase=false:=Bool.eq_false_iff.mpr active
   have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick (setPC a 55)) 26:=by
     change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
     simp only[act,Bool.false_eq_true,ite_false]
   rw[endeq]
   obtain ⟨ht,ct,ft,het,hit,hct,hpt,pct⟩:=tick_spec row a ha ca (hpa.trans hp)
   refine ⟨ht,ct,frame_trans fa ft,?_,hit.trans hia,?_,hpt,pct⟩
   · rw[het,hea];simp[slotRows,act,putRows]
   · rw[hct,hca,hc];simp[slotRows,act]

theorem tick_bounded {M T Q D A C P n N phase:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (s:State) (h:Fixed M T Q D A C P n N enabled s)
 (hp:s.natReg 747=phase) (hpc:s.pc=55) (hs:WordBound B s) (hb:60≤B) (hphase:phase+1≤B):
 BoundedRuns program m x B s 2 (setPC (applyBlock tick s) 26):=by
 have block:=block_runs tick program 55 m B x s tick_code hpc hs (by change 55+1≤B;omega)
   (by simp[tick,readable,Op.readable])
   (by simp[tick,peak,Op.peak,hp,h.one];exact hphase)
 have jump:=jump_runs B m 56 26 x (applyBlock tick s) (by simp[tick,applyBlock,Op.apply_pc,hpc])
   rfl block.final_bound (by omega)
 exact block.trans jump

theorem setPC_eq_of {s:State} {pc:ℕ} (h:s.pc=pc):setPC s pc=s:=by
 cases s
 subst pc
 rfl

theorem slot_bounded {M T Q D A C P n N ordinal count phase:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (row:Row) (s:State)
 (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hc:s.natReg 736=count) (hp:s.natReg 747=phase) (phaseBound:phase<2)
 (hpc:s.pc=26) (hs:WordBound B s) (hb:60≤B) (hP:P+2≤B) (hC:C+row.payload≤B)
 (kind:row.kind≤1) (hleft:A+row.left≤B) (hright:A+row.right≤B)
 (hdst:A+n+1+ordinal≤B) (hout:D+3*(count+1)≤B) (hcount:count+1≤B):
 ∃ticks,ticks≤21 ∧ BoundedRuns program m x B s ticks (slotEnd n C P enabled row phase s):=by
 have choose:=branch_runs B m 26 747 732 27 57 x s hpc rfl hs (by omega) (by omega)
 have test:s.natReg 747<s.natReg 732:=by rw[hp,h.two];exact phaseBound
 rw[ite_eq_left test] at choose
 obtain ⟨cost,bcost,run⟩:=selected_bounded B m x row (setPC s 27) (h.setPC 27) (cache.setPC 27)
   hp phaseBound rfl choose.final_bound hb hP hC kind
 let a:=selected C P row phase (setPC s 27)
 have spec:=selected_spec (phase:=phase) row (setPC s 27) (h.setPC 27) (cache.setPC 27)
 change Fixed M T Q D A C P n N enabled a ∧ Cache A n ordinal row a ∧ _ at spec
 have aphase:a.natReg 747=phase:=spec.2.2.2.2.2.2.1.trans hp
 have acount:a.natReg 736=count:=spec.2.2.2.2.2.1.trans hc
 by_cases active:slotActive row phase=true
 · have apc:a.pc=43:=by simpa[active] using spec.2.2.2.2.2.2.2.1
   have regs:=spec.2.2.2.2.2.2.2.2 active
   have vis:=visibility_bounded B m x a spec.1 regs.1 apc run.final_bound hb
   by_cases hv:visible n enabled (slotSource row phase)=true
   · have raw:A+slotSource row phase≤B:=by unfold slotSource;split <;> assumption
     have coef:slotCoefficient C P row phase≤B:=by
       have act:phase=0 ∨ row.opcode<2:=of_decide_eq_true active
       unfold slotCoefficient coefficientAddress;split_ifs <;> omega
     rw[ite_eq_left hv] at vis
     have storesRun:=stored_bounded B m x row (setPC a 46) (spec.1.setPC 46) (spec.2.1.setPC 46)
       acount regs.1 regs.2 rfl vis.final_bound hb hout raw hdst coef hcount
     let b:=applyBlock stores (setPC a 46)
     have stored:=stored_spec row a spec.1 spec.2.1 acount regs.1 regs.2
     change Fixed M T Q D A C P n N enabled b ∧ Cache A n ordinal row b ∧ _ at stored
     have tickRun:=tick_bounded (phase:=phase) B m x b stored.1 (stored.2.2.2.2.2.2.1.trans aphase)
       stored.2.2.2.2.2.2.2 storesRun.final_bound hb (by omega)
     have pcb:b.pc=55:=stored.2.2.2.2.2.2.2
     have self:setPC b 55=b:=setPC_eq_of pcb
     have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick b) 26:=by
       change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
       have vv:visible n enabled (a.natReg 746)=true:=by rw[regs.1];exact hv
       simp only[ite_eq_left active,emitted,ite_eq_left vv]
       change setPC (applyBlock tick (setPC b 55)) 26=_
       rw[self]
     refine ⟨1+cost+2+9+2,by omega,?_⟩
     rw[endeq]
     simpa only[Nat.add_assoc] using choose.trans (run.trans (vis.trans (storesRun.trans tickRun)))
   · have hv':visible n enabled (slotSource row phase)=false:=by cases hh:visible n enabled (slotSource row phase) <;> simp_all
     simp only[hv',Bool.false_eq_true,ite_false] at vis
     have tickRun:=tick_bounded (phase:=phase) B m x (setPC a 55) (spec.1.setPC 55) aphase rfl vis.final_bound hb (by omega)
     have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick (setPC a 55)) 26:=by
       change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
       have vv:visible n enabled (a.natReg 746)=false:=by rw[regs.1];exact hv'
       simp only[ite_eq_left active,emitted,vv,Bool.false_eq_true,ite_false,setPC]
     refine ⟨1+cost+2+2,by omega,?_⟩
     rw[endeq]
     simpa only[Nat.add_assoc] using choose.trans (run.trans (vis.trans tickRun))
 · have act:slotActive row phase=false:=by cases hh:slotActive row phase <;> simp_all
   have apc:a.pc=55:=by simpa[act] using spec.2.2.2.2.2.2.2.1
   have tickRun:=tick_bounded (phase:=phase) B m x a spec.1 aphase apc run.final_bound hb (by omega)
   have self:setPC a 55=a:=setPC_eq_of apc
   have endeq:slotEnd n C P enabled row phase s=setPC (applyBlock tick a) 26:=by
     change (let z:=if slotActive row phase then emitted n enabled a else a;setPC (applyBlock tick (setPC z 55)) 26)=_
     simp only[act,Bool.false_eq_true,ite_false];rw[self]
   refine ⟨1+cost+2,by omega,?_⟩
   rw[endeq]
   simpa only[Nat.add_assoc] using choose.trans (run.trans tickRun)


theorem slotRows_length (n A C P j phase:ℕ) (enabled:Bool) (row:Row):
 (slotRows n A C P j enabled row phase).length≤1:=by
 unfold slotRows;split
 · exact emit_length n A _ _ _ enabled
 · simp

theorem slots_expansion (n A C P j:ℕ) (enabled:Bool) (row:Row):
 slotRows n A C P j enabled row 0 ++ slotRows n A C P j enabled row 1=
 expansion n A C P j enabled row:=by
 by_cases h:row.opcode<2 <;> simp[slotRows,slotActive,slotSource,slotCoefficient,expansion,h]

def gateEnd (n C P:ℕ) (enabled:Bool) (row:Row) (s:State):State:=
 let a:=slotEnd n C P enabled row 0 s
 let b:=slotEnd n C P enabled row 1 a
 setPC (applyBlock advance (setPC b 57)) 8

theorem gate_spec {M T Q D A C P n N ordinal count:ℕ} {enabled:Bool}
 (row:Row) (s:State) (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hc:s.natReg 736=count) (hp:s.natReg 747=0):
 let u:=gateEnd n C P enabled row s
 Fixed M T Q D A C P n N enabled u ∧ Frame s u ∧
 u.natHeap=putRows (D+3*count) (expansion n A C P ordinal enabled row) s.natHeap ∧
 u.natReg 735=s.natReg 735+1 ∧ u.natReg 736=count+(expansion n A C P ordinal enabled row).length ∧
 u.pc=8:=by
 dsimp only
 let a:=slotEnd n C P enabled row 0 s
 let b:=slotEnd n C P enabled row 1 a
 obtain ⟨ha,ca,fa,hea,hia,hca,hpa,pca⟩:=slot_spec row s h cache hc hp
 change Fixed M T Q D A C P n N enabled a at ha
 change Cache A n ordinal row a at ca
 change Frame s a at fa
 change a.natHeap=putRows (D+3*count) (slotRows n A C P ordinal enabled row 0) s.natHeap at hea
 change a.natReg 735=s.natReg 735 at hia
 change a.natReg 736=count+(slotRows n A C P ordinal enabled row 0).length at hca
 change a.natReg 747=1 at hpa
 obtain ⟨hb,cb,fb,heb,hib,hcb,hpb,pcb⟩:=slot_spec row a ha ca hca hpa
 change Fixed M T Q D A C P n N enabled b at hb
 change Frame a b at fb
 change b.natHeap=putRows (D+3*(count+(slotRows n A C P ordinal enabled row 0).length))
   (slotRows n A C P ordinal enabled row 1) a.natHeap at heb
 change b.natReg 735=a.natReg 735 at hib
 change b.natReg 736=count+(slotRows n A C P ordinal enabled row 0).length+
   (slotRows n A C P ordinal enabled row 1).length at hcb
 have ff:=hb.transport (core_registers advance (setPC b 57) (by simp[advance,coreScratch]))
 refine ⟨ff.setPC 8,frame_trans fa (frame_trans fb (block_frame advance (setPC b 57) (by simp[advance,natScratch]))),?_,?_,?_,rfl⟩
 · change b.natHeap=_
   rw[heb,hea,←slots_expansion,putRows_append]
   congr 1;omega
 · change b.natReg 735+b.natReg 731=s.natReg 735+1
   rw[hb.one,hib,hia]
 · change b.natReg 736=_
   rw[hcb,←slots_expansion,List.length_append];omega

theorem gate_bounded {M T Q D A C P n N ordinal count:ℕ} {enabled:Bool}
 (B m:ℕ) (x:Fin m→ℂ) (row:Row) (s:State)
 (h:Fixed M T Q D A C P n N enabled s) (cache:Cache A n ordinal row s)
 (hc:s.natReg 736=count) (hp:s.natReg 747=0) (hpc:s.pc=26) (hs:WordBound B s)
 (hb:60≤B) (hP:P+2≤B) (hC:C+row.payload≤B) (kind:row.kind≤1)
 (hleft:A+row.left≤B) (hright:A+row.right≤B) (hdst:A+n+1+ordinal≤B)
 (hout:D+3*(count+2)≤B) (hcount:count+2≤B) (hindex:s.natReg 735+1≤B):
 ∃ticks,ticks≤45 ∧ BoundedRuns program m x B s ticks (gateEnd n C P enabled row s):=by
 obtain ⟨c0,b0,r0⟩:=slot_bounded B m x row s h cache hc hp (by decide) hpc hs hb hP hC kind
   hleft hright hdst (by omega) (by omega)
 let a:=slotEnd n C P enabled row 0 s
 obtain ⟨ha,ca,fa,hea,hia,hca,hpa,pca⟩:=slot_spec row s h cache hc hp
 change Fixed M T Q D A C P n N enabled a at ha
 change Cache A n ordinal row a at ca
 have len:=slotRows_length n A C P ordinal 0 enabled row
 obtain ⟨c1,b1,r1⟩:=slot_bounded B m x row a ha ca hca hpa (by decide) pca r0.final_bound hb hP hC kind
   hleft hright hdst (by omega) (by omega)
 let b:=slotEnd n C P enabled row 1 a
 obtain ⟨hh,cc,ff,he,hi,hc',hphase,hpc'⟩:=slot_spec row a ha ca hca hpa
 change Fixed M T Q D A C P n N enabled b at hh
 change b.natReg 735=a.natReg 735 at hi
 change b.natReg 747=2 at hphase
 change b.pc=26 at hpc'
 have branch:=branch_runs B m 26 747 732 27 57 x b hpc' rfl r1.final_bound (by omega) (by omega)
 have test:¬b.natReg 747<b.natReg 732:=by rw[hphase,hh.two];omega
 rw[ite_eq_right test] at branch
 have index:b.natReg 735+1≤B:=by rw[hi];change a.natReg 735=s.natReg 735 at hia;rw[hia];exact hindex
 have adv:=block_runs advance program 57 m B x (setPC b 57) advance_code rfl branch.final_bound
   (by change 57+1≤B;omega) (by simp[advance,readable,Op.readable])
   (by simp[advance,peak,Op.peak,setPC,hh.one];exact index)
 have jump:=jump_runs B m 58 8 x (applyBlock advance (setPC b 57)) rfl rfl adv.final_bound (by omega)
 refine ⟨c0+c1+1+1+1,by omega,?_⟩
 simpa only[gateEnd,advance,List.length_cons,List.length_nil,Nat.add_zero,Nat.add_assoc] using r0.trans (r1.trans (branch.trans (adv.trans jump)))


def OrderBank (Q:ℕ) (order:List ℕ) (s:State):Prop:=
 ∀i,(hi:i<order.length)→s.natHeap (Q+i)=some (order[i]'hi)

def Tape (G T:ℕ) (rows:ℕ→Row) (s:State):Prop:=∀j,j<G→Fields T j (rows j) s

def RowsBound (G n N:ℕ) (rows:ℕ→Row):Prop:=∀j,j<G→
 (rows j).left<n+1+j ∧ (rows j).right<n+1+j ∧ (rows j).kind≤1 ∧ (rows j).payload≤7*N

def orderedRows (n A C P:ℕ) (enabled:Bool) (rows:ℕ→Row) (order:List ℕ):List UniformInPlaceMachine.Row:=
 order.flatMap (fun j=>expansion n A C P j enabled (rows j))

theorem orderedRows_length (n A C P:ℕ) (enabled:Bool) (rows:ℕ→Row) (order:List ℕ):
 (orderedRows n A C P enabled rows order).length≤2*order.length:=by
 induction order with
 | nil=>simp[orderedRows]
 | cons j js ih=>
   simp only[orderedRows,List.flatMap_cons,List.length_append,List.length_cons] at *
   have h:=expansion_length n A C P j enabled (rows j)
   omega

def runGates (n C P:ℕ) (enabled:Bool) (rows:ℕ→Row):List ℕ→State→State
 | [],s=>setPC s 59
 | j::js,s=>runGates n C P enabled rows js (gateEnd n C P enabled (rows j) (loaded s))

theorem runGates_bounded {M T Q D A C P n N i count:ℕ} {enabled:Bool}
 (B m G:ℕ) (x:Fin m→ℂ) (rows:ℕ→Row) (order:List ℕ) (s:State)
 (h:Fixed M T Q D A C P n N enabled s) (index:s.natReg 735=i) (hc:s.natReg 736=count)
 (hpc:s.pc=8) (hs:WordBound B s) (len:i+order.length=M) (countBound:count≤2*i)
 (valid:∀j∈order,j<G) (bank:OrderBank (Q+i) order s) (tape:Tape G T rows s)
 (bounds:RowsBound G n N rows) (hcode:60≤B) (hT:T+5*G≤D) (hQ:Q+M≤D)
 (hD:D+6*M≤B) (hA:A+n+1+G≤B) (hC:C+7*N≤B) (hP:P+2≤B):
 ∃ticks,ticks≤63*order.length+1 ∧
 BoundedRuns program m x B s ticks (runGates n C P enabled rows order s) ∧
 Fixed M T Q D A C P n N enabled (runGates n C P enabled rows order s) ∧
 Frame s (runGates n C P enabled rows order s) ∧
 (runGates n C P enabled rows order s).natHeap=putRows (D+3*count) (orderedRows n A C P enabled rows order) s.natHeap ∧
 (runGates n C P enabled rows order s).natReg 735=i+order.length ∧
 (runGates n C P enabled rows order s).natReg 736=count+(orderedRows n A C P enabled rows order).length ∧
 (runGates n C P enabled rows order s).pc=59:=by
 induction order generalizing i count s with
 | nil=>
   have branch:=branch_runs B m 8 735 720 9 59 x s hpc rfl hs (by omega) (by omega)
   have test:¬s.natReg 735<s.natReg 720:=by rw[index,h.header.count];simp at len;omega
   rw[ite_eq_right test] at branch
   refine ⟨1,by simp,branch,h.setPC 59,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩,rfl,?_,?_,rfl⟩
   · simpa[runGates,setPC] using index
   · simpa[runGates,setPC,orderedRows] using hc
 | cons j js ih=>
   have jG:=valid j (by simp)
   have hrow:=bounds j jG
   have head:s.natHeap (Q+i)=some j:=by
     have hh:=bank 0 (by simp)
     exact hh
   have loadRun:=loaded_bounded B m x s (rows j) h index (by simp only[List.length_cons] at len;omega) head jG (tape j jG) hpc hs hcode (by omega) (by omega) hA
   obtain ⟨ca,ph,pca,ha,fa,hea,ia,cnta⟩:=loaded_spec s (rows j) h index head (tape j jG)
   let a:=loaded s
   change Cache A n j (rows j) a at ca
   change Fixed M T Q D A C P n N enabled a at ha
   have current:a.natReg 736=count:=cnta.trans hc
   have idx:a.natReg 735=i:=ia.trans index
   have outBudget:D+3*(count+2)≤B:=by simp only[List.length_cons] at len;omega
   obtain ⟨cg,bcg,gateRun⟩:=gate_bounded B m x (rows j) a ha ca current ph pca loadRun.final_bound
     hcode hP (by omega) hrow.2.2.1 (by omega) (by omega) (by omega) outBudget (by omega)
     (by rw[idx];simp only[List.length_cons] at len;omega)
   let b:=gateEnd n C P enabled (rows j) a
   obtain ⟨hb,fb,heb,ib,cntb,pcb⟩:=gate_spec (rows j) a ha ca current ph
   change Fixed M T Q D A C P n N enabled b at hb
   change Frame a b at fb
   change b.natHeap=putRows (D+3*count) (expansion n A C P j enabled (rows j)) a.natHeap at heb
   change b.natReg 735=a.natReg 735+1 at ib
   change b.natReg 736=count+(expansion n A C P j enabled (rows j)).length at cntb
   have unchanged:∀z,z<D→b.natHeap z=s.natHeap z:=by
     intro z hz;rw[heb];rw[putRows_outside (D+3*count) z _ _ (by omega)];exact congrFun hea z
   have bank':OrderBank (Q+(i+1)) js b:=by
     intro z hz
     rw[unchanged _ (by simp only[List.length_cons] at len;omega)]
     have old:=bank (z+1) (by simpa using hz)
     simpa only[List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using old
   have tape':Tape G T rows b:=by
     intro z hz
     unfold Fields
     have old:=tape z hz
     unfold Fields at old
     refine ⟨?_,?_,?_,?_,?_⟩
     all_goals rw[unchanged _ (by omega)]
     all_goals first | exact old.1 | exact old.2.1 | exact old.2.2.1 | exact old.2.2.2.1 | exact old.2.2.2.2
   have eLen:=expansion_length n A C P j enabled (rows j)
   obtain ⟨ct,bct,tailRun,ht,ft,het,it,cntt,pct⟩:=ih b hb (ib.trans (by rw[idx])) cntb pcb gateRun.final_bound
     (by simp only[List.length_cons] at len;omega) (by omega)
     (fun z hz=>valid z (by simp[hz])) bank' tape'
   refine ⟨18+cg+ct,by simp only[List.length_cons];omega,?_,ht,
     frame_trans fa (frame_trans fb ft),?_,?_,?_,pct⟩
   · simpa only[runGates,Nat.add_assoc] using loadRun.trans (gateRun.trans tailRun)
   · change (runGates n C P enabled rows js b).natHeap=_
     rw[het,heb]
     change a.natHeap=s.natHeap at hea
     rw[hea]
     simp only[orderedRows,List.flatMap_cons,putRows_append]
     congr 1;omega
   · change (runGates n C P enabled rows js b).natReg 735=_
     rw[it];simp only[List.length_cons];omega
   · change (runGates n C P enabled rows js b).natReg 736=_
     rw[cntt];simp only[orderedRows,List.flatMap_cons,List.length_append];omega


def Outside (D capacity:ℕ) (s u:State):Prop:=∀j,j<D ∨ D+capacity≤j→u.natHeap j=s.natHeap j

/-- Full literal printer: only physical typed fields and gate-order cells are
inputs. Every later read guard and output table is derived from those banks. -/
theorem execution (B m G T Q D A C P n N:ℕ) (x:Fin m→ℂ) (rows:ℕ→Row)
 (order:List ℕ) (enabled:Bool) (s:State) (h:Header order.length T Q D A C P n N enabled s)
 (pc:s.pc=0) (hs:WordBound B s) (bank:OrderBank Q order s) (tape:Tape G T rows s)
 (bounds:RowsBound G n N rows) (valid:∀j∈order,j<G) (hcode:60≤B)
 (hT:T+5*G≤D) (hQ:Q+order.length≤D) (hD:D+6*order.length≤B)
 (hA:A+n+1+G≤B) (hC:C+7*N≤B) (hP:P+2≤B):
 ∃u ticks,BoundedExecution program m x B s ticks u ∧ ticks≤64*order.length+10 ∧
 u.pc=59 ∧ Header order.length T Q D A C P n N enabled u ∧
 Table D (orderedRows n A C P enabled rows order) u ∧
 u.natReg 736=(orderedRows n A C P enabled rows order).length ∧
 Outside D (6*order.length) s u ∧ Frame s u:=by
 have start:=startup_bounded B m x s h pc hs hcode (by omega)
 obtain ⟨fixed,index,count,pca⟩:=started_spec s h pc
 let a:=started s
 have heap:a.natHeap=s.natHeap:=rfl
 have bank':OrderBank (Q+0) order a:=by
   intro j hj
   change s.natHeap (Q+0+j)=some (order[j]'hj)
   simpa only[Nat.add_zero] using bank j hj
 have tape':Tape G T rows a:=tape
 obtain ⟨cost,bcost,run,hf,frame,he,hi,hc,hpc⟩:=runGates_bounded B m G x rows order a fixed index count pca
   start.final_bound (by omega) (by omega) valid bank' tape' bounds hcode hT hQ hD hA hC hP
 let u:=runGates n C P enabled rows order a
 change u.pc=59 at hpc
 have halt:BoundedExecution program m x B u 1 u:=.halt run.final_bound
   (by simp[UniformMachine.step,hpc,show program[59]?=some .halt from rfl])
 refine ⟨u,8+cost+1,?_,by omega,hpc,hf.header,?_,?_,?_,?_⟩
 · exact (start.trans run).executes halt
 · intro j hj
   change u.natHeap=putRows (D+3*0) (orderedRows n A C P enabled rows order) a.natHeap at he
   rw[he]
   simpa only[Nat.mul_zero,Nat.add_zero] using putRows_fields D (orderedRows n A C P enabled rows order) a.natHeap j hj
 · simpa only[Nat.zero_add] using hc
 · intro j hj
   change u.natHeap=putRows (D+3*0) (orderedRows n A C P enabled rows order) a.natHeap at he
   rw[he]
   have len:=orderedRows_length n A C P enabled rows order
   simpa only[Nat.mul_zero,Nat.add_zero,heap] using putRows_outside D j
     (orderedRows n A C P enabled rows order) a.natHeap (by omega)
 · exact frame_trans (block_frame boot s (by simp[boot,natScratch])) frame

theorem saved_headers {s u:State} (f:Frame s u):∀j,100≤j→j≤106→u.natReg j=s.natReg j:=by
 intro j hj hl;exact f.2.2.2.2 j (by omega)

theorem master_retained {s u:State} (f:Frame s u):u.scalarHeap 0=s.scalarHeap 0:=congrFun f.1 0


open UniformReplayPrint UniformToeplitzCrossDAG

/-- Actual constructor gate expansion, indexed by its chronological ordinal. -/
def gateSweep {r n:ℕ}: {t:ℕ}→UniformReplayPrint.Program r n t→Bool→ℕ→List (ShearCode ℕ r)
 | 0,.nil,_,_=>[]
 | t+1,.step p g,enabled,j=>if j=t then
     gateCode (n+1+t)
       (OAI.ExactFourier.referenceMap enabled (fun i:Fin n=>i.val) (fun j=>n+1+j.val))
       (OAI.ExactFourier.referenceMap_avoids enabled _ _ _
         (by intro i;have:=i.isLt;omega) (by intro j;have:=j.isLt;omega)) g
     else gateSweep p enabled j

theorem gateSweep_step {r n t:ℕ} (p:UniformReplayPrint.Program r n t)
 (g:UniformReplayPrint.Gate r (n+1+t)) (enabled:Bool) (j:ℕ):
 gateSweep (p.step g) enabled j=if j=t then
 gateCode (n+1+t)
   (OAI.ExactFourier.referenceMap enabled (fun i:Fin n=>i.val) (fun j:Fin t=>n+1+j.val))
   (OAI.ExactFourier.referenceMap_avoids enabled _ _ _
     (by intro i;have:=i.isLt;omega) (by intro j;have:=j.isLt;omega)) g
 else gateSweep p enabled j:=rfl

theorem gateSweep_step_old {r n t:ℕ} (p:UniformReplayPrint.Program r n t)
 (g:UniformReplayPrint.Gate r (n+1+t)) (enabled:Bool) (j:ℕ) (hj:j<t):
 gateSweep (p.step g) enabled j=gateSweep p enabled j:=by simp[gateSweep,show j≠t by omega]

theorem gateSweep_dst {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool) (j:ℕ):
 ∀s∈gateSweep p enabled j,s.dst=n+1+j:=by
 induction p with
 | nil=>simp[gateSweep]
 | @step t p g ih=>
   rw[gateSweep_step]
   by_cases hj:j=t
   · rw[ite_eq_left hj]
     subst j
     intro s hs
     exact (UniformDAGLayers.gateCode_member _ _ _ g (runDepth p (fun _=>0)) s hs).1
   · rw[ite_eq_right hj];exact ih

theorem gateSweep_all {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool):
 (List.range t).flatMap (gateSweep p enabled)=UniformDAGLayers.natSweep p enabled:=by
 induction p with
 | nil=>rfl
 | @step t p g ih=>
   rw[List.range_succ,List.flatMap_append]
   have old:(List.range t).flatMap (gateSweep (p.step g) enabled)=
     (List.range t).flatMap (gateSweep p enabled):=by
     apply List.flatMap_congr
     intro j hj
     exact gateSweep_step_old p g enabled j (List.mem_range.mp hj)
   rw[old,ih,UniformDAGLayers.natSweep_step]
   simp[gateSweep]

def exprAt {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (j:ℕ):UniformConvolutionDAG.Expr r ℕ:=
 ((programRecords p)[j]?).getD (.add 0 0)

def rowAt {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (j:ℕ):Row:=
 UniformConvolutionTopologyMachine.encode (exprAt p j)

theorem exprAt_present {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (j:ℕ) (hj:j<t):
 (programRecords p)[j]?=some (exprAt p j):=by
 have hlen:=programRecords_length p
 have hget:=List.getElem?_eq_getElem (show j<(programRecords p).length by omega)
 simp only[exprAt,hget,Option.getD_some]

theorem exprAt_mem {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (j:ℕ) (hj:j<t):
 exprAt p j∈programRecords p:=List.mem_of_getElem? (exprAt_present p j hj)

theorem gateSweep_rows {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (j A:ℕ)
 (loc:UniformInPlaceMachine.Locations r) (enabled:Bool) (hj:j<t):
 (gateSweep p enabled j).map (shiftedRow A loc)=directRows n A loc j enabled (exprAt p j):=by
 induction p with
 | nil=>omega
 | @step t p g ih=>
   by_cases hlt:j<t
   · rw[gateSweep_step_old p g enabled j hlt]
     have ex:exprAt (p.step g) j=exprAt p j:=by
       unfold exprAt;rw[programRecords,List.getElem?_append_left (by simpa[programRecords_length] using hlt)]
     rw[ex];exact ih hlt
   · have eq:j=t:=by omega
     subst j
     have ex:exprAt (p.step g) t=gateRecord g:=by
       simp[exprAt,programRecords,programRecords_length]
     rw[ex]
     rw[gateSweep_step,ite_eq_left rfl]
     cases g with
     | add a b=>
       simp only[gateCode,List.map_append,referenceMap_sourceRef]
       rw[reference_rows,reference_rows];rfl
     | sub a b=>
       simp only[gateCode,List.map_append,referenceMap_sourceRef]
       rw[reference_rows,reference_rows];rfl
     | scale c a=>
       simp only[gateCode,referenceMap_sourceRef]
       rw[reference_rows];rfl

def orderedSweep {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool):List (ShearCode ℕ r):=
 (UniformDAGBucketMachine.order t (UniformDAGBucketMachine.typedDepth p)).flatMap (gateSweep p enabled)

theorem orderedSweep_perm {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool):
 (orderedSweep p enabled).Perm (UniformDAGLayers.natSweep p enabled):=by
 rw[orderedSweep,←gateSweep_all]
 exact (UniformDAGBucketMachine.order_perm t _ (UniformDAGBucketMachine.typedDepth_bound p)).flatMap (fun _ _=>List.Perm.refl _)

theorem orderedSweep_levels {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool):
 (orderedSweep p enabled).Pairwise (fun a b=>UniformDAGLayers.natLevel p a.dst≤UniformDAGLayers.natLevel p b.dst):=by
 unfold orderedSweep
 apply List.pairwise_flatMap.mpr
 refine ⟨?_,?_⟩
 · intro j _
   apply List.pairwise_iff_getElem.mpr
   intro a b ha hb _
   rw[gateSweep_dst p enabled j _ (List.getElem_mem ha),gateSweep_dst p enabled j _ (List.getElem_mem hb)]
 · apply (UniformDAGBucketMachine.order_stable t (UniformDAGBucketMachine.typedDepth p)).imp_of_mem
   intro i j _ _ hij a ha b hb
   rw[gateSweep_dst p enabled i a ha,gateSweep_dst p enabled j b hb]
   change UniformDAGBucketMachine.typedDepth p i≤UniformDAGBucketMachine.typedDepth p j
   rcases hij with h|⟨h,_⟩ <;> omega


theorem rowAt_bounds {n t:ℕ} (K:ℕ) (p:UniformReplayPrint.Program (bankSize K) n t)
 (good:∀g∈programRecords p,GoodExpr (UniformRadixTwoDAG.width K) g):
 RowsBound t n (UniformRadixTwoDAG.width K) (rowAt p):=by
 intro j hj
 have hg:=good (exprAt p j) (exprAt_mem p j hj)
 have prior:=UniformToeplitzCrossTopologyMachine.programRecords_before p j (exprAt p j) (exprAt_present p j hj)
 unfold rowAt
 cases eq:exprAt p j with
 | add a b=>
   have ha:=prior a (by simp[eq,UniformConvolutionDAG.Expr.refs])
   have hb:=prior b (by simp[eq,UniformConvolutionDAG.Expr.refs])
   simp only[UniformConvolutionTopologyMachine.encode]
   exact ⟨ha,hb,by omega,by omega⟩
 | sub a b=>
   have ha:=prior a (by simp[eq,UniformConvolutionDAG.Expr.refs])
   have hb:=prior b (by simp[eq,UniformConvolutionDAG.Expr.refs])
   simp only[UniformConvolutionTopologyMachine.encode]
   exact ⟨ha,hb,by omega,by omega⟩
 | scale c a=>
   have ha:=prior a (by simp[eq,UniformConvolutionDAG.Expr.refs])
   rw[eq] at hg
   rcases hg with rfl|⟨i,rfl⟩
   · simp only[UniformConvolutionTopologyMachine.encode,UniformConvolutionTopologyMachine.reciprocal_den]
     exact ⟨ha,by omega,by omega,by omega⟩
   · simp only[UniformConvolutionTopologyMachine.encode]
     have bound:=i.isLt
     simp only[bankSize] at bound
     exact ⟨ha,by omega,by omega,by omega⟩

theorem tape_of_typed {r n t T:ℕ} (p:UniformReplayPrint.Program r n t) (s:State)
 (table:UniformToeplitzCrossTopologyMachine.RowTable ((programRecords p).map UniformConvolutionTopologyMachine.encode) T s):
 Tape t T (rowAt p) s:=by
 intro j hj
 have present:=exprAt_present p j hj
 have cell:((programRecords p).map UniformConvolutionTopologyMachine.encode)[j]?=some (rowAt p j):=by
   simp only[List.getElem?_map,present,Option.map_some,rowAt]
 exact table j (rowAt p j) cell

theorem orderedRows_typed {n t:ℕ} (K A C Z P:ℕ) (p:UniformReplayPrint.Program (bankSize K) n t)
 (good:∀g∈programRecords p,GoodExpr (UniformRadixTwoDAG.width K) g) (enabled:Bool):
 orderedRows n A C P enabled (rowAt p) (UniformDAGBucketMachine.order t (UniformDAGBucketMachine.typedDepth p))=
 (orderedSweep p enabled).map (shiftedRow A (locations (bankSize K) C Z P)):=by
 unfold orderedRows orderedSweep
 rw[List.map_flatMap]
 apply List.flatMap_congr
 intro j hj
 have hj':j<t:=(UniformDAGBucketMachine.order_mem t _ j).mp hj |>.1
 rw[gateSweep_rows p j A _ enabled hj']
 exact expansion_typed K n A C Z P j enabled (exprAt p j) (good _ (exprAt_mem p j hj'))

/-- Actual Cross271 coefficient subset, including rational1/N at width1. -/
theorem cross_good (K a e:ℕ) (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K):
 ∀g∈programRecords (crossDAG K a e ha he).program,GoodExpr (UniformRadixTwoDAG.width K) g:=
 cross_records_good K a e ha he

/-- Printed table for a supplied typed DAG and the real Bucket24 order bank.
The Cross corollary below discharges the only coefficient-subset hypothesis. -/
theorem typed_execution {n t:ℕ} (K B m T Q D A C Z P:ℕ)
 (p:UniformReplayPrint.Program (bankSize K) n t) (x:Fin m→ℂ) (enabled:Bool) (s:State)
 (good:∀g∈programRecords p,GoodExpr (UniformRadixTwoDAG.width K) g)
 (h:Header t T Q D A C P n (UniformRadixTwoDAG.width K) enabled s) (pc:s.pc=0) (hs:WordBound B s)
 (bank:UniformDAGBucketMachine.Bank Q (UniformDAGBucketMachine.order t (UniformDAGBucketMachine.typedDepth p)) s)
 (tape:UniformToeplitzCrossTopologyMachine.RowTable ((programRecords p).map UniformConvolutionTopologyMachine.encode) T s)
 (hcode:60≤B) (hT:T+5*t≤D) (hQ:Q+t≤D) (hD:D+6*t≤B)
 (hA:A+n+1+t≤B) (hC:C+7*UniformRadixTwoDAG.width K≤B) (hP:P+2≤B):
 ∃u ticks,BoundedExecution program m x B s ticks u ∧ ticks≤64*t+10 ∧ u.pc=59 ∧
 Header t T Q D A C P n (UniformRadixTwoDAG.width K) enabled u ∧
 Table D ((orderedSweep p enabled).map (shiftedRow A (locations (bankSize K) C Z P))) u ∧
 u.natReg 736=(UniformDAGLayers.natSweep p enabled).length ∧ Outside D (6*t) s u ∧ Frame s u:=by
 let order:=UniformDAGBucketMachine.order t (UniformDAGBucketMachine.typedDepth p)
 have len:order.length=t:=UniformDAGBucketMachine.order_length t _ (UniformDAGBucketMachine.typedDepth_bound p)
 have header:Header order.length T Q D A C P n (UniformRadixTwoDAG.width K) enabled s:=by rw[len];exact h
 obtain ⟨u,ticks,run,cost,hpc,hh,table,count,outside,frame⟩:=execution B m t T Q D A C P n
   (UniformRadixTwoDAG.width K) x (rowAt p) order enabled s header pc hs bank (tape_of_typed p s tape)
   (rowAt_bounds K p good) (fun j hj=>(UniformDAGBucketMachine.order_mem t _ j).mp hj |>.1)
   hcode hT (by rw[len];exact hQ) (by rw[len];exact hD) hA hC hP
 have rows:=orderedRows_typed K A C Z P p good enabled
 change orderedRows n A C P enabled (rowAt p) order=_ at rows
 rw[rows] at table count
 rw[len] at hh outside cost
 refine ⟨u,ticks,run,cost,hpc,hh,table,?_,outside,frame⟩
 rw[count,List.length_map]
 exact (orderedSweep_perm p enabled).length_eq

theorem cross_execution (K a e:ℕ) (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K)
 (B m T Q D A C Z P:ℕ) (x:Fin m→ℂ) (enabled:Bool) (s:State)
 (h:Header (crossDAG K a e ha he).size T Q D A C P e (UniformRadixTwoDAG.width K) enabled s)
 (pc:s.pc=0) (hs:WordBound B s)
 (bank:UniformDAGBucketMachine.Bank Q (UniformDAGBucketMachine.order (crossDAG K a e ha he).size
   (UniformDAGBucketMachine.typedDepth (crossDAG K a e ha he).program)) s)
 (tape:UniformToeplitzCrossTopologyMachine.RowTable (UniformToeplitzCrossTopologyMachine.crossRows K a e) T s)
 (hcode:60≤B) (hT:T+5*(crossDAG K a e ha he).size≤D) (hQ:Q+(crossDAG K a e ha he).size≤D)
 (hD:D+6*(crossDAG K a e ha he).size≤B) (hA:A+e+1+(crossDAG K a e ha he).size≤B)
 (hC:C+7*UniformRadixTwoDAG.width K≤B) (hP:P+2≤B):
 ∃u ticks,BoundedExecution program m x B s ticks u ∧ ticks≤64*(crossDAG K a e ha he).size+10 ∧ u.pc=59 ∧
 Header (crossDAG K a e ha he).size T Q D A C P e (UniformRadixTwoDAG.width K) enabled u ∧
 Table D ((orderedSweep (crossDAG K a e ha he).program enabled).map
   (shiftedRow A (locations (bankSize K) C Z P))) u ∧
 u.natReg 736=(UniformDAGLayers.natSweep (crossDAG K a e ha he).program enabled).length ∧
 Outside D (6*(crossDAG K a e ha he).size) s u ∧ Frame s u:=by
 have actual:UniformToeplitzCrossTopologyMachine.RowTable
   ((programRecords (crossDAG K a e ha he).program).map UniformConvolutionTopologyMachine.encode) T s:=by
   rw[←UniformToeplitzCrossTopologyMachine.crossRows_typed K a e ha he];exact tape
 exact typed_execution K B m T Q D A C Z P (crossDAG K a e ha he).program x enabled s (cross_good K a e ha he)
   h pc hs bank actual hcode hT hQ hD hA hC hP


theorem gateSweep_filter {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool) (j d:ℕ):
 (gateSweep p enabled j).filter (fun s=>decide (UniformDAGLayers.natLevel p s.dst=d))=
 if UniformDAGBucketMachine.typedDepth p j=d then gateSweep p enabled j else []:=by
 by_cases h:UniformDAGBucketMachine.typedDepth p j=d
 · rw[ite_eq_left h]
   apply List.filter_eq_self.mpr
   intro s hs
   rw[gateSweep_dst p enabled j s hs]
   exact decide_eq_true h
 · rw[ite_eq_right h]
   apply List.filter_eq_nil_iff.mpr
   intro s hs
   rw[gateSweep_dst p enabled j s hs]
   intro hh
   exact h (of_decide_eq_true hh)

theorem selected_gateSweeps {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool) (d:ℕ) (js:List ℕ):
 (js.filter (fun j=>decide (UniformDAGBucketMachine.typedDepth p j=d))).flatMap (gateSweep p enabled)=
 (js.flatMap (gateSweep p enabled)).filter (fun s=>decide (UniformDAGLayers.natLevel p s.dst=d)):=by
 induction js with
 | nil=>rfl
 | cons j js ih=>
   simp only[List.filter_cons,List.flatMap_cons,List.filter_append,gateSweep_filter]
   by_cases h:UniformDAGBucketMachine.typedDepth p j=d <;> simp[h,ih]

/-- Exact stable depth bucket list of the actual natSweep; every repeated
operand occurrence survives. No action certificate or shear sorting oracle. -/
theorem orderedSweep_buckets {r n t:ℕ} (p:UniformReplayPrint.Program r n t) (enabled:Bool):
 orderedSweep p enabled=(List.range (t+1)).flatMap (fun d=>
   (UniformDAGLayers.natSweep p enabled).filter (fun s=>decide (UniformDAGLayers.natLevel p s.dst=d))):=by
 unfold orderedSweep UniformDAGBucketMachine.order UniformDAGBucketMachine.selected
 rw[List.flatMap_assoc]
 apply List.flatMap_congr
 intro d _
 rw[selected_gateSweeps,gateSweep_all]

/-- A coarse ordinary-address envelope; the runtime and every intermediate
word are bounded under the same caller-supplied ambient B. -/
def wordBudget (M G T Q D A C P n N:ℕ):ℕ:=60+T+5*G+Q+M+D+6*M+A+n+1+G+C+7*N+P+2

theorem wordBudget_bounds (M G T Q D A C P n N B:ℕ) (h:wordBudget M G T Q D A C P n N≤B):
 60≤B ∧ T+5*G≤B ∧ Q+M≤B ∧ D+6*M≤B ∧ A+n+1+G≤B ∧ C+7*N≤B ∧ P+2≤B:=by
 unfold wordBudget at h;omega

end
end ExactFourierCircuits.UniformCrossShearTableMachine
