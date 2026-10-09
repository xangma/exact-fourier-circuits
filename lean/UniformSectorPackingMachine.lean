import UniformSectorPacking
import UniformTensorMonomialMachine

/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.1, prefix traversal (4.1), PDF p. 18; §4.2, Lemma 4.1 and (4.2)–(4.3), p. 19 (`eq:prefix-nodes`, `lem:sector-address`, `eq:sector-updates`).

The literal program computes suffix products, performs the fixed-state DFS,
writes the inverse-address bank and gathers actual scalar values. Stack fields,
registers and exact instruction constants are implementation bookkeeping;
`execution` charges preparation, traversal, movement and the halt.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPackingMachine
open UniformMachine UniformTraversal UniformSectorPacking
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)

/-- Flat local digits use the FORWARD local permutation. Physical enumeration
runs block-position digits in their native block order and writes carried
start+offset addresses; output stores need not be sector-contiguous. -/
def flatDigit (a:Axis) (tail:List Axis) (j:Fin a.widths.sum) : PackingDigit :=
 let p:=(blockEquiv a.widths).symm j
 blockDigit a.widths p.1 p.2 (radices tail).prod a.originalPermutation

def flatLayers : List Axis → List (Layer PackingState)
 | []=>
   []
 | a::as=>
   ⟨a.widths.sum,fun j s=> packingStep (flatDigit a as j) s⟩::flatLayers as

def flatCodec : (as:List Axis) → LocalDigits as ≃ Choices (flatLayers as)
 | []=>
   Equiv.refl _
 | a::as=>
   Equiv.prodCongr (blockEquiv a.widths) (flatCodec as)

theorem flatLayers_radices (as:List Axis) : UniformTraversal.radices (flatLayers as)=radices as := by
 induction as with
 | nil=>
   rfl
 | cons a as ih=>
   exact congrArg (List.cons a.widths.sum) ih

theorem flatDigit_encode (a:Axis) (tail:List Axis) (p:BlockPosition a.widths) :
 flatDigit a tail (blockEquiv a.widths p)=blockDigit a.widths p.1 p.2 (radices tail).prod a.originalPermutation := by
 dsimp only [flatDigit]
 rw [(blockEquiv a.widths).symm_apply_apply p]

theorem follow_flat (as:List Axis) (ds:LocalDigits as) (s:PackingState) :
 follow (flatLayers as) (flatCodec as ds) s=packingFollow (packingDigits as (separate as ds)) s := by
 induction as generalizing s with
 | nil=>
   rfl
 | cons a as ih=>
   rcases ds with ⟨p,ds⟩
   change follow (flatLayers as) (flatCodec as ds) (packingStep (flatDigit a as (blockEquiv a.widths p)) s)=_
   rw [flatDigit_encode,ih]
   rfl

/-- This identifies actual physical source and target ordinals, without any
supplied whole packing permutation or operator-action certificate. -/
theorem flat_action (as:List Axis) (ds:LocalDigits as) :
 let s:=follow (flatLayers as) (flatCodec as ds) initialPacking
 s.original=(originalEquiv as (separate as ds)).val ∧ s.start+s.offset=(packedEquiv as (separate as ds)).val := by
 rw [follow_flat]
 obtain ⟨original,target,_⟩:=packingFollow_permutation as (separate as ds)
 exact ⟨original,target.trans (congrArg Fin.val (packingPermutation_original as _))⟩

theorem flat_action_packArray {α:Type*} (as:List Axis) (ds:LocalDigits as)
 (x:Fin (radices as).prod → α) :
 packArray as x (packedEquiv as (separate as ds))=x (originalEquiv as (separate as ds)) := by
 unfold packArray unpackingPermutation packingPermutation
 rw [Equiv.symm_trans_apply,Equiv.symm_apply_apply,Equiv.symm_symm]

/-- Each axis's true radix is at least2. Thus the whole one-pass radix DFS
visits fewer than2L nodes, including empty axes/L=1. -/
theorem flat_visit_bound (as:List Axis) (s:PackingState) :
 (run (flatLayers as) s).visits < 2*(radices as).prod := by
 rw [run_visits,flatLayers_radices]
 apply nodeCount_lt_twice_product
 intro r hr
 obtain ⟨a,_,rfl⟩:=List.mem_map.mp hr
 exact a.radix_two

/-- Cursor identity for a real physical block and role. No repeated prefix
scan is performed by the machine: preceding width is carried in the cursor. -/
theorem flat_digit_fields (a:Axis) (as:List Axis) (b:Fin a.widths.length) (t:Fin (a.widths.get b)) :
 let j:=blockEncode a.widths ⟨b,t⟩
 let d:=flatDigit a as j
 j.val=blockBefore a.widths b+t.val ∧ d.radix=a.widths.sum ∧ d.suffix=(radices as).prod ∧ d.preceding=blockBefore a.widths b ∧ d.blockWidth=a.widths.get b ∧ d.position=t.val ∧ d.originalDigit=(a.originalPermutation j).val := by
 dsimp only
 rw [show blockEncode a.widths ⟨b,t⟩=blockEquiv a.widths ⟨b,t⟩ from rfl,flatDigit_encode]
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


/-- Physical block cursor successor: a width1/2 role step either remains
inside the current block or advances the preceding-width sum exactly once. -/
theorem cursor_next_block (a:Axis) (b:Fin a.widths.length) (t:Fin (a.widths.get b))
 (hnext:blockBefore a.widths b+t.val+1 < a.widths.sum)
 (hend:¬t.val+1 < a.widths.get b) :
 b.val+1 < a.widths.length ∧ (a.widths.take (b.val+1)).sum=blockBefore a.widths b+a.widths.get b := by
 have ht:t.val+1=a.widths.get b:=by have h:=t.isLt;omega
 have sums:(a.widths.take (b.val+1)).sum=blockBefore a.widths b+a.widths.get b:=by
   simpa only [blockBefore,List.get_eq_getElem] using List.sum_take_succ a.widths b.val b.isLt
 refine ⟨?_,sums⟩
 by_contra hn
 have endIndex:b.val+1=a.widths.length:=by have h:=b.isLt;omega
 rw [endIndex,List.take_length] at sums
 omega

def suffixBoot : List Op := [.literal 606 0,.literal 607 1,.literal 608 2,
 .literal 609 4,.literal 610 9,.add 611 600 606,.literal 613 1,
 .add 617 602 611,.putNat 617 613]
def suffixBody : List Op := [.sub 611 611 607,.mul 618 611 609,
 .add 617 601 618,.add 617 617 608,.getNat 622 617,
 .mul 613 613 622,.add 617 602 611,.putNat 617 613]
def treeBoot : List Op := [.literal 612 0,.literal 613 1,.literal 614 0,.literal 615 0,.literal 616 0]
def enterBlock : List Op := [.mul 618 611 609,.add 617 601 618,
 .getNat 620 617,.add 617 617 607,.getNat 621 617,.add 617 617 607,
 .getNat 622 617,.add 617 617 607,.getNat 623 617,
 .add 617 602 611,.add 617 617 607,.getNat 624 617,
 .literal 625 0,.literal 626 0,.literal 627 0,.literal 628 0,
 .add 617 621 606,.getNat 629 617]
def childSave : List Op := [.add 617 623 625,.getNat 630 617,
 .mul 619 611 610,.add 619 603 619,.add 617 619 606,.putNat 617 612,
 .add 617 617 607,.putNat 617 613,.add 617 617 607,.putNat 617 614,
 .add 617 617 607,.putNat 617 615,
 .add 617 617 607,.add 618 625 607,.putNat 617 618,
 .add 617 617 607,.putNat 617 626,.add 617 617 607,.putNat 617 627,
 .add 617 617 607,.add 618 628 607,.putNat 617 618,
 .add 617 617 607,.putNat 617 629]
def childStep : List Op := [.mul 618 613 627,.mul 618 618 624,.add 612 612 618,
 .mul 613 613 629,.mul 614 614 629,.add 614 614 628,
 .mul 615 615 622,.add 615 615 630,.add 611 611 607]
def childBlock : List Op := childSave++childStep
def leafBlock : List Op := [.add 617 612 614,.add 617 637 617,.putNat 617 615,.add 616 616 607]
def popSaved : List Op := [.sub 611 611 607,.mul 619 611 610,.add 619 603 619,
 .add 617 619 606,.getNat 612 617,.add 617 617 607,.getNat 613 617,
 .add 617 617 607,.getNat 614 617,.add 617 617 607,.getNat 615 617,
 .add 617 617 607,.getNat 625 617,.add 617 617 607,.getNat 626 617,
 .add 617 617 607,.getNat 627 617,.add 617 617 607,.getNat 628 617,
 .add 617 617 607,.getNat 629 617]
def popRow : List Op := [.mul 618 611 609,.add 617 601 618,.getNat 620 617,
 .add 617 617 607,.getNat 621 617,.add 617 617 607,.getNat 622 617,
 .add 617 617 607,.getNat 623 617,
 .add 617 602 611,.add 617 617 607,.getNat 624 617]
def popBlock : List Op := popSaved++popRow
def advanceBlock : List Op := [.literal 628 0,.add 626 626 607,.add 627 627 629,
 .add 617 621 626,.getNat 629 617]
def gatherBlock : List Op := [.add 617 637 611,.getNat 630 617,
 .add 617 604 630,.getScalar 70 617,.add 617 605 611,.putScalar 617 70,.add 611 611 607]

/-- Nat600 axes,601 four-word axis rows(count,widthBase,radix,forwardPermBase),
602 fresh suffix,603 fresh nine-word stack,604 scalar source,605 scalar output,
637 fresh inverse-address bank. The full program computes the inverse bank and
then gathers actual Scalar records, retaining their exact dependency flags. -/
def program : Program := List.flatten [suffixBoot.map Op.code,[.branchLT 606 611 10 19],
 suffixBody.map Op.code,[.jump 9],treeBoot.map Op.code,
 [.branchLT 611 600 25 78],enterBlock.map Op.code,[.branchLT 625 622 44 83],
 childBlock.map Op.code,[.jump 24],leafBlock.map Op.code,[.jump 83],
 [.branchLT 606 611 84 125],popBlock.map Op.code,
 [.branchLT 625 622 118 43,.branchLT 628 629 43 119],advanceBlock.map Op.code,
 [.jump 43,.jump 126,.natLiteral 611 0,.branchLT 611 616 128 136],
 gatherBlock.map Op.code,[.jump 127,.halt]]

theorem suffixBoot_length : suffixBoot.length=9 := rfl
theorem suffixBody_length : suffixBody.length=8 := rfl
theorem treeBoot_length : treeBoot.length=5 := rfl
theorem enter_length : enterBlock.length=18 := rfl
theorem child_length : childBlock.length=33 := rfl
theorem leaf_length : leafBlock.length=4 := rfl
theorem pop_length : popBlock.length=33 := rfl
theorem advance_length : advanceBlock.length=5 := rfl
theorem gather_length : gatherBlock.length=7 := rfl
theorem program_length : program.length=137 := by
 simp only [program,List.length_flatten,List.map_cons,List.map_nil,List.length_map,
   suffixBoot_length,suffixBody_length,treeBoot_length,enter_length,child_length,
   leaf_length,pop_length,advance_length,gather_length,List.length_cons,List.length_nil,
   List.sum_cons,List.sum_nil]
 decide


theorem suffixBoot_code : BlockAt suffixBoot program 0 := by
 intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem suffixBody_code : BlockAt suffixBody program 10 := by
 intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem treeBoot_code : BlockAt treeBoot program 19 := by
 intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem enter_code : BlockAt enterBlock program 25 := by
 intro i hi;change i < 18 at hi;interval_cases i <;> rfl
theorem child_code : BlockAt childBlock program 44 := by
 intro i hi;change i < 33 at hi;interval_cases i <;> rfl
theorem leaf_code : BlockAt leafBlock program 78 := by
 intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem pop_code : BlockAt popBlock program 84 := by
 intro i hi;change i < 33 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advanceBlock program 119 := by
 intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem gather_code : BlockAt gatherBlock program 128 := by
 intro i hi;change i < 7 at hi;interval_cases i <;> rfl


noncomputable section

def suffixInitialized (s:State) : State:=applyBlock suffixBoot s
def suffixIteration (s:State) : State:=setPC (applyBlock suffixBody (setPC s 10)) 9
def initialized (s:State) : State:=applyBlock treeBoot (setPC s 19)
def entered (s:State) : State:=applyBlock enterBlock (setPC s 25)
def child (s:State) : State:=setPC (applyBlock childBlock (setPC s 44)) 24
def leaf (s:State) : State:=setPC (applyBlock leafBlock (setPC s 78)) 83
def popped (s:State) : State:=applyBlock popBlock (setPC s 84)

structure PhysicalAxis where
 geometry:Axis
 widthsBase:ℕ
 permutationBase:ℕ
abbrev physicalAxes (as:List PhysicalAxis):=as.map PhysicalAxis.geometry
abbrev physicalVolume (as:List PhysicalAxis):=(radices (physicalAxes as)).prod

def Rows (as:List PhysicalAxis) (depth base:ℕ) (s:State):Prop:=match as with
 | []=>
   True
 | a::tail=>
   s.natHeap (base+4*depth)=some a.geometry.widths.length ∧ s.natHeap (base+4*depth+1)=some a.widthsBase ∧ s.natHeap (base+4*depth+2)=some a.geometry.widths.sum ∧ s.natHeap (base+4*depth+3)=some a.permutationBase ∧ Rows tail (depth+1) base s

def Widths (as:List PhysicalAxis) (s:State):Prop:=
 ∀a∈as,∀j:Fin a.geometry.widths.length,s.natHeap (a.widthsBase+j.val)=some (a.geometry.widths.get j)
def Permutations (as:List PhysicalAxis) (s:State):Prop:=
 ∀a∈as,∀j:Fin a.geometry.widths.sum,s.natHeap (a.permutationBase+j.val)=some (a.geometry.originalPermutation j).val

structure Layout where
 ell:ℕ
 rows:ℕ
 suffix:ℕ
 stack:ℕ
 inverse:ℕ
 source:ℕ
 destination:ℕ
 total:ℕ
 B:ℕ
 code:137 ≤ B
 rowsBelow:rows+4*ell ≤ suffix
 suffixBelow:suffix+ell+1 ≤ stack
 stackBelow:stack+9*ell ≤ inverse
 inverseBound:inverse+total ≤ B
 sourceBelow:source+total ≤ destination
 destinationBound:destination+total ≤ B
 volumeBound:total ≤ B
structure Header (L:Layout) (s:State):Prop where
 count:s.natReg 600=L.ell
 rows:s.natReg 601=L.rows
 suffix:s.natReg 602=L.suffix
 stack:s.natReg 603=L.stack
 inverse:s.natReg 637=L.inverse
 source:s.natReg 604=L.source
 destination:s.natReg 605=L.destination

def Frame (s t:State):Prop:=t.scalarHeap=s.scalarHeap ∧ t.scalarReg=s.scalarReg ∧ t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧ ∀j,j < 606 ∨ 650 ≤ j ∨ j=637 → t.natReg j=s.natReg j

def Constants (s:State):Prop:=s.natReg 606=0 ∧ s.natReg 607=1 ∧ s.natReg 608=2 ∧ s.natReg 609=4 ∧ s.natReg 610=9

theorem suffix_branch : program[9]?=some (.branchLT 606 611 10 19):=rfl
theorem suffix_jump : program[18]?=some (.jump 9):=rfl

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun i hi=> (h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩
theorem Header.transport (L:Layout) (s t:State) (h:Header L s) (hf:Frame s t):Header L t:=
 ⟨(hf.2.2.2.2 600 (by omega)).trans h.count,(hf.2.2.2.2 601 (by omega)).trans h.rows,
 (hf.2.2.2.2 602 (by omega)).trans h.suffix,(hf.2.2.2.2 603 (by omega)).trans h.stack,
 (hf.2.2.2.2 637 (by simp)).trans h.inverse,(hf.2.2.2.2 604 (by omega)).trans h.source,
 (hf.2.2.2.2 605 (by omega)).trans h.destination⟩

/-- The range test concerns literal register destinations, not run-time data. -/
def NatWithin (lo : ℕ) : Op → Prop
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _ =>
   lo ≤ d ∧ d < 650 ∧ d ≠ 637
 | .putNat _ _ =>
   True
 | _ =>
   False
instance natWithinDecidable (lo : ℕ) (o : Op) : Decidable (NatWithin lo o) := by
 cases o <;> unfold NatWithin <;> infer_instance

def RangeFrame (lo : ℕ) (s t : State) : Prop := t.scalarHeap=s.scalarHeap ∧ t.scalarReg=s.scalarReg ∧ t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧ ∀j,j < lo ∨ 650 ≤ j ∨ j=637 → t.natReg j=s.natReg j

theorem RangeFrame.trans {lo : ℕ} {s u v : State} (h:RangeFrame lo s u) (h':RangeFrame lo u v) : RangeFrame lo s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun i hi=> (h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩
theorem RangeFrame.frame {lo : ℕ} {s t : State} (h:RangeFrame lo s t) (hl:606 ≤ lo) : Frame s t :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i hi=> h.2.2.2.2 i (by rcases hi with h|h <;> omega)⟩
theorem nat_op_frame (lo : ℕ) (o : Op) (s : State) (h:NatWithin lo o) : RangeFrame lo s (o.apply s) := by
 cases o <;> simp only [NatWithin] at h
 all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
 all_goals intro i hi
 all_goals first | rfl | (simp only [Op.apply,writeNat,next];rw [Function.update_of_ne (by omega)])

theorem block_frame (lo : ℕ) (b : List Op) (s : State) (h:∀o∈b,NatWithin lo o) :
 RangeFrame lo s (applyBlock b s) := by
 induction b generalizing s with
 | nil =>
   exact ⟨rfl,rfl,rfl,rfl,fun _ _=> rfl⟩
 | cons o b ih =>
   exact (nat_op_frame lo o s (h o (by simp))).trans
     (ih (o.apply s) (fun t ht=> h t (by simp [ht])))

theorem blocks_frame (s : State) :
 Frame s (suffixInitialized s) ∧ Frame s (suffixIteration s) ∧ Frame s (initialized s) ∧ Frame s (entered s) ∧ Frame s (child s) ∧ Frame s (leaf s) ∧ Frame s (popped s) := by
 have boot:=block_frame 606 suffixBoot s (by decide)
 have sb:=block_frame 606 suffixBody (setPC s 10) (by decide)
 have tb:=block_frame 606 treeBoot (setPC s 19) (by decide)
 have ent:=block_frame 606 enterBlock (setPC s 25) (by decide)
 have ch:=block_frame 606 childBlock (setPC s 44) (by decide)
 have lf:=block_frame 606 leafBlock (setPC s 78) (by decide)
 have pp:=block_frame 606 popBlock (setPC s 84) (by decide)
 exact ⟨boot,sb,tb,ent,ch,lf,pp⟩

theorem body_constants (b : List Op) (s : State) (h:Constants s)
 (hb:∀o∈b,NatWithin 611 o) : Constants (applyBlock b s) := by
 have f:=block_frame 611 b s hb
 exact ⟨(f.2.2.2.2 606 (by omega)).trans h.1,(f.2.2.2.2 607 (by omega)).trans h.2.1,
   (f.2.2.2.2 608 (by omega)).trans h.2.2.1,(f.2.2.2.2 609 (by omega)).trans h.2.2.2.1,
   (f.2.2.2.2 610 (by omega)).trans h.2.2.2.2⟩



theorem rows_get (as : List PhysicalAxis) (d b : ℕ) (s : State) (h:Rows as d b s)
 (i : Fin as.length) :
 s.natHeap (b+4*(d+i.val))=some (as.get i).geometry.widths.length ∧ s.natHeap (b+4*(d+i.val)+1)=some (as.get i).widthsBase ∧ s.natHeap (b+4*(d+i.val)+2)=some (as.get i).geometry.widths.sum := by
 induction as generalizing d with
 | nil =>
   exact Fin.elim0 i
 | cons a tail ih =>
   refine Fin.cases ?_ (fun j=> ?_) i
   · exact ⟨h.1,h.2.1,h.2.2.1⟩
   · simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ,show d+(j.val+1)=(d+1)+j.val by omega]
       using ih (d+1) h.2.2.2.2 j

theorem physicalVolume_nil : physicalVolume []=1 := rfl
theorem physicalVolume_cons (a : PhysicalAxis) (as : List PhysicalAxis) :
 physicalVolume (a::as)=a.geometry.widths.sum*physicalVolume as := rfl

theorem physicalVolume_pos (as : List PhysicalAxis) : 0 < physicalVolume as := by
 induction as with
 | nil =>
   decide
 | cons a as ih =>
   rw [physicalVolume_cons]
   exact Nat.mul_pos (by have h:=a.geometry.radix_two;omega) ih

theorem physicalVolume_tail_le (a : PhysicalAxis) (as : List PhysicalAxis) : physicalVolume as ≤ physicalVolume (a::as) := by
 rw [physicalVolume_cons]
 have h:=a.geometry.radix_two
 exact (show physicalVolume as=1*physicalVolume as by simp).le.trans (Nat.mul_le_mul_right _ (by omega))

theorem physicalVolume_drop_le (as : List PhysicalAxis) (i : ℕ) : physicalVolume (as.drop i) ≤ physicalVolume as := by
 induction as generalizing i with
 | nil =>
   simp only [List.drop_nil];rfl
 | cons a as ih =>
   cases i with
   | zero =>
     rfl
   | succ i =>
     exact (ih i).trans (physicalVolume_tail_le a as)

theorem physicalVolume_drop_step (as : List PhysicalAxis) (i : Fin as.length) :
 physicalVolume (as.drop i.val)=(as.get i).geometry.widths.sum*physicalVolume (as.drop (i.val+1)) := by
 induction as with
 | nil =>
   exact Fin.elim0 i
 | cons a as ih =>
   refine Fin.cases ?_ (fun j=> ?_) i
   · rfl
   · exact ih j

theorem axis_count_bound (as : List PhysicalAxis) : as.length+1 ≤ physicalVolume as := by
 induction as with
 | nil =>
   decide
 | cons a as ih =>
   rw [List.length_cons,physicalVolume_cons]
   have h:=a.geometry.radix_two
   have hp:=physicalVolume_pos as
   nlinarith

def WrittenSuffix (as : List PhysicalAxis) (L : Layout) (firstIndex : ℕ) (s : State) : Prop :=
 ∀j,firstIndex ≤ j → j ≤ as.length → s.natHeap (L.suffix+j)=some (physicalVolume (as.drop j))
def Outside (base len : ℕ) (s t : State) : Prop :=
 ∀i,i < base ∨ base+len ≤ i → t.natHeap i=s.natHeap i

theorem Outside.trans {base len : ℕ} {s u v : State} (h:Outside base len s u)
 (h':Outside base len u v) : Outside base len s v :=fun i hi=> (h' i hi).trans (h i hi)

theorem rows_transfer (as : List PhysicalAxis) (depth : ℕ) (L : Layout) (s t : State)
 (hlen:depth+as.length ≤ L.ell) (h:Rows as depth L.rows s)
 (hf:∀i,i < L.suffix → t.natHeap i=s.natHeap i) : Rows as depth L.rows t := by
 induction as generalizing depth with
 | nil =>
   trivial
 | cons a as ih =>
   have hd:depth < L.ell:=by simp only [List.length_cons] at hlen;omega
   have hr:L.rows+4*depth+2 < L.suffix:=by have hb:=L.rowsBelow;omega
   refine ⟨?_,?_,?_,?_,ih (depth+1) (by simp only [List.length_cons] at hlen;omega) h.2.2.2.2⟩
   · rw [hf _ (by omega)];exact h.1
   · rw [hf _ (by omega)];exact h.2.1
   · rw [hf _ hr];exact h.2.2.1
   · rw [hf _ (by have h:=L.rowsBelow;omega)];exact h.2.2.2.1

theorem widths_transfer (as : List PhysicalAxis) (L : Layout) (s t : State) (h:Widths as s)
 (hb:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ L.suffix)
 (hf:∀i,i < L.suffix → t.natHeap i=s.natHeap i) : Widths as t := by
 intro a ha j
 rw [hf _ (by have h:=hb a ha;have h':=j.isLt;omega)]
 exact h a ha j

/-- One reverse scan step reads only the actual radix row and writes the
computed earlier suffix. Every intermediate integer uses the ambient bound. -/
theorem suffix_step (as : List PhysicalAxis) (L : Layout) (n i : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hphysicalVolume:physicalVolume as=L.total) (hi:i < as.length)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 611=i+1)
 (hp:s.natReg 613=physicalVolume (as.drop (i+1))) (hr:Rows as 0 L.rows s)
 (hpc:s.pc=9) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 10 (suffixIteration s) ∧ (suffixIteration s).natReg 611=i ∧ (suffixIteration s).natReg 613=physicalVolume (as.drop i) ∧ (suffixIteration s).natHeap=Function.update s.natHeap (L.suffix+i) (some (physicalVolume (as.drop i))) ∧ Constants (suffixIteration s) ∧ Header L (suffixIteration s) ∧ Frame s (suffixIteration s) := by
 let a:=as.get ⟨i,hi⟩
 have row:s.natHeap (L.rows+4*i+2)=some a.geometry.widths.sum:=by
   simpa only [Nat.zero_add] using (rows_get as 0 L.rows s hr ⟨i,hi⟩).2.2
 have row':s.natHeap (L.rows+(i*4+2))=some a.geometry.widths.sum:=by
   simpa only [Nat.mul_comm,Nat.add_assoc] using row
 have hRadixB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ row).2
 have hnew:=physicalVolume_drop_step as ⟨i,hi⟩
 have hnewB:physicalVolume (as.drop i) ≤ L.B:=(physicalVolume_drop_le as i).trans (by rw [hphysicalVolume];exact L.volumeBound)
 have hrowB:L.rows+4*i+2 ≤ L.B:=by
   have h0:=L.rowsBelow;have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
 have hdstB:L.suffix+i ≤ L.B:=by
   have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
 have hprod:physicalVolume (as.drop (i+1))*a.geometry.widths.sum=physicalVolume (as.drop i):=by
   rw [hnew];exact Nat.mul_comm _ _
 let e:=setPC s 10
 have eb:WordBound L.B e:=changePC_bound L.B s 10 hs (by have h:=L.code;omega)
 have body:=block_runs suffixBody program 10 n L.B x e suffixBody_code rfl eb
   (by have h:=L.code;rw [suffixBody_length];omega)
   (by simp [readable,suffixBody,Op.readable,Op.apply,e,setPC,writeNat,next,
     hc.2.1,hc.2.2.1,hc.2.2.2.1,hh.rows,hd,row',Nat.add_assoc])
   (by simp [peak,suffixBody,Op.peak,Op.apply,e,setPC,writeNat,next,
     hc.2.1,hc.2.2.1,hc.2.2.2.1,hh.rows,hh.suffix,hd,hp,row',hprod,Nat.add_assoc]
       have h:=L.code
       omega)
 have bp:(applyBlock suffixBody e).pc=18:=by rw [applyBlock_pc,suffixBody_length];rfl
 have j:BoundedRuns program n x L.B (applyBlock suffixBody e) 1 (suffixIteration s):=
   .next body.final_bound (by rw [step,bp,suffix_jump];rfl)
   (.refl (changePC_bound L.B _ 9 body.final_bound (by have h:=L.code;omega)))
 have first:BoundedRuns program n x L.B s 1 e:=.next hs
   (by simp [step,hpc,suffix_branch,hc.1,hd,e,setPC]) (.refl eb)
 refine ⟨by simpa only [suffixBody_length] using first.trans (body.trans j),?_,?_,?_,?_,?_,?_⟩
 · simp [suffixIteration,setPC,applyBlock,suffixBody,Op.apply,writeNat,next,hc.2.1,hd]
 · simp [suffixIteration,setPC,applyBlock,suffixBody,Op.apply,writeNat,next,
     hc.2.1,hc.2.2.1,hc.2.2.2.1,hh.rows,hd,hp,row',hprod,Nat.add_assoc]
 · simp [suffixIteration,setPC,applyBlock,suffixBody,Op.apply,writeNat,next,
     hc.2.1,hc.2.2.1,hc.2.2.2.1,hh.rows,hh.suffix,hd,hp,row',hprod,Nat.add_assoc]
 · exact body_constants suffixBody (setPC s 10) hc (by decide)
 · exact hh.transport L s _ (blocks_frame s).2.1
 · exact (blocks_frame s).2.1



theorem suffix_step_written (as : List PhysicalAxis) (L : Layout) (i : ℕ) (s t : State)
 (_hi:i < as.length) (h:WrittenSuffix as L (i+1) s)
 (he:t.natHeap=Function.update s.natHeap (L.suffix+i) (some (physicalVolume (as.drop i)))) :
 WrittenSuffix as L i t := by
 intro j hj hj'
 rw [he]
 by_cases hji:j=i
 · subst j;simp
 · rw [Function.update_of_ne (by omega)]
   exact h j (by omega) hj'

theorem suffix_step_outside (as : List PhysicalAxis) (L : Layout) (i : ℕ) (s t : State)
 (hi:i < as.length) (hlen:as.length=L.ell)
 (he:t.natHeap=Function.update s.natHeap (L.suffix+i) (some (physicalVolume (as.drop i)))) :
 Outside L.suffix (L.ell+1) s t := by
 intro j hj
 rw [he,Function.update_of_ne (by omega)]

theorem suffix_loop (as : List PhysicalAxis) (L : Layout) (n i : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hphysicalVolume:physicalVolume as=L.total) (hi:i ≤ as.length)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 611=i)
 (hp:s.natReg 613=physicalVolume (as.drop i)) (hr:Rows as 0 L.rows s)
 (hw:WrittenSuffix as L i s) (hpc:s.pc=9) (hs:WordBound L.B s) : ∃t,
 BoundedRuns program n x L.B s (10*i) t ∧ WrittenSuffix as L 0 t ∧ t.natReg 611=0 ∧ t.natReg 613=physicalVolume as ∧ t.pc=9 ∧ Constants t ∧ Header L t ∧ Outside L.suffix (L.ell+1) s t ∧ Frame s t := by
 induction i generalizing s with
 | zero =>
   exact ⟨s,.refl hs,hw,hd,hp,hpc,hc,hh,fun _ _=> rfl,⟨rfl,rfl,rfl,rfl,fun _ _=> rfl⟩⟩
 | succ i ih =>
   obtain ⟨run,td,tp,th,tc,tH,tf⟩:=suffix_step as L n i x s hlen hphysicalVolume (by omega)
     hh hc hd hp hr hpc hs
   have outside:=suffix_step_outside as L i s (suffixIteration s) (by omega) hlen th
   have tables:Rows as 0 L.rows (suffixIteration s):=rows_transfer as 0 L s _ (by omega) hr
     (fun j hj=> outside j (Or.inl hj))
   have written:=suffix_step_written as L i s (suffixIteration s) (by omega) hw th
   have pc:(suffixIteration s).pc=9:=rfl
   obtain ⟨u,ur,uw,ud,up,uc,ucs,uh,uo,uf⟩:=ih (suffixIteration s) (by omega)
     tH tc td tp tables written pc run.final_bound
   refine ⟨u,?_,uw,ud,up,uc,ucs,uh,outside.trans uo,tf.trans uf⟩
   convert run.trans ur using 1
   omega

theorem suffix_boot (as : List PhysicalAxis) (L : Layout) (n : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hh:Header L s) (hpc:s.pc=0) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 9 (suffixInitialized s) ∧ WrittenSuffix as L as.length (suffixInitialized s) ∧ Constants (suffixInitialized s) ∧ Header L (suffixInitialized s) ∧ (suffixInitialized s).natReg 611=as.length ∧ (suffixInitialized s).natReg 613=physicalVolume (as.drop as.length) ∧ Outside L.suffix (L.ell+1) s (suffixInitialized s) := by
 have hadd:L.suffix+L.ell ≤ L.B:=by
   have a:=L.suffixBelow;have b:=L.stackBelow;have c:=L.inverseBound;omega
 have hell:L.ell ≤ L.B:=by omega
 have hheap:(suffixInitialized s).natHeap=Function.update s.natHeap (L.suffix+L.ell) (some 1):=by
   simp [suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next,hh.count,hh.suffix]
 have run:=block_runs suffixBoot program 0 n L.B x s suffixBoot_code hpc hs
   (by have h:=L.code;rw [suffixBoot_length];omega)
   (by simp [readable,suffixBoot,Op.readable])
   (by simp [peak,suffixBoot,Op.peak,Op.apply,writeNat,next,hh.count,hh.suffix]
       have h:=L.code;omega)
 refine ⟨run,?_,?_,hh.transport L s _ (blocks_frame s).1,?_,?_,?_⟩
 · intro j hj hj'
   have he:j=as.length:=by omega
   subst j
   rw [hheap,hlen]
   simp [←hlen,List.drop_length,physicalVolume_nil]
 · simp [Constants,suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next]
 · simp [suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next,hh.count,hlen]
 · simp [suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next,List.drop_length,physicalVolume_nil]
 · intro j hj
   rw [hheap,Function.update_of_ne (by omega)]

/-- Computed suffixes are not an entry contract. The literal reverse scan
establishes all of them from the original physical axis radix rows. -/
theorem suffix_preparation (as : List PhysicalAxis) (L : Layout) (n : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hphysicalVolume:physicalVolume as=L.total)
 (hh:Header L s) (hr:Rows as 0 L.rows s) (hpc:s.pc=0) (hs:WordBound L.B s) : ∃t,
 BoundedRuns program n x L.B s (10*L.ell+9) t ∧ WrittenSuffix as L 0 t ∧ t.natReg 611=0 ∧ t.natReg 613=physicalVolume as ∧ t.pc=9 ∧ Constants t ∧ Header L t ∧ Outside L.suffix (L.ell+1) s t ∧ Frame s t := by
 obtain ⟨boot,bw,bc,bh,bd,bp,bo⟩:=suffix_boot as L n x s hlen hh hpc hs
 have br:Rows as 0 L.rows (suffixInitialized s):=rows_transfer as 0 L s _ (by omega) hr
   (fun j hj=> bo j (Or.inl hj))
 have bpc:(suffixInitialized s).pc=9:=by rw [suffixInitialized,applyBlock_pc,suffixBoot_length,hpc]
 obtain ⟨t,run,tw,td,tp,tpc,tc,th,tOutside,tf⟩:=suffix_loop as L n as.length x
   (suffixInitialized s) hlen hphysicalVolume (by omega) bh bc bd bp br bw bpc boot.final_bound
 refine ⟨t,?_,tw,td,tp,tpc,tc,th,bo.trans tOutside,(blocks_frame s).1.trans tf⟩
 convert boot.trans run using 1
 omega





/-- The complete target-address computation used by the physical prefix state. -/
def target (as:List Axis) (st:PackingState) (ds:LocalDigits as):ℕ:=
 (follow (flatLayers as) (flatCodec as ds) st).start+
 (follow (flatLayers as) (flatCodec as ds) st).offset

theorem target_cons (a:Axis) (as:List Axis) (st:PackingState) (p:BlockPosition a.widths) (ds:LocalDigits as):
 target (a::as) st (p,ds)=target as
   (packingStep (blockDigit a.widths p.1 p.2 (radices as).prod a.originalPermutation) st) ds := by
 unfold target
 change (follow (flatLayers as) (flatCodec as ds) (packingStep (flatDigit a as (blockEquiv a.widths p)) st)).start+
   (follow (flatLayers as) (flatCodec as ds) (packingStep (flatDigit a as (blockEquiv a.widths p)) st)).offset=_
 rw [flatDigit_encode]

theorem target_bounds (as:List Axis) (st:PackingState) (ds:LocalDigits as) (ho:st.offset < st.width):
 st.start ≤ target as st ds ∧ target as st ds < st.start+st.width*(radices as).prod := by
 obtain ⟨hS,_,ho',_⟩:=packingFollow_formulas (packingDigits as (separate as ds)) st
 have fit:=sector_fits _ (packingDigits_valid as (separate as ds))
 have pos:=withinAddress_bound _ (packingDigits_valid as (separate as ds))
 have prod:digitProduct (packingDigits as (separate as ds))=(radices as).prod:=
   (packingDigits_products as (separate as ds)).1
 rw [target,follow_flat,hS,ho']
 refine ⟨by omega,?_⟩
 calc
  st.start+st.width*startContribution (packingDigits as (separate as ds))+
      (st.offset*blockProduct (packingDigits as (separate as ds))+withinAddress (packingDigits as (separate as ds))) < st.start+st.width*startContribution (packingDigits as (separate as ds))+
       ((st.offset+1)*blockProduct (packingDigits as (separate as ds))):=by nlinarith
  _ ≤ st.start+st.width*(startContribution (packingDigits as (separate as ds))+
       blockProduct (packingDigits as (separate as ds))):=by
    rw [Nat.mul_add]
    have hmul:=Nat.mul_le_mul_right (blockProduct (packingDigits as (separate as ds)))
      (show st.offset+1 ≤ st.width by omega)
    simpa only [Nat.add_assoc] using
      Nat.add_le_add_left hmul (st.start+st.width*startContribution (packingDigits as (separate as ds)))
  _ ≤ st.start+st.width*(radices as).prod:=by
    rw [←prod]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ fit) _

/-- Distinct physical blocks have disjoint native offset intervals. This uses
actual blockEquiv injectivity and does not assume a whole permutation table. -/
theorem block_intervals (ws:List ℕ) (hp:∀q∈ws,0 < q) (b c:Fin ws.length) (hne:b ≠ c):
 blockBefore ws b+ws.get b ≤ blockBefore ws c ∨ blockBefore ws c+ws.get c ≤ blockBefore ws b := by
 by_contra h
 push Not at h
 let j:=max (blockBefore ws b) (blockBefore ws c)
 have hb0:blockBefore ws b ≤ j:=Nat.le_max_left _ _
 have hc0:blockBefore ws c ≤ j:=Nat.le_max_right _ _
 have hbpos:=hp (ws.get b) (List.get_mem _ _)
 have hcpos:=hp (ws.get c) (List.get_mem _ _)
 have hb1:j < blockBefore ws b+ws.get b:=max_lt_iff.mpr ⟨by omega,by omega⟩
 have hc1:j < blockBefore ws c+ws.get c:=max_lt_iff.mpr ⟨by omega,by omega⟩
 let p:BlockPosition ws:=⟨b,⟨j-blockBefore ws b,by omega⟩⟩
 let q:BlockPosition ws:=⟨c,⟨j-blockBefore ws c,by omega⟩⟩
 have eq:(blockEquiv ws) p=(blockEquiv ws) q:=by
   apply Fin.ext
   change blockBefore ws b+(j-blockBefore ws b)=blockBefore ws c+(j-blockBefore ws c)
   omega
 have first:=congrArg Sigma.fst ((blockEquiv ws).injective eq)
 exact hne first

theorem step_interval_le (a:Axis) (as:List Axis) (st u:PackingState)
 (hstart:st.start=u.start) (hwidth:st.width=u.width) (p q:BlockPosition a.widths)
 (hb:blockBefore a.widths p.1+a.widths.get p.1 ≤ blockBefore a.widths q.1):
 let s:=packingStep (blockDigit a.widths p.1 p.2 (radices as).prod a.originalPermutation) st
 let t:=packingStep (blockDigit a.widths q.1 q.2 (radices as).prod a.originalPermutation) u
 s.start+s.width*(radices as).prod ≤ t.start := by
 dsimp only [packingStep,blockDigit]
 calc
  st.start+st.width*blockBefore a.widths p.1*(radices as).prod+
      (st.width*a.widths.get p.1)*(radices as).prod
   =st.start+st.width*((blockBefore a.widths p.1+a.widths.get p.1)*(radices as).prod):=by ring
  _ ≤ st.start+st.width*(blockBefore a.widths q.1*(radices as).prod):=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)) _
  _=u.start+u.width*blockBefore a.widths q.1*(radices as).prod:=by rw [hstart,hwidth];ring

/-- Exact image footprints are essential: role siblings may interleave their
stores across sectors. The complete carried target is injective even with an
arbitrary common incoming start/width and different valid incoming offsets. -/
theorem target_injective (as:List Axis) (st u:PackingState) (ds es:LocalDigits as)
 (hstart:st.start=u.start) (hwidth:st.width=u.width)
 (ho:st.offset < st.width) (hu:u.offset < u.width) (he:target as st ds=target as u es):
 st.offset=u.offset ∧ ds=es := by
 induction as generalizing st u with
 | nil=>
   cases ds;cases es
   refine ⟨?_,rfl⟩
   change st.start+st.offset=u.start+u.offset at he
   omega
 | cons a as ih=>
   rcases ds with ⟨⟨b,t⟩,ds⟩
   rcases es with ⟨⟨c,v⟩,es⟩
   let s:=packingStep (blockDigit a.widths b t (radices as).prod a.originalPermutation) st
   let z:=packingStep (blockDigit a.widths c v (radices as).prod a.originalPermutation) u
   rw [target_cons,target_cons] at he
   have hs:s.offset < s.width:=packingStep_offset_bound _ _ ho t.isLt
   have hz:z.offset < z.width:=packingStep_offset_bound _ _ hu v.isLt
   have sb:=target_bounds as s ds hs
   have zb:=target_bounds as z es hz
   have bc:b=c:=by
     by_contra hne
     rcases block_intervals a.widths
       (fun q hq=> by rcases a.widths_one_two q hq with h|h <;> omega) b c hne with h|h
     · have dis:=step_interval_le a as st u hstart hwidth ⟨b,t⟩ ⟨c,v⟩ h
       change s.start+s.width*(radices as).prod ≤ z.start at dis
       change target as s ds=target as z es at he
       omega
     · have dis:=step_interval_le a as u st hstart.symm hwidth.symm ⟨c,v⟩ ⟨b,t⟩ h
       change z.start+z.width*(radices as).prod ≤ s.start at dis
       change target as s ds=target as z es at he
       omega
   subst c
   obtain ⟨offsets,tails⟩:=ih s z ds es
     (by dsimp[s,z,packingStep,blockDigit];rw[hstart,hwidth])
     (by dsimp[s,z,packingStep,blockDigit];rw[hwidth]) hs hz he
   have values:st.offset=u.offset ∧ t.val=v.val:=by
     have ht:=t.isLt
     have hv:=v.isLt
     change st.offset*a.widths.get b+t.val=u.offset*a.widths.get b+v.val at offsets
     rcases a.widths_one_two (a.widths.get b) (List.get_mem _ _) with h|h <;> simp only [h,Nat.mul_one] at offsets ht hv <;> omega
   have tv:t=v:=Fin.ext values.2
   subst v
   subst es
   exact ⟨values.1,rfl⟩


structure Banks (as:List PhysicalAxis) (depth:ℕ) (L:Layout) (s:State):Prop where
 rows:Rows as depth L.rows s
 widths:Widths as s
 permutations:Permutations as s
 widthBelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ L.suffix
 permutationBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ L.suffix
 suffixes:∀i,i ≤ as.length → s.natHeap (L.suffix+depth+i)=some (physicalVolume (as.drop i))

structure Cursor (depth count:ℕ) (st:PackingState) (s:State):Prop where
 depth:s.natReg 611=depth
 start:s.natReg 612=st.start
 width:s.natReg 613=st.width
 offset:s.natReg 614=st.offset
 original:s.natReg 615=st.original
 count:s.natReg 616=count

def Fits (as:List PhysicalAxis) (st:PackingState) (count:ℕ) (L:Layout):Prop:=
 st.start+st.width*physicalVolume as ≤ L.total ∧ st.offset < st.width ∧ (st.original+1)*physicalVolume as ≤ L.total ∧ count+physicalVolume as ≤ L.total

structure Cache (a:PhysicalAxis) (as:List PhysicalAxis) (s:State):Prop where
 count:s.natReg 620=a.geometry.widths.length
 widths:s.natReg 621=a.widthsBase
 radix:s.natReg 622=a.geometry.widths.sum
 permutation:s.natReg 623=a.permutationBase
 tail:s.natReg 624=physicalVolume as

def Local (a:PhysicalAxis) (j:ℕ) (s:State):Prop:=
 ∃(block:Fin a.geometry.widths.length) (role:Fin (a.geometry.widths.get block)),
 j=blockBefore a.geometry.widths block+role.val ∧ s.natReg 625=j ∧ s.natReg 626=block.val ∧ s.natReg 627=blockBefore a.geometry.widths block ∧ s.natReg 628=role.val ∧ s.natReg 629=a.geometry.widths.get block

/-- Only the generated suffix, stack and inverse-address banks are writable. -/
theorem banks_transfer (as:List PhysicalAxis) (depth:ℕ) (L:Layout) (s t:State)
 (hlen:depth+as.length ≤ L.ell) (h:Banks as depth L s)
 (hf:∀i,i < L.stack → t.natHeap i=s.natHeap i):Banks as depth L t:=by
 have low:∀i,i < L.suffix → t.natHeap i=s.natHeap i:=fun i hi=> hf i (by have h:=L.suffixBelow;omega)
 refine ⟨rows_transfer as depth L s t hlen h.rows low,
   widths_transfer as L s t h.widths h.widthBelow low,?_,h.widthBelow,h.permutationBelow,?_⟩
 · intro a ha j
   rw [low _ (by have h:=h.permutationBelow a ha;have hj:=j.isLt;omega)]
   exact h.permutations a ha j
 · intro i hi
   rw [hf _ (by have h:=L.suffixBelow;omega)]
   exact h.suffixes i hi

theorem banks_tail (a:PhysicalAxis) (as:List PhysicalAxis) (depth:ℕ) (L:Layout) (s:State)
 (h:Banks (a::as) depth L s):Banks as (depth+1) L s:=by
 refine ⟨h.rows.2.2.2.2,?_,?_,?_,?_,?_⟩
 · intro b hb;exact h.widths b (by simp[hb])
 · intro b hb;exact h.permutations b (by simp[hb])
 · intro b hb;exact h.widthBelow b (by simp[hb])
 · intro b hb;exact h.permutationBelow b (by simp[hb])
 · intro i hi
   simpa only [List.drop_succ_cons,show L.suffix+(depth+1)+i=L.suffix+depth+(i+1) by omega]
     using h.suffixes (i+1) (by simp only[List.length_cons];omega)

theorem fits_child (a:PhysicalAxis) (as:List PhysicalAxis) (st:PackingState) (count:ℕ)
 (p:BlockPosition a.geometry.widths) (L:Layout) (h:Fits (a::as) st count L):
 Fits as (packingStep (blockDigit a.geometry.widths p.1 p.2 (physicalVolume as)
   a.geometry.originalPermutation) st) count L:=by
 let d:=blockDigit a.geometry.widths p.1 p.2 (physicalVolume as) a.geometry.originalPermutation
 have endB:=block_end_le_sum a.geometry.widths p.1
 have oi: d.originalDigit < a.geometry.widths.sum:=(a.geometry.originalPermutation (blockEquiv a.geometry.widths p)).isLt
 refine ⟨packingStep_remaining_bound d st L.total h.1 endB,
   packingStep_offset_bound d st h.2.1 p.2.isLt,?_,?_⟩
 · change (st.original*a.geometry.widths.sum+d.originalDigit+1)*physicalVolume as ≤ L.total
   calc
    _ ≤ ((st.original+1)*a.geometry.widths.sum)*physicalVolume as:=
      Nat.mul_le_mul_right _ (by rw [Nat.add_mul,Nat.one_mul];omega)
    _=(st.original+1)*physicalVolume (a::as):=by rw[physicalVolume_cons];ring
    _ ≤ L.total:=h.2.2.1
 · have pos:=physicalVolume_pos as
   have two:=a.geometry.radix_two
   have le:physicalVolume as ≤ physicalVolume (a::as):=by
     rw [physicalVolume_cons];simpa only[Nat.one_mul] using Nat.mul_le_mul_right (physicalVolume as) (show 1 ≤ a.geometry.widths.sum by omega)
   exact (Nat.add_le_add_left le count).trans h.2.2.2

theorem branch_block (b:List Op) (base branchPC jumpPC target yes no l r n B:ℕ)
 (x:Fin n → ℂ) (s:State) (hc:BlockAt b program base)
 (hbranch:program[branchPC]?=some (.branchLT l r yes no))
 (hjump:program[jumpPC]?=some (.jump target)) (htarget:target ≤ B)
 (hbase:base+b.length=jumpPC) (hcode:base+b.length ≤ B)
 (hpc:s.pc=branchPC) (hgo:(if s.natReg l < s.natReg r then yes else no)=base)
 (hr:readable b (setPC s base)) (hv:peak b (setPC s base) ≤ B) (hs:WordBound B s):
 BoundedRuns program n x B s (b.length+2) (setPC (applyBlock b (setPC s base)) target):=by
 let e:=setPC s base
 have he:WordBound B e:=changePC_bound B s base hs (by omega)
 have body:=block_runs b program base n B x e hc rfl he hcode hr hv
 have bp:(applyBlock b e).pc=jumpPC:=by rw[applyBlock_pc];exact hbase
 have jump:BoundedRuns program n x B (applyBlock b e) 1 (setPC (applyBlock b e) target):=
   .next body.final_bound (by rw[UniformMachine.step,bp,hjump];rfl)
     (.refl (changePC_bound B _ target body.final_bound htarget))
 have first:BoundedRuns program n x B s 1 e:=.next hs
   (by simp[UniformMachine.step,hpc,hbranch,hgo,e,setPC]) (.refl he)
 simpa only[e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.trans (body.trans jump)

theorem entry_branch : program[24]?=some (.branchLT 611 600 25 78):=rfl
theorem child_branch : program[43]?=some (.branchLT 625 622 44 83):=rfl
theorem child_jump : program[77]?=some (.jump 24):=rfl
theorem leaf_jump : program[82]?=some (.jump 83):=rfl
theorem pop_branch : program[83]?=some (.branchLT 606 611 84 125):=rfl

theorem enter_actual (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (n depth count:ℕ)
 (x:Fin n → ℂ) (st:PackingState) (s:State) (hlen:depth+(a::as).length=L.ell)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) (hb:Banks (a::as) depth L s)
 (hpc:s.pc=24) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 19 (entered s) ∧ Header L (entered s) ∧ Constants (entered s) ∧ Cursor depth count st (entered s) ∧ Cache a as (entered s) ∧ Local a 0 (entered s) ∧ (entered s).pc=43 ∧ (entered s).natHeap=s.natHeap:=by
 have hd:depth < L.ell:=by simp only[List.length_cons] at hlen;omega
 have countpos:0 < a.geometry.widths.length:=by
   by_contra hn
   have hnil:a.geometry.widths=[]:=List.length_eq_zero_iff.mp (by omega)
   have two:=a.geometry.radix_two
   simp[hnil] at two
 let b:Fin a.geometry.widths.length:=⟨0,countpos⟩
 have qpos:0 < a.geometry.widths.get b:=by
   rcases a.geometry.widths_one_two (a.geometry.widths.get b) (List.get_mem _ _) with h|h <;> omega
 have row0:s.natHeap (L.rows+depth*4)=some a.geometry.widths.length:=by simpa only[Nat.mul_comm] using hb.rows.1
 have row1:s.natHeap (L.rows+(depth*4+1))=some a.widthsBase:=by simpa only[Nat.mul_comm,Nat.add_assoc] using hb.rows.2.1
 have row2:s.natHeap (L.rows+(depth*4+2))=some a.geometry.widths.sum:=by simpa only[Nat.mul_comm,Nat.add_assoc] using hb.rows.2.2.1
 have row3:s.natHeap (L.rows+(depth*4+3))=some a.permutationBase:=by simpa only[Nat.mul_comm,Nat.add_assoc] using hb.rows.2.2.2.1
 have suffix:s.natHeap (L.suffix+(depth+1))=some (physicalVolume as):=by
   simpa only[List.drop_succ_cons,List.drop_zero,Nat.add_assoc] using hb.suffixes 1 (by simp)
 have width0:s.natHeap a.widthsBase=some (a.geometry.widths.get b):=by simpa only[b,Nat.add_zero] using hb.widths a (by simp) b
 have cB:a.geometry.widths.length ≤ L.B:=(hs.2.2.1 _ _ row0).2
 have wB:a.widthsBase ≤ L.B:=(hs.2.2.1 _ _ row1).2
 have rB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ row2).2
 have pB:a.permutationBase ≤ L.B:=(hs.2.2.1 _ _ row3).2
 have tB:physicalVolume as ≤ L.B:=(hs.2.2.1 _ _ suffix).2
 have qB:a.geometry.widths.get b ≤ L.B:=(hs.2.2.1 _ _ width0).2
 simp only [List.get_eq_getElem] at qB
 have rowB:L.rows+depth*4+3 ≤ L.B:=by
   have h0:=L.rowsBelow;have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
 have suffixB:L.suffix+(depth+1) ≤ L.B:=by
   have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
 let e:=setPC s 25
 have he:WordBound L.B e:=changePC_bound L.B s 25 hs (by have h:=L.code;omega)
 have rd:readable enterBlock e:=by
   simp[readable,enterBlock,Op.readable,Op.apply,e,setPC,writeNat,next,hc.1,hc.2.1,hc.2.2.2.1,
     cur.depth,hh.rows,hh.suffix,row0,row1,row2,row3,suffix,width0,Nat.add_assoc]
 have pk:peak enterBlock e ≤ L.B:=by
   simp[peak,enterBlock,Op.peak,Op.apply,e,setPC,writeNat,next,hc.1,hc.2.1,hc.2.2.2.1,
     cur.depth,hh.rows,hh.suffix,row0,row1,row2,row3,suffix,width0,Nat.add_assoc]
   omega
 have body:=block_runs enterBlock program 25 n L.B x e enter_code rfl he
   (by rw[enter_length];have h:=L.code;omega) rd pk
 have first:BoundedRuns program n x L.B s 1 e:=.next hs
   (by simp[UniformMachine.step,hpc,entry_branch,cur.depth,hh.count,hd,e,setPC]) (.refl he)
 refine ⟨by simpa only[enter_length,e,entered] using first.trans body,
   hh.transport L s _ (blocks_frame s).2.2.2.1,
   body_constants enterBlock e hc (by decide),?_,?_,?_,?_,?_⟩
 · constructor <;> simp[entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     cur.depth,cur.start,cur.width,cur.offset,cur.original,cur.count]
 · constructor <;> simp[entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     hc.1,hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,hh.suffix,row0,row1,row2,row3,suffix,Nat.add_assoc]
 · refine ⟨b,⟨0,qpos⟩,?_,?_,?_,?_,?_,?_⟩
   · simp[blockBefore,b]
   all_goals simp[entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     hc.1,hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,hh.suffix,row0,row1,row2,row3,suffix,width0,b,blockBefore,Nat.add_assoc]
 · rw[entered,applyBlock_pc,enter_length];rfl
 · simp[entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next]


/-- Descent saves all four carried address fields and the incremental block cursor. -/
def Saved (L:Layout) (depth j block before role q:ℕ) (st:PackingState) (s:State):Prop:=
 s.natHeap (L.stack+depth*9)=some st.start ∧ s.natHeap (L.stack+depth*9+1)=some st.width ∧ s.natHeap (L.stack+depth*9+2)=some st.offset ∧ s.natHeap (L.stack+depth*9+3)=some st.original ∧ s.natHeap (L.stack+depth*9+4)=some j ∧ s.natHeap (L.stack+depth*9+5)=some block ∧ s.natHeap (L.stack+depth*9+6)=some before ∧ s.natHeap (L.stack+depth*9+7)=some role ∧ s.natHeap (L.stack+depth*9+8)=some q

def savedHeap (L:Layout) (depth j block before role q:ℕ) (st:PackingState) (h:ℕ → Option ℕ):ℕ → Option ℕ:=
 Function.update (Function.update (Function.update (Function.update (Function.update
   (Function.update (Function.update (Function.update (Function.update h
    (L.stack+depth*9) (some st.start)) (L.stack+depth*9+1) (some st.width))
     (L.stack+depth*9+2) (some st.offset)) (L.stack+depth*9+3) (some st.original))
      (L.stack+depth*9+4) (some j)) (L.stack+depth*9+5) (some block))
       (L.stack+depth*9+6) (some before)) (L.stack+depth*9+7) (some role))
        (L.stack+depth*9+8) (some q)

theorem applyBlock_append (b c:List Op) (s:State):
 applyBlock (b++c) s=applyBlock c (applyBlock b s):=by
 induction b generalizing s with
 | nil=>
   rfl
 | cons o b ih=>
   exact ih (o.apply s)
theorem readable_append (b c:List Op) (s:State):
 readable (b++c) s ↔ readable b s ∧ readable c (applyBlock b s):=by
 induction b generalizing s with
 | nil=>
   simp[readable,applyBlock]
 | cons o b ih=>
   simp only[List.cons_append,readable,applyBlock,ih];exact and_assoc.symm
theorem peak_append (b c:List Op) (s:State):
 peak (b++c) s=max (peak b s) (peak c (applyBlock b s)):=by
 induction b generalizing s with
 | nil=>
   simp[peak,applyBlock]
 | cons o b ih=>
   simp only[List.cons_append,peak,applyBlock,ih,max_assoc]

theorem childStep_heap (s:State):(applyBlock childStep s).natHeap=s.natHeap:=by
 simp[applyBlock,childStep,Op.apply,writeNat,next]

theorem childSave_registers (s:State) (j:ℕ) (hj:j ≠ 617 ∧ j ≠ 618 ∧ j ≠ 619 ∧ j ≠ 630):
 (applyBlock childSave s).natReg j=s.natReg j:=by
 simp[applyBlock,childSave,Op.apply,writeNat,next,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2]

theorem childSave_value (s:State) (permutation j v:ℕ) (hp:s.natReg 623=permutation)
 (hj:s.natReg 625=j) (hv:s.natHeap (permutation+j)=some v):
 (applyBlock childSave s).natReg 630=v:=by
 simp[applyBlock,childSave,Op.apply,writeNat,next,hp,hj,hv]

theorem child_heap (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (depth count:ℕ)
 (st:PackingState) (b:Fin a.geometry.widths.length) (t:Fin (a.geometry.widths.get b)) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) (_cache:Cache a as s)
 (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val) (hb:s.natReg 626=b.val)
 (hp:s.natReg 627=blockBefore a.geometry.widths b) (ht:s.natReg 628=t.val)
 (hq:s.natReg 629=a.geometry.widths.get b):
 (child s).natHeap=savedHeap L depth (blockBefore a.geometry.widths b+t.val+1) b.val
   (blockBefore a.geometry.widths b) (t.val+1) (a.geometry.widths.get b) st s.natHeap:=by
 rw [child,childBlock,applyBlock_append]
 change (applyBlock childStep (applyBlock childSave (setPC s 44))).natHeap=_
 rw [childStep_heap]
 simp[applyBlock,childSave,Op.apply,writeNat,next,setPC,savedHeap,
   hc.1,hc.2.1,hc.2.2.2.2,cur.depth,cur.start,cur.width,cur.offset,cur.original,
   hh.stack,hi,hb,hp,ht,hq,Nat.add_assoc]

theorem child_cursor (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (depth count:ℕ)
 (st:PackingState) (b:Fin a.geometry.widths.length) (t:Fin (a.geometry.widths.get b)) (s:State)
 (_hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) (cache:Cache a as s)
 (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val)
 (hp:s.natReg 627=blockBefore a.geometry.widths b) (ht:s.natReg 628=t.val)
 (hq:s.natReg 629=a.geometry.widths.get b)
 (value:s.natHeap (a.permutationBase+(blockBefore a.geometry.widths b+t.val))=
   some (a.geometry.originalPermutation (blockEquiv a.geometry.widths ⟨b,t⟩)).val):
 Cursor (depth+1) count
   (packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st) (child s):=by
 let u:=applyBlock childSave (setPC s 44)
 have regs:∀j,j ≠ 617 ∧ j ≠ 618 ∧ j ≠ 619 ∧ j ≠ 630 → u.natReg j=s.natReg j:=
   fun j hj=> childSave_registers (setPC s 44) j hj
 have rv:u.natReg 630=(a.geometry.originalPermutation (blockEquiv a.geometry.widths ⟨b,t⟩)).val:=
   childSave_value (setPC s 44) _ _ _ cache.permutation hi value
 rw [child,childBlock,applyBlock_append]
 change Cursor (depth+1) count _ (setPC (applyBlock childStep u) 24)
 constructor <;> simp (disch:=decide) [applyBlock,childStep,Op.apply,writeNat,next,setPC,
   regs,rv,hc.2.1,cur.depth,cur.start,cur.width,cur.offset,cur.original,cur.count,
   cache.radix,cache.tail,hp,ht,hq,packingStep,blockDigit]
 all_goals rfl

theorem childSave_peak (B depth stack permutation j role v:ℕ) (s:State)
 (hc:Constants s) (hd:s.natReg 611=depth) (hst:s.natReg 603=stack)
 (hp:s.natReg 623=permutation) (hj:s.natReg 625=j) (hr:s.natReg 628=role)
 (hv:s.natHeap (permutation+j)=some v) (hs:WordBound B s)
 (hsb:stack+depth*9+8 ≤ B) (hpb:permutation+j ≤ B) (hjb:j+1 ≤ B) (hrb:role+1 ≤ B):
 peak childSave s ≤ B:=by
 have valueBound: v ≤ B:=(hs.2.2.1 _ _ hv).2
 have s612:=hs.2.1 612
 have s613:=hs.2.1 613
 have s614:=hs.2.1 614
 have s615:=hs.2.1 615
 have s626:=hs.2.1 626
 have s627:=hs.2.1 627
 have s629:=hs.2.1 629
 simp[peak,childSave,Op.peak,Op.apply,writeNat,next,hc.1,hc.2.1,hc.2.2.2.2,
   hd,hst,hp,hj,hr,hv,Nat.add_assoc]
 omega

theorem savedHeap_saved (L:Layout) (depth j block before role q:ℕ) (st:PackingState) (s t:State)
 (heap:t.natHeap=savedHeap L depth j block before role q st s.natHeap):
 Saved L depth j block before role q st t:=by
 unfold Saved
 rw[heap]
 simp (disch:=omega) [savedHeap,Function.update_of_ne]

theorem savedHeap_outside (L:Layout) (depth j block before role q:ℕ) (st:PackingState) (s t:State)
 (heap:t.natHeap=savedHeap L depth j block before role q st s.natHeap):
 Outside (L.stack+depth*9) 9 s t:=by
 intro i hi
 rw[heap]
 simp (disch:=omega) [savedHeap,Function.update_of_ne]

/-- All integer peaks and the forward-permutation read are derived from the
physical banks and the carried packing invariant. -/
theorem child_guard (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (n depth count:ℕ)
 (_x:Fin n → ℂ) (st:PackingState) (b:Fin a.geometry.widths.length)
 (t:Fin (a.geometry.widths.get b)) (s:State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (banks:Banks (a::as) depth L s) (hf:Fits (a::as) st 0 L)
 (cache:Cache a as s) (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val)
 (_hb:s.natReg 626=b.val) (hp:s.natReg 627=blockBefore a.geometry.widths b)
 (ht:s.natReg 628=t.val) (hq:s.natReg 629=a.geometry.widths.get b)
 (_hpc:s.pc=43) (hs:WordBound L.B s):
 readable childBlock (setPC s 44) ∧ peak childBlock (setPC s 44) ≤ L.B:=by
 let p:BlockPosition a.geometry.widths:=⟨b,t⟩
 let j:=blockEquiv a.geometry.widths p
 let v:=(a.geometry.originalPermutation j).val
 have value:s.natHeap (a.permutationBase+(blockBefore a.geometry.widths b+t.val))=some v:=
   banks.permutations a (by simp) j
 have hd:depth < L.ell:=by simp only[List.length_cons] at hlen;omega
 have endB:=block_end_le_sum a.geometry.widths b
 have tj:=t.isLt
 have jBound:blockBefore a.geometry.widths b+t.val < a.geometry.widths.sum:=j.isLt
 have origBound:v < a.geometry.widths.sum:=(a.geometry.originalPermutation j).isLt
 have stackB:L.stack+depth*9+8 ≤ L.B:=by
   have h:=L.stackBelow;have h':=L.inverseBound;omega
 have addressB:a.permutationBase+(blockBefore a.geometry.widths b+t.val) ≤ L.B:=by
   have h:=banks.permutationBelow a (by simp)
   have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
 have rB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ banks.rows.2.2.1).2
 have pB:a.permutationBase ≤ L.B:=(hs.2.2.1 _ _ banks.rows.2.2.2.1).2
 have vB:v ≤ L.B:=(hs.2.2.1 _ _ value).2
 have stB:=packing_state_word_bounds st L.total (physicalVolume (a::as)) L.total
   (physicalVolume_pos _) (by rfl) hf.1 hf.2.1 (by
     have pos:=physicalVolume_pos (a::as)
     have h:st.original+1 ≤ (st.original+1)*physicalVolume (a::as):=by
       simpa only[Nat.mul_one] using Nat.mul_le_mul_left (st.original+1) (show 1 ≤ physicalVolume (a::as) by omega)
     have fit:=hf.2.2.1;omega)
 have childfit:=fits_child a as st 0 p L hf
 dsimp only[p] at childfit
 have volB:=L.volumeBound
 have newStartB:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).start ≤ L.B:=by
   have fit:=childfit.1;omega
 have newWidthB:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).width ≤ L.B:=by
   have pos:=physicalVolume_pos as
   have hw:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).width ≤ (packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).width*physicalVolume as:=by
     simpa only[Nat.mul_one] using Nat.mul_le_mul_left _ (show 1 ≤ physicalVolume as by omega)
   have fit:=childfit.1;omega
 have newOffsetB:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).offset ≤ L.B:=by
   have h:=childfit.2.1;omega
 have newOriginalB:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).original ≤ L.B:=by
   have pos:=physicalVolume_pos as
   have ho:(packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).original+1 ≤ ((packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st).original+1)*physicalVolume as:=by
     simpa only[Nat.mul_one] using Nat.mul_le_mul_left _ (show 1 ≤ physicalVolume as by omega)
   have fit:=childfit.2.2.1;omega
 have termB:st.width*blockBefore a.geometry.widths b*physicalVolume as ≤ L.B:=by
   have h:=newStartB
   change st.start+st.width*blockBefore a.geometry.widths b*physicalVolume as ≤ L.B at h
   omega
 have factorB:st.width*blockBefore a.geometry.widths b ≤ L.B:=by
   have pos:=physicalVolume_pos as
   have h:st.width*blockBefore a.geometry.widths b ≤ st.width*blockBefore a.geometry.widths b*physicalVolume as:=by
     simpa only[Nat.mul_one] using Nat.mul_le_mul_left _ (show 1 ≤ physicalVolume as by omega)
   omega
 have qB:a.geometry.widths.get b ≤ L.B:=by have h:=endB;omega
 have bB:b.val ≤ L.B:=by
   have h: a.geometry.widths.length ≤ L.B:=(hs.2.2.1 _ _ banks.rows.1).2
   have hb:=b.isLt;omega
 have ellB:L.ell ≤ L.B:=by rw [←hh.count];exact hs.2.1 600
 simp only[packingStep,blockDigit,List.get_eq_getElem] at newStartB newWidthB newOffsetB newOriginalB qB endB tj
 let u:=applyBlock childSave (setPC s 44)
 have regs:∀j,j ≠ 617 ∧ j ≠ 618 ∧ j ≠ 619 ∧ j ≠ 630 → u.natReg j=s.natReg j:=
   fun j hj=> childSave_registers (setPC s 44) j hj
 have rv:u.natReg 630=v:=childSave_value (setPC s 44) _ _ _ cache.permutation hi value
 have nr:st.original*a.geometry.widths.sum+v ≤ L.B:=by
   exact newOriginalB
 have rdSave:readable childSave (setPC s 44):=by
   simp[readable,childSave,Op.readable,Op.apply,setPC,writeNat,next,cache.permutation,hi,value]
 have rdStep:readable childStep u:=by simp[readable,childStep,Op.readable]
 have rd:readable childBlock (setPC s 44):=by
   rw[childBlock,readable_append];exact ⟨rdSave,rdStep⟩
 have pkSave:peak childSave (setPC s 44) ≤ L.B:=
   childSave_peak L.B depth L.stack a.permutationBase
     (blockBefore a.geometry.widths b+t.val) t.val v (setPC s 44)
     hc cur.depth hh.stack cache.permutation hi ht value
     (changePC_bound L.B s 44 hs (by have h:=L.code;omega)) stackB addressB (by omega) (by omega)
 have pkStep:peak childStep u ≤ L.B:=by
   simp (disch:=decide) [peak,childStep,Op.peak,Op.apply,writeNat,next,
     regs,rv,hc.2.1,cur.depth,cur.start,cur.width,cur.offset,cur.original,
     cache.radix,cache.tail,hp,ht,hq]
   have code:=L.code
   omega
 have pk:peak childBlock (setPC s 44) ≤ L.B:=by
   rw[childBlock,peak_append];exact max_le pkSave pkStep
 exact ⟨rd,pk⟩

theorem child_saved (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (depth count:ℕ)
 (st:PackingState) (b:Fin a.geometry.widths.length) (t:Fin (a.geometry.widths.get b)) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) (_cache:Cache a as s)
 (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val) (hb:s.natReg 626=b.val)
 (hp:s.natReg 627=blockBefore a.geometry.widths b) (ht:s.natReg 628=t.val)
 (hq:s.natReg 629=a.geometry.widths.get b):
 Saved L depth (blockBefore a.geometry.widths b+t.val+1) b.val
   (blockBefore a.geometry.widths b) (t.val+1) (a.geometry.widths.get b) st (child s):=by
 exact savedHeap_saved L depth _ _ _ _ _ st s _
   (child_heap a as L depth count st b t s hh hc cur _cache hi hb hp ht hq)

theorem child_outside (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (depth count:ℕ)
 (st:PackingState) (b:Fin a.geometry.widths.length) (t:Fin (a.geometry.widths.get b)) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) (_cache:Cache a as s)
 (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val) (hb:s.natReg 626=b.val)
 (hp:s.natReg 627=blockBefore a.geometry.widths b) (ht:s.natReg 628=t.val)
 (hq:s.natReg 629=a.geometry.widths.get b):
 Outside (L.stack+depth*9) 9 s (child s):=by
 exact savedHeap_outside L depth _ _ _ _ _ st s _
   (child_heap a as L depth count st b t s hh hc cur _cache hi hb hp ht hq)

theorem child_header (L:Layout) (s:State) (hh:Header L s):Header L (child s):=
 hh.transport L s _ (blocks_frame s).2.2.2.2.1

theorem constants_setPC (s:State) (pc:ℕ) (hc:Constants s):Constants (setPC s pc):=hc

theorem child_constants (s:State) (hc:Constants s):Constants (child s):=by
 have cc:Constants (applyBlock childBlock (setPC s 44)):=
   body_constants childBlock (setPC s 44) hc (by decide)
 exact constants_setPC _ 24 cc

theorem child_actual (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (n depth count:ℕ)
 (x:Fin n → ℂ) (st:PackingState) (b:Fin a.geometry.widths.length)
 (t:Fin (a.geometry.widths.get b)) (s:State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (banks:Banks (a::as) depth L s) (hf:Fits (a::as) st 0 L)
 (cache:Cache a as s) (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val)
 (hb:s.natReg 626=b.val) (hp:s.natReg 627=blockBefore a.geometry.widths b)
 (ht:s.natReg 628=t.val) (hq:s.natReg 629=a.geometry.widths.get b)
 (hpc:s.pc=43) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 35 (child s) ∧ Header L (child s) ∧ Constants (child s) ∧ Cursor (depth+1) count
   (packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st) (child s) ∧ Saved L depth (blockBefore a.geometry.widths b+t.val+1) b.val
   (blockBefore a.geometry.widths b) (t.val+1) (a.geometry.widths.get b) st (child s) ∧ Outside (L.stack+depth*9) 9 s (child s) ∧ (child s).pc=24:=by
 let p:BlockPosition a.geometry.widths:=⟨b,t⟩
 let j:=blockEquiv a.geometry.widths p
 let v:=(a.geometry.originalPermutation j).val
 have value:s.natHeap (a.permutationBase+(blockBefore a.geometry.widths b+t.val))=some v:=
   banks.permutations a (by simp) j
 have jBound:blockBefore a.geometry.widths b+t.val < a.geometry.widths.sum:=j.isLt
 obtain ⟨rd,pk⟩:=child_guard a as L n depth count x st b t s hlen hh hc cur banks hf cache hi hb hp ht hq hpc hs
 have run:BoundedRuns program n x L.B s 35 (child s):=by
   simpa only[child_length,child] using branch_block childBlock 44 43 77 24 44 83 625 622
     n L.B x s child_code child_branch child_jump (by have h:=L.code;omega) rfl
     (by rw[child_length];have h:=L.code;omega) hpc (by rw[hi,cache.radix];simp[jBound]) rd pk hs
 exact ⟨run,child_header L s hh,child_constants s hc,
   child_cursor a as L depth count st b t s hh hc cur cache hi hp ht hq value,
   child_saved a as L depth count st b t s hh hc cur cache hi hb hp ht hq,
   child_outside a as L depth count st b t s hh hc cur cache hi hb hp ht hq,rfl⟩

def native (as:List Axis) (st:PackingState) (ds:LocalDigits as):ℕ:=
 (follow (flatLayers as) (flatCodec as ds) st).original

theorem native_cons (a:Axis) (as:List Axis) (st:PackingState) (p:BlockPosition a.widths) (ds:LocalDigits as):
 native (a::as) st (p,ds)=native as
   (packingStep (blockDigit a.widths p.1 p.2 (radices as).prod a.originalPermutation) st) ds:=by
 unfold native
 change (follow (flatLayers as) (flatCodec as ds) (packingStep (flatDigit a as (blockEquiv a.widths p)) st)).original=_
 rw [flatDigit_encode]

theorem leaf_heap (L:Layout) (depth count:ℕ) (st:PackingState) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s):
 (leaf s).natHeap=Function.update s.natHeap (L.inverse+(st.start+st.offset)) (some st.original):=by
 simp[leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,next,
   hh.inverse,hc.2.1,cur.start,cur.offset,cur.original]

theorem leaf_actual (L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:PackingState) (s:State)
 (hd:depth=L.ell) (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s)
 (hf:Fits [] st count L) (hpc:s.pc=24) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 6 (leaf s) ∧ Header L (leaf s) ∧ Constants (leaf s) ∧ Cursor depth (count+1) st (leaf s) ∧ (leaf s).pc=83:=by
 have fit:st.start+st.width ≤ L.total:=by simpa only[physicalVolume_nil,Nat.mul_one] using hf.1
 have oi:st.original+1 ≤ L.total:=by simpa only[physicalVolume_nil,Nat.mul_one] using hf.2.2.1
 have cb:count+1 ≤ L.total:=by simpa only[physicalVolume_nil] using hf.2.2.2
 have offset:=hf.2.1
 have invBound:=L.inverseBound
 have volBound:=L.volumeBound
 have rd:readable leafBlock (setPC s 78):=by simp[readable,leafBlock,Op.readable]
 have pk:peak leafBlock (setPC s 78) ≤ L.B:=by
   simp[peak,leafBlock,Op.peak,Op.apply,setPC,writeNat,next,hh.inverse,hc.2.1,
     cur.start,cur.offset,cur.original,cur.count]
   omega
 have run:BoundedRuns program n x L.B s 6 (leaf s):=by
   simpa only[leaf_length,leaf] using branch_block leafBlock 78 24 82 83 25 78 611 600
     n L.B x s leaf_code entry_branch leaf_jump (by have h:=L.code;omega) rfl
     (by rw[leaf_length];have h:=L.code;omega) hpc (by rw[cur.depth,hh.count,hd];simp) rd pk hs
 refine ⟨run,hh.transport L s _ (blocks_frame s).2.2.2.2.2.1,
   body_constants leafBlock (setPC s 78) hc (by decide),?_,rfl⟩
 constructor <;> simp[leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,next,hc.2.1,
   cur.depth,cur.start,cur.width,cur.offset,cur.original,cur.count]

structure Effect (as:List PhysicalAxis) (depth count:ℕ) (st:PackingState) (L:Layout) (s t:State):Prop where
 pc:t.pc=83
 header:Header L t
 constants:Constants t
 cursor:Cursor depth (count+physicalVolume as) st t
 frame:Frame s t
 natFrame:∀j,(j < L.stack+depth*9 ∨ L.stack+L.ell*9 ≤ j) → (∀ds:LocalDigits (physicalAxes as),j ≠ L.inverse+target (physicalAxes as) st ds) → t.natHeap j=s.natHeap j
 addresses:∀ds:LocalDigits (physicalAxes as),
   t.natHeap (L.inverse+target (physicalAxes as) st ds)=some (native (physicalAxes as) st ds)

theorem physical_leaf (L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:PackingState) (s:State)
 (hlen:depth+([]:List PhysicalAxis).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hf:Fits [] st count L) (hpc:s.pc=24) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 6 (leaf s) ∧ Effect [] depth count st L s (leaf s):=by
 obtain ⟨run,header,const,cursor,pc⟩:=leaf_actual L n depth count x st s (by simpa using hlen) hh hc cur hf hpc hs
 refine ⟨run,⟨pc,header,const,cursor,(blocks_frame s).2.2.2.2.2.1,?_,?_⟩⟩
 · intro j _ hout
   rw[leaf_heap L depth count st s hh hc cur]
   exact Function.update_of_ne (hout ()) _ _
 · intro ds
   cases ds
   rw[leaf_heap L depth count st s hh hc cur]
   change Function.update s.natHeap (L.inverse+(st.start+st.offset)) (some st.original)
     (L.inverse+(st.start+st.offset))=some st.original
   exact Function.update_self _ _ _


theorem readOnly_heap (b:List Op) (s:State)
 (h:∀o∈b,match o with | .putNat _ _=> False | _=> True):
 (applyBlock b s).natHeap=s.natHeap:=by
 induction b generalizing s with
 | nil=>
   rfl
 | cons o b ih=>
   have ho:=h o (by simp)
   have he:(o.apply s).natHeap=s.natHeap:=by cases o <;> simp only at ho <;> rfl
   exact (ih (o.apply s) (fun t ht=> h t (by simp[ht]))).trans he

theorem pop_heap (s:State):(popped s).natHeap=s.natHeap:=
 readOnly_heap popBlock (setPC s 84) (by simp[popBlock,popSaved,popRow])

theorem popRow_registers (s:State) (j:ℕ) (hj:j ≠ 617 ∧ j ≠ 618 ∧ (j < 620 ∨ 624 < j)):
 (applyBlock popRow s).natReg j=s.natReg j:=by
 simp (disch:=omega) [applyBlock,popRow,Op.apply,writeNat,next]

/-- Exact loads from the parent frame written by descent. -/
theorem pop_saved_cursor (L:Layout) (depth count j block before role q:ℕ) (st:PackingState) (s:State)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 611=depth+1) (hn:s.natReg 616=count)
 (saved:Saved L depth j block before role q st s):
 Cursor depth count st (applyBlock popSaved (setPC s 84)) ∧ (applyBlock popSaved (setPC s 84)).natReg 625=j ∧ (applyBlock popSaved (setPC s 84)).natReg 626=block ∧ (applyBlock popSaved (setPC s 84)).natReg 627=before ∧ (applyBlock popSaved (setPC s 84)).natReg 628=role ∧ (applyBlock popSaved (setPC s 84)).natReg 629=q:=by
 simp only[Saved,Nat.add_assoc] at saved
 rcases saved with ⟨ss,sw,so,si,sj,sb,sp,sr,sq⟩
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · constructor <;> simp[applyBlock,popSaved,Op.apply,writeNat,next,setPC,hd,hn,
     hc.1,hc.2.1,hc.2.2.2.2,hh.stack,ss,sw,so,si,sj,sb,sp,sr,sq,Nat.add_assoc]
 all_goals simp[applyBlock,popSaved,Op.apply,writeNat,next,setPC,hd,
   hc.1,hc.2.1,hc.2.2.2.2,hh.stack,ss,sw,so,si,sj,sb,sp,sr,sq,Nat.add_assoc]

/-- The return executes the actual saved reads and physical row reload. -/
theorem pop_actual (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (n depth count j block before role q:ℕ)
 (x:Fin n → ℂ) (st:PackingState) (s:State) (hlen:depth+(a::as).length=L.ell)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 611=depth+1) (hn:s.natReg 616=count)
 (saved:Saved L depth j block before role q st s) (banks:Banks (a::as) depth L s)
 (hpc:s.pc=83) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 34 (popped s) ∧ Header L (popped s) ∧ Constants (popped s) ∧ Cursor depth count st (popped s) ∧ Cache a as (popped s) ∧ (popped s).natReg 625=j ∧ (popped s).natReg 626=block ∧ (popped s).natReg 627=before ∧ (popped s).natReg 628=role ∧ (popped s).natReg 629=q ∧ (popped s).pc=117:=by
 have dd:depth < L.ell:=by simp only[List.length_cons] at hlen;omega
 have row0:s.natHeap (L.rows+depth*4)=some a.geometry.widths.length:=by simpa only[Nat.mul_comm] using banks.rows.1
 have row1:s.natHeap (L.rows+(depth*4+1))=some a.widthsBase:=by simpa only[Nat.mul_comm,Nat.add_assoc] using banks.rows.2.1
 have row2:s.natHeap (L.rows+(depth*4+2))=some a.geometry.widths.sum:=by simpa only[Nat.mul_comm,Nat.add_assoc] using banks.rows.2.2.1
 have row3:s.natHeap (L.rows+(depth*4+3))=some a.permutationBase:=by simpa only[Nat.mul_comm,Nat.add_assoc] using banks.rows.2.2.2.1
 have suffix:s.natHeap (L.suffix+(depth+1))=some (physicalVolume as):=by
   simpa only[List.drop_succ_cons,List.drop_zero,Nat.add_assoc] using banks.suffixes 1 (by simp)
 have stackB:L.stack+depth*9+8 ≤ L.B:=by have h:=L.stackBelow;have h':=L.inverseBound;omega
 have rowB:L.rows+depth*4+3 ≤ L.B:=by
   have h:=L.rowsBelow;have h':=L.suffixBelow;have h'':=L.stackBelow;have h3:=L.inverseBound;omega
 have suffixB:L.suffix+(depth+1) ≤ L.B:=by
   have h:=L.suffixBelow;have h':=L.stackBelow;have h'':=L.inverseBound;omega
 obtain ⟨cur,uj,ub,up,ur,uq⟩:=pop_saved_cursor L depth count j block before role q st s hh hc hd hn saved
 let u:=applyBlock popSaved (setPC s 84)
 change Cursor depth count st u at cur
 change u.natReg 625=j at uj
 change u.natReg 626=block at ub
 change u.natReg 627=before at up
 change u.natReg 628=role at ur
 change u.natReg 629=q at uq
 have uc:Constants u:=body_constants popSaved (setPC s 84) hc (by decide)
 have uf:Frame s u:=(block_frame 606 popSaved (setPC s 84) (by decide)).frame (by omega)
 have uh:Header L u:=hh.transport L s u uf
 have heap:u.natHeap=s.natHeap:=readOnly_heap popSaved (setPC s 84) (by simp[popSaved])
 have regs:∀j,j ≠ 617 ∧ j ≠ 618 ∧ (j < 620 ∨ 624 < j) → (applyBlock popRow u).natReg j=u.natReg j:=
   popRow_registers u
 have savedB:st.start ≤ L.B ∧ st.width ≤ L.B ∧ st.offset ≤ L.B ∧ st.original ≤ L.B ∧ j ≤ L.B ∧ block ≤ L.B ∧ before ≤ L.B ∧ role ≤ L.B ∧ q ≤ L.B:=by
   rcases saved with ⟨ss,sw,so,si,sj,sb,sp,sr,sq⟩
   exact ⟨(hs.2.2.1 _ _ ss).2,(hs.2.2.1 _ _ sw).2,(hs.2.2.1 _ _ so).2,
     (hs.2.2.1 _ _ si).2,(hs.2.2.1 _ _ sj).2,(hs.2.2.1 _ _ sb).2,
     (hs.2.2.1 _ _ sp).2,(hs.2.2.1 _ _ sr).2,(hs.2.2.1 _ _ sq).2⟩
 have rowsB:a.geometry.widths.length ≤ L.B ∧ a.widthsBase ≤ L.B ∧ a.geometry.widths.sum ≤ L.B ∧ a.permutationBase ≤ L.B ∧ physicalVolume as ≤ L.B:=
   ⟨(hs.2.2.1 _ _ row0).2,(hs.2.2.1 _ _ row1).2,(hs.2.2.1 _ _ row2).2,
     (hs.2.2.1 _ _ row3).2,(hs.2.2.1 _ _ suffix).2⟩
 have rdSaved:readable popSaved (setPC s 84):=by
   rcases saved with ⟨ss,sw,so,si,sj,sb,sp,sr,sq⟩
   simp only[Nat.add_assoc] at ss sw so si sj sb sp sr sq
   simp[readable,popSaved,Op.readable,Op.apply,setPC,writeNat,next,hd,
     hc.1,hc.2.1,hc.2.2.2.2,hh.stack,ss,sw,so,si,sj,sb,sp,sr,sq,Nat.add_assoc]
 have pkSaved:peak popSaved (setPC s 84) ≤ L.B:=by
   rcases saved with ⟨ss,sw,so,si,sj,sb,sp,sr,sq⟩
   simp only[Nat.add_assoc] at ss sw so si sj sb sp sr sq
   simp[peak,popSaved,Op.peak,Op.apply,setPC,writeNat,next,hd,
     hc.1,hc.2.1,hc.2.2.2.2,hh.stack,ss,sw,so,si,sj,sb,sp,sr,sq,Nat.add_assoc]
   rcases savedB with ⟨_,_,_,_,_,_,_,_,_⟩
   omega
 have rdRow:readable popRow u:=by
   simp[readable,popRow,Op.readable,Op.apply,writeNat,next,uc.2.1,uc.2.2.2.1,cur.depth,
     uh.rows,uh.suffix,heap,row0,row1,row2,row3,suffix,Nat.add_assoc]
 have pkRow:peak popRow u ≤ L.B:=by
   simp[peak,popRow,Op.peak,Op.apply,writeNat,next,uc.2.1,uc.2.2.2.1,cur.depth,
     uh.rows,uh.suffix,heap,row0,row1,row2,row3,suffix,Nat.add_assoc]
   rcases rowsB with ⟨_,_,_,_,_⟩
   omega
 let e:=setPC s 84
 have he:WordBound L.B e:=changePC_bound L.B s 84 hs (by have h:=L.code;omega)
 have body:=block_runs popBlock program 84 n L.B x e pop_code rfl he
   (by rw[pop_length];have h:=L.code;omega)
   (by rw[popBlock,readable_append];exact ⟨rdSaved,rdRow⟩)
   (by rw[popBlock,peak_append];exact max_le pkSaved pkRow)
 have first:BoundedRuns program n x L.B s 1 e:=.next hs
   (by simp[UniformMachine.step,hpc,pop_branch,hc.1,hd,e,setPC]) (.refl he)
 have eq:popped s=applyBlock popRow u:=by rw[popped,popBlock,applyBlock_append]
 refine ⟨by simpa only[pop_length,e,popped] using first.trans body,
   hh.transport L s _ (blocks_frame s).2.2.2.2.2.2,
   body_constants popBlock e hc (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw[eq]
   constructor <;> simp (disch:=omega) only[regs,cur.depth,cur.start,cur.width,cur.offset,cur.original,cur.count]
 · rw[eq]
   constructor <;> simp[applyBlock,popRow,Op.apply,writeNat,next,uc.2.1,uc.2.2.2.1,cur.depth,
     uh.rows,uh.suffix,heap,row0,row1,row2,row3,suffix,Nat.add_assoc]
 all_goals first | (rw[eq];simp (disch:=omega) only[regs,uj,ub,up,ur,uq]) |
   (rw[popped,applyBlock_pc,pop_length];rfl)


def normalized (s:State):State:=
 if s.natReg 625 < s.natReg 622 then
   if s.natReg 628 < s.natReg 629 then setPC s 43
   else setPC (applyBlock advanceBlock (setPC s 119)) 43
 else setPC s 43

theorem normalized_index (s:State):(normalized s).natReg 625=s.natReg 625:=by
 unfold normalized
 split_ifs <;> rfl

def normalizeCost (s:State):ℕ:=
 if s.natReg 625 < s.natReg 622 then (if s.natReg 628 < s.natReg 629 then 2 else 8) else 1

theorem normalize_cost_bound (s:State):normalizeCost s ≤ 8:=by
 unfold normalizeCost
 split_ifs <;> omega

theorem normalize_index_branch : program[117]?=some (.branchLT 625 622 118 43):=rfl
theorem normalize_role_branch : program[118]?=some (.branchLT 628 629 43 119):=rfl
theorem advance_jump : program[124]?=some (.jump 43):=rfl

theorem normalize_bounded (n B:ℕ) (x:Fin n → ℂ) (s:State)
 (hpc:s.pc=117) (hB:137 ≤ B) (hs:WordBound B s)
 (hr:readable advanceBlock (setPC s 119)) (hp:peak advanceBlock (setPC s 119) ≤ B):
 BoundedRuns program n x B s (normalizeCost s) (normalized s):=by
 by_cases hi:s.natReg 625 < s.natReg 622
 · let u:=setPC s 118
   have hu:WordBound B u:=changePC_bound B s 118 hs (by omega)
   have first:BoundedRuns program n x B s 1 u:=.next hs
     (by simp[UniformMachine.step,hpc,normalize_index_branch,hi,u,setPC]) (.refl hu)
   by_cases ht:s.natReg 628 < s.natReg 629
   · have last:BoundedRuns program n x B u 1 (setPC s 43):=.next hu
       (by simp[UniformMachine.step,u,setPC,normalize_role_branch,ht])
       (.refl (changePC_bound B s 43 hs (by omega)))
     simpa only[normalizeCost,normalized,ite_eq_left hi,ite_eq_left ht] using first.trans last
   · have rest:=branch_block advanceBlock 119 118 124 43 43 119 628 629
       n B x u advance_code normalize_role_branch advance_jump (by omega) rfl
       (by rw[advance_length];omega) rfl (by simp[u,setPC,ht]) hr hp hu
     simpa only[normalizeCost,normalized,ite_eq_left hi,ite_eq_right ht,advance_length,u,setPC] using first.trans rest
 · have last:BoundedRuns program n x B s 1 (setPC s 43):=.next hs
     (by simp[UniformMachine.step,hpc,normalize_index_branch,hi,setPC])
     (.refl (changePC_bound B s 43 hs (by omega)))
   simpa only[normalizeCost,normalized,ite_eq_right hi] using last

theorem header_setPC (L:Layout) (s:State) (pc:ℕ) (h:Header L s):Header L (setPC s pc):=
 ⟨h.count,h.rows,h.suffix,h.stack,h.inverse,h.source,h.destination⟩
theorem cursor_setPC (depth count:ℕ) (st:PackingState) (s:State) (pc:ℕ) (h:Cursor depth count st s):
 Cursor depth count st (setPC s pc):=⟨h.depth,h.start,h.width,h.offset,h.original,h.count⟩
theorem cache_setPC (a:PhysicalAxis) (as:List PhysicalAxis) (s:State) (pc:ℕ) (h:Cache a as s):
 Cache a as (setPC s pc):=⟨h.count,h.widths,h.radix,h.permutation,h.tail⟩

/-- Normalization advances a block only after its last role. The next width
is an actual guarded physical load; no scan over prior blocks occurs. -/
theorem normalize_actual (a:PhysicalAxis) (as:List PhysicalAxis) (L:Layout) (n depth count:ℕ)
 (x:Fin n → ℂ) (st:PackingState) (b:Fin a.geometry.widths.length)
 (t:Fin (a.geometry.widths.get b)) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s)
 (banks:Banks (a::as) depth L s) (cache:Cache a as s)
 (hi:s.natReg 625=blockBefore a.geometry.widths b+t.val+1) (hb:s.natReg 626=b.val)
 (hbefore:s.natReg 627=blockBefore a.geometry.widths b) (hrole:s.natReg 628=t.val+1)
 (hq:s.natReg 629=a.geometry.widths.get b) (hpc:s.pc=117) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s (normalizeCost s) (normalized s) ∧ Header L (normalized s) ∧ Constants (normalized s) ∧ Cursor depth count st (normalized s) ∧ Cache a as (normalized s) ∧ (blockBefore a.geometry.widths b+t.val+1 < a.geometry.widths.sum → Local a (blockBefore a.geometry.widths b+t.val+1) (normalized s)) ∧ (normalized s).pc=43 ∧ (normalized s).natHeap=s.natHeap ∧ Frame s (normalized s):=by
 by_cases hnext:blockBefore a.geometry.widths b+t.val+1 < a.geometry.widths.sum
 · have go:s.natReg 625 < s.natReg 622:=by rw[hi,cache.radix];exact hnext
   by_cases inside:t.val+1 < a.geometry.widths.get b
   · have within:s.natReg 628 < s.natReg 629:=by rw[hrole,hq];exact inside
     have nr:normalized s=setPC s 43:=by simp only[normalized,ite_eq_left go,ite_eq_left within]
     have run:BoundedRuns program n x L.B s 2 (setPC s 43):=by
       have uBound:=changePC_bound L.B s 118 hs (by have h:=L.code;omega)
       have aRun:BoundedRuns program n x L.B s 1 (setPC s 118):=.next hs
         (by simp[UniformMachine.step,hpc,normalize_index_branch,go,setPC]) (.refl uBound)
       have bRun:BoundedRuns program n x L.B (setPC s 118) 1 (setPC s 43):=.next uBound
         (by simp[UniformMachine.step,setPC,normalize_role_branch,within])
         (.refl (changePC_bound L.B s 43 hs (by have h:=L.code;omega)))
       exact aRun.trans bRun
     rw[nr]
     refine ⟨by simpa only[normalizeCost,ite_eq_left go,ite_eq_left within] using run,header_setPC L s 43 hh,hc,cursor_setPC depth count st s 43 cur,cache_setPC a as s 43 cache,?_,rfl,rfl,?_,⟩
     · intro _
       exact ⟨b,⟨t.val+1,inside⟩,rfl,hi,hb,hbefore,hrole,hq⟩
     · exact ⟨rfl,rfl,rfl,rfl,fun _ _=> rfl⟩
   · have beyond:¬s.natReg 628 < s.natReg 629:=by rw[hrole,hq];exact inside
     obtain ⟨nb,beforeNext⟩:=cursor_next_block a.geometry b t hnext inside
     let c:Fin a.geometry.widths.length:=⟨b.val+1,nb⟩
     have qpos:0 < a.geometry.widths.get c:=by
       rcases a.geometry.widths_one_two _ (List.get_mem _ c) with h|h <;> omega
     have value:s.natHeap (a.widthsBase+(b.val+1))=some (a.geometry.widths.get c):=banks.widths a (by simp) c
     have widthB:a.geometry.widths.get c ≤ L.B:=(hs.2.2.1 _ _ value).2
     have addressB:a.widthsBase+(b.val+1) ≤ L.B:=by
       have h:=banks.widthBelow a (by simp)
       have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.inverseBound;omega
     have radixB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ banks.rows.2.2.1).2
     have endB:=block_end_le_sum a.geometry.widths b
     have rd:readable advanceBlock (setPC s 119):=by
       simp[readable,advanceBlock,Op.readable,Op.apply,setPC,writeNat,next,
         hc.2.1,cache.widths,hb,value]
     have pk:peak advanceBlock (setPC s 119) ≤ L.B:=by
       simp[peak,advanceBlock,Op.peak,Op.apply,setPC,writeNat,next,
         hc.2.1,cache.widths,hb,hbefore,hq,value]
       simp only[List.get_eq_getElem] at widthB endB
       omega
     have run:=normalize_bounded n L.B x s hpc L.code hs rd pk
     have nr:normalized s=setPC (applyBlock advanceBlock (setPC s 119)) 43:=by
       simp only[normalized,ite_eq_left go,ite_eq_right beyond]
     have f:Frame s (normalized s):=by
       rw[nr]
       exact (block_frame 606 advanceBlock (setPC s 119) (by decide)).frame (by omega)
     refine ⟨run,hh.transport L s _ f,?_,?_,?_,?_,?_,?_,f⟩
     · rw[nr];exact body_constants advanceBlock (setPC s 119) hc (by decide)
     · rw[nr]
       constructor <;> simp[applyBlock,advanceBlock,Op.apply,setPC,writeNat,next,
         cur.depth,cur.start,cur.width,cur.offset,cur.original,cur.count]
     · rw[nr]
       constructor <;> simp[applyBlock,advanceBlock,Op.apply,setPC,writeNat,next,
         cache.count,cache.widths,cache.radix,cache.permutation,cache.tail]
     · intro _
       refine ⟨c,⟨0,qpos⟩,?_,?_,?_,?_,?_,?_⟩
       · change blockBefore a.geometry.widths b+t.val+1=(a.geometry.widths.take (b.val+1)).sum+0
         have ht:=t.isLt;omega
       all_goals rw[nr]
       all_goals simp[applyBlock,advanceBlock,Op.apply,setPC,writeNat,next,
         hc.2.1,cache.widths,hi,hb,hbefore,hq,value,c,blockBefore,beforeNext]
     · rw[nr];rfl
     · rw[nr];exact readOnly_heap advanceBlock (setPC s 119) (by simp[advanceBlock])
 · have stop:¬s.natReg 625 < s.natReg 622:=by rw[hi,cache.radix];exact hnext
   have nr:normalized s=setPC s 43:=by simp only[normalized,ite_eq_right stop]
   have run:BoundedRuns program n x L.B s 1 (setPC s 43):=.next hs
     (by simp[UniformMachine.step,hpc,normalize_index_branch,stop,setPC])
     (.refl (changePC_bound L.B s 43 hs (by have h:=L.code;omega)))
   rw[nr]
   exact ⟨by simpa only[normalizeCost,ite_eq_right stop] using run,header_setPC L s 43 hh,hc,cursor_setPC depth count st s 43 cur,cache_setPC a as s 43 cache,
     fun h=> False.elim (hnext h),rfl,rfl,⟨rfl,rfl,rfl,rfl,fun _ _=> rfl⟩⟩


/-- Logical reference only: every descent, return, normalization and branch
in this evaluator is matched to charged literal bytecode below. -/
def children (visit:State → State):ℕ → State → State
 | 0,s=>
   setPC s 83
 | k+1,s=>
   children visit k (normalized (popped (visit (child s))))
def tree:List PhysicalAxis → State → State
 | [],s=>
   leaf s
 | a::as,s=>
   children (tree as) a.geometry.widths.sum (entered s)
def treeBudget:List ℕ → ℕ
 | []=>
   6
 | r::rs=>
   20+r*(treeBudget rs+77)

theorem tree_budget_balance (rs:List ℕ):treeBudget rs+77+14*rs.prod=97*nodeCount rs:=by
 induction rs with
 | nil=>
   simp[treeBudget,nodeCount]
 | cons r rs ih=>
   simp only[treeBudget,List.prod_cons,nodeCount];nlinarith

theorem tree_budget_bound (as:List PhysicalAxis):
 treeBudget (radices (physicalAxes as)) < 194*physicalVolume as:=by
 have nodes:=flat_visit_bound (physicalAxes as) initialPacking
 rw[run_visits,flatLayers_radices] at nodes
 have balance:=tree_budget_balance (radices (physicalAxes as))
 change treeBudget (radices (physicalAxes as)) < 194*(radices (physicalAxes as)).prod
 omega

structure LoopEffect (a:PhysicalAxis) (as:List PhysicalAxis) (depth count i k:ℕ)
 (st:PackingState) (L:Layout) (s t:State):Prop where
 pc:t.pc=83
 header:Header L t
 constants:Constants t
 cursor:Cursor depth (count+k*physicalVolume as) st t
 frame:Frame s t
 natFrame:∀addr,(addr < L.stack+depth*9 ∨ L.stack+L.ell*9 ≤ addr) → (∀(p:BlockPosition a.geometry.widths) (ds:LocalDigits (physicalAxes as)),
     i ≤ (blockEquiv a.geometry.widths p).val → (blockEquiv a.geometry.widths p).val < i+k → addr ≠ L.inverse+target (physicalAxes (a::as)) st (p,ds)) → t.natHeap addr=s.natHeap addr
 addresses:∀(p:BlockPosition a.geometry.widths) (ds:LocalDigits (physicalAxes as)),
   i ≤ (blockEquiv a.geometry.widths p).val → (blockEquiv a.geometry.widths p).val < i+k → t.natHeap (L.inverse+target (physicalAxes (a::as)) st (p,ds))=
     some (native (physicalAxes (a::as)) st (p,ds))

def PhysicalTree (visit:State → State) (as:List PhysicalAxis):Prop:=
 ∀(L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:PackingState) (s:State),
 depth+as.length=L.ell → Header L s → Constants s → Cursor depth count st s → Banks as depth L s → Fits as st count L → s.pc=24 → WordBound L.B s → ∃ticks,ticks ≤ treeBudget (radices (physicalAxes as)) ∧ BoundedRuns program n x L.B s ticks (visit s) ∧ Effect as depth count st L s (visit s)

theorem fits_zero (as:List PhysicalAxis) (st:PackingState) (count:ℕ) (L:Layout)
 (h:Fits as st count L):Fits as st 0 L:=
 ⟨h.1,h.2.1,h.2.2.1,by have h':=h.2.2.2;omega⟩

/-- The recursive proof consumes only physical bank presence and the actual
stack written by descent. It assumes no supplied visited-address certificate. -/
theorem physical_children (visit:State → State) (as:List PhysicalAxis) (hv:PhysicalTree visit as)
 (a:PhysicalAxis) (L:Layout) (n depth count i k:ℕ) (x:Fin n → ℂ) (st:PackingState) (s:State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (banks:Banks (a::as) depth L s)
 (hgeo:Fits (a::as) st 0 L) (hik:i+k=a.geometry.widths.sum)
 (hcount:count+k*physicalVolume as ≤ L.total) (cache:Cache a as s)
 (index:s.natReg 625=i) (localCursor:i < a.geometry.widths.sum → Local a i s)
 (hpc:s.pc=43) (hs:WordBound L.B s):
 ∃ticks,ticks ≤ 1+k*(treeBudget (radices (physicalAxes as))+77) ∧ BoundedRuns program n x L.B s ticks (children visit k s) ∧ LoopEffect a as depth count i k st L s (children visit k s):=by
 induction k generalizing s count i with
 | zero=>
   have stop:¬s.natReg 625 < s.natReg 622:=by rw[index,cache.radix];omega
   have run:BoundedRuns program n x L.B s 1 (setPC s 83):=.next hs
     (by simp[UniformMachine.step,hpc,child_branch,stop,setPC])
     (.refl (changePC_bound L.B s 83 hs (by have h:=L.code;omega)))
   refine ⟨1,by simp,run,?_,⟩
   refine ⟨rfl,header_setPC L s 83 hh,hc,?_,⟨rfl,rfl,rfl,rfl,fun _ _=> rfl⟩,
     fun _ _ _=> rfl,?_⟩
   · simpa only[children,Nat.zero_mul,Nat.add_zero] using cursor_setPC depth count st s 83 cur
   · intro p ds h0 h1;omega
 | succ k ih=>
   obtain ⟨b,t,ord,jj,bi,before,role,width⟩:=localCursor (by omega)
   have jb:(blockEquiv a.geometry.widths ⟨b,t⟩).val=i:=ord.symm
   have depthBound:depth < L.ell:=by simp only[List.length_cons] at hlen;omega
   have cBound:count+physicalVolume as ≤ L.total:=by
     have h:physicalVolume as ≤ (k+1)*physicalVolume as:=by
       simpa only[Nat.one_mul] using Nat.mul_le_mul_right (physicalVolume as) (show 1 ≤ k+1 by omega)
     omega
   obtain ⟨descent,ch,cc,cp,saved,foot,cpc⟩:=child_actual a as L n depth count x st b t s
     hlen hh hc cur banks hgeo cache (by rw[jj,ord]) bi before role width hpc hs
   have cb:Banks (a::as) depth L (child s):=banks_transfer (a::as) depth L s _
     (by omega) banks (fun addr haddr=> foot addr (Or.inl (by omega)))
   let cs:=packingStep (blockDigit a.geometry.widths b t (physicalVolume as) a.geometry.originalPermutation) st
   have geometry:=fits_child a as st 0 ⟨b,t⟩ L hgeo
   have fits:Fits as cs count L:=⟨geometry.1,geometry.2.1,geometry.2.2.1,cBound⟩
   obtain ⟨subTicks,subBound,sub,e⟩:=hv L n (depth+1) count x cs (child s)
     (by simp only[List.length_cons] at hlen;omega) ch cc cp (banks_tail a as depth L _ cb)
     fits cpc descent.final_bound
   have eb:Banks (a::as) depth L (visit (child s)):=banks_transfer (a::as) depth L _ _
     (by omega) cb (fun addr haddr=> e.natFrame addr (Or.inl (by omega))
       (fun ds=> by have h:=L.stackBelow;omega))
   have keepSaved:Saved L depth (blockBefore a.geometry.widths b+t.val+1) b.val
     (blockBefore a.geometry.widths b) (t.val+1) (a.geometry.widths.get b) st (visit (child s)):=by
     unfold Saved at saved ⊢
     rcases saved with ⟨ss,sw,so,si,sj,sb,sp,sr,sq⟩
     refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
     all_goals apply (e.natFrame _ (Or.inl (by omega)) (fun _=> by have h:=L.stackBelow;omega)).trans
     all_goals assumption
   obtain ⟨ret,rh,rc,rp,rCache,ri,rb,rBefore,rRole,rq,rpc⟩:=pop_actual a as L n depth
     (count+physicalVolume as) (blockBefore a.geometry.widths b+t.val+1) b.val
     (blockBefore a.geometry.widths b) (t.val+1) (a.geometry.widths.get b) x st (visit (child s))
     hlen e.header e.constants e.cursor.depth e.cursor.count keepSaved eb e.pc sub.final_bound
   have rbanks:Banks (a::as) depth L (popped (visit (child s))):=banks_transfer (a::as) depth L _ _
     (by omega) eb (fun addr _=> congrFun (pop_heap _) addr)
   obtain ⟨norm,nh,nc,np,ncache,nlocal,npc,nheap,nframe⟩:=normalize_actual a as L n depth
     (count+physicalVolume as) x st b t (popped (visit (child s))) rh rc rp rbanks rCache
     ri rb rBefore rRole rq rpc ret.final_bound
   let u:=normalized (popped (visit (child s)))
   have ubanks:Banks (a::as) depth L u:=banks_transfer (a::as) depth L _ _
     (by omega) rbanks (fun addr _=> congrFun nheap addr)
   have endCount:(count+physicalVolume as)+k*physicalVolume as=count+(k+1)*physicalVolume as:=by ring
   have ni:u.natReg 625=i+1:=
     (normalized_index (popped (visit (child s)))).trans (by simpa only[ord] using ri)
   obtain ⟨restTicks,restBound,rest,f⟩:=ih (count+physicalVolume as) (i+1) u nh nc np ubanks
     (by omega) (by rw[endCount];exact hcount) ncache ni (by simpa only[ord] using nlocal)
     npc norm.final_bound
   have costBound:=normalize_cost_bound (popped (visit (child s)))
   rw[show children visit (k+1) s=children visit k u from rfl]
   refine ⟨35+subTicks+34+normalizeCost (popped (visit (child s)))+restTicks,by nlinarith,?_,?_,⟩
   · simpa only[Nat.add_assoc] using descent.trans (sub.trans (ret.trans (norm.trans rest)))
   · refine ⟨f.pc,f.header,f.constants,?_,
       (blocks_frame s).2.2.2.2.1.trans (e.frame.trans ((blocks_frame _).2.2.2.2.2.2.trans (nframe.trans f.frame))),?_,?_⟩
     · simpa only[endCount] using f.cursor
     · intro addr hstack hout
       rw[f.natFrame addr hstack (fun p ds h0 h1=> hout p ds (by omega) (by omega)),
         congrFun nheap addr,congrFun (pop_heap _) addr,
         e.natFrame addr (by rcases hstack with h|h;exact Or.inl (by omega);exact Or.inr h)
           (fun ds=> by
             have v:=hout ⟨b,t⟩ ds (by simp only[jb,Nat.le_refl]) (by rw[jb];omega)
             change addr≠L.inverse+target (a.geometry::physicalAxes as) st (⟨b,t⟩,ds) at v
             rw[target_cons] at v
             exact v)]
       apply foot addr
       rcases hstack with h|h
       · exact Or.inl h
       · exact Or.inr (by omega)
     · intro p ds h0 h1
       by_cases pi:(blockEquiv a.geometry.widths p).val=i
       · have same:p=⟨b,t⟩:=by apply (blockEquiv a.geometry.widths).injective;apply Fin.ext;omega
         subst p
         have retained:(children visit k u).natHeap
           (L.inverse+target (physicalAxes (a::as)) st (⟨b,t⟩,ds))=
           u.natHeap (L.inverse+target (physicalAxes (a::as)) st (⟨b,t⟩,ds)):=
           f.natFrame _ (Or.inr (by have h:=L.stackBelow;omega)) (by
             intro q es q0 _ eq
             have targets:target (physicalAxes (a::as)) st (⟨b,t⟩,ds)=
               target (physicalAxes (a::as)) st (q,es):=by omega
             have injected:((⟨b,t⟩,ds):LocalDigits (physicalAxes (a::as)))=(q,es):=
               (target_injective _ st st _ _ rfl rfl hgeo.2.1 hgeo.2.1 targets).2
             have qp:⟨b,t⟩=q:=congrArg Prod.fst injected
             rw[←qp,jb] at q0;omega)
         rw[retained,congrFun nheap _,congrFun (pop_heap _) _]
         change (visit (child s)).natHeap
           (L.inverse+target (a.geometry::physicalAxes as) st (⟨b,t⟩,ds))=
           some (native (a.geometry::physicalAxes as) st (⟨b,t⟩,ds))
         rw[target_cons,native_cons]
         exact e.addresses ds
       · exact f.addresses p ds (by omega) (by omega)

theorem physical_tree (as:List PhysicalAxis):PhysicalTree (tree as) as:=by
 induction as with
 | nil=>
   intro L n depth count x st s hlen hh hc cur _ hf hpc hs
   obtain ⟨run,e⟩:=physical_leaf L n depth count x st s hlen hh hc cur hf hpc hs
   exact ⟨6,by rfl,run,e⟩
 | cons a as ih=>
   intro L n depth count x st s hlen hh hc cur hb hf hpc hs
   obtain ⟨entry,eh,ec,ep,cache,localCursor,epc,heap⟩:=enter_actual a as L n depth count x st s
     hlen hh hc cur hb hpc hs
   have banks:Banks (a::as) depth L (entered s):=banks_transfer (a::as) depth L s _
     (by omega) hb (fun addr _=> congrFun heap addr)
   obtain ⟨ticks,bound,loop,e⟩:=physical_children (tree as) as ih a L n depth count 0
     a.geometry.widths.sum x st (entered s) hlen eh ec ep banks (fits_zero _ _ _ _ hf) (by omega)
     (by simpa only[physicalVolume_cons] using hf.2.2.2) cache (by rcases localCursor with ⟨_,_,_,h,_,_,_,_⟩;exact h) (fun _=> localCursor)
     epc entry.final_bound
   refine ⟨19+ticks,by
     change 19+ticks ≤ 20+a.geometry.widths.sum*(treeBudget (radices (physicalAxes as))+77)
     omega,entry.trans loop,?_⟩
   refine ⟨e.pc,e.header,e.constants,?_,(blocks_frame s).2.2.2.1.trans e.frame,?_,?_⟩
   · simpa only[tree,Nat.zero_add,physicalVolume_cons] using e.cursor
   · intro addr hstack hout
     exact (e.natFrame addr hstack (fun p ds _ _=> hout (p,ds))).trans (congrFun heap addr)
   · intro ds
     rcases ds with ⟨p,ds⟩
     exact e.addresses p ds (by omega) (by simpa only[Nat.zero_add] using (blockEquiv a.geometry.widths p).isLt)


/-- A generated inverse-address table; the end-to-end theorem derives it from
physical rows/permutations, rather than accepting it as input. -/
def InverseReady (L:Layout) (e:Equiv.Perm (Fin L.total)) (s:State):Prop:=
 ∀i:Fin L.total,s.natHeap (L.inverse+i.val)=some (e i).val

def SourceReady (L:Layout) (v:Fin L.total→Scalar) (s:State):Prop:=
 ∀i:Fin L.total,s.scalarHeap (L.source+i.val)=some (v i)

def GatherFrame (s t:State):Prop:=t.natHeap=s.natHeap ∧t.outputs=s.outputs ∧t.rootOrders=s.rootOrders ∧
 (∀j,j<606 ∨650 ≤ j ∨j=637 →t.natReg j=s.natReg j) ∧
 (∀j,j≠70 →t.scalarReg j=s.scalarReg j)

theorem GatherFrame.trans {s t u:State} (h:GatherFrame s t) (h':GatherFrame t u):GatherFrame s u:=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   fun j hj=>(h'.2.2.2.1 j hj).trans (h.2.2.2.1 j hj),
   fun j hj=>(h'.2.2.2.2 j hj).trans (h.2.2.2.2 j hj)⟩

def gathered (s:State):State:=setPC (applyBlock gatherBlock (setPC s 128)) 127

theorem gather_frame (s:State):GatherFrame s (gathered s):=by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact readOnly_heap gatherBlock (setPC s 128) (by simp[gatherBlock])
 · simp[gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next]
 · simp[gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next]
 · intro j hj
   simp (disch:=omega) [gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next]
 · intro j hj
   simp[gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next,hj]

theorem gather_header (L:Layout) (s:State) (hh:Header L s):Header L (gathered s):=by
 have f:=gather_frame s
 exact ⟨(f.2.2.2.1 600 (by omega)).trans hh.count,(f.2.2.2.1 601 (by omega)).trans hh.rows,
   (f.2.2.2.1 602 (by omega)).trans hh.suffix,(f.2.2.2.1 603 (by omega)).trans hh.stack,
   (f.2.2.2.1 637 (by simp)).trans hh.inverse,(f.2.2.2.1 604 (by omega)).trans hh.source,
   (f.2.2.2.1 605 (by omega)).trans hh.destination⟩

theorem gather_constants (s:State) (hc:Constants s):Constants (gathered s):=by
 constructor <;> first | exact hc.1 | skip
 all_goals simp[gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next,
   hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2]

theorem gather_branch : program[127]?=some (.branchLT 611 616 128 136):=rfl
theorem gather_jump : program[135]?=some (.jump 127):=rfl

theorem gather_actual (L:Layout) (n j:ℕ) (x:Fin n→ℂ) (e:Equiv.Perm (Fin L.total))
 (v:Fin L.total→Scalar) (s:State) (hj:j<L.total) (hh:Header L s) (hc:Constants s)
 (index:s.natReg 611=j) (count:s.natReg 616=L.total) (hr:InverseReady L e s)
 (hv:SourceReady L v s) (hpc:s.pc=127) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 9 (gathered s) ∧Header L (gathered s) ∧Constants (gathered s) ∧
 (gathered s).natReg 611=j+1 ∧(gathered s).natReg 616=L.total ∧(gathered s).pc=127 ∧
 (gathered s).scalarHeap=Function.update s.scalarHeap (L.destination+j) (some (v (e ⟨j,hj⟩))):=by
 let i:Fin L.total:=⟨j,hj⟩
 have perm:s.natHeap (L.inverse+j)=some (e i).val:=hr i
 have src:s.scalarHeap (L.source+(e i).val)=some (v (e i)):=hv (e i)
 have ii: (e i).val<L.total:=(e i).isLt
 have invB:=L.inverseBound
 have sourceB:=L.sourceBelow
 have destB:=L.destinationBound
 have totalB:=L.volumeBound
 have rd:readable gatherBlock (setPC s 128):=by
   simp[readable,gatherBlock,Op.readable,Op.apply,setPC,writeNat,next,
     hh.inverse,hh.source,index,perm,src]
 have pk:peak gatherBlock (setPC s 128) ≤ L.B:=by
   simp[peak,gatherBlock,Op.peak,Op.apply,setPC,writeNat,writeScalar,next,
     hc.2.1,hh.inverse,hh.source,hh.destination,index,perm,src]
   omega
 have run:BoundedRuns program n x L.B s 9 (gathered s):=by
   simpa only[gathered,gather_length] using branch_block gatherBlock 128 127 135 127 128 136 611 616
     n L.B x s gather_code gather_branch gather_jump (by have h:=L.code;omega) rfl
     (by rw[gather_length];have h:=L.code;omega) hpc (by rw[index,count];simp only[ite_eq_left hj]) rd pk hs
 refine ⟨run,gather_header L s hh,gather_constants s hc,?_,?_,rfl,?_⟩
 all_goals simp[gathered,applyBlock,gatherBlock,Op.apply,setPC,writeNat,writeScalar,next,
   hc.2.1,hh.inverse,hh.source,hh.destination,index,count,perm,src,i]

def gatherLoop:ℕ→State→State
 | 0,s=>setPC s 136
 | k+1,s=>gatherLoop k (gathered s)

theorem gather_loop (L:Layout) (n j k:ℕ) (x:Fin n→ℂ) (e:Equiv.Perm (Fin L.total))
 (v:Fin L.total→Scalar) (s:State) (hjk:j+k=L.total) (hh:Header L s) (hc:Constants s)
 (index:s.natReg 611=j) (count:s.natReg 616=L.total) (hr:InverseReady L e s)
 (hv:SourceReady L v s) (hpc:s.pc=127) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s (9*k+1) (gatherLoop k s) ∧Header L (gatherLoop k s) ∧
 Constants (gatherLoop k s) ∧(gatherLoop k s).natReg 611=L.total ∧(gatherLoop k s).pc=136 ∧
 GatherFrame s (gatherLoop k s) ∧
 (∀i:Fin L.total,j ≤ i.val →(gatherLoop k s).scalarHeap (L.destination+i.val)=some (v (e i))) ∧
 (∀addr,addr<L.destination+j ∨L.destination+(j+k) ≤ addr →(gatherLoop k s).scalarHeap addr=s.scalarHeap addr):=by
 induction k generalizing j s with
 | zero=>
   have stop:¬s.natReg 611<s.natReg 616:=by rw[index,count];omega
   have run:BoundedRuns program n x L.B s 1 (setPC s 136):=.next hs
     (by simp[UniformMachine.step,hpc,gather_branch,stop,setPC])
     (.refl (changePC_bound L.B s 136 hs (by have h:=L.code;omega)))
   refine ⟨run,header_setPC L s 136 hh,hc,?_,rfl,
     ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩,?_,fun _ _=>rfl⟩
   · simpa only[gatherLoop,setPC,Nat.add_zero] using index.trans (show j=L.total by omega)
   · intro i h;have hi:=i.isLt;omega
 | succ k ih=>
   have hj:j<L.total:=by omega
   obtain ⟨one,oh,oc,oi,ct,opc,heap⟩:=gather_actual L n j x e v s hj hh hc index count hr hv hpc hs
   have f:=gather_frame s
   have ri:InverseReady L e (gathered s):=by intro i;rw[f.1];exact hr i
   have vi:SourceReady L v (gathered s):=by
     intro i
     rw[heap,Function.update_of_ne (by have h:=L.sourceBelow;have hi:=i.isLt;omega)]
     exact hv i
   obtain ⟨rest,rh,rc,idx,pc,rf,values,outside⟩:=ih (j+1) (gathered s) (by omega) oh oc oi ct ri vi opc one.final_bound
   rw[gatherLoop]
   refine ⟨by simpa only[show 9+(9*k+1)=9*(k+1)+1 by omega] using one.trans rest,
     rh,rc,idx,pc,f.trans rf,?_,?_⟩
   · intro i h0
     by_cases eq:i.val=j
     · rw[outside _ (Or.inl (by omega)),heap,eq,Function.update_self]
       have ii:i=⟨j,hj⟩:=Fin.ext eq
       rw[ii]
     · exact values i (by omega)
   · intro addr haddr
     rw[outside addr (by rcases haddr with h|h;exact Or.inl (by omega);exact Or.inr (by omega)),heap,
       Function.update_of_ne (by rcases haddr with h|h <;> omega)]


/-- The canonical inverse permutation in the caller's actual volume type. -/
def physicalUnpacking (as:List PhysicalAxis) (L:Layout) (hvolume:physicalVolume as=L.total):
 Equiv.Perm (Fin L.total):=
 (finCongr hvolume).symm.trans ((unpackingPermutation (physicalAxes as)).trans (finCongr hvolume))

theorem inverse_of_effect (as:List PhysicalAxis) (L:Layout) (hvolume:physicalVolume as=L.total)
 (s t:State) (e:Effect as 0 0 initialPacking L s t):
 InverseReady L (physicalUnpacking as L hvolume) t:=by
 intro i
 let i0:Fin (physicalVolume as):=(finCongr hvolume).symm i
 let sp:SectorPosition (physicalAxes as):=(packedEquiv (physicalAxes as)).symm i0
 let ds:LocalDigits (physicalAxes as):=combine (physicalAxes as) sp
 have sep:separate (physicalAxes as) ds=sp:=separate_combine _ sp
 obtain ⟨ni,ti⟩:=flat_action (physicalAxes as) ds
 change native (physicalAxes as) initialPacking ds=(originalEquiv (physicalAxes as) (separate _ ds)).val at ni
 change target (physicalAxes as) initialPacking ds=(packedEquiv (physicalAxes as) (separate _ ds)).val at ti
 rw[sep] at ni ti
 have targetEq:target (physicalAxes as) initialPacking ds=i.val:=by
   have castVal:i0.val=i.val:=rfl
   have ti0:target (physicalAxes as) initialPacking ds=i0.val:=by
     simpa only[sp,Equiv.apply_symm_apply] using ti
   exact ti0.trans castVal
 have nativeEq:native (physicalAxes as) initialPacking ds=(physicalUnpacking as L hvolume i).val:=by
   rw[ni]
   rfl
 rw[←targetEq,e.addresses,nativeEq]

theorem initialized_properties (L:Layout) (s:State) (hh:Header L s) (hc:Constants s)
 (hd:s.natReg 611=0):
 Header L (initialized s)  ∧ Constants (initialized s)  ∧ Cursor 0 0 initialPacking (initialized s)  ∧
 (initialized s).pc=24  ∧ (initialized s).natHeap=s.natHeap:=by
 refine ⟨hh.transport L s _ (blocks_frame s).2.2.1,
   body_constants treeBoot (setPC s 19) hc (by decide),?_,?_,?_⟩
 · constructor <;> simp[initialized,setPC,applyBlock,treeBoot,Op.apply,writeNat,next,initialPacking,hd]
 · rw[initialized,applyBlock_pc,treeBoot_length];rfl
 · exact readOnly_heap treeBoot (setPC s 19) (by simp[treeBoot])

theorem initialize_bounded (L:Layout) (n:ℕ) (x:Fin n → ℂ) (s:State)
 (hc:Constants s) (hd:s.natReg 611=0) (hpc:s.pc=9) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 6 (initialized s):=by
 let u:=setPC s 19
 have ub:WordBound L.B u:=changePC_bound L.B s 19 hs (by have h:=L.code;omega)
 have first:BoundedRuns program n x L.B s 1 u:=.next hs
   (by simp[UniformMachine.step,hpc,suffix_branch,hc.1,hd,u,setPC]) (.refl ub)
 have body:=block_runs treeBoot program 19 n L.B x u treeBoot_code rfl ub
   (by rw[treeBoot_length];have h:=L.code;omega)
   (by simp[readable,treeBoot,Op.readable])
   (by simp[peak,treeBoot,Op.peak];have h:=L.code;omega)
 simpa only[treeBoot_length,initialized,u] using first.trans body

def startGather (s:State):State:=writeNat (setPC s 126) 611 0

theorem gather_start (L:Layout) (n:ℕ) (x:Fin n → ℂ) (s:State) (hc:Constants s)
 (hd:s.natReg 611=0) (hpc:s.pc=83) (hs:WordBound L.B s):
 BoundedRuns program n x L.B s 3 (startGather s)  ∧ Frame s (startGather s)  ∧
 (startGather s).pc=127  ∧ (startGather s).natReg 611=0  ∧
 (startGather s).natReg 616=s.natReg 616  ∧ (startGather s).natHeap=s.natHeap:=by
 have b125:=changePC_bound L.B s 125 hs (by have h:=L.code;omega)
 have first:BoundedRuns program n x L.B s 1 (setPC s 125):=.next hs
   (by simp[UniformMachine.step,hpc,pop_branch,hc.1,hd,setPC]) (.refl b125)
 have second:BoundedRuns program n x L.B (setPC s 125) 1 (setPC s 126):=.next b125
   (by rw[UniformMachine.step];rfl)
   (.refl (changePC_bound L.B s 126 hs (by have h:=L.code;omega)))
 have sb:WordBound L.B (startGather s):=writeNat_bound L.B (setPC s 126) 611 0
   second.final_bound (by change 126+1 ≤ L.B;have h:=L.code;omega) (by omega)
 have third:BoundedRuns program n x L.B (setPC s 126) 1 (startGather s):=.next second.final_bound
   (by rw[UniformMachine.step];rfl) (.refl sb)
 refine ⟨first.trans (second.trans third),?_,rfl,?_,?_,rfl⟩
 · refine ⟨rfl,rfl,rfl,rfl,?_⟩
   intro j hj
   simp (disch:=omega) [startGather,writeNat,next,setPC]
 · simp[startGather,writeNat,next,setPC]
 · simp[startGather,writeNat,next,setPC]

/-- Precise frames cover all untouched Nat cells, including source widths and
forward local permutations, and all untouched Scalar cells/actual tags. -/
def OutsideAllocation (L:Layout) (s t:State):Prop:=
 ∀addr,(addr < L.suffix  ∨ L.suffix+L.ell+1  ≤  addr)  →
   (addr < L.stack  ∨ L.stack+9*L.ell  ≤  addr)  →
   (addr < L.inverse  ∨ L.inverse+L.total  ≤  addr)  → t.natHeap addr=s.natHeap addr

def FinalFrame (s t:State):Prop:=
 t.outputs=s.outputs  ∧ t.rootOrders=s.rootOrders  ∧
 (∀j,j < 606  ∨ 650  ≤  j  ∨ j=637  → t.natReg j=s.natReg j)  ∧
 (∀j,j ≠ 70  → t.scalarReg j=s.scalarReg j)

theorem packed_target_bound (as:List PhysicalAxis) (ds:LocalDigits (physicalAxes as)):
 target (physicalAxes as) initialPacking ds < physicalVolume as:=by
 obtain ⟨_,h⟩:=target_bounds (physicalAxes as) initialPacking ds (by decide)
 simpa only[initialPacking,Nat.zero_add,Nat.one_mul] using h

/- Lemma 4.1, (4.3), p. 19: suffix preparation, physical DFS and scalar gather are joined through their actual intermediate states; the final count includes every branch and halt. -/
/-- End-to-end literal execution: computed suffixes, actual forward table
reads, generated inverse-address bank, continuous scalar gather and halt.
Physical input rows/permutation/scalar presence are the only source-bank premises. -/
theorem execution (as:List PhysicalAxis) (L:Layout) (n:ℕ) (x:Fin n → ℂ)
 (v:Fin L.total → Scalar) (s:State) (hlen:as.length=L.ell) (hvolume:physicalVolume as=L.total)
 (hh:Header L s) (rows:Rows as 0 L.rows s) (widths:Widths as s) (perms:Permutations as s)
 (widthBelow:∀a∈as,a.widthsBase+a.geometry.widths.length  ≤  L.suffix)
 (permBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum  ≤  L.suffix)
 (source:SourceReady L v s) (hpc:s.pc=0) (hs:WordBound L.B s):
 ∃t ticks,ticks  ≤  213*L.total+20  ∧ BoundedExecution program n x L.B s ticks t  ∧
 t.pc=136  ∧ InverseReady L (physicalUnpacking as L hvolume) t  ∧
 (∀i:Fin L.total,t.scalarHeap (L.destination+i.val)=some (v (physicalUnpacking as L hvolume i)))  ∧
 (∀addr,addr < L.destination  ∨ L.destination+L.total  ≤  addr  → t.scalarHeap addr=s.scalarHeap addr)  ∧
 OutsideAllocation L s t  ∧ FinalFrame s t:=by
 obtain ⟨u,suffixRun,written,depth,product,upc,constants,header,outside,frame⟩:=
   suffix_preparation as L n x s hlen hvolume hh rows hpc hs
 have banks:Banks as 0 L u:=by
   have low:∀addr,addr < L.suffix  → u.natHeap addr=s.natHeap addr:=fun addr haddr=>outside addr (Or.inl haddr)
   refine ⟨rows_transfer as 0 L s u (by omega) rows low,
     widths_transfer as L s u widths widthBelow low,?_,widthBelow,permBelow,?_⟩
   · intro a ha j
     rw[low _ (by have h:=permBelow a ha;have hj:=j.isLt;omega)]
     exact perms a ha j
   · intro j hj
     simpa only[Nat.add_zero] using written j (by omega) hj
 have initRun:=initialize_bounded L n x u constants depth upc suffixRun.final_bound
 obtain ⟨ih,ic,cur,ipc,heap⟩:=initialized_properties L u header constants depth
 have ibanks:Banks as 0 L (initialized u):=banks_transfer as 0 L u _ (by omega) banks (fun addr _=>congrFun heap addr)
 have fits:Fits as initialPacking 0 L:=by
   simp only[Fits,initialPacking,Nat.zero_add,Nat.one_mul,hvolume]
   exact ⟨by rfl,by decide,by rfl,by rfl⟩
 obtain ⟨treeTicks,treeBound,trun,e⟩:=physical_tree as L n 0 0 x initialPacking (initialized u)
   (by omega) ih ic cur ibanks fits ipc initRun.final_bound
 let w:=tree as (initialized u)
 have before:Frame s w:=frame.trans ((blocks_frame u).2.2.1.trans e.frame)
 have inverse:InverseReady L (physicalUnpacking as L hvolume) w:=inverse_of_effect as L hvolume _ _ e
 have count:w.natReg 616=L.total:=by simpa only[Nat.zero_add,hvolume] using e.cursor.count
 obtain ⟨exit,exitFrame,gpc,gzero,gcount,gheap⟩:=gather_start L n x w e.constants e.cursor.depth e.pc trun.final_bound
 have gHeader:Header L (startGather w):=e.header.transport L w _ exitFrame
 have gConstants:Constants (startGather w):=by
   simpa only[startGather,writeNat,next,setPC,Constants,Function.update_of_ne (by decide:606 ≠ 611),
     Function.update_of_ne (by decide:607 ≠ 611),Function.update_of_ne (by decide:608 ≠ 611),
     Function.update_of_ne (by decide:609 ≠ 611),Function.update_of_ne (by decide:610 ≠ 611)] using e.constants
 have gi:InverseReady L (physicalUnpacking as L hvolume) (startGather w):=by intro i;rw[gheap];exact inverse i
 have gs:SourceReady L v (startGather w):=by intro i;rw[exitFrame.1,before.1];exact source i
 obtain ⟨gather,gh,gc,idx,tpc,gframe,values,gOutside⟩:=gather_loop L n 0 L.total x
   (physicalUnpacking as L hvolume) v (startGather w) (by omega) gHeader gConstants gzero
   (gcount.trans count) gi gs gpc exit.final_bound
 let t:=gatherLoop L.total (startGather w)
 have run:=suffixRun.trans (initRun.trans (trun.trans (exit.trans gather)))
 have halt:step program n x t=.halted t:=by rw[step,tpc];rfl
 have hb:=tree_budget_bound as
 have length:=axis_count_bound as
 have totalTicks:(10*L.ell+9)+(6+(treeTicks+(3+(9*L.total+1))))+1  ≤  213*L.total+20:=by
   rw[hlen] at length
   rw[hvolume] at hb length
   omega
 refine ⟨t,_,totalTicks,?_,tpc,?_,fun i=>values i (by omega),?_,?_,?_⟩
 · exact run.executes (.halt run.final_bound halt)
 · intro i
   rw[gframe.1,gheap]
   exact inverse i
 · intro addr haddr
   rw[gOutside addr (by simpa only[Nat.zero_add,Nat.add_zero] using haddr),exitFrame.1,before.1]
 · intro addr hSuffix hStack hInverse
   rw[gframe.1,gheap,
     e.natFrame addr (by simpa only[Nat.zero_mul,Nat.add_zero,Nat.mul_comm] using hStack)
       (fun ds=>by
         have bound:=packed_target_bound as ds
         rw[hvolume] at bound
         rcases hInverse with h|h <;> omega),congrFun heap addr]
   exact outside addr hSuffix
 · have overall:=before.trans exitFrame
   exact ⟨gframe.2.1.trans overall.2.2.1,gframe.2.2.1.trans overall.2.2.2.1,
     fun j hj=>(gframe.2.2.2.1 j hj).trans (overall.2.2.2.2 j hj),
     fun j hj=>(gframe.2.2.2.2 j hj).trans (congrFun overall.2.1 j)⟩

/-- The final values in `execution` are exactly the paper's packing action,
transported only through the supplied equality of physical array lengths. -/
theorem physicalUnpacking_packArray {a:Type*} (as:List PhysicalAxis) (L:Layout)
 (hvolume:physicalVolume as=L.total) (v:Fin L.total → a) (i:Fin L.total):
 v (physicalUnpacking as L hvolume i)=
   packArray (physicalAxes as) (fun j=>v (finCongr hvolume j)) ((finCongr hvolume).symm i):=rfl

theorem protected_prefix (L:Layout) (s t:State) (h:OutsideAllocation L s t)
 (i:ℕ) (hi:i < L.suffix):t.natHeap i=s.natHeap i:=
 h i (Or.inl hi) (Or.inl (by have b:=L.suffixBelow;omega))
   (Or.inl (by have b:=L.suffixBelow;have c:=L.stackBelow;omega))

theorem saved_registers (s t:State) (h:FinalFrame s t) (i:ℕ) (hi:100 ≤ i ∧ i ≤ 106):
 t.natReg i=s.natReg i:=h.2.2.1 i (Or.inl (by omega))

/-- Linear allocation envelope for suffixes, stack, generated inverse bank
and a fresh scalar result. Existing dirty words retain the same ambient B. -/
def wordBudget (natEnd scalarSource:ℕ) (as:List PhysicalAxis):ℕ:=
 natEnd+scalarSource+10*as.length+3*physicalVolume as+138

theorem wordBudget_linear (natEnd scalarSource:ℕ) (as:List PhysicalAxis):
 wordBudget natEnd scalarSource as ≤ natEnd+scalarSource+13*physicalVolume as+138:=by
 have h:=axis_count_bound as
 unfold wordBudget
 omega

def allocatedLayout (as:List PhysicalAxis) (rows natEnd scalarSource B:ℕ)
 (hr:rows+4*as.length ≤ natEnd) (hB:wordBudget natEnd scalarSource as ≤ B):Layout where
 ell:=as.length
 rows:=rows
 suffix:=natEnd
 stack:=natEnd+as.length+1
 inverse:=natEnd+10*as.length+1
 source:=scalarSource
 destination:=scalarSource+physicalVolume as
 total:=physicalVolume as
 B:=B
 code:=by unfold wordBudget at hB;omega
 rowsBelow:=hr
 suffixBelow:=by omega
 stackBelow:=by omega
 inverseBound:=by unfold wordBudget at hB;omega
 sourceBelow:=by omega
 destinationBound:=by unfold wordBudget at hB;omega
 volumeBound:=by unfold wordBudget at hB;omega

def copyOnly:Instruction → Bool
 | .natLiteral _ _ | .natBinary _ _ _ _ | .loadNat _ _ | .storeNat _ _ |
   .loadScalar _ _ | .storeScalar _ _ | .branchLT _ _ _ _ | .jump _ | .halt=>true
 | _=>false

/-- The bytecode performs only Nat arithmetic and exact scalar load/store;
it neither computes a scalar nor changes its dependency flag. -/
theorem no_scalar_arithmetic_input_root_output:∀i∈program,copyOnly i=true:=by
 simp [program,copyOnly,suffixBoot,suffixBody,treeBoot,enterBlock,childBlock,
   childSave,childStep,leafBlock,popBlock,popSaved,popRow,advanceBlock,gatherBlock,Op.code]

end

end ExactFourierCircuits.UniformSectorPackingMachine
