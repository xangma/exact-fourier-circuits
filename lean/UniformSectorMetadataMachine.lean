import UniformSectorPacking
import UniformSectorTraversalOrder
import UniformTensorMonomialMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorMetadataMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)
open UniformSectorPacking (BlockState)
open scoped BigOperators

/-- Caller Nat450=axes,451=axis rows,452=fresh suffix bank,453=fresh
five-word stack,454=fresh three-word sector directory. Scratch455..478 only.
No scalar, input, root, or output instruction occurs. -/
def suffixBoot : List Op := [.literal 455 0,.literal 456 1,.literal 457 2,
 .literal 458 3,.literal 459 5,.add 460 450 455,.literal 462 1,
 .add 465 452 460,.putNat 465 462]
def suffixBody : List Op := [.sub 460 460 456,.mul 466 460 458,
 .add 465 451 466,.add 465 465 457,.getNat 472 465,
 .mul 462 462 472,.add 465 452 460,.putNat 465 462]
def treeBoot : List Op := [.literal 461 0,.literal 462 1,.literal 463 0,.literal 464 0]
def enterBlock : List Op := [.mul 466 460 458,.add 465 451 466,
 .getNat 467 465,.add 465 465 456,.getNat 468 465,
 .add 465 452 460,.add 465 465 456,.getNat 469 465,
 .literal 470 0,.literal 471 0]
def childBlock : List Op := [.add 465 468 470,.getNat 472 465,
 .mul 473 460 459,.add 473 453 473,.add 465 473 455,.putNat 465 461,
 .add 465 465 456,.putNat 465 462,.add 465 465 456,.putNat 465 463,
 .add 465 465 456,.add 466 470 456,.putNat 465 466,
 .add 465 465 456,.add 466 471 472,.putNat 465 466,
 .mul 466 462 471,.mul 466 466 469,.add 461 461 466,
 .mul 462 462 472,.sub 466 472 456,.add 463 463 466,.add 460 460 456]
def leafBlock : List Op := [.mul 466 464 458,.add 465 454 466,.putNat 465 461,
 .add 465 465 456,.putNat 465 462,.add 465 465 456,.putNat 465 463,
 .add 464 464 456]
def popBlock : List Op := [.sub 460 460 456,.mul 473 460 459,.add 473 453 473,
 .add 465 473 455,.getNat 461 465,.add 465 465 456,.getNat 462 465,
 .add 465 465 456,.getNat 463 465,.add 465 465 456,.getNat 470 465,
 .add 465 465 456,.getNat 471 465,
 .mul 466 460 458,.add 465 451 466,.getNat 467 465,
 .add 465 465 456,.getNat 468 465,.add 465 452 460,.add 465 465 456,.getNat 469 465]

def program : Program := suffixBoot.map Op.code ++ [.branchLT 455 460 10 19] ++
 suffixBody.map Op.code ++ [.jump 9] ++ treeBoot.map Op.code ++
 [.branchLT 460 450 24 59] ++ enterBlock.map Op.code ++ [.branchLT 470 467 35 68] ++
 childBlock.map Op.code ++ [.jump 23] ++ leafBlock.map Op.code ++ [.jump 68] ++
 [.branchLT 455 460 69 91] ++ popBlock.map Op.code ++ [.jump 34,.halt]

theorem suffixBoot_length : suffixBoot.length=9 := rfl
theorem suffixBody_length : suffixBody.length=8 := rfl
theorem treeBoot_length : treeBoot.length=4 := rfl
theorem enter_length : enterBlock.length=10 := rfl
theorem child_length : childBlock.length=23 := rfl
theorem leaf_length : leafBlock.length=8 := rfl
theorem pop_length : popBlock.length=21 := rfl
theorem program_length : program.length=92 := rfl
theorem suffix_branch : program[9]?=some (.branchLT 455 460 10 19) := rfl
theorem suffix_jump : program[18]?=some (.jump 9) := rfl
theorem entry_branch : program[23]?=some (.branchLT 460 450 24 59) := rfl
theorem child_branch : program[34]?=some (.branchLT 470 467 35 68) := rfl
theorem child_jump : program[58]?=some (.jump 23) := rfl
theorem leaf_jump : program[67]?=some (.jump 68) := rfl
theorem pop_branch : program[68]?=some (.branchLT 455 460 69 91) := rfl
theorem pop_jump : program[90]?=some (.jump 34) := rfl
theorem halt_at : program[91]?=some .halt := rfl

theorem suffixBoot_code : BlockAt suffixBoot program 0 := by
 intro i hi;change i<9 at hi;interval_cases i <;> rfl
theorem suffixBody_code : BlockAt suffixBody program 10 := by
 intro i hi;change i<8 at hi;interval_cases i <;> rfl
theorem treeBoot_code : BlockAt treeBoot program 19 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem enter_code : BlockAt enterBlock program 24 := by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
theorem child_code : BlockAt childBlock program 35 := by
 intro i hi;change i<23 at hi;interval_cases i <;> rfl
theorem leaf_code : BlockAt leafBlock program 59 := by
 intro i hi;change i<8 at hi;interval_cases i <;> rfl
theorem pop_code : BlockAt popBlock program 69 := by
 intro i hi;change i<21 at hi;interval_cases i <;> rfl

noncomputable section

def suffixInitialized (s : State) : State := applyBlock suffixBoot s
def suffixIteration (s : State) : State := setPC (applyBlock suffixBody (setPC s 10)) 9
def initialized (s : State) : State := applyBlock treeBoot (setPC s 19)
def entered (s : State) : State := applyBlock enterBlock (setPC s 24)
def child (s : State) : State := setPC (applyBlock childBlock (setPC s 35)) 23
def leaf (s : State) : State := setPC (applyBlock leafBlock (setPC s 59)) 68
def popped (s : State) : State := setPC (applyBlock popBlock (setPC s 69)) 34

def children (visit : State → State) : ℕ → State → State
 | 0,s=>setPC s 68
 | k+1,s=>children visit k (popped (visit (child s)))
def tree : List ℕ → State → State
 | [],s=>leaf s
 | r::rs,s=>children (tree rs) r (entered s)
def treeCost : List ℕ → ℕ
 | []=>10
 | r::rs=>12+r*(treeCost rs+48)

theorem treeCost_balance (rs : List ℕ) :
 treeCost rs+48+2*rs.prod=60*UniformTraversal.nodeCount rs := by
 induction rs with
 | nil => norm_num [treeCost,UniformTraversal.nodeCount]
 | cons r rs ih =>
  simp only [treeCost,UniformTraversal.nodeCount,List.prod_cons]
  calc
  12+r*(treeCost rs+48)+48+2*(r*rs.prod)
   =60+r*(treeCost rs+48+2*rs.prod):=by ring
  _=60*(1+r*UniformTraversal.nodeCount rs):=by rw [ih];ring

/-- Physical axis records contain count,width-bank base,actual radix.
Only these records and the width cells are initial data; suffixes and sectors
are generated by the program. The local permutation is irrelevant here. -/
structure Axis where
 geometry : UniformSectorPacking.Axis
 widthsBase : ℕ
abbrev axes (as : List Axis) := as.map Axis.geometry
abbrev volume (as : List Axis) := (UniformSectorPacking.radices (axes as)).prod

def Rows (as : List Axis) (depth base : ℕ) (s : State) : Prop := match as with
 | []=>True
 | a::tail=>s.natHeap (base+3*depth)=some a.geometry.widths.length ∧
  s.natHeap (base+3*depth+1)=some a.widthsBase ∧
  s.natHeap (base+3*depth+2)=some a.geometry.widths.sum ∧Rows tail (depth+1) base s

def Widths (as : List Axis) (s : State) : Prop :=
 ∀a∈as,∀j:Fin a.geometry.widths.length,
  s.natHeap (a.widthsBase+j.val)=some (a.geometry.widths.get j)
structure Layout where
 ell : ℕ
 rows : ℕ
 suffix : ℕ
 stack : ℕ
 directory : ℕ
 total : ℕ
 B : ℕ
 code : 92 ≤ B
 rowsBelow : rows+3*ell ≤ suffix
 suffixBelow : suffix+ell+1 ≤ stack
 stackBelow : stack+5*ell ≤ directory
 directoryBound : directory+3*total ≤ B
 volumeBound : total ≤ B
structure Header (L : Layout) (s : State) : Prop where
 count : s.natReg 450=L.ell
 rows : s.natReg 451=L.rows
 suffix : s.natReg 452=L.suffix
 stack : s.natReg 453=L.stack
 directory : s.natReg 454=L.directory

def Frame (s t : State) : Prop := t.scalarHeap=s.scalarHeap ∧t.scalarReg=s.scalarReg ∧
 t.outputs=s.outputs ∧t.rootOrders=s.rootOrders ∧
 ∀j,j<455 ∨479 ≤ j → t.natReg j=s.natReg j

def Constants (s : State) : Prop := s.natReg 455=0 ∧s.natReg 456=1 ∧
 s.natReg 457=2 ∧s.natReg 458=3 ∧s.natReg 459=5

def cursor (s : State) : BlockState := ⟨s.natReg 461,s.natReg 462,s.natReg 463⟩



theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun i hi=>(h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩
theorem Header.transport (L : Layout) (s t : State) (h:Header L s) (hf:Frame s t) : Header L t :=
 ⟨(hf.2.2.2.2 450 (by omega)).trans h.count,(hf.2.2.2.2 451 (by omega)).trans h.rows,
 (hf.2.2.2.2 452 (by omega)).trans h.suffix,(hf.2.2.2.2 453 (by omega)).trans h.stack,
 (hf.2.2.2.2 454 (by omega)).trans h.directory⟩


/-- The range test concerns literal register destinations, not run-time data. -/
def NatWithin (lo : ℕ) : Op → Prop
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _ =>lo ≤ d ∧d<479
 | .putNat _ _ =>True
 | _ =>False
instance natWithinDecidable (lo : ℕ) (o : Op) : Decidable (NatWithin lo o) := by
 cases o <;> unfold NatWithin <;> infer_instance

def RangeFrame (lo : ℕ) (s t : State) : Prop := t.scalarHeap=s.scalarHeap ∧t.scalarReg=s.scalarReg ∧
 t.outputs=s.outputs ∧t.rootOrders=s.rootOrders ∧∀j,j<lo ∨479 ≤ j → t.natReg j=s.natReg j

theorem RangeFrame.trans {lo : ℕ} {s u v : State} (h:RangeFrame lo s u) (h':RangeFrame lo u v) : RangeFrame lo s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun i hi=>(h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩
theorem RangeFrame.frame {lo : ℕ} {s t : State} (h:RangeFrame lo s t) (hl:455 ≤ lo) : Frame s t :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i hi=>h.2.2.2.2 i (by rcases hi with h|h <;> omega)⟩
theorem nat_op_frame (lo : ℕ) (o : Op) (s : State) (h:NatWithin lo o) : RangeFrame lo s (o.apply s) := by
 cases o <;> simp only [NatWithin] at h
 all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
 all_goals intro i hi
 all_goals first | rfl | (simp only [Op.apply,writeNat,next];rw [Function.update_of_ne (by omega)])

theorem block_frame (lo : ℕ) (b : List Op) (s : State) (h:∀o∈b,NatWithin lo o) :
 RangeFrame lo s (applyBlock b s) := by
 induction b generalizing s with
 | nil =>exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | cons o b ih =>
   exact (nat_op_frame lo o s (h o (by simp))).trans
     (ih (o.apply s) (fun t ht=>h t (by simp [ht])))

theorem blocks_frame (s : State) :
 Frame s (suffixInitialized s) ∧Frame s (suffixIteration s) ∧Frame s (initialized s) ∧
 Frame s (entered s) ∧Frame s (child s) ∧Frame s (leaf s) ∧Frame s (popped s) := by
 have boot:=block_frame 455 suffixBoot s (by decide)
 have sb:=block_frame 455 suffixBody (setPC s 10) (by decide)
 have tb:=block_frame 455 treeBoot (setPC s 19) (by decide)
 have ent:=block_frame 455 enterBlock (setPC s 24) (by decide)
 have ch:=block_frame 455 childBlock (setPC s 35) (by decide)
 have lf:=block_frame 455 leafBlock (setPC s 59) (by decide)
 have pp:=block_frame 455 popBlock (setPC s 69) (by decide)
 exact ⟨boot,sb,tb,ent,ch,lf,pp⟩

theorem body_constants (b : List Op) (s : State) (h:Constants s)
 (hb:∀o∈b,NatWithin 460 o) : Constants (applyBlock b s) := by
 have f:=block_frame 460 b s hb
 exact ⟨(f.2.2.2.2 455 (by omega)).trans h.1,(f.2.2.2.2 456 (by omega)).trans h.2.1,
   (f.2.2.2.2 457 (by omega)).trans h.2.2.1,(f.2.2.2.2 458 (by omega)).trans h.2.2.2.1,
   (f.2.2.2.2 459 (by omega)).trans h.2.2.2.2⟩



theorem rows_get (as : List Axis) (d b : ℕ) (s : State) (h:Rows as d b s)
 (i : Fin as.length) :
 s.natHeap (b+3*(d+i.val))=some (as.get i).geometry.widths.length ∧
 s.natHeap (b+3*(d+i.val)+1)=some (as.get i).widthsBase ∧
 s.natHeap (b+3*(d+i.val)+2)=some (as.get i).geometry.widths.sum := by
 induction as generalizing d with
 | nil =>exact Fin.elim0 i
 | cons a tail ih =>
   refine Fin.cases ?_ (fun j=>?_) i
   · exact ⟨h.1,h.2.1,h.2.2.1⟩
   · simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ,show d+(j.val+1)=(d+1)+j.val by omega]
       using ih (d+1) h.2.2.2 j

theorem volume_nil : volume []=1 := rfl
theorem volume_cons (a : Axis) (as : List Axis) :
 volume (a::as)=a.geometry.widths.sum*volume as := rfl

theorem volume_pos (as : List Axis) : 0<volume as := by
 induction as with
 | nil =>decide
 | cons a as ih =>
   rw [volume_cons]
   exact Nat.mul_pos (by have h:=a.geometry.radix_two;omega) ih

theorem volume_tail_le (a : Axis) (as : List Axis) : volume as ≤ volume (a::as) := by
 rw [volume_cons]
 have h:=a.geometry.radix_two
 exact (show volume as=1*volume as by simp).le.trans (Nat.mul_le_mul_right _ (by omega))

theorem volume_drop_le (as : List Axis) (i : ℕ) : volume (as.drop i) ≤ volume as := by
 induction as generalizing i with
 | nil =>simp only [List.drop_nil];rfl
 | cons a as ih =>
   cases i with
   | zero =>rfl
   | succ i =>exact (ih i).trans (volume_tail_le a as)

theorem volume_drop_step (as : List Axis) (i : Fin as.length) :
 volume (as.drop i.val)=(as.get i).geometry.widths.sum*volume (as.drop (i.val+1)) := by
 induction as with
 | nil =>exact Fin.elim0 i
 | cons a as ih =>
   refine Fin.cases ?_ (fun j=>?_) i
   · rfl
   · exact ih j

theorem axis_count_bound (as : List Axis) : as.length+1 ≤ volume as := by
 induction as with
 | nil =>decide
 | cons a as ih =>
   rw [List.length_cons,volume_cons]
   have h:=a.geometry.radix_two
   have hp:=volume_pos as
   nlinarith

def WrittenSuffix (as : List Axis) (L : Layout) (firstIndex : ℕ) (s : State) : Prop :=
 ∀j,firstIndex ≤ j → j ≤ as.length → s.natHeap (L.suffix+j)=some (volume (as.drop j))
def Outside (base len : ℕ) (s t : State) : Prop :=
 ∀i,i<base ∨base+len ≤ i → t.natHeap i=s.natHeap i

theorem Outside.trans {base len : ℕ} {s u v : State} (h:Outside base len s u)
 (h':Outside base len u v) : Outside base len s v :=fun i hi=>(h' i hi).trans (h i hi)

theorem rows_transfer (as : List Axis) (depth : ℕ) (L : Layout) (s t : State)
 (hlen:depth+as.length ≤ L.ell) (h:Rows as depth L.rows s)
 (hf:∀i,i<L.suffix → t.natHeap i=s.natHeap i) : Rows as depth L.rows t := by
 induction as generalizing depth with
 | nil =>trivial
 | cons a as ih =>
   have hd:depth<L.ell:=by simp only [List.length_cons] at hlen;omega
   have hr:L.rows+3*depth+2<L.suffix:=by have hb:=L.rowsBelow;omega
   refine ⟨?_,?_,?_,ih (depth+1) (by simp only [List.length_cons] at hlen;omega) h.2.2.2⟩
   · rw [hf _ (by omega)];exact h.1
   · rw [hf _ (by omega)];exact h.2.1
   · rw [hf _ hr];exact h.2.2.1

theorem widths_transfer (as : List Axis) (L : Layout) (s t : State) (h:Widths as s)
 (hb:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ L.suffix)
 (hf:∀i,i<L.suffix → t.natHeap i=s.natHeap i) : Widths as t := by
 intro a ha j
 rw [hf _ (by have h:=hb a ha;have h':=j.isLt;omega)]
 exact h a ha j

/-- One reverse scan step reads only the actual radix row and writes the
computed earlier suffix. Every intermediate integer uses the ambient bound. -/
theorem suffix_step (as : List Axis) (L : Layout) (n i : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hvolume:volume as=L.total) (hi:i<as.length)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 460=i+1)
 (hp:s.natReg 462=volume (as.drop (i+1))) (hr:Rows as 0 L.rows s)
 (hpc:s.pc=9) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 10 (suffixIteration s) ∧
 (suffixIteration s).natReg 460=i ∧
 (suffixIteration s).natReg 462=volume (as.drop i) ∧
 (suffixIteration s).natHeap=Function.update s.natHeap (L.suffix+i) (some (volume (as.drop i))) ∧
 Constants (suffixIteration s) ∧Header L (suffixIteration s) ∧Frame s (suffixIteration s) := by
 let a:=as.get ⟨i,hi⟩
 have row:s.natHeap (L.rows+3*i+2)=some a.geometry.widths.sum:=by
   simpa only [Nat.zero_add] using (rows_get as 0 L.rows s hr ⟨i,hi⟩).2.2
 have row':s.natHeap (L.rows+(i*3+2))=some a.geometry.widths.sum:=by
   simpa only [Nat.mul_comm,Nat.add_assoc] using row
 have hRadixB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ row).2
 have hnew:=volume_drop_step as ⟨i,hi⟩
 have hnewB:volume (as.drop i) ≤ L.B:=(volume_drop_le as i).trans (by rw [hvolume];exact L.volumeBound)
 have hrowB:L.rows+3*i+2 ≤ L.B:=by
   have h0:=L.rowsBelow;have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.directoryBound;omega
 have hdstB:L.suffix+i ≤ L.B:=by
   have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.directoryBound;omega
 have hprod:volume (as.drop (i+1))*a.geometry.widths.sum=volume (as.drop i):=by
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



theorem suffix_step_written (as : List Axis) (L : Layout) (i : ℕ) (s t : State)
 (_hi:i<as.length) (h:WrittenSuffix as L (i+1) s)
 (he:t.natHeap=Function.update s.natHeap (L.suffix+i) (some (volume (as.drop i)))) :
 WrittenSuffix as L i t := by
 intro j hj hj'
 rw [he]
 by_cases hji:j=i
 · subst j;simp
 · rw [Function.update_of_ne (by omega)]
   exact h j (by omega) hj'

theorem suffix_step_outside (as : List Axis) (L : Layout) (i : ℕ) (s t : State)
 (hi:i<as.length) (hlen:as.length=L.ell)
 (he:t.natHeap=Function.update s.natHeap (L.suffix+i) (some (volume (as.drop i)))) :
 Outside L.suffix (L.ell+1) s t := by
 intro j hj
 rw [he,Function.update_of_ne (by omega)]

theorem suffix_loop (as : List Axis) (L : Layout) (n i : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hvolume:volume as=L.total) (hi:i ≤ as.length)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 460=i)
 (hp:s.natReg 462=volume (as.drop i)) (hr:Rows as 0 L.rows s)
 (hw:WrittenSuffix as L i s) (hpc:s.pc=9) (hs:WordBound L.B s) : ∃t,
 BoundedRuns program n x L.B s (10*i) t ∧WrittenSuffix as L 0 t ∧
 t.natReg 460=0 ∧t.natReg 462=volume as ∧t.pc=9 ∧Constants t ∧Header L t ∧
 Outside L.suffix (L.ell+1) s t ∧Frame s t := by
 induction i generalizing s with
 | zero =>exact ⟨s,.refl hs,hw,hd,hp,hpc,hc,hh,fun _ _=>rfl,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
 | succ i ih =>
   obtain ⟨run,td,tp,th,tc,tH,tf⟩:=suffix_step as L n i x s hlen hvolume (by omega)
     hh hc hd hp hr hpc hs
   have outside:=suffix_step_outside as L i s (suffixIteration s) (by omega) hlen th
   have tables:Rows as 0 L.rows (suffixIteration s):=rows_transfer as 0 L s _ (by omega) hr
     (fun j hj=>outside j (Or.inl hj))
   have written:=suffix_step_written as L i s (suffixIteration s) (by omega) hw th
   have pc:(suffixIteration s).pc=9:=rfl
   obtain ⟨u,ur,uw,ud,up,uc,ucs,uh,uo,uf⟩:=ih (suffixIteration s) (by omega)
     tH tc td tp tables written pc run.final_bound
   refine ⟨u,?_,uw,ud,up,uc,ucs,uh,outside.trans uo,tf.trans uf⟩
   convert run.trans ur using 1
   omega

theorem suffix_boot (as : List Axis) (L : Layout) (n : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hh:Header L s) (hpc:s.pc=0) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 9 (suffixInitialized s) ∧
 WrittenSuffix as L as.length (suffixInitialized s) ∧Constants (suffixInitialized s) ∧
 Header L (suffixInitialized s) ∧(suffixInitialized s).natReg 460=as.length ∧
 (suffixInitialized s).natReg 462=volume (as.drop as.length) ∧
 Outside L.suffix (L.ell+1) s (suffixInitialized s) := by
 have hadd:L.suffix+L.ell ≤ L.B:=by
   have a:=L.suffixBelow;have b:=L.stackBelow;have c:=L.directoryBound;omega
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
   simp [←hlen,List.drop_length,volume_nil]
 · simp [Constants,suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next]
 · simp [suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next,hh.count,hlen]
 · simp [suffixInitialized,applyBlock,suffixBoot,Op.apply,writeNat,next,List.drop_length,volume_nil]
 · intro j hj
   rw [hheap,Function.update_of_ne (by omega)]

/-- Computed suffixes are not an entry contract. The literal reverse scan
establishes all of them from the original physical axis radix rows. -/
theorem suffix_preparation (as : List Axis) (L : Layout) (n : ℕ) (x : Fin n → ℂ) (s : State)
 (hlen:as.length=L.ell) (hvolume:volume as=L.total)
 (hh:Header L s) (hr:Rows as 0 L.rows s) (hpc:s.pc=0) (hs:WordBound L.B s) : ∃t,
 BoundedRuns program n x L.B s (10*L.ell+9) t ∧WrittenSuffix as L 0 t ∧
 t.natReg 460=0 ∧t.natReg 462=volume as ∧t.pc=9 ∧Constants t ∧Header L t ∧
 Outside L.suffix (L.ell+1) s t ∧Frame s t := by
 obtain ⟨boot,bw,bc,bh,bd,bp,bo⟩:=suffix_boot as L n x s hlen hh hpc hs
 have br:Rows as 0 L.rows (suffixInitialized s):=rows_transfer as 0 L s _ (by omega) hr
   (fun j hj=>bo j (Or.inl hj))
 have bpc:(suffixInitialized s).pc=9:=by rw [suffixInitialized,applyBlock_pc,suffixBoot_length,hpc]
 obtain ⟨t,run,tw,td,tp,tpc,tc,th,tOutside,tf⟩:=suffix_loop as L n as.length x
   (suffixInitialized s) hlen hvolume (by omega) bh bc bd bp br bw bpc boot.final_bound
 refine ⟨t,?_,tw,td,tp,tpc,tc,th,bo.trans tOutside,(blocks_frame s).1.trans tf⟩
 convert boot.trans run using 1
 omega



/-- Actual branch/straight-line/jump segments of this92-instruction program. -/
theorem branched_block (b : List Op) (base branchPC jumpPC target yes no l r n B : ℕ)
 (x : Fin n → ℂ) (s : State) (hc:BlockAt b program base)
 (hbranch:program[branchPC]?=some (.branchLT l r yes no))
 (hjump:program[jumpPC]?=some (.jump target)) (htarget:target ≤ B)
 (hbase:base+b.length=jumpPC) (hcode:base+b.length ≤ B)
 (hpc:s.pc=branchPC) (hgo:(if s.natReg l<s.natReg r then yes else no)=base)
 (hr:readable b (setPC s base)) (hv:peak b (setPC s base) ≤ B)
 (hs:WordBound B s) : BoundedRuns program n x B s (b.length+2)
   (setPC (applyBlock b (setPC s base)) target) := by
 let e:=setPC s base
 have he:WordBound B e:=changePC_bound B s base hs (by omega)
 have body:=block_runs b program base n B x e hc rfl he hcode hr hv
 have bp:(applyBlock b e).pc=jumpPC:=by rw [applyBlock_pc];exact hbase
 have jump:BoundedRuns program n x B (applyBlock b e) 1
   (setPC (applyBlock b e) target):=.next body.final_bound
   (by rw [step,bp,hjump];rfl)
   (.refl (changePC_bound B _ target body.final_bound htarget))
 have first:BoundedRuns program n x B s 1 e:=.next hs
   (by simp [step,hpc,hbranch,hgo,e,setPC]) (.refl he)
 simpa only [e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.trans (body.trans jump)

structure EntrySafe (B : ℕ) (s : State) : Prop where
 pc : s.pc=23
 go : s.natReg 460<s.natReg 450
 readable : readable enterBlock (setPC s 24)
 peak : peak enterBlock (setPC s 24) ≤ B
structure DescentSafe (B : ℕ) (s : State) : Prop where
 pc : s.pc=34
 go : s.natReg 470<s.natReg 467
 readable : readable childBlock (setPC s 35)
 peak : peak childBlock (setPC s 35) ≤ B
structure LeafSafe (B : ℕ) (s : State) : Prop where
 pc : s.pc=23
 stop : ¬s.natReg 460<s.natReg 450
 readable : readable leafBlock (setPC s 59)
 peak : peak leafBlock (setPC s 59) ≤ B
structure ReturnSafe (B : ℕ) (s : State) : Prop where
 pc : s.pc=68
 go : s.natReg 455<s.natReg 460
 readable : readable popBlock (setPC s 69)
 peak : peak popBlock (setPC s 69) ≤ B
structure Exhausted (s : State) : Prop where
 pc : s.pc=34
 stop : ¬s.natReg 470<s.natReg 467

theorem safe_enter (n B : ℕ) (x : Fin n → ℂ) (s : State) (hB:92 ≤ B)
 (h:EntrySafe B s) (hs:WordBound B s) : BoundedRuns program n x B s 11 (entered s) := by
 let e:=setPC s 24
 have eb:WordBound B e:=changePC_bound B s 24 hs (by omega)
 have body:=block_runs enterBlock program 24 n B x e enter_code rfl eb
   (by rw [enter_length];omega) h.readable h.peak
 have first:BoundedRuns program n x B s 1 e:=.next hs
   (by simp [step,h.pc,entry_branch,h.go,e,setPC]) (.refl eb)
 simpa only [enter_length,entered,e] using first.trans body

theorem safe_child (n B : ℕ) (x : Fin n → ℂ) (s : State) (hB:92 ≤ B)
 (h:DescentSafe B s) (hs:WordBound B s) : BoundedRuns program n x B s 25 (child s) := by
 simpa only [child_length,child] using branched_block childBlock 35 34 58 23 35 68 470 467
   n B x s child_code child_branch child_jump (by omega) rfl (by rw [child_length];omega)
   h.pc (by simp [h.go]) h.readable h.peak hs

theorem safe_leaf (n B : ℕ) (x : Fin n → ℂ) (s : State) (hB:92 ≤ B)
 (h:LeafSafe B s) (hs:WordBound B s) : BoundedRuns program n x B s 10 (leaf s) := by
 simpa only [leaf_length,leaf] using branched_block leafBlock 59 23 67 68 24 59 460 450
   n B x s leaf_code entry_branch leaf_jump (by omega) rfl (by rw [leaf_length];omega)
   h.pc (by simp [h.stop]) h.readable h.peak hs

theorem safe_pop (n B : ℕ) (x : Fin n → ℂ) (s : State) (hB:92 ≤ B)
 (h:ReturnSafe B s) (hs:WordBound B s) : BoundedRuns program n x B s 23 (popped s) := by
 simpa only [pop_length,popped] using branched_block popBlock 69 68 90 34 69 91 455 460
   n B x s pop_code pop_branch pop_jump (by omega) rfl (by rw [pop_length];omega)
   h.pc (by simp [h.go]) h.readable h.peak hs

theorem safe_exhausted (n B : ℕ) (x : Fin n → ℂ) (s : State) (hB:92 ≤ B)
 (h:Exhausted s) (hs:WordBound B s) : BoundedRuns program n x B s 1 (setPC s 68) :=
 .next hs (by simp [step,h.pc,child_branch,h.stop,setPC])
   (.refl (changePC_bound B s 68 hs (by omega)))

def ChildrenSafe (B : ℕ) (visit : State → State) (valid : State → Prop) : ℕ → State → Prop
 | 0,s=>Exhausted s
 | k+1,s=>DescentSafe B s ∧valid (child s) ∧ReturnSafe B (visit (child s)) ∧
   ChildrenSafe B visit valid k (popped (visit (child s)))
def TreeSafe (B : ℕ) : List ℕ → State → Prop
 | [],s=>LeafSafe B s
 | r::rs,s=>EntrySafe B s ∧ChildrenSafe B (tree rs) (TreeSafe B rs) r (entered s)

theorem children_bounded (B n : ℕ) (x : Fin n → ℂ) (visit : State → State)
 (valid : State → Prop) (cost : ℕ) (hB:92 ≤ B)
 (hv:∀s,valid s → WordBound B s → BoundedRuns program n x B s cost (visit s))
 (k : ℕ) (s : State) (h:ChildrenSafe B visit valid k s) (hs:WordBound B s) :
 BoundedRuns program n x B s (1+k*(cost+48)) (children visit k s) := by
 induction k generalizing s with
 | zero =>simpa [children] using safe_exhausted n B x s hB h hs
 | succ k ih =>
   have descent:=safe_child n B x s hB h.1 hs
   have sub:=hv (child s) h.2.1 descent.final_bound
   have ret:=safe_pop n B x (visit (child s)) hB h.2.2.1 sub.final_bound
   have rest:=ih (popped (visit (child s))) h.2.2.2 ret.final_bound
   simpa only [children,show 25+(cost+(23+(1+k*(cost+48))))=1+(k+1)*(cost+48) by ring]
     using descent.trans (sub.trans (ret.trans rest))

theorem tree_bounded (rs : List ℕ) (B n : ℕ) (x : Fin n → ℂ) (s : State)
 (hB:92 ≤ B) (h:TreeSafe B rs s) (hs:WordBound B s) :
 BoundedRuns program n x B s (treeCost rs) (tree rs s) := by
 induction rs generalizing s with
 | nil =>exact safe_leaf n B x s hB h hs
 | cons r rs ih =>
   have entry:=safe_enter n B x s hB h.1 hs
   have rest:=children_bounded B n x (tree rs) (TreeSafe B rs) (treeCost rs) hB
     (fun t ht hb=>ih t ht hb) r (entered s) h.2 entry.final_bound
   simpa only [tree,treeCost,show 11+(1+r*(treeCost rs+48))=12+r*(treeCost rs+48) by omega]
     using entry.trans rest



abbrev counts (as : List Axis) := UniformSectorPacking.blockCounts (axes as)
def states (as : List Axis) (st : BlockState) : List BlockState :=
 UniformSectorTraversalOrder.lexOutcomes (UniformSectorPacking.blockLayers (axes as)) st

def Suffixes (as : List Axis) (depth : ℕ) (L : Layout) (s : State) : Prop :=
 ∀i,i ≤ as.length → s.natHeap (L.suffix+depth+i)=some (volume (as.drop i))
structure Banks (as : List Axis) (depth : ℕ) (L : Layout) (s : State) : Prop where
 rows : Rows as depth L.rows s
 widths : Widths as s
 below : ∀a∈as,a.widthsBase+a.geometry.widths.length ≤ L.suffix
 suffixes : Suffixes as depth L s

structure Cursor (depth count : ℕ) (st : BlockState) (s : State) : Prop where
 depth : s.natReg 460=depth
 start : s.natReg 461=st.start
 width : s.natReg 462=st.width
 pairs : s.natReg 463=st.pairs
 count : s.natReg 464=count

def Fits (as : List Axis) (st : BlockState) (count : ℕ) (L : Layout) : Prop :=
 st.start+st.width*volume as ≤ L.total ∧st.pairs+as.length ≤ L.ell ∧
 count+(counts as).prod ≤ L.total

theorem banks_transfer (as : List Axis) (depth : ℕ) (L : Layout) (s t : State)
 (hlen:depth+as.length ≤ L.ell) (h:Banks as depth L s)
 (hf:∀i,i<L.stack → t.natHeap i=s.natHeap i) : Banks as depth L t := by
 have hlow:∀i,i<L.suffix → t.natHeap i=s.natHeap i:=fun i hi=>hf i (by have hb:=L.suffixBelow;omega)
 refine ⟨rows_transfer as depth L s t hlen h.rows hlow,widths_transfer as L s t h.widths h.below hlow,h.below,?_⟩
 intro i hi
 rw [hf _ (by have hb:=L.suffixBelow;omega)]
 exact h.suffixes i hi

theorem banks_tail (a : Axis) (as : List Axis) (depth : ℕ) (L : Layout) (s : State)
 (h:Banks (a::as) depth L s) : Banks as (depth+1) L s := by
 refine ⟨h.rows.2.2.2,?_,?_,?_⟩
 · intro b hb j;exact h.widths b (by simp [hb]) j
 · intro b hb;exact h.below b (by simp [hb])
 · intro i hi
   simpa only [List.drop_succ_cons,show L.suffix+(depth+1)+i=L.suffix+depth+(i+1) by omega]
     using h.suffixes (i+1) (by simp only [List.length_cons];omega)

theorem child_fits (a : Axis) (as : List Axis) (st : BlockState) (count : ℕ)
 (i : Fin a.geometry.widths.length) (L : Layout)
 (hf:st.start+st.width*volume (a::as) ≤ L.total ∧st.pairs+(a::as).length ≤ L.ell) (hcount:count+(counts as).prod ≤ L.total) :
 Fits as (UniformSectorPacking.blockAdvance a.geometry (volume as) i st) count L := by
 have b:=UniformTraversal.block_end_le_sum a.geometry.widths i
 refine ⟨?_,?_,hcount⟩
 · have hfit:=hf.1
   change st.start+st.width*(a.geometry.widths.sum*volume as) ≤ L.total at hfit
   calc
    _=st.start+st.width*((UniformTraversal.blockBefore a.geometry.widths i+a.geometry.widths.get i)*volume as):=by
      simp only [UniformSectorPacking.blockAdvance];ring
    _ ≤ st.start+st.width*(a.geometry.widths.sum*volume as):=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ b)) _
    _ ≤ L.total:=hfit
 · have hp:=hf.2
   simp only [List.length_cons] at hp
   change st.pairs+(if a.geometry.widths.get i=2 then 1 else 0)+as.length ≤ L.ell
   split_ifs <;> omega

/-- Loads the current physical row and the suffix computed by the earlier scan. -/
theorem enter_actual (a : Axis) (as : List Axis) (L : Layout) (n depth count : ℕ)
 (x : Fin n → ℂ) (st : BlockState) (s : State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hb:Banks (a::as) depth L s)
 (hpc:s.pc=23) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 11 (entered s) ∧Header L (entered s) ∧Constants (entered s) ∧
 Cursor depth count st (entered s) ∧(entered s).natReg 467=a.geometry.widths.length ∧
 (entered s).natReg 468=a.widthsBase ∧(entered s).natReg 469=volume as ∧
 (entered s).natReg 470=0 ∧(entered s).natReg 471=0 ∧(entered s).pc=34 ∧
 (entered s).natHeap=s.natHeap := by
 have hd:depth<L.ell:=by simp only [List.length_cons] at hlen;omega
 have row0:s.natHeap (L.rows+depth*3)=some a.geometry.widths.length:=by
   simpa only [Nat.mul_comm] using hb.rows.1
 have row1:s.natHeap (L.rows+(depth*3+1))=some a.widthsBase:=by
   simpa only [Nat.mul_comm,Nat.add_assoc] using hb.rows.2.1
 have suffix:s.natHeap (L.suffix+(depth+1))=some (volume as):=by
   simpa only [List.drop_succ_cons,List.drop_zero,Nat.add_assoc] using hb.suffixes 1 (by simp)
 have rB:a.geometry.widths.length ≤ L.B:=(hs.2.2.1 _ _ row0).2
 have wB:a.widthsBase ≤ L.B:=(hs.2.2.1 _ _ row1).2
 have tB:volume as ≤ L.B:=(hs.2.2.1 _ _ suffix).2
 have rowB:L.rows+depth*3+1 ≤ L.B:=by
   have h0:=L.rowsBelow;have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.directoryBound;omega
 have suffixB:L.suffix+(depth+1) ≤ L.B:=by
   have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.directoryBound;omega
 have go:s.natReg 460<s.natReg 450:=by rw [cur.depth,hh.count];omega
 have safe:EntrySafe L.B s:=by
   refine ⟨hpc,go,?_,?_⟩
   · simp [readable,enterBlock,Op.readable,Op.apply,setPC,writeNat,next,
       hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,hh.suffix,row0,row1,suffix,Nat.add_assoc]
   · simp [peak,enterBlock,Op.peak,Op.apply,setPC,writeNat,next,
       hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,hh.suffix,row0,row1,suffix,Nat.add_assoc]
     omega
 refine ⟨safe_enter n L.B x s L.code safe hs,hh.transport L s _ (blocks_frame s).2.2.2.1,
   body_constants enterBlock (setPC s 24) hc (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor <;> simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     cur.depth,cur.start,cur.width,cur.pairs,cur.count]
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,row0,Nat.add_assoc]
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     hc.2.1,hc.2.2.2.1,cur.depth,hh.rows,row1,Nat.add_assoc]
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next,
     hc.2.1,cur.depth,hh.suffix,suffix,Nat.add_assoc]
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next]
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next]
 · rw [entered,applyBlock_pc,enter_length];rfl
 · simp [entered,setPC,applyBlock,enterBlock,Op.apply,writeNat,next]



/-- The entire parent cursor and both sibling counters are stored by descent. -/
def Saved (L : Layout) (depth index before : ℕ) (st : BlockState) (s : State) : Prop :=
 s.natHeap (L.stack+depth*5)=some st.start ∧
 s.natHeap (L.stack+depth*5+1)=some st.width ∧
 s.natHeap (L.stack+depth*5+2)=some st.pairs ∧
 s.natHeap (L.stack+depth*5+3)=some index ∧
 s.natHeap (L.stack+depth*5+4)=some before


theorem constants_setPC (s : State) (k : ℕ) (h : Constants s) : Constants (setPC s k) := h

theorem child_constants (s : State) (hc : Constants s) : Constants (child s) := by
 change Constants (setPC (applyBlock childBlock (setPC s 35)) 23)
 exact constants_setPC _ 23 (body_constants childBlock (setPC s 35)
   (constants_setPC s 35 hc) (by decide))

/-- Raw descent memory identity; source readability is discharged separately. -/
theorem child_heap (L : Layout) (depth count index base before q : ℕ) (st : BlockState) (s : State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s)
 (hi:s.natReg 470=index) (hb:s.natReg 471=before) (hw:s.natReg 468=base)
 (hv:s.natHeap (base+index)=some q) :
 (child s).natHeap=Function.update
   (Function.update (Function.update (Function.update (Function.update s.natHeap
     (L.stack+depth*5) (some st.start)) (L.stack+depth*5+1) (some st.width))
       (L.stack+depth*5+2) (some st.pairs)) (L.stack+depth*5+3) (some (index+1)))
       (L.stack+depth*5+4) (some (before+q)) := by
 simp [child,setPC,applyBlock,childBlock,Op.apply,writeNat,next,hc.1,hc.2.1,hc.2.2.2.2,
   cur.depth,cur.start,cur.width,cur.pairs,hh.stack,hw,hi,hb,hv,Nat.add_assoc]

theorem child_cursor (depth count index base before q tail : ℕ) (st : BlockState) (s : State)
 (hc:Constants s) (cur:Cursor depth count st s)
 (hi:s.natReg 470=index) (hb:s.natReg 471=before) (hw:s.natReg 468=base)
 (ht:s.natReg 469=tail) (hv:s.natHeap (base+index)=some q) :
 Cursor (depth+1) count ⟨st.start+st.width*before*tail,st.width*q,st.pairs+(q-1)⟩ (child s) := by
 constructor <;> simp [child,setPC,applyBlock,childBlock,Op.apply,writeNat,next,
   hc.2.1,cur.depth,cur.start,cur.width,cur.pairs,cur.count,hw,hi,hb,ht,hv]

/-- Physical descent derives the width read and every intermediate bound.
The running preceding-width sum is advanced once before the recursive child. -/
theorem child_safe (a : Axis) (as : List Axis) (L : Layout) (n depth count : ℕ)
 (_x : Fin n → ℂ) (st : BlockState) (i : Fin a.geometry.widths.length) (s : State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hb:Banks (a::as) depth L s) (hf:st.start+st.width*volume (a::as) ≤ L.total ∧st.pairs+(a::as).length ≤ L.ell)
 (hindex:s.natReg 470=i.val) (hbefore:s.natReg 471=UniformTraversal.blockBefore a.geometry.widths i)
 (hwidthBase:s.natReg 468=a.widthsBase) (hsuffix:s.natReg 469=volume as)
 (hradix:s.natReg 467=a.geometry.widths.length) (hpc:s.pc=34) (hs:WordBound L.B s) : DescentSafe L.B s := by
 let before:=UniformTraversal.blockBefore a.geometry.widths i
 let q:=a.geometry.widths.get i
 have hd:depth<L.ell:=by simp only [List.length_cons] at hlen;omega
 have value:s.natHeap (a.widthsBase+i.val)=some q:=hb.widths a (by simp) i
 have qBound:q ≤ 2:=by
   rcases a.geometry.widths_one_two q (List.get_mem _ _) with h|h <;> omega
 have endB:before+q ≤ a.geometry.widths.sum:=UniformTraversal.block_end_le_sum _ i
 have stackB:L.stack+depth*5+4 ≤ L.B:=by
   have h0:=L.stackBelow;have h1:=L.directoryBound;omega
 have srcB:a.widthsBase+i.val ≤ L.B:=by
   have h0:=hb.below a (by simp);have h1:=L.suffixBelow;have h2:=L.stackBelow;have h3:=L.directoryBound
   have hi:=i.isLt;omega
 have qB:q ≤ L.B:=(hs.2.2.1 _ _ value).2
 have headB:a.geometry.widths.sum ≤ L.B:=(hs.2.2.1 _ _ hb.rows.2.2.1).2
 have indexB:i.val+1 ≤ L.B:=by have h:=hs.2.1 467;rw [hradix] at h;have hi:=i.isLt;omega
 have startB:st.start ≤ L.B:=by simpa only [cur.start] using hs.2.1 461
 have widthB:st.width ≤ L.B:=by simpa only [cur.width] using hs.2.1 462
 have pairsB:st.pairs ≤ L.B:=by simpa only [cur.pairs] using hs.2.1 463
 have countB:count ≤ L.B:=by simpa only [cur.count] using hs.2.1 464
 have ellB:L.ell ≤ L.B:=by simpa only [hh.count] using hs.2.1 450
 have prefixFit:st.start+st.width*(a.geometry.widths.sum*volume as) ≤ L.total:=hf.1
 have fullB:st.width*(a.geometry.widths.sum*volume as) ≤ L.total:=by omega
 have tailPos:1 ≤ volume as:=volume_pos as
 have temp2:st.width*before*volume as ≤ st.width*(a.geometry.widths.sum*volume as):=by
   rw [←Nat.mul_assoc]
   exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
 have temp1:st.width*before ≤ st.width*before*volume as:=by
   simpa only [Nat.mul_one] using Nat.mul_le_mul_left (st.width*before) tailPos
 have tempB:st.width*before ≤ L.B:=temp1.trans (temp2.trans (fullB.trans L.volumeBound))
 have temp2B:st.width*before*volume as ≤ L.B:=temp2.trans (fullB.trans L.volumeBound)
 have newStartB:st.start+st.width*before*volume as ≤ L.B:=by
   have h:st.start+st.width*before*volume as ≤ L.total:=by
     simpa only [Nat.mul_assoc] using (Nat.add_le_add_left temp2 st.start).trans prefixFit
   exact h.trans L.volumeBound
 have newWidthB:st.width*q ≤ L.B:=by
   have h:st.width*q*volume as ≤ st.width*(a.geometry.widths.sum*volume as):=by
     rw [←Nat.mul_assoc];exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
   have h':st.width*q ≤ st.width*q*volume as:=by
     simpa only [Nat.mul_one] using Nat.mul_le_mul_left (st.width*q) tailPos
   exact h'.trans (h.trans (fullB.trans L.volumeBound))
 have newPairB:st.pairs+(q-1) ≤ L.B:=by
   have h:=hf.2
   simp only [List.length_cons] at h
   omega
 simp only [before,q,List.get_eq_getElem] at *
 have safe:DescentSafe L.B s:=by
   refine ⟨hpc,by rw [hindex,hradix];exact i.isLt,?_,?_⟩
   · simp [readable,childBlock,Op.readable,Op.apply,setPC,writeNat,next,
       hwidthBase,hindex,value]
   · simp [peak,childBlock,Op.peak,Op.apply,setPC,writeNat,next,
       hc.1,hc.2.1,hc.2.2.2.2,cur.depth,cur.start,cur.width,cur.pairs,
       hh.stack,hwidthBase,hindex,hbefore,hsuffix,value,Nat.add_assoc]
     have h:=L.code
     omega
 exact safe

theorem child_actual (a : Axis) (as : List Axis) (L : Layout) (n depth count : ℕ)
 (x : Fin n → ℂ) (st : BlockState) (i : Fin a.geometry.widths.length) (s : State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hb:Banks (a::as) depth L s) (hf:st.start+st.width*volume (a::as) ≤ L.total ∧st.pairs+(a::as).length ≤ L.ell)
 (hindex:s.natReg 470=i.val) (hbefore:s.natReg 471=UniformTraversal.blockBefore a.geometry.widths i)
 (hwidthBase:s.natReg 468=a.widthsBase) (hsuffix:s.natReg 469=volume as)
 (hradix:s.natReg 467=a.geometry.widths.length) (hpc:s.pc=34) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 25 (child s) ∧Header L (child s) ∧Constants (child s) ∧
 Cursor (depth+1) count (UniformSectorPacking.blockAdvance a.geometry (volume as) i st) (child s) ∧
 Saved L depth (i.val+1) ((a.geometry.widths.take (i.val+1)).sum) st (child s) ∧
 Outside (L.stack+depth*5) 5 s (child s) ∧(child s).pc=23 := by
 let before:=UniformTraversal.blockBefore a.geometry.widths i
 let q:=a.geometry.widths.get i
 have value:s.natHeap (a.widthsBase+i.val)=some q:=hb.widths a (by simp) i
 have flag:q-1=(if q=2 then 1 else 0):=by
   rcases a.geometry.widths_one_two q (List.get_mem _ _) with h|h <;> simp [h]
 have sumBefore:(a.geometry.widths.take (i.val+1)).sum=before+q:=by
   simpa only [before,q,UniformTraversal.blockBefore,List.get_eq_getElem] using List.sum_take_succ a.geometry.widths i.val i.isLt
 have safe:=child_safe a as L n depth count x st i s hlen hh hc cur hb hf
   hindex hbefore hwidthBase hsuffix hradix hpc hs
 have heap:(child s).natHeap=Function.update
   (Function.update (Function.update (Function.update (Function.update s.natHeap
     (L.stack+depth*5) (some st.start)) (L.stack+depth*5+1) (some st.width))
       (L.stack+depth*5+2) (some st.pairs)) (L.stack+depth*5+3) (some (i.val+1)))
       (L.stack+depth*5+4) (some (before+q)):=child_heap L depth count i.val a.widthsBase before q st s hh hc cur hindex hbefore hwidthBase value
 refine ⟨safe_child n L.B x s L.code safe hs,hh.transport L s _ (blocks_frame s).2.2.2.2.1,
   child_constants s hc,?_,?_,?_,rfl⟩
 · have c:=child_cursor depth count i.val a.widthsBase before q (volume as) st s hc cur
     hindex hbefore hwidthBase hsuffix value
   convert c using 1
   simp only [UniformSectorPacking.blockAdvance,before,q,flag]
 · unfold Saved
   rw [heap,sumBefore]
   simp (disch:=omega) [Function.update_of_ne]
 · intro j hj
   rw [heap]
   simp [Function.update_of_ne (show j≠L.stack+depth*5+4 by omega),
     Function.update_of_ne (show j≠L.stack+depth*5+3 by omega),
     Function.update_of_ne (show j≠L.stack+depth*5+2 by omega),
     Function.update_of_ne (show j≠L.stack+depth*5+1 by omega),
     Function.update_of_ne (show j≠L.stack+depth*5 by omega)]

theorem pop_heap (s : State) : (popped s).natHeap=s.natHeap := by
 simp [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,next]
theorem pop_constants (s : State) (hc:Constants s) : Constants (popped s) := by
 change Constants (setPC (applyBlock popBlock (setPC s 69)) 34)
 exact constants_setPC _ 34 (body_constants popBlock (setPC s 69)
   (constants_setPC s 69 hc) (by decide))

theorem pop_cursor (L : Layout) (depth count index before : ℕ) (st : BlockState) (s : State)
 (hh:Header L s) (hc:Constants s) (hd:s.natReg 460=depth+1) (hn:s.natReg 464=count)
 (saved:Saved L depth index before st s) : Cursor depth count st (popped s) := by
 simp only [Saved,Nat.add_assoc] at saved
 constructor <;> simp [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,next,
   hd,hn,hc.1,hc.2.1,hc.2.2.2.2,hh.stack,saved.1,saved.2.1,saved.2.2.1,
   saved.2.2.2.1,saved.2.2.2.2,Nat.add_assoc]

theorem pop_actual (a:Axis) (as:List Axis) (L:Layout) (n depth count index before:ℕ)
 (x:Fin n → ℂ) (st:BlockState) (s:State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (hd:s.natReg 460=depth+1) (hn:s.natReg 464=count)
 (saved:Saved L depth index before st s) (hb:Banks (a::as) depth L s)
 (hpc:s.pc=68) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 23 (popped s) ∧Header L (popped s) ∧Constants (popped s) ∧
 Cursor depth count st (popped s) ∧(popped s).natReg 467=a.geometry.widths.length ∧
 (popped s).natReg 468=a.widthsBase ∧(popped s).natReg 469=volume as ∧
 (popped s).natReg 470=index ∧(popped s).natReg 471=before ∧(popped s).pc=34 := by
 simp only [Saved,Nat.add_assoc] at saved
 have dd:depth<L.ell:=by simp only [List.length_cons] at hlen;omega
 have row0:s.natHeap (L.rows+depth*3)=some a.geometry.widths.length:=by
   simpa only [Nat.mul_comm] using hb.rows.1
 have row1:s.natHeap (L.rows+(depth*3+1))=some a.widthsBase:=by
   simpa only [Nat.mul_comm,Nat.add_assoc] using hb.rows.2.1
 have suffix:s.natHeap (L.suffix+(depth+1))=some (volume as):=by
   simpa only [List.drop_succ_cons,List.drop_zero,Nat.add_assoc] using hb.suffixes 1 (by simp)
 have stackB:L.stack+depth*5+4 ≤ L.B:=by
   have h:=L.stackBelow;have h':=L.directoryBound;omega
 have rowB:L.rows+depth*3+1 ≤ L.B:=by
   have h:=L.rowsBelow;have h':=L.suffixBelow;have h'':=L.stackBelow;have hd:=L.directoryBound;omega
 have suffixB:L.suffix+(depth+1) ≤ L.B:=by
   have h:=L.suffixBelow;have h':=L.stackBelow;have h'':=L.directoryBound;omega
 have startB:st.start ≤ L.B:=(hs.2.2.1 _ _ saved.1).2
 have widthB:st.width ≤ L.B:=(hs.2.2.1 _ _ saved.2.1).2
 have pairsB:st.pairs ≤ L.B:=(hs.2.2.1 _ _ saved.2.2.1).2
 have indexB:index ≤ L.B:=(hs.2.2.1 _ _ saved.2.2.2.1).2
 have beforeB:before ≤ L.B:=(hs.2.2.1 _ _ saved.2.2.2.2).2
 have radixB:a.geometry.widths.length ≤ L.B:=(hs.2.2.1 _ _ row0).2
 have baseB:a.widthsBase ≤ L.B:=(hs.2.2.1 _ _ row1).2
 have tailB:volume as ≤ L.B:=(hs.2.2.1 _ _ suffix).2
 have safe:ReturnSafe L.B s:=by
   refine ⟨hpc,by rw [hc.1,hd];omega,?_,?_⟩
   · simp [readable,popBlock,Op.readable,Op.apply,setPC,writeNat,next,hd,
       hc.1,hc.2.1,hc.2.2.2.1,hc.2.2.2.2,hh.stack,hh.rows,hh.suffix,
       saved.1,saved.2.1,saved.2.2.1,saved.2.2.2.1,saved.2.2.2.2,
       row0,row1,suffix,Nat.add_assoc]
   · simp [peak,popBlock,Op.peak,Op.apply,setPC,writeNat,next,hd,
       hc.1,hc.2.1,hc.2.2.2.1,hc.2.2.2.2,hh.stack,hh.rows,hh.suffix,
       saved.1,saved.2.1,saved.2.2.1,saved.2.2.2.1,saved.2.2.2.2,
       row0,row1,suffix,Nat.add_assoc]
     have h:=L.code;omega
 refine ⟨safe_pop n L.B x s L.code safe hs,
   hh.transport L s _ (blocks_frame s).2.2.2.2.2.2,
   pop_constants s hc,pop_cursor L depth count index before st s hh hc hd hn saved,?_,?_,?_,?_,?_,rfl⟩
 all_goals simp [popped,setPC,applyBlock,popBlock,Op.apply,writeNat,next,hd,
   hc.1,hc.2.1,hc.2.2.2.1,hc.2.2.2.2,hh.stack,hh.rows,hh.suffix,
   saved.1,saved.2.1,saved.2.2.1,saved.2.2.2.1,saved.2.2.2.2,
   row0,row1,suffix,Nat.add_assoc]

theorem leaf_heap (L:Layout) (depth count:ℕ) (st:BlockState) (s:State)
 (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s) :
 (leaf s).natHeap=Function.update (Function.update (Function.update s.natHeap
  (L.directory+count*3) (some st.start)) (L.directory+count*3+1) (some st.width))
  (L.directory+count*3+2) (some st.pairs) := by
 simp [leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,next,
   hh.directory,hc.2.1,hc.2.2.2.1,cur.start,cur.width,cur.pairs,cur.count,Nat.add_assoc]

theorem leaf_actual (L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:BlockState) (s:State)
 (hd:depth=L.ell) (hh:Header L s) (hc:Constants s) (cur:Cursor depth count st s)
 (hf:Fits [] st count L) (hpc:s.pc=23) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s 10 (leaf s) ∧Header L (leaf s) ∧Constants (leaf s) ∧
 Cursor depth (count+1) st (leaf s) ∧Outside (L.directory+count*3) 3 s (leaf s) ∧
 (leaf s).pc=68 := by
 have cB:count+1 ≤ L.total:=by simpa only [counts,axes,UniformSectorPacking.blockCounts,List.map_nil,List.prod_nil] using hf.2.2
 have startB:st.start ≤ L.B:=by simpa only [cur.start] using hs.2.1 461
 have widthB:st.width ≤ L.B:=by simpa only [cur.width] using hs.2.1 462
 have pairsB:st.pairs ≤ L.B:=by simpa only [cur.pairs] using hs.2.1 463
 have dirB:L.directory+count*3+2 ≤ L.B:=by have h:=L.directoryBound;omega
 have countB:count+1 ≤ L.B:=cB.trans L.volumeBound
 have safe:LeafSafe L.B s:=by
   refine ⟨hpc,by rw [cur.depth,hh.count,hd];omega,by simp [readable,leafBlock,Op.readable],?_⟩
   simp [peak,leafBlock,Op.peak,Op.apply,setPC,writeNat,next,
     hh.directory,hc.2.1,hc.2.2.2.1,cur.start,cur.width,cur.pairs,cur.count,Nat.add_assoc]
   have h:=L.code;omega
 refine ⟨safe_leaf n L.B x s L.code safe hs,
   hh.transport L s _ (blocks_frame s).2.2.2.2.2.1,
   body_constants leafBlock (setPC s 59) hc (by decide),?_,?_,rfl⟩
 · constructor <;> simp [leaf,setPC,applyBlock,leafBlock,Op.apply,writeNat,next,
     hc.2.1,cur.depth,cur.start,cur.width,cur.pairs,cur.count]
 · intro j hj
   rw [leaf_heap L depth count st s hh hc cur]
   simp [Function.update_of_ne (show j≠L.directory+count*3+2 by omega),
     Function.update_of_ne (show j≠L.directory+count*3+1 by omega),
     Function.update_of_ne (show j≠L.directory+count*3 by omega)]

/-- A physical directory cell holds all three metadata fields. -/
def Cell (L:Layout) (count:ℕ) (st:BlockState) (s:State) : Prop :=
 s.natHeap (L.directory+count*3)=some st.start ∧
 s.natHeap (L.directory+count*3+1)=some st.width ∧
 s.natHeap (L.directory+count*3+2)=some st.pairs
def Directory (L:Layout) : ℕ → List BlockState → State → Prop
 | _,[],_=>True
 | count,st::xs,s=>Cell L count st s ∧Directory L (count+1) xs s

theorem directory_append (L:Layout) (count:ℕ) (xs ys:List BlockState) (s:State) :
 Directory L count (xs++ys) s ↔ Directory L count xs s ∧Directory L (count+xs.length) ys s := by
 induction xs generalizing count with
 | nil =>simp [Directory]
 | cons st xs ih =>
   simp only [List.cons_append,Directory,ih,List.length_cons]
   rw [show count+(xs.length+1)=(count+1)+xs.length by omega]
   exact and_assoc.symm

theorem directory_transfer (L:Layout) (count:ℕ) (xs:List BlockState) (s t:State)
 (hd:Directory L count xs s)
 (he:∀j,L.directory+count*3 ≤ j → j<L.directory+(count+xs.length)*3 → t.natHeap j=s.natHeap j) :
 Directory L count xs t := by
 induction xs generalizing count with
 | nil =>trivial
 | cons st xs ih =>
   rcases hd with ⟨cell,rest⟩
   refine ⟨⟨?_,?_,?_⟩,ih (count+1) rest ?_⟩
   · exact (he _ (by omega) (by simp only [List.length_cons];omega)).trans cell.1
   · exact (he _ (by omega) (by simp only [List.length_cons];omega)).trans cell.2.1
   · exact (he _ (by omega) (by simp only [List.length_cons];omega)).trans cell.2.2
   · intro j h0 h1
     apply he j (by omega)
     simp only [List.length_cons];omega

/-- Natural ordinal enumeration is a specification only. The executable
program increments the ordinal and carries the preceding-width sum. -/
def enumerate (f:ℕ → List BlockState) : ℕ → ℕ → List BlockState
 | _,0=>[]
 | i,k+1=>f i++enumerate f (i+1) k
def advanceAt (a:Axis) (as:List Axis) (st:BlockState) (i:ℕ) : BlockState :=
 if hi:i<a.geometry.widths.length then
   UniformSectorPacking.blockAdvance a.geometry (volume as) ⟨i,hi⟩ st else st
def outcomes (a:Axis) (as:List Axis) (st:BlockState) (i k:ℕ) : List BlockState :=
 enumerate (fun j=>states as (advanceAt a as st j)) i k

theorem advanceAt_fin (a:Axis) (as:List Axis) (st:BlockState) (i:Fin a.geometry.widths.length) :
 advanceAt a as st i.val=UniformSectorPacking.blockAdvance a.geometry (volume as) i st := by
 simp [advanceAt,i.isLt]

theorem enumerate_ofFn (f:ℕ → List BlockState) (i k:ℕ) :
 enumerate f i k=(List.ofFn (fun j:Fin k=>f (i+j.val))).flatten := by
 induction k generalizing i with
 | zero =>simp [enumerate]
 | succ k ih =>
   simp only [enumerate,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ,ih]
   congr 2
   apply congrArg List.ofFn
   funext j
   rw [show i+(j.val+1)=(i+1)+j.val by omega]

theorem states_length (as:List Axis) (st:BlockState) : (states as st).length=(counts as).prod := by
 rw [states,UniformSectorTraversalOrder.block_lex_ofFn,List.length_ofFn]

theorem outcomes_length (a:Axis) (as:List Axis) (st:BlockState) (i k:ℕ) :
 (outcomes a as st i k).length=k*(counts as).prod := by
 induction k generalizing i with
 | zero =>simp [outcomes,enumerate]
 | succ k ih =>
   change (states as (advanceAt a as st i)++outcomes a as st (i+1) k).length=_
   rw [List.length_append,states_length,ih]
   ring

theorem states_cons (a:Axis) (as:List Axis) (st:BlockState) :
 states (a::as) st=outcomes a as st 0 a.geometry.widths.length := by
 rw [outcomes,enumerate_ofFn]
 change ((List.finRange a.geometry.widths.length).map (fun i=>
   states as (UniformSectorPacking.blockAdvance a.geometry (volume as) i st))).flatten=_
 rw [←List.ofFn_eq_map]
 congr 1
 apply congrArg List.ofFn
 funext i
 simpa only [Nat.zero_add] using (congrArg (states as) (advanceAt_fin a as st i)).symm

structure Effect (as:List Axis) (depth count:ℕ) (st:BlockState) (L:Layout) (s t:State) : Prop where
 pc : t.pc=68
 header : Header L t
 constants : Constants t
 cursor : Cursor depth (count+(counts as).prod) st t
 frame : Frame s t
 natFrame : ∀j,(j<L.stack+depth*5 ∨ L.stack+L.ell*5 ≤ j) →
   (j<L.directory+count*3 ∨ L.directory+(count+(counts as).prod)*3 ≤ j) → t.natHeap j=s.natHeap j
 directory : Directory L count (states as st) t

theorem header_setPC (L:Layout) (s:State) (p:ℕ) (h:Header L s) : Header L (setPC s p) :=
 ⟨h.count,h.rows,h.suffix,h.stack,h.directory⟩
theorem cursor_setPC (depth count:ℕ) (st:BlockState) (s:State) (p:ℕ) (h:Cursor depth count st s) :
 Cursor depth count st (setPC s p) := ⟨h.depth,h.start,h.width,h.pairs,h.count⟩

structure LoopEffect (a:Axis) (as:List Axis) (depth count i k:ℕ) (st:BlockState) (L:Layout) (s t:State) : Prop where
 pc : t.pc=68
 header : Header L t
 constants : Constants t
 cursor : Cursor depth (count+k*(counts as).prod) st t
 frame : Frame s t
 natFrame : ∀j,(j<L.stack+depth*5 ∨ L.stack+L.ell*5 ≤ j) →
   (j<L.directory+count*3 ∨ L.directory+(count+k*(counts as).prod)*3 ≤ j) → t.natHeap j=s.natHeap j
 directory : Directory L count (outcomes a as st i k) t

def PhysicalTree (visit:State → State) (as:List Axis) : Prop :=
 ∀(L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:BlockState) (s:State),
 depth+as.length=L.ell → Header L s → Constants s → Cursor depth count st s → Banks as depth L s →
 Fits as st count L → s.pc=23 → WordBound L.B s →
 BoundedRuns program n x L.B s (treeCost (counts as)) (visit s) ∧Effect as depth count st L s (visit s)

theorem physical_leaf (L:Layout) (n depth count:ℕ) (x:Fin n → ℂ) (st:BlockState) (s:State)
 (hlen:depth+([]:List Axis).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hf:Fits [] st count L) (hpc:s.pc=23) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s (treeCost (counts [])) (leaf s) ∧Effect [] depth count st L s (leaf s) := by
 obtain ⟨run,header,const,cursor,foot,pc⟩:=leaf_actual L n depth count x st s (by simpa using hlen) hh hc cur hf hpc hs
 refine ⟨run,⟨pc,header,const,cursor,(blocks_frame s).2.2.2.2.2.1,?_,?_⟩⟩
 · intro j _ hout
   apply foot j
   simp only [counts,axes,UniformSectorPacking.blockCounts,List.map_nil,List.prod_nil] at hout
   omega
 · change Cell L count st (leaf s) ∧True
   refine ⟨?_,trivial⟩
   unfold Cell
   rw [leaf_heap L depth count st s hh hc cur]
   simp (disch:=omega) [Function.update_of_ne]

/-- This induction derives every read and word guard from physical rows,
widths, suffixes generated earlier, and the stack written by descent. -/
theorem physical_children (visit:State → State) (as:List Axis) (hv:PhysicalTree visit as)
 (a:Axis) (L:Layout) (n depth count i k:ℕ) (x:Fin n → ℂ) (st:BlockState) (s:State)
 (hlen:depth+(a::as).length=L.ell) (hh:Header L s) (hc:Constants s)
 (cur:Cursor depth count st s) (hb:Banks (a::as) depth L s)
 (hgeo:st.start+st.width*volume (a::as) ≤ L.total ∧st.pairs+(a::as).length ≤ L.ell)
 (hik:i+k=a.geometry.widths.length) (hcount:count+k*(counts as).prod ≤ L.total)
 (hindex:s.natReg 470=i) (hbefore:s.natReg 471=(a.geometry.widths.take i).sum)
 (hwidthBase:s.natReg 468=a.widthsBase) (hsuffix:s.natReg 469=volume as)
 (hradix:s.natReg 467=a.geometry.widths.length) (hpc:s.pc=34) (hs:WordBound L.B s) :
 BoundedRuns program n x L.B s (1+k*(treeCost (counts as)+48)) (children visit k s) ∧
 LoopEffect a as depth count i k st L s (children visit k s) := by
 induction k generalizing s count i with
 | zero =>
   have ex:Exhausted s:=⟨hpc,by rw [hindex,hradix];omega⟩
   refine ⟨by simpa [children] using safe_exhausted n L.B x s L.code ex hs,?_,⟩
   change LoopEffect a as depth count i 0 st L s (setPC s 68)
   refine ⟨rfl,header_setPC L s 68 hh,constants_setPC s 68 hc,?_,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩,fun _ _ _=>rfl,trivial⟩
   simpa only [Nat.zero_mul,Nat.add_zero] using cursor_setPC depth count st s 68 cur
 | succ k ih =>
   have hd:depth<L.ell:=by simp only [List.length_cons] at hlen;omega
   let digit:Fin a.geometry.widths.length:=⟨i,by omega⟩
   have nextBound:count+(counts as).prod ≤ L.total:=by
     have h:(counts as).prod ≤ (k+1)*(counts as).prod:=by
       simpa only [Nat.one_mul] using Nat.mul_le_mul_right (counts as).prod (show 1 ≤ k+1 by omega)
     omega
   obtain ⟨descent,ch,cc,cp,saved,cfoot,cpc⟩:=child_actual a as L n depth count x st digit s
     hlen hh hc cur hb hgeo hindex hbefore hwidthBase hsuffix hradix hpc hs
   have cb:Banks (a::as) depth L (child s):=banks_transfer (a::as) depth L s (child s)
     (by omega) hb (fun j hj=>cfoot j (Or.inl (by omega)))
   have fits:=child_fits a as st count digit L hgeo nextBound
   obtain ⟨sub,e⟩:=hv L n (depth+1) count x
     (UniformSectorPacking.blockAdvance a.geometry (volume as) digit st) (child s)
     (by simp only [List.length_cons] at hlen;omega) ch cc cp (banks_tail a as depth L _ cb)
     fits cpc descent.final_bound
   have eb:Banks (a::as) depth L (visit (child s)):=banks_transfer (a::as) depth L _ _
     (by omega) cb (fun j hj=>e.natFrame j (Or.inl (by omega))
       (Or.inl (by have h:=L.stackBelow;omega)))
   have keepSaved:Saved L depth (i+1) ((a.geometry.widths.take (i+1)).sum) st (visit (child s)):=by
     unfold Saved at saved ⊢
     simp only [digit] at saved
     rcases saved with ⟨sStart,sWidth,sPairs,sIndex,sBefore⟩
     refine ⟨?_,?_,?_,?_,?_⟩
     all_goals apply (e.natFrame _ (Or.inl (by omega)) (Or.inl (by have h:=L.stackBelow;omega))).trans
     all_goals assumption
   obtain ⟨ret,rh,rc,rp,rr,rb,rt,ri,rBefore,rpc⟩:=pop_actual a as L n depth
     (count+(counts as).prod) (i+1) ((a.geometry.widths.take (i+1)).sum) x st (visit (child s))
     hlen e.header e.constants e.cursor.depth e.cursor.count keepSaved eb e.pc sub.final_bound
   let t:=popped (visit (child s))
   have tb:Banks (a::as) depth L t:=banks_transfer (a::as) depth L _ _ (by omega) eb
     (fun j _=>congrFun (pop_heap _) j)
   have endCount:(count+(counts as).prod)+k*(counts as).prod=count+(k+1)*(counts as).prod:=by ring
   obtain ⟨rest,f⟩:=ih (count+(counts as).prod) (i+1) t rh rc rp tb (by omega)
     (by rw [endCount];exact hcount) ri rBefore rb rt rr rpc ret.final_bound
   have totalCost:25+(treeCost (counts as)+(23+(1+k*(treeCost (counts as)+48))))=
     1+(k+1)*(treeCost (counts as)+48):=by ring
   rw [show children visit (k+1) s=children visit k t by rfl]
   refine ⟨by simpa only [totalCost] using descent.trans (sub.trans (ret.trans rest)),?_,⟩
   refine ⟨f.pc,f.header,f.constants,?_,
     (blocks_frame s).2.2.2.2.1.trans (e.frame.trans ((blocks_frame _).2.2.2.2.2.2.trans f.frame)),?_,?_⟩
   · simpa only [endCount] using f.cursor
   · intro j hstack hout
     rw [f.natFrame j hstack (by
       rcases hout with h|h
       · exact Or.inl (by omega)
       · exact Or.inr (by simpa only [endCount] using h)),
       show t.natHeap=(visit (child s)).natHeap from pop_heap _,
       e.natFrame j (by rcases hstack with h|h;exact Or.inl (by omega);exact Or.inr h)
         (by rcases hout with h|h;exact Or.inl h;exact Or.inr (by
           have h':count+(counts as).prod ≤ count+(k+1)*(counts as).prod:=by
             simp only [Nat.add_mul,Nat.one_mul];omega
           omega))]
     apply cfoot j
     rcases hstack with h|h
     · exact Or.inl h
     · exact Or.inr (by omega)
   · change Directory L count (states as (advanceAt a as st i)++outcomes a as st (i+1) k) _
     apply (directory_append L count _ _ _).2
     refine ⟨?_,?_⟩
     · rw [show advanceAt a as st i=UniformSectorPacking.blockAdvance a.geometry (volume as) digit st
           from advanceAt_fin a as st digit]
       apply directory_transfer L count _ (visit (child s)) _ e.directory
       intro j hj0 hj1
       rw [states_length] at hj1
       exact (f.natFrame j (Or.inr (by have h:=L.stackBelow;omega)) (Or.inl hj1)).trans
         (congrFun (pop_heap _) j)
     · simpa only [states_length] using f.directory

theorem physical_tree (as:List Axis) : PhysicalTree (tree (counts as)) as := by
 induction as with
 | nil =>
   intro L n depth count x st s hlen hh hc cur _ hf hpc hs
   exact physical_leaf L n depth count x st s hlen hh hc cur hf hpc hs
 | cons a as ih =>
   intro L n depth count x st s hlen hh hc cur hb hf hpc hs
   obtain ⟨entry,eh,ec,ep,er,eb,et,ei,eBefore,epc,heap⟩:=enter_actual a as L n depth count x st s
     hlen hh hc cur hb hpc hs
   have banks:Banks (a::as) depth L (entered s):=banks_transfer (a::as) depth L s _
     (by omega) hb (fun j _=>congrFun heap j)
   obtain ⟨loop,e⟩:=physical_children (tree (counts as)) as ih a L n depth count 0
     a.geometry.widths.length x st (entered s) hlen eh ec ep banks ⟨hf.1,hf.2.1⟩ (by omega)
     hf.2.2 ei (by simpa using eBefore) eb et er epc entry.final_bound
   change BoundedRuns program n x L.B s (12+a.geometry.widths.length*(treeCost (counts as)+48))
     (children (tree (counts as)) a.geometry.widths.length (entered s)) ∧ _
   refine ⟨by simpa only [show 11+(1+a.geometry.widths.length*(treeCost (counts as)+48))=
       12+a.geometry.widths.length*(treeCost (counts as)+48) by omega] using entry.trans loop,?_,⟩
   refine ⟨e.pc,e.header,e.constants,e.cursor,(blocks_frame s).2.2.2.1.trans e.frame,?_,?_⟩
   · intro j hstack hout
     exact (e.natFrame j hstack hout).trans (congrFun heap j)
   · rw [states_cons]
     exact e.directory

theorem sector_count_le_volume (as:List Axis) : (counts as).prod ≤ volume as := by
 induction as with
 | nil =>rfl
 | cons a as ih =>
   have h:=UniformTraversal.block_count_le_sum a.geometry.widths (by
     intro q hq
     rcases a.geometry.widths_one_two q hq with h|h <;> omega)
   exact Nat.mul_le_mul h ih

theorem runtime_bound (as:List Axis) :
 treeCost (counts as)+10*as.length+16 ≤ 130*volume as+16 := by
 have nodes:=UniformSectorPacking.block_traversal_prefix_bound (axes as)
 rw [UniformTraversal.run_visits,UniformSectorPacking.blockLayers_radices] at nodes
 change UniformTraversal.nodeCount (counts as)<2*volume as at nodes
 have balance:=treeCost_balance (counts as)
 have length:=axis_count_bound as
 omega

theorem initialized_properties (L:Layout) (s:State) (hh:Header L s) (hc:Constants s)
 (hd:s.natReg 460=0) : Header L (initialized s) ∧Constants (initialized s) ∧
 Cursor 0 0 UniformSectorPacking.initialBlockState (initialized s) ∧
 (initialized s).pc=23 ∧(initialized s).natHeap=s.natHeap := by
 refine ⟨hh.transport L s _ (blocks_frame s).2.2.1,
   body_constants treeBoot (setPC s 19) hc (by decide),?_,?_,?_⟩
 · constructor <;> simp [initialized,setPC,applyBlock,treeBoot,Op.apply,writeNat,next,
     UniformSectorPacking.initialBlockState,hd]
 · rw [initialized,applyBlock_pc,treeBoot_length];rfl
 · simp [initialized,setPC,applyBlock,treeBoot,Op.apply,writeNat,next]

/-- Only the suffix bank, stack, and actual directory are writable. -/
def OutsideAllocation (L:Layout) (sectors:ℕ) (s t:State) : Prop :=
 ∀j,(j<L.suffix ∨L.suffix+L.ell+1 ≤ j)→
   (j<L.stack ∨L.stack+L.ell*5 ≤ j)→
   (j<L.directory ∨L.directory+sectors*3 ≤ j)→t.natHeap j=s.natHeap j

/-- The single literal program computes suffix volumes, traverses the physical
block tables, emits the exact lexicographic sector directory, and halts.
No computed suffix, sector directory, traversal safety or action certificate
is an entry premise. Physical axis rows and width cells are the input. -/
theorem execution (as:List Axis) (L:Layout) (n:ℕ) (x:Fin n→ℂ) (s:State)
 (hlen:as.length=L.ell) (hvolume:volume as=L.total) (hh:Header L s)
 (hr:Rows as 0 L.rows s) (hw:Widths as s)
 (hbelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ L.suffix)
 (hpc:s.pc=0) (hs:WordBound L.B s) : ∃t,
 BoundedExecution program n x L.B s (treeCost (counts as)+10*L.ell+16) t ∧
 t.pc=91 ∧Header L t ∧Constants t ∧Cursor 0 (counts as).prod UniformSectorPacking.initialBlockState t ∧
 Directory L 0 (UniformSectorPacking.sectorStates (axes as)) t ∧
 WrittenSuffix as L 0 t ∧OutsideAllocation L (counts as).prod s t ∧Frame s t := by
 obtain ⟨u,scan,suffix,depth,product,pc,const,header,foot,frame⟩:=
   suffix_preparation as L n x s hlen hvolume hh hr hpc hs
 let v:=setPC u 19
 have vb:WordBound L.B v:=changePC_bound L.B u 19 scan.final_bound (by have h:=L.code;omega)
 have exit:BoundedRuns program n x L.B u 1 v:=.next scan.final_bound
   (by simp [step,pc,suffix_branch,const.1,depth,v,setPC]) (.refl vb)
 have boot:BoundedRuns program n x L.B v 4 (initialized u):=by
   exact block_runs treeBoot program 19 n L.B x v treeBoot_code rfl vb
     (by rw [treeBoot_length];have h:=L.code;omega)
     (by simp [readable,treeBoot,Op.readable])
     (by simp [peak,treeBoot,Op.peak];have h:=L.code;omega)
 obtain ⟨ih,ic,cur,ipc,heap⟩:=initialized_properties L u header const depth
 have low:∀j,j<L.suffix→(initialized u).natHeap j=s.natHeap j:=by
   intro j hj
   exact (congrFun heap j).trans (foot j (Or.inl hj))
 have rows:Rows as 0 L.rows (initialized u):=rows_transfer as 0 L s _ (by omega) hr low
 have widths:Widths as (initialized u):=widths_transfer as L s _ hw hbelow low
 have banks:Banks as 0 L (initialized u):=by
   refine ⟨rows,widths,hbelow,?_⟩
   intro j hj
   rw [congrFun heap]
   simpa only [Nat.add_zero] using suffix j (by omega) hj
 have fits:Fits as UniformSectorPacking.initialBlockState 0 L:=by
   refine ⟨?_,?_,?_⟩
   · simp only [UniformSectorPacking.initialBlockState,Nat.one_mul,Nat.zero_add,hvolume];exact Nat.le_refl _
   · simp only [UniformSectorPacking.initialBlockState,Nat.zero_add,hlen];exact Nat.le_refl _
   · simpa only [Nat.zero_add,hvolume] using sector_count_le_volume as
 obtain ⟨run,e⟩:=physical_tree as L n 0 0 x UniformSectorPacking.initialBlockState
   (initialized u) (by omega) ih ic cur banks fits ipc boot.final_bound
 let t:=setPC (tree (counts as) (initialized u)) 91
 have tb:WordBound L.B t:=changePC_bound L.B _ 91 run.final_bound (by have h:=L.code;omega)
 have stop:¬(tree (counts as) (initialized u)).natReg 455<
     (tree (counts as) (initialized u)).natReg 460:=by rw [e.constants.1,e.cursor.depth];omega
 have finish:BoundedRuns program n x L.B (tree (counts as) (initialized u)) 1 t:=.next run.final_bound
   (by rw [step,e.pc,pop_branch];simp only [ite_eq_right stop];rfl) (.refl tb)
 have halt:BoundedExecution program n x L.B t 1 t:=.halt tb (by rw [step];simp [t,setPC,halt_at])
 refine ⟨t,?_,rfl,header_setPC L _ 91 e.header,constants_setPC _ 91 e.constants,?_,?_,?_,?_,?_,⟩
 · convert scan.executes (exit.executes (boot.executes (run.executes (finish.executes halt)))) using 1
   omega
 · simpa only [Nat.zero_add] using cursor_setPC 0 (0+(counts as).prod)
     UniformSectorPacking.initialBlockState _ 91 e.cursor
 · apply directory_transfer L 0 _ (tree (counts as) (initialized u)) t ?_ (fun _ _ _=>rfl)
   rw [←UniformSectorTraversalOrder.block_lex_sectorStates]
   exact e.directory
 · intro j h0 h1
   change (tree (counts as) (initialized u)).natHeap (L.suffix+j)=some (volume (as.drop j))
   rw [e.natFrame _ (Or.inl (by have h:=L.suffixBelow;omega))
       (Or.inl (by have h:=L.suffixBelow;have h':=L.stackBelow;omega)),congrFun heap]
   exact suffix j h0 h1
 · intro j hSuffix hStack hDir
   change (tree (counts as) (initialized u)).natHeap j=s.natHeap j
   rw [e.natFrame j (by simpa only [Nat.zero_mul,Nat.add_zero] using hStack)
     (by simpa only [Nat.zero_add,Nat.zero_mul,Nat.add_zero] using hDir),congrFun heap]
   exact foot j hSuffix
 · exact frame.trans ((blocks_frame u).2.2.1.trans e.frame)

theorem execution_cost (as:List Axis) (L:Layout) (hlen:as.length=L.ell) (hvol:volume as=L.total) :
 treeCost (counts as)+10*L.ell+16 ≤ 130*L.total+16 := by
 simpa only [hlen,hvol] using runtime_bound as

theorem protected_prefix (as:List Axis) (L:Layout) (s t:State)
 (h:OutsideAllocation L (counts as).prod s t) (i:ℕ) (hi:i<L.suffix) : t.natHeap i=s.natHeap i :=
 h i (Or.inl hi) (Or.inl (by have b:=L.suffixBelow;omega))
   (Or.inl (by have b:=L.suffixBelow;have b':=L.stackBelow;omega))

theorem saved_registers (s t:State) (h:Frame s t) (i:ℕ) (hi:100 ≤ i ∧i ≤ 106) :
 t.natReg i=s.natReg i := h.2.2.2.2 i (Or.inl (by omega))

/-- The fresh banks fit a linear allocation envelope. Existing dirty state
words still have the same caller-supplied WordBound B. -/
def wordBudget (sourceEnd:ℕ) (as:List Axis) : ℕ :=
 sourceEnd+6*as.length+3*volume as+93
theorem wordBudget_linear (sourceEnd:ℕ) (as:List Axis) :
 wordBudget sourceEnd as ≤ sourceEnd+9*volume as+93 := by
 have h:=axis_count_bound as
 unfold wordBudget
 omega

def allocatedLayout (as:List Axis) (rows sourceEnd B:ℕ)
 (hr:rows+3*as.length ≤ sourceEnd) (hB:wordBudget sourceEnd as ≤ B) : Layout where
 ell:=as.length
 rows:=rows
 suffix:=sourceEnd
 stack:=sourceEnd+as.length+1
 directory:=sourceEnd+6*as.length+1
 total:=volume as
 B:=B
 code:=by unfold wordBudget at hB;omega
 rowsBelow:=hr
 suffixBelow:=by omega
 stackBelow:=by omega
 directoryBound:=by unfold wordBudget at hB;omega
 volumeBound:=by unfold wordBudget at hB;omega

/-- Fixed code has only natural arithmetic, physical Nat reads/writes,
natural branches, jumps and halt. Scalars and data flags are untouched. -/
def natOnly : Instruction→Bool
 | .natLiteral _ _ | .natBinary _ _ _ _ | .loadNat _ _ | .storeNat _ _ |
   .branchLT _ _ _ _ | .jump _ | .halt=>true
 | _=>false
theorem no_scalar_input_root_output : ∀i∈program,natOnly i=true := by decide

end
end ExactFourierCircuits.UniformSectorMetadataMachine
