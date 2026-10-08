import UniformBlockXorMachine
import UniformBinaryXorCoordinates
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRepeatedMaskMachine
open UniformMachine
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def setPC (s : State) (p : ℕ) : State := {s with pc:=p}
def boot : List Op := [.literal 3371 0,.literal 3372 2,.literal 3373 1,
 .literal 3374 0,.literal 3375 1,.binary .mul 3378 3368 3369]
def body : List Op := [.binary .mod 3376 3374 3369,.binary .add 3377 3370 3376,.load 3376 3377,
 .binary .mul 3377 3375 3376,.binary .add 3371 3371 3377,
 .binary .mul 3375 3375 3372,.binary .add 3374 3374 3373]
/-- Repeated original-width direction is constructed from real printed bits.
There is no mask or copied vector supplied at entry. -/
def program : Program := boot.map Op.code++[.branchLT 3374 3378 7 15]++body.map Op.code++[.jump 6,.halt]
lemma program_length : program.length=16 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i < 6 at hi;interval_cases i <;> rfl
lemma body_code : BlockAt body program 7 := by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
lemma branch_at : program[6]?=some (.branchLT 3374 3378 7 15) := rfl
lemma jump_at : program[14]?=some (.jump 6) := rfl
lemma halt_at : program[15]?=some .halt := rfl
open BinaryFrames
open scoped BigOperators

def bits {w : ℕ} (u : Vec (Fin w)) (j : ℕ) : ℕ := if h:j < w then (u ⟨j,h⟩).val else 0
lemma bits_lt {w : ℕ} (u : Vec (Fin w)) (j : ℕ) : bits u j < 2 := by
 unfold bits
 split
 · exact ZMod.val_lt _
 · omega
def maskPrefix {w : ℕ} (u : Vec (Fin w)) (k : ℕ) : ℕ := ∑i∈Finset.range k,2^i*bits u (i%w)
lemma maskPrefix_zero {w : ℕ} (u : Vec (Fin w)) : maskPrefix u 0=0 := by simp [maskPrefix]
lemma maskPrefix_succ {w : ℕ} (u : Vec (Fin w)) (k : ℕ) :
 maskPrefix u (k+1)=maskPrefix u k+2^k*bits u (k%w) := by simp [maskPrefix,Finset.sum_range_succ]
lemma maskPrefix_lt {w : ℕ} (u : Vec (Fin w)) (k : ℕ) : maskPrefix u k < 2^k := by
 induction k with
 | zero => simp [maskPrefix_zero]
 | succ k ih =>
   rw [maskPrefix_succ,Nat.pow_succ]
   have bit : bits u (k%w) ≤ 1 := by have h:=bits_lt u (k%w);omega
   have le:=Nat.mul_le_mul_left (2^k) bit
   simp only [Nat.mul_one] at le
   omega
lemma maskPrefix_direction (q w : ℕ) (u : Vec (Fin w)) :
 maskPrefix u (q*w)=(UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).val := by
 rw [UniformBinaryXorCoordinates.encode_value]
 have point (i : Fin (q*w)) : (ColumnTerminalFlat.direction q u i).val=bits u (i.val%w) := by
  have wp : 0 < w := by have h:=i.isLt;nlinarith only [h]
  have rem:=Nat.mod_lt i.val wp
  simp [bits,rem,ColumnTerminalFlat.direction,StageFrames.coordinates,BinaryColumns.globalDirection,finProdFinEquiv]
  congr 2
 calc
  maskPrefix u (q*w)=∑i:Fin (q*w),2^i.val*bits u (i.val%w) := by
   exact (Fin.sum_univ_eq_sum_range (fun i=>2^i*bits u (i%w)) (q*w)).symm
  _=∑i:Fin (q*w),2^i.val*(ColumnTerminalFlat.direction q u i).val := by
   apply Finset.sum_congr rfl
   intro i _
   rw [point]

structure Control (q w A i : ℕ) {u : Vec (Fin w)} (s : State) : Prop where
 pc : s.pc=6
 columns : s.natReg 3368=q
 width : s.natReg 3369=w
 source : s.natReg 3370=A
 mask : s.natReg 3371=maskPrefix u i
 two : s.natReg 3372=2
 one : s.natReg 3373=1
 index : s.natReg 3374=i
 place : s.natReg 3375=2^i
 length : s.natReg 3378=q*w

def Source {w : ℕ} (A : ℕ) (u : Vec (Fin w)) (s : State) := ∀i:Fin w,s.natHeap (A+i.val)=some (u i).val
structure Frame (s t : State) : Prop where
 natHeap : t.natHeap=s.natHeap
 scalarHeap : t.scalarHeap=s.scalarHeap
 scalarReg : t.scalarReg=s.scalarReg
 outputs : t.outputs=s.outputs
 roots : t.rootOrders=s.rootOrders
 natReg : ∀r,r < 3371 ∨ 3379 ≤ r → t.natReg r=s.natReg r
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s t v : State} (f : Frame s t) (g : Frame t v) : Frame s v :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
 g.outputs.trans f.outputs,g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma Frame.pc {s t : State} (f : Frame s t) (p : ℕ) : Frame s (setPC t p) :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma frame_boot (s : State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h
 simp (disch:=omega) [boot,applyBlock,Op.apply,evalNat,writeNat,next]
lemma frame_body (s : State) : Frame s (applyBlock body s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h
 simp (disch:=omega) [body,applyBlock,Op.apply,evalNat,writeNat,next]

lemma iteration (q w A i B n : ℕ) (u : Vec (Fin w)) (x : Fin n → ℂ) (s : State)
 (c : Control q w A i (u:=u) s) (src : Source A u s) (hi : i < q*w)
 (hs : WordBound B s) (code : 16 ≤ B) (sourceEnd : A+w ≤ B) (volume : 2^(q*w) ≤ B) : ∃t,
 BoundedRuns program n x B s 9 t ∧ Control q w A (i+1) (u:=u) t ∧ Frame s t := by
 have wp : 0 < w := by nlinarith only [hi]
 have rem:=Nat.mod_lt i wp
 have load : s.natHeap (A+i%w)=some (bits u (i%w)) := by simpa [bits,rem] using src ⟨i%w,rem⟩
 have mb:=maskPrefix_lt u (i+1)
 have nextBound : 2^(i+1) ≤ 2^(q*w) := Nat.pow_le_pow_right (by decide) (by omega)
 have lengthBound : q*w ≤ B := by
  have ll : q*w < 2^(q*w) := Nat.lt_two_pow_self
  omega
 let enter:=setPC s 7
 have eb:=changePC_bound B s 7 hs (by omega)
 have br : BoundedRuns program n x B s 1 enter:=.next hs
  (by simp [step,c.pc,branch_at,c.index,c.length,hi,enter,setPC]) (.refl eb)
 have safe : readable body enter∧peak body enter ≤ B := by
  have bitBound:=bits_lt u (i%w)
  have term : 2^i*bits u (i%w) ≤ maskPrefix u (i+1) := by rw [maskPrefix_succ];omega
  rw [maskPrefix_succ] at mb
  simp [body,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,enter,setPC,
   c.width,c.source,c.mask,c.two,c.one,c.index,c.place,wp.ne',load]
  rw [Nat.pow_succ] at nextBound
  omega
 have bd:=block_runs body program 7 n B x enter body_code rfl eb (by change 14 ≤ B;omega) safe.1 safe.2
 let ready:=applyBlock body enter
 let t:=setPC ready 6
 have tb:=changePC_bound B ready 6 bd.final_bound (by omega)
 have jump : BoundedRuns program n x B ready 1 t:=.next bd.final_bound
  (by simp [step,ready,body,applyBlock,Op.apply,evalNat,writeNat,next,enter,setPC,jump_at,t]) (.refl tb)
 have ct : Control q w A (i+1) (u:=u) t := by
  constructor <;> simp [t,setPC,ready,body,applyBlock,Op.apply,evalNat,writeNat,next,enter,
   c.columns,c.width,c.source,c.mask,c.two,c.one,c.index,c.place,c.length,wp.ne',load,maskPrefix_succ,Nat.pow_succ]
 refine ⟨t,?_,ct,(Frame.refl s).pc 7 |>.trans (frame_body enter) |>.pc 6⟩
 convert br.trans (bd.trans jump) using 1
 rfl
lemma loop_execution (q w A i fuel B n : ℕ) (u : Vec (Fin w)) (x : Fin n → ℂ) (s : State)
 (c : Control q w A i (u:=u) s) (src : Source A u s) (total : i+fuel=q*w)
 (hs : WordBound B s) (code : 16 ≤ B) (sourceEnd : A+w ≤ B) (volume : 2^(q*w) ≤ B) : ∃t,
 BoundedExecution program n x B s (9*fuel+2) t ∧ t.pc=15 ∧
 t.natReg 3371=maskPrefix u (q*w) ∧ t.natReg 3375=2^(q*w) ∧ Frame s t := by
 induction fuel generalizing i s with
 | zero =>
   have eq : i=q*w:=by omega
   let t:=setPC s 15
   have tb:=changePC_bound B s 15 hs (by omega)
   refine ⟨t,.next hs ?_ (.halt tb ?_),rfl,?_,?_,(Frame.refl s).pc 15⟩
   · simp [step,c.pc,branch_at,c.index,c.length,eq,t,setPC]
   · simp [step,t,setPC,halt_at]
   · simpa [t,setPC,eq] using c.mask
   · simpa [t,setPC,eq] using c.place
 | succ fuel ih =>
   obtain ⟨v,rv,cv,fv⟩:=iteration q w A i B n u x s c src (by omega) hs code sourceEnd volume
   have sv : Source A u v:=by simpa only [Source,fv.natHeap] using src
   obtain ⟨t,rt,pt,mask,place,ft⟩:=ih (i+1) v cv sv (by omega) rv.final_bound
   refine ⟨t,?_,pt,mask,place,fv.trans ft⟩
   convert rv.executes rt using 1
   ring

/-- The prepared mask and volume are both computed physically from q/width and
actual descriptor cells. Zero width or zero columns are supported. -/
theorem execution (q w A B n : ℕ) (u : Vec (Fin w)) (x : Fin n → ℂ) (s : State)
 (pc : s.pc=0) (columns : s.natReg 3368=q) (width : s.natReg 3369=w) (source : s.natReg 3370=A)
 (src : Source A u s) (hs : WordBound B s) (code : 16 ≤ B) (sourceEnd : A+w ≤ B) (volume : 2^(q*w) ≤ B) : ∃t,
 BoundedExecution program n x B s (9*(q*w)+8) t ∧ t.pc=15 ∧
 t.natReg 3371=(UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).val ∧
 t.natReg 3375=2^(q*w) ∧ Frame s t := by
 have lengthBound : q*w ≤ B:=by
  have ll : q*w<2^(q*w):=Nat.lt_two_pow_self
  omega
 have start:=block_runs boot program 0 n B x s boot_code pc hs (by change 6 ≤ B;omega)
  (by simp [boot,readable,Op.readable,evalNat])
  (by simp [boot,peak,Op.peak,Op.apply,evalNat,writeNat,next,columns,width];omega)
 let v:=applyBlock boot s
 have c : Control q w A 0 (u:=u) v:=by
  constructor <;> simp [v,boot,applyBlock,Op.apply,evalNat,writeNat,next,pc,columns,width,source,maskPrefix_zero]
 have sv : Source A u v:=src
 obtain ⟨t,rt,pt,mask,place,ft⟩:=loop_execution q w A 0 (q*w) B n u x v c sv (by omega) start.final_bound code sourceEnd volume
 refine ⟨t,?_,pt,mask.trans (maskPrefix_direction q w u),place,(frame_boot s).trans ft⟩
 convert start.executes rt using 1
 simp only [boot,List.length_cons,List.length_nil]
 omega
end
end ExactFourierCircuits.UniformRepeatedMaskMachine

